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
import NominalWPPReplayChunk009StructuralPart051


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

noncomputable def g_nnpw1ex
    (n : Var) (M : Class) (a : Var) (dv_M_a : a ∉ M.fv) (dv_M_n : n ∉ M.fv) (dv_a_n : a ≠ n) :
    Nominal.NPrf (.imp (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wreu n (syn_cnnc) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n))))) := by
  let proofSupport : Finset Var := ({n} : Finset Var) ∪ M.fv ∪ ({a} : Finset Var)
  let p : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let q : Var := freshVar proofSupport 2
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_ne_n : p ≠ n := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_p : n ≠ p :=
    Ne.symm fresh_p_ne_n
  have fresh_p_not_M : p ∉ M.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_ne_a : p ≠ a := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_a_ne_p : a ≠ p :=
    Ne.symm fresh_p_ne_a
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_ne_n : b ≠ n := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_b : n ≠ b :=
    Ne.symm fresh_b_ne_n
  have fresh_b_not_M : b ∉ M.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_ne_a : b ≠ a := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_a_ne_b : a ≠ b :=
    Ne.symm fresh_b_ne_a
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_q_ne_n : q ≠ n := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_q : n ≠ q :=
    Ne.symm fresh_q_ne_n
  have fresh_q_not_M : q ∉ M.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_ne_a : q ≠ a := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_a_ne_q : a ≠ q :=
    Ne.symm fresh_q_ne_a
  have fresh_p_ne_b : p ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_p : b ≠ p :=
    Ne.symm fresh_p_ne_b
  have fresh_p_ne_q : p ≠ q := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_q_ne_p : q ≠ p :=
    Ne.symm fresh_p_ne_q
  have fresh_b_ne_q : b ≠ q := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_q_ne_b : q ≠ b :=
    Ne.symm fresh_b_ne_q
  have p0000 :=
    @g_ncfinraise (.cv a) (.cv a) n M (by exact (show n ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show n ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show n ≠ a from (by exact Ne.symm dv_a_n))))))) (by exact (show n ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show n ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show n ≠ a from (by exact Ne.symm dv_a_n)))))))
  have p0001 :=
    @g_anidm (.classMem (syn_cpw1 (.cv a)) (.cv n))
  have p0002 :=
    @g_rexbii (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv a)) (.cv n))) (.classMem (syn_cpw1 (.cv a)) (.cv n)) n (syn_cnnc) p0001
  have p0003 :=
    @g_sylib (syn_w3a (.classMem M (syn_cnnc)) (.classMem (.cv a) M) (.classMem (.cv a) M)) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv a)) (.cv n)))) (syn_wrex n (syn_cnnc) (.classMem (syn_cpw1 (.cv a)) (.cv n))) p0000 p0002
  have p0004 :=
    @g_n_3anidm23 (.classMem M (syn_cnnc)) (.classMem (.cv a) M) (syn_wrex n (syn_cnnc) (.classMem (syn_cpw1 (.cv a)) (.cv n))) p0003
  have p0005 :=
    @g_ex (.classMem M (syn_cnnc)) (.classMem (.cv a) M) (syn_wrex n (syn_cnnc) (.classMem (syn_cpw1 (.cv a)) (.cv n))) p0004
  have p0006 :=
    @g_ancld (.classMem M (syn_cnnc)) (.classMem (.cv a) M) (syn_wrex n (syn_cnnc) (.classMem (syn_cpw1 (.cv a)) (.cv n))) p0005
  have p0007 :=
    @g_eximdv (.classMem M (syn_cnnc)) (.classMem (.cv a) M) (syn_wa (.classMem (.cv a) M) (syn_wrex n (syn_cnnc) (.classMem (syn_cpw1 (.cv a)) (.cv n)))) a (by exact (show a ∉ ((Wff.classMem M (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show a ∉ ((M).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (M).fv from (by exact dv_M_a)) (show a ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0006
  have p0008 :=
    @g_imp (.classMem M (syn_cnnc)) (syn_wex a (.classMem (.cv a) M)) (syn_wex a (syn_wa (.classMem (.cv a) M) (syn_wrex n (syn_cnnc) (.classMem (syn_cpw1 (.cv a)) (.cv n))))) p0007
  have p0009 :=
    @g_n0 a M (by exact (show a ∉ (M).fv from (by exact dv_M_a)))
  have p0010 :=
    @g_anbi2i (syn_wne M (syn_c0)) (syn_wex a (.classMem (.cv a) M)) (.classMem M (syn_cnnc)) p0009
  have p0011 :=
    @g_rexcom (.classMem (syn_cpw1 (.cv a)) (.cv n)) n a (syn_cnnc) M (by exact (show a ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show n ∉ (M).fv from (by exact dv_M_n))) (show n ≠ a from (by exact Ne.symm dv_a_n))
  have p0012 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex a M (syn_wrex n (syn_cnnc) (.classMem (syn_cpw1 (.cv a)) (.cv n))))))
  have p0013 :=
    @g_bitri (syn_wrex n (syn_cnnc) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n)))) (syn_wrex a M (syn_wrex n (syn_cnnc) (.classMem (syn_cpw1 (.cv a)) (.cv n)))) (syn_wex a (syn_wa (.classMem (.cv a) M) (syn_wrex n (syn_cnnc) (.classMem (syn_cpw1 (.cv a)) (.cv n))))) p0011 p0012
  have p0014 :=
    @g_n_3imtr4i (syn_wa (.classMem M (syn_cnnc)) (syn_wex a (.classMem (.cv a) M))) (syn_wex a (syn_wa (.classMem (.cv a) M) (syn_wrex n (syn_cnnc) (.classMem (syn_cpw1 (.cv a)) (.cv n))))) (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wrex n (syn_cnnc) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n)))) p0008 p0010 p0013
  have p0015 :=
    @g_pw1eq (.cv a) (.cv b)
  have p0016_e00_recanon : Nominal.NPrf (.imp (.objEq a b) (.classEq (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cpw syn_wss syn_c1c syn_wex syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0015
  have p0016 :=
    @g_eleq1d (.objEq a b) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)) (.cv p) p0016_e00_recanon
  have p0017 :=
    @g_cbvrexv (.classMem (syn_cpw1 (.cv a)) (.cv p)) (.classMem (syn_cpw1 (.cv b)) (.cv p)) a b M (by exact (show a ∉ (M).fv from (by exact dv_M_a))) (by exact (show b ∉ (M).fv from (by exact fresh_b_not_M))) (by exact (show b ∉ ((Wff.classMem (syn_cpw1 (.cv a)) (.cv p))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ (((syn_cpw1 (.cv a))).fv) ∪ (((Class.cv p)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_cpw1 (.cv a))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show b ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ a from (by exact fresh_b_ne_a)))))))) (show b ∉ ((Class.cv p)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({p} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ p from (by exact fresh_b_ne_p))))))))))) (by exact (show a ∉ ((Wff.classMem (syn_cpw1 (.cv b)) (.cv p))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show a ∉ (((syn_cpw1 (.cv b))).fv) ∪ (((Class.cv p)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((syn_cpw1 (.cv b))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show a ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ b from (by exact fresh_a_ne_b)))))))) (show a ∉ ((Class.cv p)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({p} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ p from (by exact fresh_a_ne_p))))))))))) p0016
  have p0018 :=
    @g_anbi2i (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv p))) (syn_wrex b M (.classMem (syn_cpw1 (.cv b)) (.cv p))) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n))) p0017
  have p0019 :=
    @g_reeanv (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p)) a b M M (by exact (show b ∉ (M).fv from (by exact fresh_b_not_M))) (by exact (show a ∉ (M).fv from (by exact dv_M_a))) (by exact (show b ∉ ((Wff.classMem (syn_cpw1 (.cv a)) (.cv n))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ (((syn_cpw1 (.cv a))).fv) ∪ (((Class.cv n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_cpw1 (.cv a))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show b ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ a from (by exact fresh_b_ne_a)))))))) (show b ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ n from (by exact fresh_b_ne_n))))))))))) (by exact (show a ∉ ((Wff.classMem (syn_cpw1 (.cv b)) (.cv p))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show a ∉ (((syn_cpw1 (.cv b))).fv) ∪ (((Class.cv p)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((syn_cpw1 (.cv b))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show a ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ b from (by exact fresh_a_ne_b)))))))) (show a ∉ ((Class.cv p)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({p} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ p from (by exact fresh_a_ne_p))))))))))) (show a ≠ b from (by exact fresh_a_ne_b))
  have p0020 :=
    @g_bitr4i (syn_wa (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n))) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv p)))) (syn_wa (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n))) (syn_wrex b M (.classMem (syn_cpw1 (.cv b)) (.cv p)))) (syn_wrex a M (syn_wrex b M (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p))))) p0018 p0019
  have p0021 :=
    @g_simplll (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc))) (syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p))))
  have p0022 :=
    @g_simprll (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)))) (.classMem (.cv a) M) (.classMem (.cv b) M) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p)))
  have p0023 :=
    @g_simprlr (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)))) (.classMem (.cv a) M) (.classMem (.cv b) M) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p)))
  have p0024 :=
    @g_ncfinraise (.cv a) (.cv b) q M (by exact (show q ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show q ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show q ≠ a from (by exact fresh_q_ne_a))))))) (by exact (show q ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show q ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show q ≠ b from (by exact fresh_q_ne_b)))))))
  have p0025 :=
    @g_syl3anc (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)))) (syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p))))) (.classMem M (syn_cnnc)) (.classMem (.cv a) M) (.classMem (.cv b) M) (syn_wrex q (syn_cnnc) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv q)) (.classMem (syn_cpw1 (.cv b)) (.cv q)))) p0021 p0022 p0023 p0024
  have p0026 :=
    @g_simp1rl (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)) (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p)))) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv q)) (.classMem (syn_cpw1 (.cv b)) (.cv q))))
  have p0027 :=
    @g_simp3l (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)))) (syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p)))) (.classMem (.cv q) (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv q)) (.classMem (syn_cpw1 (.cv b)) (.cv q)))
  have p0028 :=
    @g_simp2rl (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p)) (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M)) (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)))) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv q)) (.classMem (syn_cpw1 (.cv b)) (.cv q))))
  have p0029 :=
    @g_simp3rl (.classMem (syn_cpw1 (.cv a)) (.cv q)) (.classMem (syn_cpw1 (.cv b)) (.cv q)) (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)))) (syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p))))
  have p0030 :=
    @g_nnceleq (syn_cpw1 (.cv a)) (.cv n) (.cv q)
  have p0031_e04_recanon : Nominal.NPrf (.imp (syn_wa (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv q) (syn_cnnc))) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv a)) (.cv q)))) (.objEq n q)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0030
  have p0031 :=
    @g_syl22anc (syn_w3a (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)))) (syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p)))) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv q)) (.classMem (syn_cpw1 (.cv b)) (.cv q))))) (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv a)) (.cv q)) (.objEq n q) p0026 p0027 p0028 p0029 p0031_e04_recanon
  have p0032 :=
    @g_simp1rr (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)) (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p)))) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv q)) (.classMem (syn_cpw1 (.cv b)) (.cv q))))
  have p0033 :=
    @g_simp2rr (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p)) (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M)) (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)))) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv q)) (.classMem (syn_cpw1 (.cv b)) (.cv q))))
  have p0034 :=
    @g_simp3rr (.classMem (syn_cpw1 (.cv a)) (.cv q)) (.classMem (syn_cpw1 (.cv b)) (.cv q)) (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)))) (syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p))))
  have p0035 :=
    @g_nnceleq (syn_cpw1 (.cv b)) (.cv p) (.cv q)
  have p0036_e04_recanon : Nominal.NPrf (.imp (syn_wa (syn_wa (.classMem (.cv p) (syn_cnnc)) (.classMem (.cv q) (syn_cnnc))) (syn_wa (.classMem (syn_cpw1 (.cv b)) (.cv p)) (.classMem (syn_cpw1 (.cv b)) (.cv q)))) (.objEq p q)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0035
  have p0036 :=
    @g_syl22anc (syn_w3a (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)))) (syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p)))) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv q)) (.classMem (syn_cpw1 (.cv b)) (.cv q))))) (.classMem (.cv p) (syn_cnnc)) (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cpw1 (.cv b)) (.cv p)) (.classMem (syn_cpw1 (.cv b)) (.cv q)) (.objEq p q) p0032 p0027 p0033 p0034 p0036_e04_recanon
  have p0037_e00_recanon : Nominal.NPrf (.imp (syn_w3a (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)))) (syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p)))) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv q)) (.classMem (syn_cpw1 (.cv b)) (.cv q))))) (.classEq (.cv n) (.cv q))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
      )
      p0031
  have p0037_e01_recanon : Nominal.NPrf (.imp (syn_w3a (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)))) (syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p)))) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv q)) (.classMem (syn_cpw1 (.cv b)) (.cv q))))) (.classEq (.cv p) (.cv q))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
      )
      p0036
  have p0037 :=
    @g_eqtr4d (syn_w3a (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)))) (syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p)))) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv q)) (.classMem (syn_cpw1 (.cv b)) (.cv q))))) (.cv n) (.cv q) (.cv p) p0037_e00_recanon p0037_e01_recanon
  have p0038_e00_recanon : Nominal.NPrf (.imp (syn_w3a (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)))) (syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p)))) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv q)) (.classMem (syn_cpw1 (.cv b)) (.cv q))))) (.objEq n p)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0037
  have p0038 :=
    @g_n_3expa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)))) (syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p)))) (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv q)) (.classMem (syn_cpw1 (.cv b)) (.cv q)))) (.objEq n p) p0038_e00_recanon
  have p0039 :=
    @g_exp32 (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)))) (syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p))))) (.classMem (.cv q) (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv q)) (.classMem (syn_cpw1 (.cv b)) (.cv q))) (.objEq n p) p0038
  have p0040 :=
    @g_rexlimdv (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)))) (syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p))))) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv q)) (.classMem (syn_cpw1 (.cv b)) (.cv q))) (.objEq n p) q (syn_cnnc) (by exact (show q ∉ ((Wff.objEq n p)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]; exact (show q ∉ ({n, p} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show q ≠ n from (by exact fresh_q_ne_n)), (show q ≠ p from (by exact fresh_q_ne_p))⟩))))) (by exact (show q ∉ ((syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)))) (syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show q ∉ (((syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc))))).fv) ∪ (((syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show q ∉ ((syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show q ∉ (((syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))).fv) ∪ (((syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show q ∉ ((syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show q ∉ (((Wff.classMem M (syn_cnnc))).fv) ∪ (((syn_wne M (syn_c0))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show q ∉ ((Wff.classMem M (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show q ∉ ((M).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show q ∉ (M).fv from (by exact fresh_q_not_M)) (show q ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show q ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show q ∉ ((syn_wne M (syn_c0))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne]; exact (show q ∉ ((M).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show q ∉ (M).fv from (by exact fresh_q_not_M)) (show q ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show q ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (show q ∉ ((syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show q ∉ (((Wff.classMem (.cv n) (syn_cnnc))).fv) ∪ (((Wff.classMem (.cv p) (syn_cnnc))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show q ∉ ((Wff.classMem (.cv n) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show q ∉ (((Class.cv n)).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show q ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show q ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show q ≠ n from (by exact fresh_q_ne_n)))))) (show q ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show q ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show q ∉ ((Wff.classMem (.cv p) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show q ∉ (((Class.cv p)).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show q ∉ ((Class.cv p)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show q ∉ ({p} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show q ≠ p from (by exact fresh_q_ne_p)))))) (show q ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show q ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))))) (show q ∉ ((syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show q ∉ (((syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M))).fv) ∪ (((syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show q ∉ ((syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show q ∉ (((Wff.classMem (.cv a) M)).fv) ∪ (((Wff.classMem (.cv b) M)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show q ∉ ((Wff.classMem (.cv a) M)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show q ∉ (((Class.cv a)).fv) ∪ ((M).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show q ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show q ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show q ≠ a from (by exact fresh_q_ne_a)))))) (show q ∉ (M).fv from (by exact fresh_q_not_M)))))) (show q ∉ ((Wff.classMem (.cv b) M)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show q ∉ (((Class.cv b)).fv) ∪ ((M).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show q ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show q ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show q ≠ b from (by exact fresh_q_ne_b)))))) (show q ∉ (M).fv from (by exact fresh_q_not_M)))))))))) (show q ∉ ((syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show q ∉ (((Wff.classMem (syn_cpw1 (.cv a)) (.cv n))).fv) ∪ (((Wff.classMem (syn_cpw1 (.cv b)) (.cv p))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show q ∉ ((Wff.classMem (syn_cpw1 (.cv a)) (.cv n))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show q ∉ (((syn_cpw1 (.cv a))).fv) ∪ (((Class.cv n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show q ∉ ((syn_cpw1 (.cv a))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show q ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show q ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show q ≠ a from (by exact fresh_q_ne_a)))))))) (show q ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show q ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show q ≠ n from (by exact fresh_q_ne_n)))))))))) (show q ∉ ((Wff.classMem (syn_cpw1 (.cv b)) (.cv p))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show q ∉ (((syn_cpw1 (.cv b))).fv) ∪ (((Class.cv p)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show q ∉ ((syn_cpw1 (.cv b))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show q ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show q ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show q ≠ b from (by exact fresh_q_ne_b)))))))) (show q ∉ ((Class.cv p)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show q ∉ ({p} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show q ≠ p from (by exact fresh_q_ne_p))))))))))))))))))))))) p0039
  have p0041 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)))) (syn_wa (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p))))) (syn_wrex q (syn_cnnc) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv q)) (.classMem (syn_cpw1 (.cv b)) (.cv q)))) (.objEq n p) p0025 p0040
  have p0042 :=
    @g_exp32 (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)))) (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) M)) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p))) (.objEq n p) p0041
  have p0043 :=
    @g_rexlimdvv (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)))) (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p))) (.objEq n p) a b M M (by exact (show b ∉ (M).fv from (by exact fresh_b_not_M))) (by exact (show a ∉ ((Wff.objEq n p)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]; exact (show a ∉ ({n, p} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show a ≠ n from (by exact dv_a_n)), (show a ≠ p from (by exact fresh_a_ne_p))⟩))))) (by exact (show b ∉ ((Wff.objEq n p)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]; exact (show b ∉ ({n, p} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show b ≠ n from (by exact fresh_b_ne_n)), (show b ≠ p from (by exact fresh_b_ne_p))⟩))))) (by exact (show a ∉ ((syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show a ∉ (((syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))).fv) ∪ (((syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show a ∉ (((Wff.classMem M (syn_cnnc))).fv) ∪ (((syn_wne M (syn_c0))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Wff.classMem M (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show a ∉ ((M).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (M).fv from (by exact dv_M_a)) (show a ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show a ∉ ((syn_wne M (syn_c0))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne]; exact (show a ∉ ((M).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (M).fv from (by exact dv_M_a)) (show a ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (show a ∉ ((syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show a ∉ (((Wff.classMem (.cv n) (syn_cnnc))).fv) ∪ (((Wff.classMem (.cv p) (syn_cnnc))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Wff.classMem (.cv n) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show a ∉ (((Class.cv n)).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ n from (by exact dv_a_n)))))) (show a ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show a ∉ ((Wff.classMem (.cv p) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show a ∉ (((Class.cv p)).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Class.cv p)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({p} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ p from (by exact fresh_a_ne_p)))))) (show a ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))))))) (by exact (show b ∉ ((syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show b ∉ (((syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))).fv) ∪ (((syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show b ∉ (((Wff.classMem M (syn_cnnc))).fv) ∪ (((syn_wne M (syn_c0))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Wff.classMem M (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ ((M).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ (M).fv from (by exact fresh_b_not_M)) (show b ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show b ∉ ((syn_wne M (syn_c0))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne]; exact (show b ∉ ((M).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ (M).fv from (by exact fresh_b_not_M)) (show b ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (show b ∉ ((syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show b ∉ (((Wff.classMem (.cv n) (syn_cnnc))).fv) ∪ (((Wff.classMem (.cv p) (syn_cnnc))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Wff.classMem (.cv n) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ (((Class.cv n)).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ n from (by exact fresh_b_ne_n)))))) (show b ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show b ∉ ((Wff.classMem (.cv p) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ (((Class.cv p)).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv p)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({p} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ p from (by exact fresh_b_ne_p)))))) (show b ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))))))) (show a ≠ b from (by exact fresh_a_ne_b)) p0042
  have p0044 :=
    @g_syl5bi (syn_wa (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n))) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv p)))) (syn_wrex a M (syn_wrex b M (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv p))))) (syn_wa (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)))) (.objEq n p) p0020 p0043
  have p0045 :=
    @g_ralrimivva (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (.imp (syn_wa (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n))) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv p)))) (.objEq n p)) n p (syn_cnnc) (syn_cnnc) (by exact (show p ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show p ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show n ∉ ((syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show n ∉ (((Wff.classMem M (syn_cnnc))).fv) ∪ (((syn_wne M (syn_c0))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((Wff.classMem M (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show n ∉ ((M).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ (M).fv from (by exact dv_M_n)) (show n ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show n ∉ ((syn_wne M (syn_c0))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne]; exact (show n ∉ ((M).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ (M).fv from (by exact dv_M_n)) (show n ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (by exact (show p ∉ ((syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show p ∉ (((Wff.classMem M (syn_cnnc))).fv) ∪ (((syn_wne M (syn_c0))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((Wff.classMem M (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show p ∉ ((M).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ (M).fv from (by exact fresh_p_not_M)) (show p ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show p ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show p ∉ ((syn_wne M (syn_c0))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne]; exact (show p ∉ ((M).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ (M).fv from (by exact fresh_p_not_M)) (show p ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show p ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (show n ≠ p from (by exact fresh_n_ne_p)) p0044
  have p0046 :=
    @g_eleq2 (.cv n) (.cv p) (syn_cpw1 (.cv a))
  have p0047_e00_recanon : Nominal.NPrf (.imp (.objEq n p) (syn_wb (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv a)) (.cv p)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cpw syn_wss syn_c1c syn_wex syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0046
  have p0047 :=
    @g_rexbidv (.objEq n p) (.classMem (syn_cpw1 (.cv a)) (.cv n)) (.classMem (syn_cpw1 (.cv a)) (.cv p)) a M (by exact (show a ∉ ((Wff.objEq n p)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]; exact (show a ∉ ({n, p} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show a ≠ n from (by exact dv_a_n)), (show a ≠ p from (by exact fresh_a_ne_p))⟩))))) p0047_e00_recanon
  have p0048 :=
    @g_reu4 (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n))) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv p))) n p (syn_cnnc) (by exact (show n ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show p ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show p ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show p ∉ ((syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex]; exact (show p ∉ (((M).fv).erase a) ∪ ((((Wff.classMem (syn_cpw1 (.cv a)) (.cv n))).fv).erase a) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((M).fv).erase a from (fun hmem => (show p ∉ (M).fv from (by exact fresh_p_not_M)) (Finset.mem_of_mem_erase hmem))) (show p ∉ (((Wff.classMem (syn_cpw1 (.cv a)) (.cv n))).fv).erase a from (fun hmem => (show p ∉ ((Wff.classMem (syn_cpw1 (.cv a)) (.cv n))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show p ∉ (((syn_cpw1 (.cv a))).fv) ∪ (((Class.cv n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show p ∉ ((syn_cpw1 (.cv a))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show p ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show p ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ a from (by exact fresh_p_ne_a)))))))) (show p ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show p ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show p ≠ n from (by exact fresh_p_ne_n)))))))))) (Finset.mem_of_mem_erase hmem)))))))) (by exact (show n ∉ ((syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv p)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex]; exact (show n ∉ (((M).fv).erase a) ∪ ((((Wff.classMem (syn_cpw1 (.cv a)) (.cv p))).fv).erase a) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((M).fv).erase a from (fun hmem => (show n ∉ (M).fv from (by exact dv_M_n)) (Finset.mem_of_mem_erase hmem))) (show n ∉ (((Wff.classMem (syn_cpw1 (.cv a)) (.cv p))).fv).erase a from (fun hmem => (show n ∉ ((Wff.classMem (syn_cpw1 (.cv a)) (.cv p))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show n ∉ (((syn_cpw1 (.cv a))).fv) ∪ (((Class.cv p)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((syn_cpw1 (.cv a))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show n ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show n ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show n ≠ a from (by exact Ne.symm dv_a_n)))))))) (show n ∉ ((Class.cv p)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show n ∉ ({p} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show n ≠ p from (by exact fresh_n_ne_p)))))))))) (Finset.mem_of_mem_erase hmem)))))))) (show n ≠ p from (by exact fresh_n_ne_p)) p0047
  have p0049 :=
    @g_sylanbrc (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_wrex n (syn_cnnc) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n)))) (syn_wral n (syn_cnnc) (syn_wral p (syn_cnnc) (.imp (syn_wa (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n))) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv p)))) (.objEq n p)))) (syn_wreu n (syn_cnnc) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n)))) p0014 p0045 p0048
  exact p0049

noncomputable def g_tfinex
    (A : Class) :
    Nominal.NPrf (.classMem (syn_ctfin A) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_tfin x A y (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (show y ≠ x from (by exact fresh_y_ne_x))
  have p0001 :=
    @g_n_0ex
  have p0002 :=
    @g_iotaex (syn_wa (.classMem (.cv x) (syn_cnnc)) (syn_wrex y A (.classMem (syn_cpw1 (.cv y)) (.cv x)))) x
  have p0003 :=
    @g_ifex (.classEq A (syn_c0)) (syn_c0) (syn_cio x (syn_wa (.classMem (.cv x) (syn_cnnc)) (syn_wrex y A (.classMem (syn_cpw1 (.cv y)) (.cv x))))) p0001 p0002
  have p0004 :=
    @g_eqeltri (syn_ctfin A) (syn_cif (.classEq A (syn_c0)) (syn_c0) (syn_cio x (syn_wa (.classMem (.cv x) (syn_cnnc)) (syn_wrex y A (.classMem (syn_cpw1 (.cv y)) (.cv x)))))) (syn_cvv) p0000 p0003
  exact p0004



#print axioms g_tfinex

end NFChoice.DirectNominalPrf.WPPReplay
