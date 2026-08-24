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
import NominalWPPReplayChunk009StructuralPart002


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

noncomputable def g_opkabssvvk
    (ph : Wff) (x : Var) (y : Var) (z : Var) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) :
    Nominal.NPrf (syn_wss (.cab x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) ph)))) (syn_cxpk (syn_cvv) (syn_cvv))) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var)
  let w : Var := freshVar proofSupport 0
  let t : Var := freshVar proofSupport 1
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_w : y ≠ w :=
    Ne.symm fresh_w_ne_y
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_z_ne_w : z ≠ w :=
    Ne.symm fresh_w_ne_z
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_t_not_ph : t ∉ ph.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_t_ne_x : t ≠ x := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_t : x ≠ t :=
    Ne.symm fresh_t_ne_x
  have fresh_t_ne_y : t ≠ y := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_t : y ≠ t :=
    Ne.symm fresh_t_ne_y
  have fresh_t_ne_z : t ≠ z := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_z_ne_t : z ≠ t :=
    Ne.symm fresh_t_ne_z
  have fresh_w_ne_t : w ≠ t := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_t_ne_w : t ≠ w :=
    Ne.symm fresh_w_ne_t
  have p0000 :=
    @g_eqid (syn_copk (.cv y) (.cv z))
  have p0001 :=
    @g_vex y
  have p0002 :=
    @g_vex z
  have p0003 :=
    @g_opkeq12 (.cv w) (.cv t) (.cv y) (.cv z)
  have p0004_e00_recanon : Nominal.NPrf (.imp (syn_wa (.objEq w y) (.objEq t z)) (.classEq (syn_copk (.cv w) (.cv t)) (syn_copk (.cv y) (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_ccompl syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
      p0003
  have p0004 :=
    @g_eqeq2d (syn_wa (.objEq w y) (.objEq t z)) (syn_copk (.cv w) (.cv t)) (syn_copk (.cv y) (.cv z)) (syn_copk (.cv y) (.cv z)) p0004_e00_recanon
  have p0005_e02_recanon : Nominal.NPrf (.imp (syn_wa (.classEq (.cv w) (.cv y)) (.classEq (.cv t) (.cv z))) (syn_wb (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk (.cv w) (.cv t))) (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk (.cv y) (.cv z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wb syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_ccompl syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0004
  have p0005 :=
    @g_spc2ev (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk (.cv w) (.cv t))) (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk (.cv y) (.cv z))) w t (.cv y) (.cv z) (by exact (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y))))))) (by exact (show t ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ y from (by exact fresh_t_ne_y))))))) (by exact (show w ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ z from (by exact fresh_w_ne_z))))))) (by exact (show t ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ z from (by exact fresh_t_ne_z))))))) (by exact (show w ∉ ((Wff.classEq (syn_copk (.cv y) (.cv z)) (syn_copk (.cv y) (.cv z)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show w ∉ (((syn_copk (.cv y) (.cv z))).fv) ∪ (((syn_copk (.cv y) (.cv z))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((syn_copk (.cv y) (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show w ∉ (((Class.cv y)).fv) ∪ (((Class.cv z)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y)))))) (show w ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ z from (by exact fresh_w_ne_z)))))))))) (show w ∉ ((syn_copk (.cv y) (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show w ∉ (((Class.cv y)).fv) ∪ (((Class.cv z)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y)))))) (show w ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ z from (by exact fresh_w_ne_z))))))))))))))) (by exact (show t ∉ ((Wff.classEq (syn_copk (.cv y) (.cv z)) (syn_copk (.cv y) (.cv z)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show t ∉ (((syn_copk (.cv y) (.cv z))).fv) ∪ (((syn_copk (.cv y) (.cv z))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_copk (.cv y) (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show t ∉ (((Class.cv y)).fv) ∪ (((Class.cv z)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ y from (by exact fresh_t_ne_y)))))) (show t ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ z from (by exact fresh_t_ne_z)))))))))) (show t ∉ ((syn_copk (.cv y) (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show t ∉ (((Class.cv y)).fv) ∪ (((Class.cv z)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ y from (by exact fresh_t_ne_y)))))) (show t ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ z from (by exact fresh_t_ne_z))))))))))))))) (show w ≠ t from (by exact fresh_w_ne_t)) p0001 p0002 p0005_e02_recanon
  have p0006 :=
    Nominal.mp p0000 p0005
  have p0007 :=
    @g_elvvk w t (syn_copk (.cv y) (.cv z)) (by exact (show w ∉ ((syn_copk (.cv y) (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show w ∉ (((Class.cv y)).fv) ∪ (((Class.cv z)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y)))))) (show w ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ z from (by exact fresh_w_ne_z))))))))))) (by exact (show t ∉ ((syn_copk (.cv y) (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show t ∉ (((Class.cv y)).fv) ∪ (((Class.cv z)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ y from (by exact fresh_t_ne_y)))))) (show t ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ z from (by exact fresh_t_ne_z))))))))))) (show w ≠ t from (by exact fresh_w_ne_t))
  have p0008 :=
    @g_mpbir (.classMem (syn_copk (.cv y) (.cv z)) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_wex w (syn_wex t (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk (.cv w) (.cv t))))) p0006 p0007
  have p0009 :=
    @g_eleq1 (.cv x) (syn_copk (.cv y) (.cv z)) (syn_cxpk (syn_cvv) (syn_cvv))
  have p0010 :=
    @g_mpbiri (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (.classMem (.cv x) (syn_cxpk (syn_cvv) (syn_cvv))) (.classMem (syn_copk (.cv y) (.cv z)) (syn_cxpk (syn_cvv) (syn_cvv))) p0008 p0009
  have p0011 :=
    @g_adantr (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (.classMem (.cv x) (syn_cxpk (syn_cvv) (syn_cvv))) ph p0010
  have p0012 :=
    @g_exlimivv (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) ph) (.classMem (.cv x) (syn_cxpk (syn_cvv) (syn_cvv))) y z (by exact (show y ∉ ((Wff.classMem (.cv x) (syn_cxpk (syn_cvv) (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((Class.cv x)).fv) ∪ (((syn_cxpk (syn_cvv) (syn_cvv))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact Ne.symm dv_x_y)))))) (show y ∉ ((syn_cxpk (syn_cvv) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show y ∉ (((syn_cvv)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show y ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (by exact (show z ∉ ((Wff.classMem (.cv x) (syn_cxpk (syn_cvv) (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show z ∉ (((Class.cv x)).fv) ∪ (((syn_cxpk (syn_cvv) (syn_cvv))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact Ne.symm dv_x_z)))))) (show z ∉ ((syn_cxpk (syn_cvv) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show z ∉ (((syn_cvv)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show z ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) p0011
  have p0013 :=
    @g_abssi (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) ph))) x (syn_cxpk (syn_cvv) (syn_cvv)) (by exact (show x ∉ ((syn_cxpk (syn_cvv) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show x ∉ (((syn_cvv)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show x ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0012
  exact p0013

noncomputable def g_opkabssvvki
    (ph : Wff) (x : Var) (y : Var) (z : Var) (A : Class) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (hyp_opkabssvvki_1 : Nominal.NPrf (.classEq A (.cab x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) ph)))))) :
    Nominal.NPrf (syn_wss A (syn_cxpk (syn_cvv) (syn_cvv))) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ A.fv
  have p0000 :=
    @g_opkabssvvk ph x y z (show x ≠ y from (by exact dv_x_y)) (show x ≠ z from (by exact dv_x_z))
  have p0001 :=
    @g_eqsstri A (.cab x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) ph)))) (syn_cxpk (syn_cvv) (syn_cvv)) hyp_opkabssvvki_1 p0000
  exact p0001

noncomputable def g_xpkssvvk
    (A : Class) (B : Class) :
    Nominal.NPrf (syn_wss (syn_cxpk A B) (syn_cxpk (syn_cvv) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_z_ne_x : z ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xpk x y z A B (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A))) (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B))) (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B))) (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B))) (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z)) (show y ≠ z from (by exact fresh_y_ne_z))
  have p0001 :=
    @g_opkabssvvki (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B)) x y z (syn_cxpk A B) (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z)) p0000
  exact p0001

noncomputable def g_ssrelk
    (x : Var) (y : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (syn_wss A (syn_cxpk (syn_cvv) (syn_cvv))) (syn_wb (syn_wss A B) (.all x (.all y (.imp (.classMem (syn_copk (.cv x) (.cv y)) A) (.classMem (syn_copk (.cv x) (.cv y)) B)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_ssofss z A B (syn_cxpk (syn_cvv) (syn_cvv)) (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A))) (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B))) (by exact (show z ∉ ((syn_cxpk (syn_cvv) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show z ∉ (((syn_cvv)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show z ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))
  have p0001 :=
    (by simpa [syn_wb, syn_wral] using (Nominal.biimpRefl (syn_wral z (syn_cxpk (syn_cvv) (syn_cvv)) (.imp (.classMem (.cv z) A) (.classMem (.cv z) B)))))
  have p0002 :=
    @g_elvvk x y (.cv z) (by exact (show x ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ z from (by exact fresh_x_ne_z))))))) (by exact (show y ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ z from (by exact fresh_y_ne_z))))))) (show x ≠ y from (by exact dv_x_y))
  have p0003 :=
    @g_imbi1i (.classMem (.cv z) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_wex x (syn_wex y (.classEq (.cv z) (syn_copk (.cv x) (.cv y))))) (.imp (.classMem (.cv z) A) (.classMem (.cv z) B)) p0002
  have p0004 :=
    @g_n_19_23vv (.classEq (.cv z) (syn_copk (.cv x) (.cv y))) (.imp (.classMem (.cv z) A) (.classMem (.cv z) B)) x y (by exact (show x ∉ ((Wff.imp (.classMem (.cv z) A) (.classMem (.cv z) B))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show x ∉ (((Wff.classMem (.cv z) A)).fv) ∪ (((Wff.classMem (.cv z) B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Wff.classMem (.cv z) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((Class.cv z)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ z from (by exact fresh_x_ne_z)))))) (show x ∉ (A).fv from (by exact dv_A_x)))))) (show x ∉ ((Wff.classMem (.cv z) B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((Class.cv z)).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ z from (by exact fresh_x_ne_z)))))) (show x ∉ (B).fv from (by exact dv_B_x))))))))))) (by exact (show y ∉ ((Wff.imp (.classMem (.cv z) A) (.classMem (.cv z) B))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show y ∉ (((Wff.classMem (.cv z) A)).fv) ∪ (((Wff.classMem (.cv z) B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Wff.classMem (.cv z) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((Class.cv z)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ z from (by exact fresh_y_ne_z)))))) (show y ∉ (A).fv from (by exact dv_A_y)))))) (show y ∉ ((Wff.classMem (.cv z) B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((Class.cv z)).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ z from (by exact fresh_y_ne_z)))))) (show y ∉ (B).fv from (by exact dv_B_y)))))))))))
  have p0005 :=
    @g_bitr4i (.imp (.classMem (.cv z) (syn_cxpk (syn_cvv) (syn_cvv))) (.imp (.classMem (.cv z) A) (.classMem (.cv z) B))) (.imp (syn_wex x (syn_wex y (.classEq (.cv z) (syn_copk (.cv x) (.cv y))))) (.imp (.classMem (.cv z) A) (.classMem (.cv z) B))) (.all x (.all y (.imp (.classEq (.cv z) (syn_copk (.cv x) (.cv y))) (.imp (.classMem (.cv z) A) (.classMem (.cv z) B))))) p0003 p0004
  have p0006 :=
    @g_albii (.imp (.classMem (.cv z) (syn_cxpk (syn_cvv) (syn_cvv))) (.imp (.classMem (.cv z) A) (.classMem (.cv z) B))) (.all x (.all y (.imp (.classEq (.cv z) (syn_copk (.cv x) (.cv y))) (.imp (.classMem (.cv z) A) (.classMem (.cv z) B))))) z p0005
  have p0007 :=
    @g_alrot3 (.imp (.classEq (.cv z) (syn_copk (.cv x) (.cv y))) (.imp (.classMem (.cv z) A) (.classMem (.cv z) B))) z x y
  have p0008 :=
    @g_bitri (.all z (.imp (.classMem (.cv z) (syn_cxpk (syn_cvv) (syn_cvv))) (.imp (.classMem (.cv z) A) (.classMem (.cv z) B)))) (.all z (.all x (.all y (.imp (.classEq (.cv z) (syn_copk (.cv x) (.cv y))) (.imp (.classMem (.cv z) A) (.classMem (.cv z) B)))))) (.all x (.all y (.all z (.imp (.classEq (.cv z) (syn_copk (.cv x) (.cv y))) (.imp (.classMem (.cv z) A) (.classMem (.cv z) B)))))) p0006 p0007
  have p0009 :=
    @g_bitri (syn_wral z (syn_cxpk (syn_cvv) (syn_cvv)) (.imp (.classMem (.cv z) A) (.classMem (.cv z) B))) (.all z (.imp (.classMem (.cv z) (syn_cxpk (syn_cvv) (syn_cvv))) (.imp (.classMem (.cv z) A) (.classMem (.cv z) B)))) (.all x (.all y (.all z (.imp (.classEq (.cv z) (syn_copk (.cv x) (.cv y))) (.imp (.classMem (.cv z) A) (.classMem (.cv z) B)))))) p0001 p0008
  have p0010 :=
    @g_opkex (.cv x) (.cv y)
  have p0011 :=
    @g_eleq1 (.cv z) (syn_copk (.cv x) (.cv y)) A
  have p0012 :=
    @g_eleq1 (.cv z) (syn_copk (.cv x) (.cv y)) B
  have p0013 :=
    @g_imbi12d (.classEq (.cv z) (syn_copk (.cv x) (.cv y))) (.classMem (.cv z) A) (.classMem (syn_copk (.cv x) (.cv y)) A) (.classMem (.cv z) B) (.classMem (syn_copk (.cv x) (.cv y)) B) p0011 p0012
  have p0014 :=
    @g_ceqsalv (.imp (.classMem (.cv z) A) (.classMem (.cv z) B)) (.imp (.classMem (syn_copk (.cv x) (.cv y)) A) (.classMem (syn_copk (.cv x) (.cv y)) B)) z (syn_copk (.cv x) (.cv y)) (by exact (show z ∉ ((syn_copk (.cv x) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show z ∉ (((Class.cv x)).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))) (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y))))))))))) (by exact (show z ∉ ((Wff.imp (.classMem (syn_copk (.cv x) (.cv y)) A) (.classMem (syn_copk (.cv x) (.cv y)) B))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show z ∉ (((Wff.classMem (syn_copk (.cv x) (.cv y)) A)).fv) ∪ (((Wff.classMem (syn_copk (.cv x) (.cv y)) B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Wff.classMem (syn_copk (.cv x) (.cv y)) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show z ∉ (((syn_copk (.cv x) (.cv y))).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_copk (.cv x) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show z ∉ (((Class.cv x)).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))) (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y)))))))))) (show z ∉ (A).fv from (by exact fresh_z_not_A)))))) (show z ∉ ((Wff.classMem (syn_copk (.cv x) (.cv y)) B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show z ∉ (((syn_copk (.cv x) (.cv y))).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_copk (.cv x) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show z ∉ (((Class.cv x)).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))) (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y)))))))))) (show z ∉ (B).fv from (by exact fresh_z_not_B))))))))))) p0010 p0013
  have p0015 :=
    @g_n_2albii (.all z (.imp (.classEq (.cv z) (syn_copk (.cv x) (.cv y))) (.imp (.classMem (.cv z) A) (.classMem (.cv z) B)))) (.imp (.classMem (syn_copk (.cv x) (.cv y)) A) (.classMem (syn_copk (.cv x) (.cv y)) B)) x y p0014
  have p0016 :=
    @g_bitri (syn_wral z (syn_cxpk (syn_cvv) (syn_cvv)) (.imp (.classMem (.cv z) A) (.classMem (.cv z) B))) (.all x (.all y (.all z (.imp (.classEq (.cv z) (syn_copk (.cv x) (.cv y))) (.imp (.classMem (.cv z) A) (.classMem (.cv z) B)))))) (.all x (.all y (.imp (.classMem (syn_copk (.cv x) (.cv y)) A) (.classMem (syn_copk (.cv x) (.cv y)) B)))) p0009 p0015
  have p0017 :=
    @g_syl6bb (syn_wss A (syn_cxpk (syn_cvv) (syn_cvv))) (syn_wss A B) (syn_wral z (syn_cxpk (syn_cvv) (syn_cvv)) (.imp (.classMem (.cv z) A) (.classMem (.cv z) B))) (.all x (.all y (.imp (.classMem (syn_copk (.cv x) (.cv y)) A) (.classMem (syn_copk (.cv x) (.cv y)) B)))) p0000 p0016
  exact p0017

noncomputable def g_eqrelk
    (x : Var) (y : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (syn_wa (syn_wss A (syn_cxpk (syn_cvv) (syn_cvv))) (syn_wss B (syn_cxpk (syn_cvv) (syn_cvv)))) (syn_wb (.classEq A B) (.all x (.all y (syn_wb (.classMem (syn_copk (.cv x) (.cv y)) A) (.classMem (syn_copk (.cv x) (.cv y)) B)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_ssofeq z A B (syn_cxpk (syn_cvv) (syn_cvv)) (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A))) (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B))) (by exact (show z ∉ ((syn_cxpk (syn_cvv) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show z ∉ (((syn_cvv)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show z ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))
  have p0001 :=
    (by simpa [syn_wb, syn_wral] using (Nominal.biimpRefl (syn_wral z (syn_cxpk (syn_cvv) (syn_cvv)) (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)))))
  have p0002 :=
    @g_elvvk x y (.cv z) (by exact (show x ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ z from (by exact fresh_x_ne_z))))))) (by exact (show y ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ z from (by exact fresh_y_ne_z))))))) (show x ≠ y from (by exact dv_x_y))
  have p0003 :=
    @g_imbi1i (.classMem (.cv z) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_wex x (syn_wex y (.classEq (.cv z) (syn_copk (.cv x) (.cv y))))) (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)) p0002
  have p0004 :=
    @g_n_19_23vv (.classEq (.cv z) (syn_copk (.cv x) (.cv y))) (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)) x y (by exact (show x ∉ ((syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb]; exact (show x ∉ (((Wff.classMem (.cv z) A)).fv) ∪ (((Wff.classMem (.cv z) B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Wff.classMem (.cv z) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((Class.cv z)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ z from (by exact fresh_x_ne_z)))))) (show x ∉ (A).fv from (by exact dv_A_x)))))) (show x ∉ ((Wff.classMem (.cv z) B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((Class.cv z)).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ z from (by exact fresh_x_ne_z)))))) (show x ∉ (B).fv from (by exact dv_B_x))))))))))) (by exact (show y ∉ ((syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb]; exact (show y ∉ (((Wff.classMem (.cv z) A)).fv) ∪ (((Wff.classMem (.cv z) B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Wff.classMem (.cv z) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((Class.cv z)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ z from (by exact fresh_y_ne_z)))))) (show y ∉ (A).fv from (by exact dv_A_y)))))) (show y ∉ ((Wff.classMem (.cv z) B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((Class.cv z)).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ z from (by exact fresh_y_ne_z)))))) (show y ∉ (B).fv from (by exact dv_B_y)))))))))))
  have p0005 :=
    @g_bitr4i (.imp (.classMem (.cv z) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))) (.imp (syn_wex x (syn_wex y (.classEq (.cv z) (syn_copk (.cv x) (.cv y))))) (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))) (.all x (.all y (.imp (.classEq (.cv z) (syn_copk (.cv x) (.cv y))) (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))))) p0003 p0004
  have p0006 :=
    @g_albii (.imp (.classMem (.cv z) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))) (.all x (.all y (.imp (.classEq (.cv z) (syn_copk (.cv x) (.cv y))) (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))))) z p0005
  have p0007 :=
    @g_alrot3 (.imp (.classEq (.cv z) (syn_copk (.cv x) (.cv y))) (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))) z x y
  have p0008 :=
    @g_bitri (.all z (.imp (.classMem (.cv z) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)))) (.all z (.all x (.all y (.imp (.classEq (.cv z) (syn_copk (.cv x) (.cv y))) (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)))))) (.all x (.all y (.all z (.imp (.classEq (.cv z) (syn_copk (.cv x) (.cv y))) (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)))))) p0006 p0007
  have p0009 :=
    @g_opkex (.cv x) (.cv y)
  have p0010 :=
    @g_eleq1 (.cv z) (syn_copk (.cv x) (.cv y)) A
  have p0011 :=
    @g_eleq1 (.cv z) (syn_copk (.cv x) (.cv y)) B
  have p0012 :=
    @g_bibi12d (.classEq (.cv z) (syn_copk (.cv x) (.cv y))) (.classMem (.cv z) A) (.classMem (syn_copk (.cv x) (.cv y)) A) (.classMem (.cv z) B) (.classMem (syn_copk (.cv x) (.cv y)) B) p0010 p0011
  have p0013 :=
    @g_ceqsalv (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)) (syn_wb (.classMem (syn_copk (.cv x) (.cv y)) A) (.classMem (syn_copk (.cv x) (.cv y)) B)) z (syn_copk (.cv x) (.cv y)) (by exact (show z ∉ ((syn_copk (.cv x) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show z ∉ (((Class.cv x)).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))) (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y))))))))))) (by exact (show z ∉ ((syn_wb (.classMem (syn_copk (.cv x) (.cv y)) A) (.classMem (syn_copk (.cv x) (.cv y)) B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb]; exact (show z ∉ (((Wff.classMem (syn_copk (.cv x) (.cv y)) A)).fv) ∪ (((Wff.classMem (syn_copk (.cv x) (.cv y)) B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Wff.classMem (syn_copk (.cv x) (.cv y)) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show z ∉ (((syn_copk (.cv x) (.cv y))).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_copk (.cv x) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show z ∉ (((Class.cv x)).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))) (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y)))))))))) (show z ∉ (A).fv from (by exact fresh_z_not_A)))))) (show z ∉ ((Wff.classMem (syn_copk (.cv x) (.cv y)) B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show z ∉ (((syn_copk (.cv x) (.cv y))).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_copk (.cv x) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show z ∉ (((Class.cv x)).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))) (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y)))))))))) (show z ∉ (B).fv from (by exact fresh_z_not_B))))))))))) p0009 p0012
  have p0014 :=
    @g_n_2albii (.all z (.imp (.classEq (.cv z) (syn_copk (.cv x) (.cv y))) (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)))) (syn_wb (.classMem (syn_copk (.cv x) (.cv y)) A) (.classMem (syn_copk (.cv x) (.cv y)) B)) x y p0013
  have p0015 :=
    @g_n_3bitri (syn_wral z (syn_cxpk (syn_cvv) (syn_cvv)) (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))) (.all z (.imp (.classMem (.cv z) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)))) (.all x (.all y (.all z (.imp (.classEq (.cv z) (syn_copk (.cv x) (.cv y))) (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)))))) (.all x (.all y (syn_wb (.classMem (syn_copk (.cv x) (.cv y)) A) (.classMem (syn_copk (.cv x) (.cv y)) B)))) p0001 p0008 p0014
  have p0016 :=
    @g_syl6bb (syn_wa (syn_wss A (syn_cxpk (syn_cvv) (syn_cvv))) (syn_wss B (syn_cxpk (syn_cvv) (syn_cvv)))) (.classEq A B) (syn_wral z (syn_cxpk (syn_cvv) (syn_cvv)) (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))) (.all x (.all y (syn_wb (.classMem (syn_copk (.cv x) (.cv y)) A) (.classMem (syn_copk (.cv x) (.cv y)) B)))) p0000 p0015
  exact p0016

noncomputable def g_eqrelkriiv
    (x : Var) (y : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) (hyp_eqrelkriiv_1 : Nominal.NPrf (syn_wss A (syn_cxpk (syn_cvv) (syn_cvv)))) (hyp_eqrelkriiv_2 : Nominal.NPrf (syn_wss B (syn_cxpk (syn_cvv) (syn_cvv)))) (hyp_eqrelkriiv_3 : Nominal.NPrf (syn_wb (.classMem (syn_copk (.cv x) (.cv y)) A) (.classMem (syn_copk (.cv x) (.cv y)) B))) :
    Nominal.NPrf (.classEq A B) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_gen2 (syn_wb (.classMem (syn_copk (.cv x) (.cv y)) A) (.classMem (syn_copk (.cv x) (.cv y)) B)) x y hyp_eqrelkriiv_3
  have p0001 :=
    @g_eqrelk x y A B (by exact (show x ∉ (A).fv from (by exact dv_A_x))) (by exact (show y ∉ (A).fv from (by exact dv_A_y))) (by exact (show x ∉ (B).fv from (by exact dv_B_x))) (by exact (show y ∉ (B).fv from (by exact dv_B_y))) (show x ≠ y from (by exact dv_x_y))
  have p0002 :=
    @g_mp2an (syn_wss A (syn_cxpk (syn_cvv) (syn_cvv))) (syn_wss B (syn_cxpk (syn_cvv) (syn_cvv))) (syn_wb (.classEq A B) (.all x (.all y (syn_wb (.classMem (syn_copk (.cv x) (.cv y)) A) (.classMem (syn_copk (.cv x) (.cv y)) B))))) hyp_eqrelkriiv_1 hyp_eqrelkriiv_2 p0001
  have p0003 :=
    @g_mpbir (.classEq A B) (.all x (.all y (syn_wb (.classMem (syn_copk (.cv x) (.cv y)) A) (.classMem (syn_copk (.cv x) (.cv y)) B)))) p0000 p0002
  exact p0003

noncomputable def g_cnvkeq
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_ccnvk A) (syn_ccnvk B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
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
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have p0000 :=
    @g_eleq2 A B (syn_copk (.cv z) (.cv y))
  have p0001 :=
    @g_anbi2d (.classEq A B) (.classMem (syn_copk (.cv z) (.cv y)) A) (.classMem (syn_copk (.cv z) (.cv y)) B) (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) p0000
  have p0002 :=
    @g_n_2exbidv (.classEq A B) (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv z) (.cv y)) A)) (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv z) (.cv y)) B)) y z (by exact (show y ∉ ((Wff.classEq A B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ (B).fv from (by exact fresh_y_not_B))))))) (by exact (show z ∉ ((Wff.classEq A B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show z ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ (A).fv from (by exact fresh_z_not_A)) (show z ∉ (B).fv from (by exact fresh_z_not_B))))))) p0001
  have p0003 :=
    @g_abbidv (.classEq A B) (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv z) (.cv y)) A)))) (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv z) (.cv y)) B)))) x (by exact (show x ∉ ((Wff.classEq A B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ (B).fv from (by exact fresh_x_not_B))))))) p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_cnvk x y z A (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A))) (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z)) (show y ≠ z from (by exact fresh_y_ne_z))
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_cnvk x y z B (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B))) (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B))) (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B))) (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z)) (show y ≠ z from (by exact fresh_y_ne_z))
  have p0006 :=
    @g_n_3eqtr4g (.classEq A B) (.cab x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv z) (.cv y)) A))))) (.cab x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv z) (.cv y)) B))))) (syn_ccnvk A) (syn_ccnvk B) p0003 p0004 p0005
  exact p0006



#print axioms g_cnvkeq

end NFChoice.DirectNominalPrf.WPPReplay
