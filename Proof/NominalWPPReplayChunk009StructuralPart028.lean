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
import NominalWPPReplayChunk009StructuralPart027


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

noncomputable def g_elsuc
    (x : Var) (A : Class) (M : Class) (b : Var) (dv_A_b : b ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_M_b : b ∉ M.fv) (dv_b_x : b ≠ x) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cplc M (syn_c1c))) (syn_wrex b M (syn_wrex x (syn_ccompl (.cv b)) (.classEq A (syn_cun (.cv b) (syn_csn (.cv x))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ M.fv ∪ ({b} : Finset Var)
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_M : y ∉ M.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_b : y ≠ b := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b_ne_y : b ≠ y :=
    Ne.symm fresh_y_ne_b
  have p0000 :=
    @g_eladdc A M (syn_c1c) b y (by exact (show b ∉ (A).fv from (by exact dv_A_b))) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show b ∉ (M).fv from (by exact dv_M_b))) (by exact (show y ∉ (M).fv from (by exact fresh_y_not_M))) (by exact (show b ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show y ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (show b ≠ y from (by exact fresh_b_ne_y))
  have p0001 :=
    @g_snex (.cv x)
  have p0002 :=
    @g_ineq2 (.cv y) (syn_csn (.cv x)) (.cv b)
  have p0003 :=
    @g_eqeq1d (.classEq (.cv y) (syn_csn (.cv x))) (syn_cin (.cv b) (.cv y)) (syn_cin (.cv b) (syn_csn (.cv x))) (syn_c0) p0002
  have p0004 :=
    @g_uneq2 (.cv y) (syn_csn (.cv x)) (.cv b)
  have p0005 :=
    @g_eqeq2d (.classEq (.cv y) (syn_csn (.cv x))) (syn_cun (.cv b) (.cv y)) (syn_cun (.cv b) (syn_csn (.cv x))) A p0004
  have p0006 :=
    @g_anbi12d (.classEq (.cv y) (syn_csn (.cv x))) (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0)) (.classEq (syn_cin (.cv b) (syn_csn (.cv x))) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv y))) (.classEq A (syn_cun (.cv b) (syn_csn (.cv x)))) p0003 p0005
  have p0007 :=
    @g_ceqsexv (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv y)))) (syn_wa (.classEq (syn_cin (.cv b) (syn_csn (.cv x))) (syn_c0)) (.classEq A (syn_cun (.cv b) (syn_csn (.cv x))))) y (syn_csn (.cv x)) (by exact (show y ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))))) (by exact (show y ∉ ((syn_wa (.classEq (syn_cin (.cv b) (syn_csn (.cv x))) (syn_c0)) (.classEq A (syn_cun (.cv b) (syn_csn (.cv x)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show y ∉ (((Wff.classEq (syn_cin (.cv b) (syn_csn (.cv x))) (syn_c0))).fv) ∪ (((Wff.classEq A (syn_cun (.cv b) (syn_csn (.cv x))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Wff.classEq (syn_cin (.cv b) (syn_csn (.cv x))) (syn_c0))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ (((syn_cin (.cv b) (syn_csn (.cv x)))).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cin (.cv b) (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show y ∉ (((Class.cv b)).fv) ∪ (((syn_csn (.cv x))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ b from (by exact fresh_y_ne_b)))))) (show y ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))))))))) (show y ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show y ∉ ((Wff.classEq A (syn_cun (.cv b) (syn_csn (.cv x))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ ((A).fv) ∪ (((syn_cun (.cv b) (syn_csn (.cv x)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ ((syn_cun (.cv b) (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show y ∉ (((Class.cv b)).fv) ∪ (((syn_csn (.cv x))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ b from (by exact fresh_y_ne_b)))))) (show y ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))))))))))))))))) p0001 p0006
  have p0008 :=
    @g_disjsn (.cv b) (.cv x)
  have p0009 :=
    @g_vex x
  have p0010 :=
    @g_elcompl (.cv x) (.cv b) p0009
  have p0011_e00_recanon : Nominal.NPrf (syn_wb (.classEq (syn_cin (.cv b) (syn_csn (.cv x))) (syn_c0)) (.neg (.objMem x b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_csn syn_c0 syn_cdif syn_cvv
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
      p0008
  have p0011_e01_recanon : Nominal.NPrf (syn_wb (.classMem (.cv x) (syn_ccompl (.cv b))) (.neg (.objMem x b))) :=
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
      p0010
  have p0011 :=
    @g_bitr4i (.classEq (syn_cin (.cv b) (syn_csn (.cv x))) (syn_c0)) (.neg (.objMem x b)) (.classMem (.cv x) (syn_ccompl (.cv b))) p0011_e00_recanon p0011_e01_recanon
  have p0012 :=
    @g_anbi1i (.classEq (syn_cin (.cv b) (syn_csn (.cv x))) (syn_c0)) (.classMem (.cv x) (syn_ccompl (.cv b))) (.classEq A (syn_cun (.cv b) (syn_csn (.cv x)))) p0011
  have p0013 :=
    @g_bitri (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv y)))))) (syn_wa (.classEq (syn_cin (.cv b) (syn_csn (.cv x))) (syn_c0)) (.classEq A (syn_cun (.cv b) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv x) (syn_ccompl (.cv b))) (.classEq A (syn_cun (.cv b) (syn_csn (.cv x))))) p0007 p0012
  have p0014 :=
    @g_exbii (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv y)))))) (syn_wa (.classMem (.cv x) (syn_ccompl (.cv b))) (.classEq A (syn_cun (.cv b) (syn_csn (.cv x))))) x p0013
  have p0015 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex y (syn_c1c) (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv y)))))))
  have p0016 :=
    @g_el1c x (.cv y) (by exact (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y)))))))
  have p0017 :=
    @g_anbi1i (.classMem (.cv y) (syn_c1c)) (syn_wex x (.classEq (.cv y) (syn_csn (.cv x)))) (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv y)))) p0016
  have p0018 :=
    @g_n_19_41v (.classEq (.cv y) (syn_csn (.cv x))) (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv y)))) x (by exact (show x ∉ ((syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv y))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show x ∉ (((Wff.classEq (syn_cin (.cv b) (.cv y)) (syn_c0))).fv) ∪ (((Wff.classEq A (syn_cun (.cv b) (.cv y)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Wff.classEq (syn_cin (.cv b) (.cv y)) (syn_c0))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ (((syn_cin (.cv b) (.cv y))).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cin (.cv b) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show x ∉ (((Class.cv b)).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ b from (by exact Ne.symm dv_b_x)))))) (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y)))))))))) (show x ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show x ∉ ((Wff.classEq A (syn_cun (.cv b) (.cv y)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ ((A).fv) ∪ (((syn_cun (.cv b) (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact dv_A_x)) (show x ∉ ((syn_cun (.cv b) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show x ∉ (((Class.cv b)).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ b from (by exact Ne.symm dv_b_x)))))) (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y)))))))))))))))))))
  have p0019 :=
    @g_bitr4i (syn_wa (.classMem (.cv y) (syn_c1c)) (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv y))))) (syn_wa (syn_wex x (.classEq (.cv y) (syn_csn (.cv x)))) (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv y))))) (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv y)))))) p0017 p0018
  have p0020 :=
    @g_exbii (syn_wa (.classMem (.cv y) (syn_c1c)) (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv y))))) (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv y)))))) y p0019
  have p0021 :=
    @g_excom (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv y))))) y x
  have p0022 :=
    @g_bitri (syn_wex y (syn_wa (.classMem (.cv y) (syn_c1c)) (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv y)))))) (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv y))))))) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv y))))))) p0020 p0021
  have p0023 :=
    @g_bitri (syn_wrex y (syn_c1c) (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv y))))) (syn_wex y (syn_wa (.classMem (.cv y) (syn_c1c)) (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv y)))))) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv y))))))) p0015 p0022
  have p0024 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex x (syn_ccompl (.cv b)) (.classEq A (syn_cun (.cv b) (syn_csn (.cv x)))))))
  have p0025 :=
    @g_n_3bitr4i (syn_wex x (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (.cv x))) (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv y))))))) (syn_wex x (syn_wa (.classMem (.cv x) (syn_ccompl (.cv b))) (.classEq A (syn_cun (.cv b) (syn_csn (.cv x)))))) (syn_wrex y (syn_c1c) (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv y))))) (syn_wrex x (syn_ccompl (.cv b)) (.classEq A (syn_cun (.cv b) (syn_csn (.cv x))))) p0014 p0023 p0024
  have p0026 :=
    @g_rexbii (syn_wrex y (syn_c1c) (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv y))))) (syn_wrex x (syn_ccompl (.cv b)) (.classEq A (syn_cun (.cv b) (syn_csn (.cv x))))) b M p0025
  have p0027 :=
    @g_bitri (.classMem A (syn_cplc M (syn_c1c))) (syn_wrex b M (syn_wrex y (syn_c1c) (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0)) (.classEq A (syn_cun (.cv b) (.cv y)))))) (syn_wrex b M (syn_wrex x (syn_ccompl (.cv b)) (.classEq A (syn_cun (.cv b) (syn_csn (.cv x)))))) p0000 p0026
  exact p0027

noncomputable def g_elsuci
    (A : Class) (N : Class) (X : Class) (hyp_elsuci_1 : Nominal.NPrf (.classMem X (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wa (.classMem A N) (.neg (.classMem X A))) (.classMem (syn_cun A (syn_csn X)) (syn_cplc N (syn_c1c)))) := by
  let proofSupport : Finset Var := A.fv ∪ N.fv ∪ X.fv
  let a : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_a_not_N : a ∉ N.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_X : a ∉ X.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_N : x ∉ N.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_X : x ∉ X.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_a_ne_x : a ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_a : x ≠ a :=
    Ne.symm fresh_a_ne_x
  have p0000 :=
    @g_elcompl X A hyp_elsuci_1
  have p0001 :=
    @g_eqid (syn_cun A (syn_csn X))
  have p0002 :=
    @g_sneq (.cv x) X
  have p0003 :=
    @g_uneq2d (.classEq (.cv x) X) (syn_csn (.cv x)) (syn_csn X) A p0002
  have p0004 :=
    @g_eqeq2d (.classEq (.cv x) X) (syn_cun A (syn_csn (.cv x))) (syn_cun A (syn_csn X)) (syn_cun A (syn_csn X)) p0003
  have p0005 :=
    @g_rspcev (.classEq (syn_cun A (syn_csn X)) (syn_cun A (syn_csn (.cv x)))) (.classEq (syn_cun A (syn_csn X)) (syn_cun A (syn_csn X))) x X (syn_ccompl A) (by exact (show x ∉ (X).fv from (by exact fresh_x_not_X))) (by exact (show x ∉ ((syn_ccompl A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl]; exact (show x ∉ (A).fv from (by exact fresh_x_not_A))))) (by exact (show x ∉ ((Wff.classEq (syn_cun A (syn_csn X)) (syn_cun A (syn_csn X)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ (((syn_cun A (syn_csn X))).fv) ∪ (((syn_cun A (syn_csn X))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cun A (syn_csn X))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show x ∉ ((A).fv) ∪ (((syn_csn X)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ ((syn_csn X)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ (X).fv from (by exact fresh_x_not_X)))))))) (show x ∉ ((syn_cun A (syn_csn X))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show x ∉ ((A).fv) ∪ (((syn_csn X)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ ((syn_csn X)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ (X).fv from (by exact fresh_x_not_X))))))))))))) p0004
  have p0006 :=
    @g_mpan2 (.classMem X (syn_ccompl A)) (.classEq (syn_cun A (syn_csn X)) (syn_cun A (syn_csn X))) (syn_wrex x (syn_ccompl A) (.classEq (syn_cun A (syn_csn X)) (syn_cun A (syn_csn (.cv x))))) p0001 p0005
  have p0007 :=
    @g_sylbir (.neg (.classMem X A)) (.classMem X (syn_ccompl A)) (syn_wrex x (syn_ccompl A) (.classEq (syn_cun A (syn_csn X)) (syn_cun A (syn_csn (.cv x))))) p0000 p0006
  have p0008 :=
    @g_compleq (.cv a) A
  have p0009 :=
    @g_uneq1 (.cv a) A (syn_csn (.cv x))
  have p0010 :=
    @g_eqeq2d (.classEq (.cv a) A) (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun A (syn_csn (.cv x))) (syn_cun A (syn_csn X)) p0009
  have p0011 :=
    @g_rexeqbidv (.classEq (.cv a) A) (.classEq (syn_cun A (syn_csn X)) (syn_cun (.cv a) (syn_csn (.cv x)))) (.classEq (syn_cun A (syn_csn X)) (syn_cun A (syn_csn (.cv x)))) x (syn_ccompl (.cv a)) (syn_ccompl A) (by exact (show x ∉ ((syn_ccompl (.cv a))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl]; exact (show x ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ a from (by exact fresh_x_ne_a))))))))) (by exact (show x ∉ ((syn_ccompl A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl]; exact (show x ∉ (A).fv from (by exact fresh_x_not_A))))) (by exact (show x ∉ ((Wff.classEq (.cv a) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ (((Class.cv a)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ a from (by exact fresh_x_ne_a)))))) (show x ∉ (A).fv from (by exact fresh_x_not_A))))))) p0008 p0010
  have p0012 :=
    @g_rspcev (syn_wrex x (syn_ccompl (.cv a)) (.classEq (syn_cun A (syn_csn X)) (syn_cun (.cv a) (syn_csn (.cv x))))) (syn_wrex x (syn_ccompl A) (.classEq (syn_cun A (syn_csn X)) (syn_cun A (syn_csn (.cv x))))) a A N (by exact (show a ∉ (A).fv from (by exact fresh_a_not_A))) (by exact (show a ∉ (N).fv from (by exact fresh_a_not_N))) (by exact (show a ∉ ((syn_wrex x (syn_ccompl A) (.classEq (syn_cun A (syn_csn X)) (syn_cun A (syn_csn (.cv x)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex]; exact (show a ∉ ((((syn_ccompl A)).fv).erase x) ∪ ((((Wff.classEq (syn_cun A (syn_csn X)) (syn_cun A (syn_csn (.cv x))))).fv).erase x) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (((syn_ccompl A)).fv).erase x from (fun hmem => (show a ∉ ((syn_ccompl A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl]; exact (show a ∉ (A).fv from (by exact fresh_a_not_A)))) (Finset.mem_of_mem_erase hmem))) (show a ∉ (((Wff.classEq (syn_cun A (syn_csn X)) (syn_cun A (syn_csn (.cv x))))).fv).erase x from (fun hmem => (show a ∉ ((Wff.classEq (syn_cun A (syn_csn X)) (syn_cun A (syn_csn (.cv x))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show a ∉ (((syn_cun A (syn_csn X))).fv) ∪ (((syn_cun A (syn_csn (.cv x)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((syn_cun A (syn_csn X))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show a ∉ ((A).fv) ∪ (((syn_csn X)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (A).fv from (by exact fresh_a_not_A)) (show a ∉ ((syn_csn X)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show a ∉ (X).fv from (by exact fresh_a_not_X)))))))) (show a ∉ ((syn_cun A (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show a ∉ ((A).fv) ∪ (((syn_csn (.cv x))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (A).fv from (by exact fresh_a_not_A)) (show a ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show a ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ x from (by exact fresh_a_ne_x)))))))))))))))) (Finset.mem_of_mem_erase hmem)))))))) p0011
  have p0013 :=
    @g_sylan2 (.neg (.classMem X A)) (.classMem A N) (syn_wrex x (syn_ccompl A) (.classEq (syn_cun A (syn_csn X)) (syn_cun A (syn_csn (.cv x))))) (syn_wrex a N (syn_wrex x (syn_ccompl (.cv a)) (.classEq (syn_cun A (syn_csn X)) (syn_cun (.cv a) (syn_csn (.cv x)))))) p0007 p0012
  have p0014 :=
    @g_elsuc x (syn_cun A (syn_csn X)) N a (by exact (show a ∉ ((syn_cun A (syn_csn X))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show a ∉ ((A).fv) ∪ (((syn_csn X)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (A).fv from (by exact fresh_a_not_A)) (show a ∉ ((syn_csn X)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show a ∉ (X).fv from (by exact fresh_a_not_X))))))))) (by exact (show x ∉ ((syn_cun A (syn_csn X))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show x ∉ ((A).fv) ∪ (((syn_csn X)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ ((syn_csn X)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ (X).fv from (by exact fresh_x_not_X))))))))) (by exact (show a ∉ (N).fv from (by exact fresh_a_not_N))) (show a ≠ x from (by exact fresh_a_ne_x))
  have p0015 :=
    @g_sylibr (syn_wa (.classMem A N) (.neg (.classMem X A))) (syn_wrex a N (syn_wrex x (syn_ccompl (.cv a)) (.classEq (syn_cun A (syn_csn X)) (syn_cun (.cv a) (syn_csn (.cv x)))))) (.classMem (syn_cun A (syn_csn X)) (syn_cplc N (syn_c1c))) p0013 p0014
  exact p0015



#print axioms g_elsuci

end NFChoice.DirectNominalPrf.WPPReplay
