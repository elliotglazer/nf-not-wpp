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
import NominalWPPReplayChunk009StructuralPart039


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

noncomputable def g_leltfintr
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (.imp (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_cltfin))) (.classMem (syn_copk A C) (syn_cltfin)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_C : z ∉ C.fv := by
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
    @g_opklefing x A B (syn_cnnc) (syn_cnnc) (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
  have p0001 :=
    @g_n_3adant3 (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (syn_wb (.classMem (syn_copk A B) (syn_clefin)) (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc A (.cv x))))) (.classMem C (syn_cnnc)) p0000
  have p0002 :=
    @g_addcnnul A (.cv x)
  have p0003 :=
    @g_simpld (syn_wne (syn_cplc A (.cv x)) (syn_c0)) (syn_wne A (syn_c0)) (syn_wne (.cv x) (syn_c0)) p0002
  have p0004 :=
    @g_a1i (.imp (syn_wne (syn_cplc A (.cv x)) (syn_c0)) (syn_wne A (syn_c0))) (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem C (syn_cnnc))) (.classMem (.cv x) (syn_cnnc))) p0003
  have p0005 :=
    @g_nncaddccl (.cv x) (.cv y)
  have p0006 :=
    @g_n_3adant1 (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (syn_cplc (.cv x) (.cv y)) (syn_cnnc)) (.classMem A (syn_cnnc)) p0005
  have p0007 :=
    @g_addcass A (.cv x) (.cv y)
  have p0008 :=
    @g_addceq1 (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_cplc A (syn_cplc (.cv x) (.cv y))) (syn_c1c)
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_a1i (.classEq (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c)) (syn_cplc (syn_cplc A (syn_cplc (.cv x) (.cv y))) (syn_c1c))) (syn_w3a (.classMem A (syn_cnnc)) (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) p0009
  have p0011 :=
    @g_addceq2 (.cv z) (syn_cplc (.cv x) (.cv y)) A
  have p0012 :=
    @g_addceq1 (syn_cplc A (.cv z)) (syn_cplc A (syn_cplc (.cv x) (.cv y))) (syn_c1c)
  have p0013 :=
    @g_syl (.classEq (.cv z) (syn_cplc (.cv x) (.cv y))) (.classEq (syn_cplc A (.cv z)) (syn_cplc A (syn_cplc (.cv x) (.cv y)))) (.classEq (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)) (syn_cplc (syn_cplc A (syn_cplc (.cv x) (.cv y))) (syn_c1c))) p0011 p0012
  have p0014 :=
    @g_eqeq2d (.classEq (.cv z) (syn_cplc (.cv x) (.cv y))) (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)) (syn_cplc (syn_cplc A (syn_cplc (.cv x) (.cv y))) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c)) p0013
  have p0015 :=
    @g_rspcev (.classEq (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c)) (syn_cplc (syn_cplc A (.cv z)) (syn_c1c))) (.classEq (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c)) (syn_cplc (syn_cplc A (syn_cplc (.cv x) (.cv y))) (syn_c1c))) z (syn_cplc (.cv x) (.cv y)) (syn_cnnc) (by exact (show z ∉ ((syn_cplc (.cv x) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show z ∉ (((Class.cv x)).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))) (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y))))))))))) (by exact (show z ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show z ∉ ((Wff.classEq (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c)) (syn_cplc (syn_cplc A (syn_cplc (.cv x) (.cv y))) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show z ∉ (((syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c))).fv) ∪ (((syn_cplc (syn_cplc A (syn_cplc (.cv x) (.cv y))) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show z ∉ (((syn_cplc (syn_cplc A (.cv x)) (.cv y))).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_cplc (syn_cplc A (.cv x)) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show z ∉ (((syn_cplc A (.cv x))).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_cplc A (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show z ∉ ((A).fv) ∪ (((Class.cv x)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ (A).fv from (by exact fresh_z_not_A)) (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))))))) (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y)))))))))) (show z ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show z ∉ ((syn_cplc (syn_cplc A (syn_cplc (.cv x) (.cv y))) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show z ∉ (((syn_cplc A (syn_cplc (.cv x) (.cv y)))).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_cplc A (syn_cplc (.cv x) (.cv y)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show z ∉ ((A).fv) ∪ (((syn_cplc (.cv x) (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ (A).fv from (by exact fresh_z_not_A)) (show z ∉ ((syn_cplc (.cv x) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show z ∉ (((Class.cv x)).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))) (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y)))))))))))))) (show z ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) p0014
  have p0016 :=
    @g_syl2anc (syn_w3a (.classMem A (syn_cnnc)) (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (.classMem (syn_cplc (.cv x) (.cv y)) (syn_cnnc)) (.classEq (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c)) (syn_cplc (syn_cplc A (syn_cplc (.cv x) (.cv y))) (syn_c1c))) (syn_wrex z (syn_cnnc) (.classEq (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c)) (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))) p0006 p0010 p0015
  have p0017 :=
    @g_eqeq1 C (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c)) (syn_cplc (syn_cplc A (.cv z)) (syn_c1c))
  have p0018 :=
    @g_rexbidv (.classEq C (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c))) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c))) (.classEq (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c)) (syn_cplc (syn_cplc A (.cv z)) (syn_c1c))) z (syn_cnnc) (by exact (show z ∉ ((Wff.classEq C (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show z ∉ ((C).fv) ∪ (((syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ (C).fv from (by exact fresh_z_not_C)) (show z ∉ ((syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show z ∉ (((syn_cplc (syn_cplc A (.cv x)) (.cv y))).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_cplc (syn_cplc A (.cv x)) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show z ∉ (((syn_cplc A (.cv x))).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_cplc A (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show z ∉ ((A).fv) ∪ (((Class.cv x)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ (A).fv from (by exact fresh_z_not_A)) (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))))))) (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y)))))))))) (show z ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) p0017
  have p0019 :=
    @g_syl5ibrcom (syn_w3a (.classMem A (syn_cnnc)) (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wrex z (syn_cnnc) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))) (.classEq C (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c))) (syn_wrex z (syn_cnnc) (.classEq (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c)) (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))) p0016 p0018
  have p0020 :=
    @g_n_3expa (.classMem A (syn_cnnc)) (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.imp (.classEq C (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c))) (syn_wrex z (syn_cnnc) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c))))) p0019
  have p0021 :=
    @g_adantllr (.classMem A (syn_cnnc)) (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.imp (.classEq C (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c))) (syn_wrex z (syn_cnnc) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c))))) (.classMem C (syn_cnnc)) p0020
  have p0022 :=
    @g_rexlimdva (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem C (syn_cnnc))) (.classMem (.cv x) (syn_cnnc))) (.classEq C (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c))) (syn_wrex z (syn_cnnc) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))) y (syn_cnnc) (by exact (show y ∉ ((syn_wrex z (syn_cnnc) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex]; exact (show y ∉ ((((syn_cnnc)).fv).erase z) ∪ ((((Wff.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))).fv).erase z) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (((syn_cnnc)).fv).erase z from (fun hmem => (show y ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (Finset.mem_of_mem_erase hmem))) (show y ∉ (((Wff.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))).fv).erase z from (fun hmem => (show y ∉ ((Wff.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ ((C).fv) ∪ (((syn_cplc (syn_cplc A (.cv z)) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (C).fv from (by exact fresh_y_not_C)) (show y ∉ ((syn_cplc (syn_cplc A (.cv z)) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show y ∉ (((syn_cplc A (.cv z))).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cplc A (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show y ∉ ((A).fv) ∪ (((Class.cv z)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ z from (by exact fresh_y_ne_z)))))))))) (show y ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (Finset.mem_of_mem_erase hmem)))))))) (by exact (show y ∉ ((syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem C (syn_cnnc))) (.classMem (.cv x) (syn_cnnc)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show y ∉ (((syn_wa (.classMem A (syn_cnnc)) (.classMem C (syn_cnnc)))).fv) ∪ (((Wff.classMem (.cv x) (syn_cnnc))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_wa (.classMem A (syn_cnnc)) (.classMem C (syn_cnnc)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show y ∉ (((Wff.classMem A (syn_cnnc))).fv) ∪ (((Wff.classMem C (syn_cnnc))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Wff.classMem A (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ ((A).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show y ∉ ((Wff.classMem C (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ ((C).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (C).fv from (by exact fresh_y_not_C)) (show y ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (show y ∉ ((Wff.classMem (.cv x) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((Class.cv x)).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))) (show y ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) p0021
  have p0023 :=
    @g_anim12d (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem C (syn_cnnc))) (.classMem (.cv x) (syn_cnnc))) (syn_wne (syn_cplc A (.cv x)) (syn_c0)) (syn_wne A (syn_c0)) (syn_wrex y (syn_cnnc) (.classEq C (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c)))) (syn_wrex z (syn_cnnc) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))) p0004 p0022
  have p0024 :=
    @g_addcexg A (.cv x) (syn_cnnc) (syn_cnnc)
  have p0025 :=
    @g_adantlr (.classMem A (syn_cnnc)) (.classMem (.cv x) (syn_cnnc)) (.classMem (syn_cplc A (.cv x)) (syn_cvv)) (.classMem C (syn_cnnc)) p0024
  have p0026 :=
    @g_simplr (.classMem A (syn_cnnc)) (.classMem C (syn_cnnc)) (.classMem (.cv x) (syn_cnnc))
  have p0027 :=
    @g_opkltfing y (syn_cplc A (.cv x)) C (syn_cvv) (syn_cnnc) (by exact (show y ∉ ((syn_cplc A (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show y ∉ ((A).fv) ∪ (((Class.cv x)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))))))) (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C)))
  have p0028 :=
    @g_syl2anc (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem C (syn_cnnc))) (.classMem (.cv x) (syn_cnnc))) (.classMem (syn_cplc A (.cv x)) (syn_cvv)) (.classMem C (syn_cnnc)) (syn_wb (.classMem (syn_copk (syn_cplc A (.cv x)) C) (syn_cltfin)) (syn_wa (syn_wne (syn_cplc A (.cv x)) (syn_c0)) (syn_wrex y (syn_cnnc) (.classEq C (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c)))))) p0025 p0026 p0027
  have p0029 :=
    @g_opkltfing z A C (syn_cnnc) (syn_cnnc) (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A))) (by exact (show z ∉ (C).fv from (by exact fresh_z_not_C)))
  have p0030 :=
    @g_adantr (syn_wa (.classMem A (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wb (.classMem (syn_copk A C) (syn_cltfin)) (syn_wa (syn_wne A (syn_c0)) (syn_wrex z (syn_cnnc) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))))) (.classMem (.cv x) (syn_cnnc)) p0029
  have p0031 :=
    @g_n_3imtr4d (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem C (syn_cnnc))) (.classMem (.cv x) (syn_cnnc))) (syn_wa (syn_wne (syn_cplc A (.cv x)) (syn_c0)) (syn_wrex y (syn_cnnc) (.classEq C (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c))))) (syn_wa (syn_wne A (syn_c0)) (syn_wrex z (syn_cnnc) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c))))) (.classMem (syn_copk (syn_cplc A (.cv x)) C) (syn_cltfin)) (.classMem (syn_copk A C) (syn_cltfin)) p0023 p0028 p0030
  have p0032 :=
    @g_opkeq1 B (syn_cplc A (.cv x)) C
  have p0033 :=
    @g_eleq1d (.classEq B (syn_cplc A (.cv x))) (syn_copk B C) (syn_copk (syn_cplc A (.cv x)) C) (syn_cltfin) p0032
  have p0034 :=
    @g_imbi1d (.classEq B (syn_cplc A (.cv x))) (.classMem (syn_copk B C) (syn_cltfin)) (.classMem (syn_copk (syn_cplc A (.cv x)) C) (syn_cltfin)) (.classMem (syn_copk A C) (syn_cltfin)) p0033
  have p0035 :=
    @g_syl5ibrcom (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem C (syn_cnnc))) (.classMem (.cv x) (syn_cnnc))) (.imp (.classMem (syn_copk B C) (syn_cltfin)) (.classMem (syn_copk A C) (syn_cltfin))) (.classEq B (syn_cplc A (.cv x))) (.imp (.classMem (syn_copk (syn_cplc A (.cv x)) C) (syn_cltfin)) (.classMem (syn_copk A C) (syn_cltfin))) p0031 p0034
  have p0036 :=
    @g_rexlimdva (syn_wa (.classMem A (syn_cnnc)) (.classMem C (syn_cnnc))) (.classEq B (syn_cplc A (.cv x))) (.imp (.classMem (syn_copk B C) (syn_cltfin)) (.classMem (syn_copk A C) (syn_cltfin))) x (syn_cnnc) (by exact (show x ∉ ((Wff.imp (.classMem (syn_copk B C) (syn_cltfin)) (.classMem (syn_copk A C) (syn_cltfin)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show x ∉ (((Wff.classMem (syn_copk B C) (syn_cltfin))).fv) ∪ (((Wff.classMem (syn_copk A C) (syn_cltfin))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Wff.classMem (syn_copk B C) (syn_cltfin))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((syn_copk B C)).fv) ∪ (((syn_cltfin)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_copk B C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show x ∉ ((B).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (B).fv from (by exact fresh_x_not_B)) (show x ∉ (C).fv from (by exact fresh_x_not_C)))))) (show x ∉ ((syn_cltfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show x ∉ ((Wff.classMem (syn_copk A C) (syn_cltfin))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((syn_copk A C)).fv) ∪ (((syn_cltfin)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_copk A C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show x ∉ ((A).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ (C).fv from (by exact fresh_x_not_C)))))) (show x ∉ ((syn_cltfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (by exact (show x ∉ ((syn_wa (.classMem A (syn_cnnc)) (.classMem C (syn_cnnc)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show x ∉ (((Wff.classMem A (syn_cnnc))).fv) ∪ (((Wff.classMem C (syn_cnnc))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Wff.classMem A (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ ((A).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show x ∉ ((Wff.classMem C (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ ((C).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (C).fv from (by exact fresh_x_not_C)) (show x ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) p0035
  have p0037 :=
    @g_n_3adant2 (.classMem A (syn_cnnc)) (.classMem C (syn_cnnc)) (.imp (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc A (.cv x)))) (.imp (.classMem (syn_copk B C) (syn_cltfin)) (.classMem (syn_copk A C) (syn_cltfin)))) (.classMem B (syn_cnnc)) p0036
  have p0038 :=
    @g_sylbid (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (.classMem (syn_copk A B) (syn_clefin)) (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc A (.cv x)))) (.imp (.classMem (syn_copk B C) (syn_cltfin)) (.classMem (syn_copk A C) (syn_cltfin))) p0001 p0037
  have p0039 :=
    @g_imp3a (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_cltfin)) (.classMem (syn_copk A C) (syn_cltfin)) p0038
  exact p0039

noncomputable def g_ltfintr
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (.imp (syn_wa (.classMem (syn_copk A B) (syn_cltfin)) (.classMem (syn_copk B C) (syn_cltfin))) (.classMem (syn_copk A C) (syn_cltfin)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_C : z ∉ C.fv := by
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
    @g_an4 (syn_wne A (syn_c0)) (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))) (syn_wne B (syn_c0)) (syn_wrex y (syn_cnnc) (.classEq C (syn_cplc (syn_cplc B (.cv y)) (syn_c1c))))
  have p0001 :=
    @g_simpl (syn_wne A (syn_c0)) (syn_wne B (syn_c0))
  have p0002 :=
    @g_a1i (.imp (syn_wa (syn_wne A (syn_c0)) (syn_wne B (syn_c0))) (syn_wne A (syn_c0))) (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) p0001
  have p0003 :=
    @g_reeanv (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))) (.classEq C (syn_cplc (syn_cplc B (.cv y)) (syn_c1c))) x y (syn_cnnc) (syn_cnnc) (by exact (show y ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show x ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show y ∉ ((Wff.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ ((B).fv) ∪ (((syn_cplc (syn_cplc A (.cv x)) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (B).fv from (by exact fresh_y_not_B)) (show y ∉ ((syn_cplc (syn_cplc A (.cv x)) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show y ∉ (((syn_cplc A (.cv x))).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cplc A (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show y ∉ ((A).fv) ∪ (((Class.cv x)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))))))) (show y ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (by exact (show x ∉ ((Wff.classEq C (syn_cplc (syn_cplc B (.cv y)) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ ((C).fv) ∪ (((syn_cplc (syn_cplc B (.cv y)) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (C).fv from (by exact fresh_x_not_C)) (show x ∉ ((syn_cplc (syn_cplc B (.cv y)) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ (((syn_cplc B (.cv y))).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cplc B (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ ((B).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (B).fv from (by exact fresh_x_not_B)) (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y)))))))))) (show x ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (show x ≠ y from (by exact fresh_x_ne_y))
  have p0004 :=
    @g_addccom (syn_c1c) (.cv y)
  have p0005 :=
    @g_peano2 (.cv y)
  have p0006 :=
    @g_syl5eqel (.classMem (.cv y) (syn_cnnc)) (syn_cplc (syn_c1c) (.cv y)) (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc) p0004 p0005
  have p0007 :=
    @g_nncaddccl (.cv x) (syn_cplc (syn_c1c) (.cv y))
  have p0008 :=
    @g_sylan2 (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv x) (syn_cnnc)) (.classMem (syn_cplc (syn_c1c) (.cv y)) (syn_cnnc)) (.classMem (syn_cplc (.cv x) (syn_cplc (syn_c1c) (.cv y))) (syn_cnnc)) p0006 p0007
  have p0009 :=
    @g_adantl (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (.classMem (syn_cplc (.cv x) (syn_cplc (syn_c1c) (.cv y))) (syn_cnnc)) (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) p0008
  have p0010 :=
    @g_addceq1 B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv y)
  have p0011 :=
    @g_addceq1 (syn_cplc B (.cv y)) (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv y)) (syn_c1c)
  have p0012 :=
    @g_syl (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))) (.classEq (syn_cplc B (.cv y)) (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv y))) (.classEq (syn_cplc (syn_cplc B (.cv y)) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv y)) (syn_c1c))) p0010 p0011
  have p0013 :=
    @g_eqeq2d (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))) (syn_cplc (syn_cplc B (.cv y)) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv y)) (syn_c1c)) C p0012
  have p0014 :=
    @g_biimpa (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))) (.classEq C (syn_cplc (syn_cplc B (.cv y)) (syn_c1c))) (.classEq C (syn_cplc (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv y)) (syn_c1c))) p0013
  have p0015 :=
    @g_addceq2 (.cv z) (syn_cplc (.cv x) (syn_cplc (syn_c1c) (.cv y))) A
  have p0016 :=
    @g_addcass (syn_cplc A (.cv x)) (syn_c1c) (.cv y)
  have p0017 :=
    @g_addcass A (.cv x) (syn_cplc (syn_c1c) (.cv y))
  have p0018 :=
    @g_eqtri (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv y)) (syn_cplc (syn_cplc A (.cv x)) (syn_cplc (syn_c1c) (.cv y))) (syn_cplc A (syn_cplc (.cv x) (syn_cplc (syn_c1c) (.cv y)))) p0016 p0017
  have p0019 :=
    @g_syl6eqr (.classEq (.cv z) (syn_cplc (.cv x) (syn_cplc (syn_c1c) (.cv y)))) (syn_cplc A (.cv z)) (syn_cplc A (syn_cplc (.cv x) (syn_cplc (syn_c1c) (.cv y)))) (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv y)) p0015 p0018
  have p0020 :=
    @g_addceq1 (syn_cplc A (.cv z)) (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv y)) (syn_c1c)
  have p0021 :=
    @g_syl (.classEq (.cv z) (syn_cplc (.cv x) (syn_cplc (syn_c1c) (.cv y)))) (.classEq (syn_cplc A (.cv z)) (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv y))) (.classEq (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv y)) (syn_c1c))) p0019 p0020
  have p0022 :=
    @g_eqeq2d (.classEq (.cv z) (syn_cplc (.cv x) (syn_cplc (syn_c1c) (.cv y)))) (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv y)) (syn_c1c)) C p0021
  have p0023 :=
    @g_rspcev (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c))) (.classEq C (syn_cplc (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv y)) (syn_c1c))) z (syn_cplc (.cv x) (syn_cplc (syn_c1c) (.cv y))) (syn_cnnc) (by exact (show z ∉ ((syn_cplc (.cv x) (syn_cplc (syn_c1c) (.cv y)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show z ∉ (((Class.cv x)).fv) ∪ (((syn_cplc (syn_c1c) (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))) (show z ∉ ((syn_cplc (syn_c1c) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show z ∉ (((syn_c1c)).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y))))))))))))))) (by exact (show z ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show z ∉ ((Wff.classEq C (syn_cplc (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv y)) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show z ∉ ((C).fv) ∪ (((syn_cplc (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv y)) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ (C).fv from (by exact fresh_z_not_C)) (show z ∉ ((syn_cplc (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv y)) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show z ∉ (((syn_cplc (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv y))).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_cplc (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show z ∉ (((syn_cplc (syn_cplc A (.cv x)) (syn_c1c))).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_cplc (syn_cplc A (.cv x)) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show z ∉ (((syn_cplc A (.cv x))).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_cplc A (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show z ∉ ((A).fv) ∪ (((Class.cv x)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ (A).fv from (by exact fresh_z_not_A)) (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))))))) (show z ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y)))))))))) (show z ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) p0022
  have p0024 :=
    @g_ex (.classMem (syn_cplc (.cv x) (syn_cplc (syn_c1c) (.cv y))) (syn_cnnc)) (.classEq C (syn_cplc (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv y)) (syn_c1c))) (syn_wrex z (syn_cnnc) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))) p0023
  have p0025 :=
    @g_syl2im (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))) (.classMem (syn_cplc (.cv x) (syn_cplc (syn_c1c) (.cv y))) (syn_cnnc)) (syn_wa (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))) (.classEq C (syn_cplc (syn_cplc B (.cv y)) (syn_c1c)))) (.classEq C (syn_cplc (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv y)) (syn_c1c))) (syn_wrex z (syn_cnnc) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))) p0009 p0014 p0024
  have p0026 :=
    @g_rexlimdvva (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))) (.classEq C (syn_cplc (syn_cplc B (.cv y)) (syn_c1c)))) (syn_wrex z (syn_cnnc) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))) x y (syn_cnnc) (syn_cnnc) (by exact (show y ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show x ∉ ((syn_wrex z (syn_cnnc) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex]; exact (show x ∉ ((((syn_cnnc)).fv).erase z) ∪ ((((Wff.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))).fv).erase z) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (((syn_cnnc)).fv).erase z from (fun hmem => (show x ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (Finset.mem_of_mem_erase hmem))) (show x ∉ (((Wff.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))).fv).erase z from (fun hmem => (show x ∉ ((Wff.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ ((C).fv) ∪ (((syn_cplc (syn_cplc A (.cv z)) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (C).fv from (by exact fresh_x_not_C)) (show x ∉ ((syn_cplc (syn_cplc A (.cv z)) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ (((syn_cplc A (.cv z))).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cplc A (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ ((A).fv) ∪ (((Class.cv z)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ z from (by exact fresh_x_ne_z)))))))))) (show x ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (Finset.mem_of_mem_erase hmem)))))))) (by exact (show y ∉ ((syn_wrex z (syn_cnnc) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex]; exact (show y ∉ ((((syn_cnnc)).fv).erase z) ∪ ((((Wff.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))).fv).erase z) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (((syn_cnnc)).fv).erase z from (fun hmem => (show y ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (Finset.mem_of_mem_erase hmem))) (show y ∉ (((Wff.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))).fv).erase z from (fun hmem => (show y ∉ ((Wff.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ ((C).fv) ∪ (((syn_cplc (syn_cplc A (.cv z)) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (C).fv from (by exact fresh_y_not_C)) (show y ∉ ((syn_cplc (syn_cplc A (.cv z)) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show y ∉ (((syn_cplc A (.cv z))).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cplc A (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show y ∉ ((A).fv) ∪ (((Class.cv z)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ z from (by exact fresh_y_ne_z)))))))))) (show y ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (Finset.mem_of_mem_erase hmem)))))))) (by exact (show x ∉ ((syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a]; exact (show x ∉ (((Wff.classMem C (syn_cnnc))).fv) ∪ (((Wff.classMem A (syn_cnnc))).fv) ∪ (((Wff.classMem B (syn_cnnc))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Wff.classMem C (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ ((C).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (C).fv from (by exact fresh_x_not_C)) (show x ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show x ∉ ((Wff.classMem A (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ ((A).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) (show x ∉ ((Wff.classMem B (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ ((B).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (B).fv from (by exact fresh_x_not_B)) (show x ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (by exact (show y ∉ ((syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a]; exact (show y ∉ (((Wff.classMem C (syn_cnnc))).fv) ∪ (((Wff.classMem A (syn_cnnc))).fv) ∪ (((Wff.classMem B (syn_cnnc))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Wff.classMem C (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ ((C).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (C).fv from (by exact fresh_y_not_C)) (show y ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show y ∉ ((Wff.classMem A (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ ((A).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) (show y ∉ ((Wff.classMem B (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ ((B).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (B).fv from (by exact fresh_y_not_B)) (show y ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (show x ≠ y from (by exact fresh_x_ne_y)) p0025
  have p0027 :=
    @g_syl5bir (syn_wa (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))) (syn_wrex y (syn_cnnc) (.classEq C (syn_cplc (syn_cplc B (.cv y)) (syn_c1c))))) (syn_wrex x (syn_cnnc) (syn_wrex y (syn_cnnc) (syn_wa (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))) (.classEq C (syn_cplc (syn_cplc B (.cv y)) (syn_c1c)))))) (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wrex z (syn_cnnc) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))) p0003 p0026
  have p0028 :=
    @g_anim12d (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (syn_wne A (syn_c0)) (syn_wne B (syn_c0))) (syn_wne A (syn_c0)) (syn_wa (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))) (syn_wrex y (syn_cnnc) (.classEq C (syn_cplc (syn_cplc B (.cv y)) (syn_c1c))))) (syn_wrex z (syn_cnnc) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))) p0002 p0027
  have p0029 :=
    @g_syl5bi (syn_wa (syn_wa (syn_wne A (syn_c0)) (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))) (syn_wa (syn_wne B (syn_c0)) (syn_wrex y (syn_cnnc) (.classEq C (syn_cplc (syn_cplc B (.cv y)) (syn_c1c)))))) (syn_wa (syn_wa (syn_wne A (syn_c0)) (syn_wne B (syn_c0))) (syn_wa (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))) (syn_wrex y (syn_cnnc) (.classEq C (syn_cplc (syn_cplc B (.cv y)) (syn_c1c)))))) (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (syn_wne A (syn_c0)) (syn_wrex z (syn_cnnc) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c))))) p0000 p0028
  have p0030 :=
    @g_opkltfing x A B (syn_cnnc) (syn_cnnc) (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
  have p0031 :=
    @g_n_3adant3 (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (syn_wb (.classMem (syn_copk A B) (syn_cltfin)) (syn_wa (syn_wne A (syn_c0)) (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))))) (.classMem C (syn_cnnc)) p0030
  have p0032 :=
    @g_opkltfing y B C (syn_cnnc) (syn_cnnc) (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B))) (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C)))
  have p0033 :=
    @g_n_3adant1 (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc)) (syn_wb (.classMem (syn_copk B C) (syn_cltfin)) (syn_wa (syn_wne B (syn_c0)) (syn_wrex y (syn_cnnc) (.classEq C (syn_cplc (syn_cplc B (.cv y)) (syn_c1c)))))) (.classMem A (syn_cnnc)) p0032
  have p0034 :=
    @g_anbi12d (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (.classMem (syn_copk A B) (syn_cltfin)) (syn_wa (syn_wne A (syn_c0)) (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))) (.classMem (syn_copk B C) (syn_cltfin)) (syn_wa (syn_wne B (syn_c0)) (syn_wrex y (syn_cnnc) (.classEq C (syn_cplc (syn_cplc B (.cv y)) (syn_c1c))))) p0031 p0033
  have p0035 :=
    @g_opkltfing z A C (syn_cnnc) (syn_cnnc) (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A))) (by exact (show z ∉ (C).fv from (by exact fresh_z_not_C)))
  have p0036 :=
    @g_n_3adant2 (.classMem A (syn_cnnc)) (.classMem C (syn_cnnc)) (syn_wb (.classMem (syn_copk A C) (syn_cltfin)) (syn_wa (syn_wne A (syn_c0)) (syn_wrex z (syn_cnnc) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))))) (.classMem B (syn_cnnc)) p0035
  have p0037 :=
    @g_n_3imtr4d (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))) (syn_wa (syn_wa (syn_wne A (syn_c0)) (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))) (syn_wa (syn_wne B (syn_c0)) (syn_wrex y (syn_cnnc) (.classEq C (syn_cplc (syn_cplc B (.cv y)) (syn_c1c)))))) (syn_wa (syn_wne A (syn_c0)) (syn_wrex z (syn_cnnc) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c))))) (syn_wa (.classMem (syn_copk A B) (syn_cltfin)) (.classMem (syn_copk B C) (syn_cltfin))) (.classMem (syn_copk A C) (syn_cltfin)) p0029 p0034 p0036
  exact p0037

noncomputable def g_ltfinasym
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.imp (.classMem (syn_copk A B) (syn_cltfin)) (.neg (.classMem (syn_copk B A) (syn_cltfin))))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_ltfinirr A
  have p0001 :=
    @g_ad2antrr (.classMem A (syn_cnnc)) (.neg (.classMem (syn_copk A A) (syn_cltfin))) (.classMem B (syn_cnnc)) (.classMem (syn_copk A B) (syn_cltfin)) p0000
  have p0002 :=
    @g_ltfintr A B A
  have p0003 :=
    @g_n_3anidm13 (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.imp (syn_wa (.classMem (syn_copk A B) (syn_cltfin)) (.classMem (syn_copk B A) (syn_cltfin))) (.classMem (syn_copk A A) (syn_cltfin))) p0002
  have p0004 :=
    @g_expdimp (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk A B) (syn_cltfin)) (.classMem (syn_copk B A) (syn_cltfin)) (.classMem (syn_copk A A) (syn_cltfin)) p0003
  have p0005 :=
    @g_mtod (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk A B) (syn_cltfin))) (.classMem (syn_copk B A) (syn_cltfin)) (.classMem (syn_copk A A) (syn_cltfin)) p0001 p0004
  have p0006 :=
    @g_ex (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk A B) (syn_cltfin)) (.neg (.classMem (syn_copk B A) (syn_cltfin))) p0005
  exact p0006

noncomputable def g_n_0cminle
    (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cnnc)) (.classMem (syn_copk (syn_c0c) A) (syn_clefin))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_addcid2 A
  have p0001 :=
    @g_opkeq2i (syn_cplc (syn_c0c) A) A (syn_c0c) p0000
  have p0002 :=
    @g_peano1
  have p0003 :=
    @g_lefinaddc (syn_c0c) A (syn_cnnc)
  have p0004 :=
    @g_mpan (.classMem (syn_c0c) (syn_cnnc)) (.classMem A (syn_cnnc)) (.classMem (syn_copk (syn_c0c) (syn_cplc (syn_c0c) A)) (syn_clefin)) p0002 p0003
  have p0005 :=
    @g_syl5eqelr (.classMem A (syn_cnnc)) (syn_copk (syn_c0c) A) (syn_copk (syn_c0c) (syn_cplc (syn_c0c) A)) (syn_clefin) p0001 p0004
  exact p0005

noncomputable def g_ltfinp1
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (syn_wne A (syn_c0))) (.classMem (syn_copk A (syn_cplc A (syn_c1c))) (syn_cltfin))) := by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_simpr (.classMem A V) (syn_wne A (syn_c0))
  have p0001 :=
    @g_peano1
  have p0002 :=
    @g_addcid1 A
  have p0003 :=
    @g_addceq1i (syn_cplc A (syn_c0c)) A (syn_c1c) p0002
  have p0004 :=
    @g_eqcomi (syn_cplc (syn_cplc A (syn_c0c)) (syn_c1c)) (syn_cplc A (syn_c1c)) p0003
  have p0005 :=
    @g_addceq2 (.cv x) (syn_c0c) A
  have p0006 :=
    @g_addceq1d (.classEq (.cv x) (syn_c0c)) (syn_cplc A (.cv x)) (syn_cplc A (syn_c0c)) (syn_c1c) p0005
  have p0007 :=
    @g_eqeq2d (.classEq (.cv x) (syn_c0c)) (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (syn_cplc (syn_cplc A (syn_c0c)) (syn_c1c)) (syn_cplc A (syn_c1c)) p0006
  have p0008 :=
    @g_rspcev (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc A (syn_c0c)) (syn_c1c))) x (syn_c0c) (syn_cnnc) (by exact (show x ∉ ((syn_c0c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show x ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show x ∉ ((Wff.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc A (syn_c0c)) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ (((syn_cplc A (syn_c1c))).fv) ∪ (((syn_cplc (syn_cplc A (syn_c0c)) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cplc A (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ ((A).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show x ∉ ((syn_cplc (syn_cplc A (syn_c0c)) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ (((syn_cplc A (syn_c0c))).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cplc A (syn_c0c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ ((A).fv) ∪ (((syn_c0c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ ((syn_c0c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show x ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) p0007
  have p0009 :=
    @g_mp2an (.classMem (syn_c0c) (syn_cnnc)) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc A (syn_c0c)) (syn_c1c))) (syn_wrex x (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))) p0001 p0004 p0008
  have p0010 :=
    @g_jctir (syn_wa (.classMem A V) (syn_wne A (syn_c0))) (syn_wne A (syn_c0)) (syn_wrex x (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))) p0000 p0009
  have p0011 :=
    @g_n_1cex
  have p0012 :=
    @g_addcexg A (syn_c1c) V (syn_cvv)
  have p0013 :=
    @g_mpan2 (.classMem A V) (.classMem (syn_c1c) (syn_cvv)) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) p0011 p0012
  have p0014 :=
    @g_opkltfing x A (syn_cplc A (syn_c1c)) V (syn_cvv) (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show x ∉ ((syn_cplc A (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ ((A).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))
  have p0015 :=
    @g_mpdan (.classMem A V) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) (syn_wb (.classMem (syn_copk A (syn_cplc A (syn_c1c))) (syn_cltfin)) (syn_wa (syn_wne A (syn_c0)) (syn_wrex x (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))))) p0013 p0014
  have p0016 :=
    @g_adantr (.classMem A V) (syn_wb (.classMem (syn_copk A (syn_cplc A (syn_c1c))) (syn_cltfin)) (syn_wa (syn_wne A (syn_c0)) (syn_wrex x (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))))) (syn_wne A (syn_c0)) p0015
  have p0017 :=
    @g_mpbird (syn_wa (.classMem A V) (syn_wne A (syn_c0))) (.classMem (syn_copk A (syn_cplc A (syn_c1c))) (syn_cltfin)) (syn_wa (syn_wne A (syn_c0)) (syn_wrex x (syn_cnnc) (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))) p0010 p0016
  exact p0017



#print axioms g_ltfinp1

end NFChoice.DirectNominalPrf.WPPReplay
