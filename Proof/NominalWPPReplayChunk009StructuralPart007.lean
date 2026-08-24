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
import NominalWPPReplayChunk009StructuralPart006


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

noncomputable def g_otkelins3kg
    (A : Class) (B : Class) (C : Class) (D : Class) (T : Class) (V : Class) (W : Class) :
    Nominal.NPrf (.imp (syn_w3a (.classMem A V) (.classMem B W) (.classMem C T)) (syn_wb (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_cins3k D)) (.classMem (syn_copk A B) D))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ T.fv ∪ V.fv ∪ W.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_T : x ∉ T.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_W : x ∉ W.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_T : y ∉ T.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_V : y ∉ V.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_W : y ∉ W.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_T : z ∉ T.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_V : z ∉ V.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_W : z ∉ W.fv := by
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
    @g_snex (syn_csn A)
  have p0001 :=
    @g_opkex B C
  have p0002 :=
    @g_opkelins3kg x y z (syn_csn (syn_csn A)) (syn_copk B C) D (syn_cvv) (syn_cvv) (by exact (show x ∉ ((syn_csn (syn_csn A))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ ((syn_csn A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ (A).fv from (by exact fresh_x_not_A))))))) (by exact (show y ∉ ((syn_csn (syn_csn A))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ (A).fv from (by exact fresh_y_not_A))))))) (by exact (show z ∉ ((syn_csn (syn_csn A))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show z ∉ ((syn_csn A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show z ∉ (A).fv from (by exact fresh_z_not_A))))))) (by exact (show x ∉ ((syn_copk B C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show x ∉ ((B).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (B).fv from (by exact fresh_x_not_B)) (show x ∉ (C).fv from (by exact fresh_x_not_C))))))) (by exact (show y ∉ ((syn_copk B C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show y ∉ ((B).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (B).fv from (by exact fresh_y_not_B)) (show y ∉ (C).fv from (by exact fresh_y_not_C))))))) (by exact (show z ∉ ((syn_copk B C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show z ∉ ((B).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ (B).fv from (by exact fresh_z_not_B)) (show z ∉ (C).fv from (by exact fresh_z_not_C))))))) (by exact (show x ∉ (D).fv from (by exact fresh_x_not_D))) (by exact (show y ∉ (D).fv from (by exact fresh_y_not_D))) (by exact (show z ∉ (D).fv from (by exact fresh_z_not_D))) (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z)) (show y ≠ z from (by exact fresh_y_ne_z))
  have p0003 :=
    @g_mp2an (.classMem (syn_csn (syn_csn A)) (syn_cvv)) (.classMem (syn_copk B C) (syn_cvv)) (syn_wb (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_cins3k D)) (syn_wex x (syn_wex y (syn_wex z (syn_w3a (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x)))) (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) D)))))) p0000 p0001 p0002
  have p0004 :=
    @g_n_3anass (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x)))) (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) D)
  have p0005 :=
    @g_eqcom (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x)))
  have p0006 :=
    @g_snex (.cv x)
  have p0007 :=
    @g_sneqb (syn_csn (.cv x)) (syn_csn A) p0006
  have p0008 :=
    @g_vex x
  have p0009 :=
    @g_sneqb (.cv x) A p0008
  have p0010 :=
    @g_bitri (.classEq (syn_csn (syn_csn (.cv x))) (syn_csn (syn_csn A))) (.classEq (syn_csn (.cv x)) (syn_csn A)) (.classEq (.cv x) A) p0007 p0009
  have p0011 :=
    @g_bitri (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x)))) (.classEq (syn_csn (syn_csn (.cv x))) (syn_csn (syn_csn A))) (.classEq (.cv x) A) p0005 p0010
  have p0012 :=
    @g_anbi1i (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x)))) (.classEq (.cv x) A) (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) D)) p0011
  have p0013 :=
    @g_bitri (syn_w3a (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x)))) (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) D)) (syn_wa (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x)))) (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) D))) (syn_wa (.classEq (.cv x) A) (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) D))) p0004 p0012
  have p0014 :=
    @g_n_2exbii (syn_w3a (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x)))) (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) D)) (syn_wa (.classEq (.cv x) A) (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) D))) y z p0013
  have p0015 :=
    @g_n_19_42vv (.classEq (.cv x) A) (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) D)) y z (by exact (show y ∉ ((Wff.classEq (.cv x) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ (((Class.cv x)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))) (show y ∉ (A).fv from (by exact fresh_y_not_A))))))) (by exact (show z ∉ ((Wff.classEq (.cv x) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show z ∉ (((Class.cv x)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))) (show z ∉ (A).fv from (by exact fresh_z_not_A)))))))
  have p0016 :=
    @g_bitri (syn_wex y (syn_wex z (syn_w3a (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x)))) (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) D)))) (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) A) (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) D))))) (syn_wa (.classEq (.cv x) A) (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) D))))) p0014 p0015
  have p0017 :=
    @g_exbii (syn_wex y (syn_wex z (syn_w3a (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x)))) (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) D)))) (syn_wa (.classEq (.cv x) A) (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) D))))) x p0016
  have p0018 :=
    @g_opkeq1 (.cv x) A (.cv y)
  have p0019 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_copk (.cv x) (.cv y)) (syn_copk A (.cv y)) D p0018
  have p0020 :=
    @g_anbi2d (.classEq (.cv x) A) (.classMem (syn_copk (.cv x) (.cv y)) D) (.classMem (syn_copk A (.cv y)) D) (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) p0019
  have p0021 :=
    @g_n_2exbidv (.classEq (.cv x) A) (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) D)) (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk A (.cv y)) D)) y z (by exact (show y ∉ ((Wff.classEq (.cv x) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ (((Class.cv x)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))) (show y ∉ (A).fv from (by exact fresh_y_not_A))))))) (by exact (show z ∉ ((Wff.classEq (.cv x) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show z ∉ (((Class.cv x)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))) (show z ∉ (A).fv from (by exact fresh_z_not_A))))))) p0020
  have p0022 :=
    @g_ceqsexgv (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) D)))) (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk A (.cv y)) D)))) x A V (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show x ∉ ((syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk A (.cv y)) D))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex]; exact (show x ∉ (((syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk A (.cv y)) D)))).fv).erase y from (fun hmem => (show x ∉ ((syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk A (.cv y)) D)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex]; exact (show x ∉ (((syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk A (.cv y)) D))).fv).erase z from (fun hmem => (show x ∉ ((syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk A (.cv y)) D))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show x ∉ (((Wff.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))).fv) ∪ (((Wff.classMem (syn_copk A (.cv y)) D)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Wff.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ (((syn_copk B C)).fv) ∪ (((syn_copk (.cv y) (.cv z))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_copk B C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show x ∉ ((B).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (B).fv from (by exact fresh_x_not_B)) (show x ∉ (C).fv from (by exact fresh_x_not_C)))))) (show x ∉ ((syn_copk (.cv y) (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show x ∉ (((Class.cv y)).fv) ∪ (((Class.cv z)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y)))))) (show x ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ z from (by exact fresh_x_ne_z)))))))))))))) (show x ∉ ((Wff.classMem (syn_copk A (.cv y)) D)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((syn_copk A (.cv y))).fv) ∪ ((D).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_copk A (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show x ∉ ((A).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y)))))))))) (show x ∉ (D).fv from (by exact fresh_x_not_D)))))))))) (Finset.mem_of_mem_erase hmem))))) (Finset.mem_of_mem_erase hmem)))))) p0021
  have p0023 :=
    @g_syl5bb (syn_wex x (syn_wex y (syn_wex z (syn_w3a (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x)))) (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) D))))) (syn_wex x (syn_wa (.classEq (.cv x) A) (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) D)))))) (.classMem A V) (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk A (.cv y)) D)))) p0017 p0022
  have p0024 :=
    @g_n_3ad2ant1 (.classMem A V) (.classMem B W) (syn_wb (syn_wex x (syn_wex y (syn_wex z (syn_w3a (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x)))) (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) D))))) (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk A (.cv y)) D))))) (.classMem C T) p0023
  have p0025 :=
    @g_eqcom (syn_copk B C) (syn_copk (.cv y) (.cv z))
  have p0026 :=
    @g_vex y
  have p0027 :=
    @g_vex z
  have p0028 :=
    @g_opkthg (.cv y) (.cv z) B C T (syn_cvv) (syn_cvv)
  have p0029 :=
    @g_mp3an12 (.classMem (.cv y) (syn_cvv)) (.classMem (.cv z) (syn_cvv)) (.classMem C T) (syn_wb (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C)) (syn_wa (.classEq (.cv y) B) (.classEq (.cv z) C))) p0026 p0027 p0028
  have p0030 :=
    @g_syl5bb (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C)) (.classMem C T) (syn_wa (.classEq (.cv y) B) (.classEq (.cv z) C)) p0025 p0029
  have p0031 :=
    @g_anbi1d (.classMem C T) (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (syn_wa (.classEq (.cv y) B) (.classEq (.cv z) C)) (.classMem (syn_copk A (.cv y)) D) p0030
  have p0032 :=
    @g_anass (.classEq (.cv y) B) (.classEq (.cv z) C) (.classMem (syn_copk A (.cv y)) D)
  have p0033 :=
    @g_syl6bb (.classMem C T) (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk A (.cv y)) D)) (syn_wa (syn_wa (.classEq (.cv y) B) (.classEq (.cv z) C)) (.classMem (syn_copk A (.cv y)) D)) (syn_wa (.classEq (.cv y) B) (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv y)) D))) p0031 p0032
  have p0034 :=
    @g_n_2exbidv (.classMem C T) (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk A (.cv y)) D)) (syn_wa (.classEq (.cv y) B) (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv y)) D))) y z (by exact (show y ∉ ((Wff.classMem C T)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ ((C).fv) ∪ ((T).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (C).fv from (by exact fresh_y_not_C)) (show y ∉ (T).fv from (by exact fresh_y_not_T))))))) (by exact (show z ∉ ((Wff.classMem C T)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show z ∉ ((C).fv) ∪ ((T).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ (C).fv from (by exact fresh_z_not_C)) (show z ∉ (T).fv from (by exact fresh_z_not_T))))))) p0033
  have p0035 :=
    @g_exdistr (.classEq (.cv y) B) (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv y)) D)) y z (by exact (show z ∉ ((Wff.classEq (.cv y) B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show z ∉ (((Class.cv y)).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y)))))) (show z ∉ (B).fv from (by exact fresh_z_not_B)))))))
  have p0036 :=
    @g_syl6bb (.classMem C T) (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk A (.cv y)) D)))) (syn_wex y (syn_wex z (syn_wa (.classEq (.cv y) B) (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv y)) D))))) (syn_wex y (syn_wa (.classEq (.cv y) B) (syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv y)) D))))) p0034 p0035
  have p0037 :=
    @g_adantl (.classMem C T) (syn_wb (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk A (.cv y)) D)))) (syn_wex y (syn_wa (.classEq (.cv y) B) (syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv y)) D)))))) (.classMem B W) p0036
  have p0038 :=
    @g_opkeq2 (.cv y) B A
  have p0039 :=
    @g_eleq1d (.classEq (.cv y) B) (syn_copk A (.cv y)) (syn_copk A B) D p0038
  have p0040 :=
    @g_anbi2d (.classEq (.cv y) B) (.classMem (syn_copk A (.cv y)) D) (.classMem (syn_copk A B) D) (.classEq (.cv z) C) p0039
  have p0041 :=
    @g_exbidv (.classEq (.cv y) B) (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv y)) D)) (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A B) D)) z (by exact (show z ∉ ((Wff.classEq (.cv y) B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show z ∉ (((Class.cv y)).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y)))))) (show z ∉ (B).fv from (by exact fresh_z_not_B))))))) p0040
  have p0042 :=
    @g_ceqsexgv (syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv y)) D))) (syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A B) D))) y B W (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B))) (by exact (show y ∉ ((syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A B) D)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex]; exact (show y ∉ (((syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A B) D))).fv).erase z from (fun hmem => (show y ∉ ((syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A B) D))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show y ∉ (((Wff.classEq (.cv z) C)).fv) ∪ (((Wff.classMem (syn_copk A B) D)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Wff.classEq (.cv z) C)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ (((Class.cv z)).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ z from (by exact fresh_y_ne_z)))))) (show y ∉ (C).fv from (by exact fresh_y_not_C)))))) (show y ∉ ((Wff.classMem (syn_copk A B) D)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((syn_copk A B)).fv) ∪ ((D).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_copk A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show y ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ (B).fv from (by exact fresh_y_not_B)))))) (show y ∉ (D).fv from (by exact fresh_y_not_D)))))))))) (Finset.mem_of_mem_erase hmem)))))) p0041
  have p0043 :=
    @g_biidd (.classEq (.cv z) C) (.classMem (syn_copk A B) D)
  have p0044 :=
    @g_ceqsexgv (.classMem (syn_copk A B) D) (.classMem (syn_copk A B) D) z C T (by exact (show z ∉ (C).fv from (by exact fresh_z_not_C))) (by exact (show z ∉ ((Wff.classMem (syn_copk A B) D)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show z ∉ (((syn_copk A B)).fv) ∪ ((D).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_copk A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show z ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ (A).fv from (by exact fresh_z_not_A)) (show z ∉ (B).fv from (by exact fresh_z_not_B)))))) (show z ∉ (D).fv from (by exact fresh_z_not_D))))))) p0043
  have p0045 :=
    @g_sylan9bb (.classMem B W) (syn_wex y (syn_wa (.classEq (.cv y) B) (syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv y)) D))))) (syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A B) D))) (.classMem C T) (.classMem (syn_copk A B) D) p0042 p0044
  have p0046 :=
    @g_bitrd (syn_wa (.classMem B W) (.classMem C T)) (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk A (.cv y)) D)))) (syn_wex y (syn_wa (.classEq (.cv y) B) (syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv y)) D))))) (.classMem (syn_copk A B) D) p0037 p0045
  have p0047 :=
    @g_n_3adant1 (.classMem B W) (.classMem C T) (syn_wb (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk A (.cv y)) D)))) (.classMem (syn_copk A B) D)) (.classMem A V) p0046
  have p0048 :=
    @g_bitrd (syn_w3a (.classMem A V) (.classMem B W) (.classMem C T)) (syn_wex x (syn_wex y (syn_wex z (syn_w3a (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x)))) (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) D))))) (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk A (.cv y)) D)))) (.classMem (syn_copk A B) D) p0024 p0047
  have p0049 :=
    @g_syl5bb (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_cins3k D)) (syn_wex x (syn_wex y (syn_wex z (syn_w3a (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x)))) (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) D))))) (syn_w3a (.classMem A V) (.classMem B W) (.classMem C T)) (.classMem (syn_copk A B) D) p0003 p0048
  exact p0049

noncomputable def g_otkelins2k
    (A : Class) (B : Class) (C : Class) (D : Class) (hyp_otkelinsk_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_otkelinsk_2 : Nominal.NPrf (.classMem B (syn_cvv))) (hyp_otkelinsk_3 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_cins2k D)) (.classMem (syn_copk A C) D)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  have p0000 :=
    @g_otkelins2kg A B C D (syn_cvv) (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp3an (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv)) (syn_wb (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_cins2k D)) (.classMem (syn_copk A C) D)) hyp_otkelinsk_1 hyp_otkelinsk_2 hyp_otkelinsk_3 p0000
  exact p0001

noncomputable def g_otkelins3k
    (A : Class) (B : Class) (C : Class) (D : Class) (hyp_otkelinsk_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_otkelinsk_2 : Nominal.NPrf (.classMem B (syn_cvv))) (hyp_otkelinsk_3 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_cins3k D)) (.classMem (syn_copk A B) D)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  have p0000 :=
    @g_otkelins3kg A B C D (syn_cvv) (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp3an (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv)) (syn_wb (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_cins3k D)) (.classMem (syn_copk A B) D)) hyp_otkelinsk_1 hyp_otkelinsk_2 hyp_otkelinsk_3 p0000
  exact p0001

noncomputable def g_elimakg
    (y : Var) (A : Class) (B : Class) (C : Class) (V : Class) (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_C_y : y ∉ C.fv) :
    Nominal.NPrf (.imp (.classMem C V) (syn_wb (.classMem C (syn_cimak A B)) (syn_wrex y B (.classMem (syn_copk (.cv y) C) A)))) := by
  let proofSupport : Finset Var := ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_y : x ≠ y := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_opkeq2 (.cv x) C (.cv y)
  have p0001 :=
    @g_eleq1d (.classEq (.cv x) C) (syn_copk (.cv y) (.cv x)) (syn_copk (.cv y) C) A p0000
  have p0002 :=
    @g_rexbidv (.classEq (.cv x) C) (.classMem (syn_copk (.cv y) (.cv x)) A) (.classMem (syn_copk (.cv y) C) A) y B (by exact (show y ∉ ((Wff.classEq (.cv x) C)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ (((Class.cv x)).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))) (show y ∉ (C).fv from (by exact dv_C_y))))))) p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_imak x y A B (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show y ∉ (A).fv from (by exact dv_A_y))) (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B))) (by exact (show y ∉ (B).fv from (by exact dv_B_y))) (show x ≠ y from (by exact fresh_x_ne_y))
  have p0004 :=
    @g_elab2g (syn_wrex y B (.classMem (syn_copk (.cv y) (.cv x)) A)) (syn_wrex y B (.classMem (syn_copk (.cv y) C) A)) x C (syn_cimak A B) V (by exact (show x ∉ (C).fv from (by exact fresh_x_not_C))) (by exact (show x ∉ ((syn_wrex y B (.classMem (syn_copk (.cv y) C) A))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex]; exact (show x ∉ (((B).fv).erase y) ∪ ((((Wff.classMem (syn_copk (.cv y) C) A)).fv).erase y) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((B).fv).erase y from (fun hmem => (show x ∉ (B).fv from (by exact fresh_x_not_B)) (Finset.mem_of_mem_erase hmem))) (show x ∉ (((Wff.classMem (syn_copk (.cv y) C) A)).fv).erase y from (fun hmem => (show x ∉ ((Wff.classMem (syn_copk (.cv y) C) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((syn_copk (.cv y) C)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_copk (.cv y) C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show x ∉ (((Class.cv y)).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y)))))) (show x ∉ (C).fv from (by exact fresh_x_not_C)))))) (show x ∉ (A).fv from (by exact fresh_x_not_A)))))) (Finset.mem_of_mem_erase hmem)))))))) p0002 p0003
  exact p0004

noncomputable def g_elimakvg
    (y : Var) (A : Class) (C : Class) (V : Class) (dv_A_y : y ∉ A.fv) (dv_C_y : y ∉ C.fv) :
    Nominal.NPrf (.imp (.classMem C V) (syn_wb (.classMem C (syn_cimak A (syn_cvv))) (syn_wex y (.classMem (syn_copk (.cv y) C) A)))) := by
  let proofSupport : Finset Var := ({y} : Finset Var) ∪ A.fv ∪ C.fv ∪ V.fv
  have p0000 :=
    @g_elimakg y A (syn_cvv) C V (by exact (show y ∉ (A).fv from (by exact dv_A_y))) (by exact (show y ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show y ∉ (C).fv from (by exact dv_C_y)))
  have p0001 :=
    @g_rexv (.classMem (syn_copk (.cv y) C) A) y
  have p0002 :=
    @g_syl6bb (.classMem C V) (.classMem C (syn_cimak A (syn_cvv))) (syn_wrex y (syn_cvv) (.classMem (syn_copk (.cv y) C) A)) (syn_wex y (.classMem (syn_copk (.cv y) C) A)) p0000 p0001
  exact p0002

noncomputable def g_elimak
    (y : Var) (A : Class) (B : Class) (C : Class) (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_C_y : y ∉ C.fv) (hyp_elimak_1 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem C (syn_cimak A B)) (syn_wrex y B (.classMem (syn_copk (.cv y) C) A))) := by
  let proofSupport : Finset Var := ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_elimakg y A B C (syn_cvv) (by exact (show y ∉ (A).fv from (by exact dv_A_y))) (by exact (show y ∉ (B).fv from (by exact dv_B_y))) (by exact (show y ∉ (C).fv from (by exact dv_C_y)))
  have p0001 :=
    Nominal.mp hyp_elimak_1 p0000
  exact p0001

noncomputable def g_elimakv
    (y : Var) (A : Class) (C : Class) (dv_A_y : y ∉ A.fv) (dv_C_y : y ∉ C.fv) (hyp_elimak_1 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem C (syn_cimak A (syn_cvv))) (syn_wex y (.classMem (syn_copk (.cv y) C) A))) := by
  let proofSupport : Finset Var := ({y} : Finset Var) ∪ A.fv ∪ C.fv
  have p0000 :=
    @g_elimakvg y A C (syn_cvv) (by exact (show y ∉ (A).fv from (by exact dv_A_y))) (by exact (show y ∉ (C).fv from (by exact dv_C_y)))
  have p0001 :=
    Nominal.mp hyp_elimak_1 p0000
  exact p0001



#print axioms g_elimakv

end NFChoice.DirectNominalPrf.WPPReplay
