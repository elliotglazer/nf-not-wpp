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
import NominalWPPReplayChunk009StructuralPart040


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

noncomputable def g_lefinlteq
    (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf (.imp (syn_w3a (.classMem A V) (.classMem B W) (syn_wne A (syn_c0))) (syn_wb (.classMem (syn_copk A B) (syn_clefin)) (syn_wo (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
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
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_V : y ∉ V.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_W : y ∉ W.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have p0000 :=
    @g_nnc0suc y (.cv x) (by exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))))
  have p0001 :=
    @g_addceq2 (.cv x) (syn_c0c) A
  have p0002 :=
    @g_addcid1 A
  have p0003 :=
    @g_syl6req (.classEq (.cv x) (syn_c0c)) (syn_cplc A (.cv x)) (syn_cplc A (syn_c0c)) A p0001 p0002
  have p0004 :=
    @g_addceq2 (.cv x) (syn_cplc (.cv y) (syn_c1c)) A
  have p0005 :=
    @g_addcass A (.cv y) (syn_c1c)
  have p0006 :=
    @g_syl6eqr (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (syn_cplc A (.cv x)) (syn_cplc A (syn_cplc (.cv y) (syn_c1c))) (syn_cplc (syn_cplc A (.cv y)) (syn_c1c)) p0004 p0005
  have p0007 :=
    @g_reximi (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.classEq (syn_cplc A (.cv x)) (syn_cplc (syn_cplc A (.cv y)) (syn_c1c))) y (syn_cnnc) p0006
  have p0008 :=
    @g_orim12i (.classEq (.cv x) (syn_c0c)) (.classEq A (syn_cplc A (.cv x))) (syn_wrex y (syn_cnnc) (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c)))) (syn_wrex y (syn_cnnc) (.classEq (syn_cplc A (.cv x)) (syn_cplc (syn_cplc A (.cv y)) (syn_c1c)))) p0003 p0007
  have p0009 :=
    @g_sylbi (.classMem (.cv x) (syn_cnnc)) (syn_wo (.classEq (.cv x) (syn_c0c)) (syn_wrex y (syn_cnnc) (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))))) (syn_wo (.classEq A (syn_cplc A (.cv x))) (syn_wrex y (syn_cnnc) (.classEq (syn_cplc A (.cv x)) (syn_cplc (syn_cplc A (.cv y)) (syn_c1c))))) p0000 p0008
  have p0010 :=
    @g_orcomd (.classMem (.cv x) (syn_cnnc)) (.classEq A (syn_cplc A (.cv x))) (syn_wrex y (syn_cnnc) (.classEq (syn_cplc A (.cv x)) (syn_cplc (syn_cplc A (.cv y)) (syn_c1c)))) p0009
  have p0011 :=
    @g_eqeq1 B (syn_cplc A (.cv x)) (syn_cplc (syn_cplc A (.cv y)) (syn_c1c))
  have p0012 :=
    @g_rexbidv (.classEq B (syn_cplc A (.cv x))) (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c))) (.classEq (syn_cplc A (.cv x)) (syn_cplc (syn_cplc A (.cv y)) (syn_c1c))) y (syn_cnnc) (by exact (show y ∉ ((Wff.classEq B (syn_cplc A (.cv x)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ ((B).fv) ∪ (((syn_cplc A (.cv x))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (B).fv from (by exact fresh_y_not_B)) (show y ∉ ((syn_cplc A (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show y ∉ ((A).fv) ∪ (((Class.cv x)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))))))))))) p0011
  have p0013 :=
    @g_eqeq2 B (syn_cplc A (.cv x)) A
  have p0014 :=
    @g_orbi12d (.classEq B (syn_cplc A (.cv x))) (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c)))) (syn_wrex y (syn_cnnc) (.classEq (syn_cplc A (.cv x)) (syn_cplc (syn_cplc A (.cv y)) (syn_c1c)))) (.classEq A B) (.classEq A (syn_cplc A (.cv x))) p0012 p0013
  have p0015 :=
    @g_syl5ibrcom (.classMem (.cv x) (syn_cnnc)) (syn_wo (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c)))) (.classEq A B)) (.classEq B (syn_cplc A (.cv x))) (syn_wo (syn_wrex y (syn_cnnc) (.classEq (syn_cplc A (.cv x)) (syn_cplc (syn_cplc A (.cv y)) (syn_c1c)))) (.classEq A (syn_cplc A (.cv x)))) p0010 p0014
  have p0016 :=
    @g_rexlimiv (.classEq B (syn_cplc A (.cv x))) (syn_wo (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c)))) (.classEq A B)) x (syn_cnnc) (by exact (show x ∉ ((syn_wo (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c)))) (.classEq A B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo]; exact (show x ∉ (((syn_wrex y (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c))))).fv) ∪ (((Wff.classEq A B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_wrex y (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex]; exact (show x ∉ ((((syn_cnnc)).fv).erase y) ∪ ((((Wff.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c)))).fv).erase y) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (((syn_cnnc)).fv).erase y from (fun hmem => (show x ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (Finset.mem_of_mem_erase hmem))) (show x ∉ (((Wff.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c)))).fv).erase y from (fun hmem => (show x ∉ ((Wff.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ ((B).fv) ∪ (((syn_cplc (syn_cplc A (.cv y)) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (B).fv from (by exact fresh_x_not_B)) (show x ∉ ((syn_cplc (syn_cplc A (.cv y)) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ (((syn_cplc A (.cv y))).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cplc A (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ ((A).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y)))))))))) (show x ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (Finset.mem_of_mem_erase hmem))))))) (show x ∉ ((Wff.classEq A B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ (B).fv from (by exact fresh_x_not_B))))))))))) p0015
  have p0017 :=
    @g_eqeq2i (syn_cplc (syn_cplc A (.cv y)) (syn_c1c)) (syn_cplc A (syn_cplc (.cv y) (syn_c1c))) B p0005
  have p0018 :=
    @g_peano2 (.cv y)
  have p0019 :=
    @g_eqeq2d (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (syn_cplc A (.cv x)) (syn_cplc A (syn_cplc (.cv y) (syn_c1c))) B p0004
  have p0020 :=
    @g_rspcev (.classEq B (syn_cplc A (.cv x))) (.classEq B (syn_cplc A (syn_cplc (.cv y) (syn_c1c)))) x (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc) (by exact (show x ∉ ((syn_cplc (.cv y) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ (((Class.cv y)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y)))))) (show x ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) (by exact (show x ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show x ∉ ((Wff.classEq B (syn_cplc A (syn_cplc (.cv y) (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ ((B).fv) ∪ (((syn_cplc A (syn_cplc (.cv y) (syn_c1c)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (B).fv from (by exact fresh_x_not_B)) (show x ∉ ((syn_cplc A (syn_cplc (.cv y) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ ((A).fv) ∪ (((syn_cplc (.cv y) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ ((syn_cplc (.cv y) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ (((Class.cv y)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y)))))) (show x ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))))))) p0019
  have p0021 :=
    @g_sylan (.classMem (.cv y) (syn_cnnc)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classEq B (syn_cplc A (syn_cplc (.cv y) (syn_c1c)))) (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc A (.cv x)))) p0018 p0020
  have p0022 :=
    @g_sylan2b (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c))) (.classMem (.cv y) (syn_cnnc)) (.classEq B (syn_cplc A (syn_cplc (.cv y) (syn_c1c)))) (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc A (.cv x)))) p0017 p0021
  have p0023 :=
    @g_rexlimiva (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c))) (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc A (.cv x)))) y (syn_cnnc) (by exact (show y ∉ ((syn_wrex x (syn_cnnc) (.classEq B (syn_cplc A (.cv x))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex]; exact (show y ∉ ((((syn_cnnc)).fv).erase x) ∪ ((((Wff.classEq B (syn_cplc A (.cv x)))).fv).erase x) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (((syn_cnnc)).fv).erase x from (fun hmem => (show y ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (Finset.mem_of_mem_erase hmem))) (show y ∉ (((Wff.classEq B (syn_cplc A (.cv x)))).fv).erase x from (fun hmem => (show y ∉ ((Wff.classEq B (syn_cplc A (.cv x)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ ((B).fv) ∪ (((syn_cplc A (.cv x))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (B).fv from (by exact fresh_y_not_B)) (show y ∉ ((syn_cplc A (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show y ∉ ((A).fv) ∪ (((Class.cv x)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))))))))))) (Finset.mem_of_mem_erase hmem)))))))) p0022
  have p0024 :=
    @g_peano1
  have p0025 :=
    @g_eqcomi (syn_cplc A (syn_c0c)) A p0002
  have p0026 :=
    @g_eqeq2d (.classEq (.cv x) (syn_c0c)) (syn_cplc A (.cv x)) (syn_cplc A (syn_c0c)) A p0001
  have p0027 :=
    @g_rspcev (.classEq A (syn_cplc A (.cv x))) (.classEq A (syn_cplc A (syn_c0c))) x (syn_c0c) (syn_cnnc) (by exact (show x ∉ ((syn_c0c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show x ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show x ∉ ((Wff.classEq A (syn_cplc A (syn_c0c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ ((A).fv) ∪ (((syn_cplc A (syn_c0c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ ((syn_cplc A (syn_c0c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ ((A).fv) ∪ (((syn_c0c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ ((syn_c0c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) p0026
  have p0028 :=
    @g_mp2an (.classMem (syn_c0c) (syn_cnnc)) (.classEq A (syn_cplc A (syn_c0c))) (syn_wrex x (syn_cnnc) (.classEq A (syn_cplc A (.cv x)))) p0024 p0025 p0027
  have p0029 :=
    @g_eqeq1 A B (syn_cplc A (.cv x))
  have p0030 :=
    @g_rexbidv (.classEq A B) (.classEq A (syn_cplc A (.cv x))) (.classEq B (syn_cplc A (.cv x))) x (syn_cnnc) (by exact (show x ∉ ((Wff.classEq A B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ (B).fv from (by exact fresh_x_not_B))))))) p0029
  have p0031 :=
    @g_mpbii (.classEq A B) (syn_wrex x (syn_cnnc) (.classEq A (syn_cplc A (.cv x)))) (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc A (.cv x)))) p0028 p0030
  have p0032 :=
    @g_jaoi (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c)))) (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc A (.cv x)))) (.classEq A B) p0023 p0031
  have p0033 :=
    @g_impbii (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc A (.cv x)))) (syn_wo (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c)))) (.classEq A B)) p0016 p0032
  have p0034 :=
    @g_a1i (syn_wb (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc A (.cv x)))) (syn_wo (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c)))) (.classEq A B))) (syn_w3a (.classMem A V) (.classMem B W) (syn_wne A (syn_c0))) p0033
  have p0035 :=
    @g_opklefing x A B V W (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
  have p0036 :=
    @g_n_3adant3 (.classMem A V) (.classMem B W) (syn_wb (.classMem (syn_copk A B) (syn_clefin)) (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc A (.cv x))))) (syn_wne A (syn_c0)) p0035
  have p0037 :=
    @g_opkltfing y A B V W (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
  have p0038 :=
    @g_adantr (syn_wa (.classMem A V) (.classMem B W)) (syn_wb (.classMem (syn_copk A B) (syn_cltfin)) (syn_wa (syn_wne A (syn_c0)) (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c)))))) (syn_wne A (syn_c0)) p0037
  have p0039 :=
    @g_ibar (syn_wne A (syn_c0)) (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c))))
  have p0040 :=
    @g_adantl (syn_wne A (syn_c0)) (syn_wb (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c)))) (syn_wa (syn_wne A (syn_c0)) (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c)))))) (syn_wa (.classMem A V) (.classMem B W)) p0039
  have p0041 :=
    @g_bitr4d (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (syn_wne A (syn_c0))) (.classMem (syn_copk A B) (syn_cltfin)) (syn_wa (syn_wne A (syn_c0)) (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c))))) (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c)))) p0038 p0040
  have p0042 :=
    @g_orbi1d (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (syn_wne A (syn_c0))) (.classMem (syn_copk A B) (syn_cltfin)) (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c)))) (.classEq A B) p0041
  have p0043 :=
    @g_n_3impa (.classMem A V) (.classMem B W) (syn_wne A (syn_c0)) (syn_wb (syn_wo (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B)) (syn_wo (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c)))) (.classEq A B))) p0042
  have p0044 :=
    @g_n_3bitr4d (syn_w3a (.classMem A V) (.classMem B W) (syn_wne A (syn_c0))) (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc A (.cv x)))) (syn_wo (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c)))) (.classEq A B)) (.classMem (syn_copk A B) (syn_clefin)) (syn_wo (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B)) p0034 p0036 p0043
  exact p0044



#print axioms g_lefinlteq

end NFChoice.DirectNominalPrf.WPPReplay
