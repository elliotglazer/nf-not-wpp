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
import NominalWPPReplayChunk009StructuralPart015


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

noncomputable def g_insklem
    (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) (hyp_insklem_1 : Nominal.NPrf (syn_wss A (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))) (hyp_insklem_2 : Nominal.NPrf (syn_wss B (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))) :
    Nominal.NPrf (syn_wb (.classEq A B) (.all x (.all y (.all z (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) A) (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) B)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ A.fv ∪ B.fv
  let w : Var := freshVar proofSupport 0
  let t : Var := freshVar proofSupport 1
  let u : Var := freshVar proofSupport 2
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_w : y ≠ w :=
    Ne.symm fresh_w_ne_y
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_z_ne_w : z ≠ w :=
    Ne.symm fresh_w_ne_z
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_t_ne_x : t ≠ x := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_t : x ≠ t :=
    Ne.symm fresh_t_ne_x
  have fresh_t_ne_y : t ≠ y := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_t : y ≠ t :=
    Ne.symm fresh_t_ne_y
  have fresh_t_ne_z : t ≠ z := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_z_ne_t : z ≠ t :=
    Ne.symm fresh_t_ne_z
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_u_ne_x : u ≠ x := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_u : x ≠ u :=
    Ne.symm fresh_u_ne_x
  have fresh_u_ne_y : u ≠ y := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_u : y ≠ u :=
    Ne.symm fresh_u_ne_y
  have fresh_u_ne_z : u ≠ z := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_z_ne_u : z ≠ u :=
    Ne.symm fresh_u_ne_z
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_w_ne_t : w ≠ t := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_t_ne_w : t ≠ w :=
    Ne.symm fresh_w_ne_t
  have fresh_w_ne_u : w ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_u_ne_w : u ≠ w :=
    Ne.symm fresh_w_ne_u
  have fresh_t_ne_u : t ≠ u := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_u_ne_t : u ≠ t :=
    Ne.symm fresh_t_ne_u
  have p0000 :=
    @g_ssofeq w A B (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (by exact (show w ∉ (A).fv from (by exact fresh_w_not_A))) (by exact (show w ∉ (B).fv from (by exact fresh_w_not_B))) (by exact (show w ∉ ((syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show w ∉ (((syn_cpw1 (syn_c1c))).fv) ∪ (((syn_cxpk (syn_cvv) (syn_cvv))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((syn_cpw1 (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show w ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))) (show w ∉ ((syn_cxpk (syn_cvv) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show w ∉ (((syn_cvv)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show w ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))
  have p0001 :=
    @g_mp2an (syn_wss A (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))) (syn_wss B (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))) (syn_wb (.classEq A B) (syn_wral w (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B)))) hyp_insklem_1 hyp_insklem_2 p0000
  have p0002 :=
    @g_n_19_23v (syn_wex y (syn_wex z (.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))))) (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B)) x (by exact (show x ∉ ((syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb]; exact (show x ∉ (((Wff.classMem (.cv w) A)).fv) ∪ (((Wff.classMem (.cv w) B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Wff.classMem (.cv w) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((Class.cv w)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv w)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({w} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ w from (by exact fresh_x_ne_w)))))) (show x ∉ (A).fv from (by exact dv_A_x)))))) (show x ∉ ((Wff.classMem (.cv w) B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((Class.cv w)).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv w)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({w} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ w from (by exact fresh_x_ne_w)))))) (show x ∉ (B).fv from (by exact dv_B_x)))))))))))
  have p0003 :=
    @g_n_19_23vv (.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))) (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B)) y z (by exact (show y ∉ ((syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb]; exact (show y ∉ (((Wff.classMem (.cv w) A)).fv) ∪ (((Wff.classMem (.cv w) B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Wff.classMem (.cv w) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((Class.cv w)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv w)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({w} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ w from (by exact fresh_y_ne_w)))))) (show y ∉ (A).fv from (by exact dv_A_y)))))) (show y ∉ ((Wff.classMem (.cv w) B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((Class.cv w)).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv w)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({w} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ w from (by exact fresh_y_ne_w)))))) (show y ∉ (B).fv from (by exact dv_B_y))))))))))) (by exact (show z ∉ ((syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb]; exact (show z ∉ (((Wff.classMem (.cv w) A)).fv) ∪ (((Wff.classMem (.cv w) B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Wff.classMem (.cv w) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show z ∉ (((Class.cv w)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv w)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({w} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ w from (by exact fresh_z_ne_w)))))) (show z ∉ (A).fv from (by exact dv_A_z)))))) (show z ∉ ((Wff.classMem (.cv w) B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show z ∉ (((Class.cv w)).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv w)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({w} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ w from (by exact fresh_z_ne_w)))))) (show z ∉ (B).fv from (by exact dv_B_z)))))))))))
  have p0004 :=
    @g_albii (.all y (.all z (.imp (.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))) (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B))))) (.imp (syn_wex y (syn_wex z (.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))))) (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B))) x p0003
  have p0005 :=
    @g_n_19_42vv (.classMem (.cv t) (syn_cpw1 (syn_c1c))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) y z (by exact (show y ∉ ((Wff.classMem (.cv t) (syn_cpw1 (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((Class.cv t)).fv) ∪ (((syn_cpw1 (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv t)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({t} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ t from (by exact fresh_y_ne_t)))))) (show y ∉ ((syn_cpw1 (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show y ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))) (by exact (show z ∉ ((Wff.classMem (.cv t) (syn_cpw1 (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show z ∉ (((Class.cv t)).fv) ∪ (((syn_cpw1 (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv t)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({t} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ t from (by exact fresh_z_ne_t)))))) (show z ∉ ((syn_cpw1 (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show z ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))
  have p0006 :=
    @g_anbi2i (syn_wex y (syn_wex z (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))))) (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c))) (syn_wex y (syn_wex z (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))))) (.classEq (.cv w) (syn_copk (.cv t) (.cv u))) p0005
  have p0007 :=
    @g_n_19_42vv (.classEq (.cv w) (syn_copk (.cv t) (.cv u))) (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))) y z (by exact (show y ∉ ((Wff.classEq (.cv w) (syn_copk (.cv t) (.cv u)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ (((Class.cv w)).fv) ∪ (((syn_copk (.cv t) (.cv u))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv w)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({w} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ w from (by exact fresh_y_ne_w)))))) (show y ∉ ((syn_copk (.cv t) (.cv u))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show y ∉ (((Class.cv t)).fv) ∪ (((Class.cv u)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv t)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({t} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ t from (by exact fresh_y_ne_t)))))) (show y ∉ ((Class.cv u)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({u} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ u from (by exact fresh_y_ne_u))))))))))))))) (by exact (show z ∉ ((Wff.classEq (.cv w) (syn_copk (.cv t) (.cv u)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show z ∉ (((Class.cv w)).fv) ∪ (((syn_copk (.cv t) (.cv u))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv w)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({w} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ w from (by exact fresh_z_ne_w)))))) (show z ∉ ((syn_copk (.cv t) (.cv u))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show z ∉ (((Class.cv t)).fv) ∪ (((Class.cv u)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv t)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({t} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ t from (by exact fresh_z_ne_t)))))) (show z ∉ ((Class.cv u)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({u} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ u from (by exact fresh_z_ne_u)))))))))))))))
  have p0008 :=
    @g_elvvk y z (.cv u) (by exact (show y ∉ ((Class.cv u)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({u} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ u from (by exact fresh_y_ne_u))))))) (by exact (show z ∉ ((Class.cv u)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({u} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ u from (by exact fresh_z_ne_u))))))) (show y ≠ z from (by exact dv_y_z))
  have p0009 :=
    @g_anbi2i (.classMem (.cv u) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_wex y (syn_wex z (.classEq (.cv u) (syn_copk (.cv y) (.cv z))))) (.classMem (.cv t) (syn_cpw1 (syn_c1c))) p0008
  have p0010 :=
    @g_anbi2i (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c))) (.classMem (.cv u) (syn_cxpk (syn_cvv) (syn_cvv)))) (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c))) (syn_wex y (syn_wex z (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))))) (.classEq (.cv w) (syn_copk (.cv t) (.cv u))) p0009
  have p0011 :=
    @g_n_3bitr4ri (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u))) (syn_wex y (syn_wex z (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z))))))) (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u))) (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c))) (syn_wex y (syn_wex z (.classEq (.cv u) (syn_copk (.cv y) (.cv z))))))) (syn_wex y (syn_wex z (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u))) (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z))))))) (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u))) (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c))) (.classMem (.cv u) (syn_cxpk (syn_cvv) (syn_cvv))))) p0006 p0007 p0010
  have p0012 :=
    @g_n_2exbii (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u))) (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c))) (.classMem (.cv u) (syn_cxpk (syn_cvv) (syn_cvv))))) (syn_wex y (syn_wex z (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u))) (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z))))))) t u p0011
  have p0013 :=
    @g_elxpk t u (.cv w) (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)) (by exact (show t ∉ ((Class.cv w)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({w} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ w from (by exact fresh_t_ne_w))))))) (by exact (show u ∉ ((Class.cv w)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show u ∉ ({w} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show u ≠ w from (by exact fresh_u_ne_w))))))) (by exact (show t ∉ ((syn_cpw1 (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show t ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))) (by exact (show u ∉ ((syn_cpw1 (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show u ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show u ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))) (by exact (show t ∉ ((syn_cxpk (syn_cvv) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show t ∉ (((syn_cvv)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show t ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) (by exact (show u ∉ ((syn_cxpk (syn_cvv) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show u ∉ (((syn_cvv)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show u ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show u ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show u ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show u ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) (show t ≠ u from (by exact fresh_t_ne_u))
  have p0014 :=
    @g_exrot3 (.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))) x y z
  have p0015 :=
    @g_exancom (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z)))) (.classMem (.cv t) (syn_cpw1 (syn_c1c))) t
  have p0016 :=
    @g_elpw11c x (.cv t) (by exact (show x ∉ ((Class.cv t)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({t} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ t from (by exact fresh_x_ne_t)))))))
  have p0017 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_c1c))) (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (.cv x))))) (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z)))) p0016
  have p0018 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (.cv x)))) (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z)))) x (by exact (show x ∉ ((Wff.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ (((Class.cv w)).fv) ∪ (((syn_copk (.cv t) (syn_copk (.cv y) (.cv z)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv w)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({w} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ w from (by exact fresh_x_ne_w)))))) (show x ∉ ((syn_copk (.cv t) (syn_copk (.cv y) (.cv z)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show x ∉ (((Class.cv t)).fv) ∪ (((syn_copk (.cv y) (.cv z))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv t)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({t} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ t from (by exact fresh_x_ne_t)))))) (show x ∉ ((syn_copk (.cv y) (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show x ∉ (((Class.cv y)).fv) ∪ (((Class.cv z)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact dv_x_y)))))) (show x ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ z from (by exact dv_x_z)))))))))))))))))))
  have p0019 :=
    @g_bitr4i (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c))) (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z))))) (syn_wa (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (.cv x))))) (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z))))) (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv x)))) (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z)))))) p0017 p0018
  have p0020 :=
    @g_exbii (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c))) (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z))))) (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv x)))) (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z)))))) t p0019
  have p0021 :=
    @g_bitri (syn_wex t (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z)))) (.classMem (.cv t) (syn_cpw1 (syn_c1c))))) (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c))) (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z)))))) (syn_wex t (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv x)))) (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z))))))) p0015 p0020
  have p0022 :=
    @g_ancom (.classMem (.cv t) (syn_cpw1 (syn_c1c))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))
  have p0023 :=
    @g_anbi2i (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))) (syn_wa (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (.classMem (.cv t) (syn_cpw1 (syn_c1c)))) (.classEq (.cv w) (syn_copk (.cv t) (.cv u))) p0022
  have p0024 :=
    @g_an12 (.classEq (.cv w) (syn_copk (.cv t) (.cv u))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
  have p0025 :=
    @g_bitri (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u))) (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z))))) (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u))) (syn_wa (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (.classMem (.cv t) (syn_cpw1 (syn_c1c))))) (syn_wa (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u))) (.classMem (.cv t) (syn_cpw1 (syn_c1c))))) p0023 p0024
  have p0026 :=
    @g_n_2exbii (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u))) (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z))))) (syn_wa (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u))) (.classMem (.cv t) (syn_cpw1 (syn_c1c))))) t u p0025
  have p0027 :=
    @g_opkex (.cv y) (.cv z)
  have p0028 :=
    @g_opkeq2 (.cv u) (syn_copk (.cv y) (.cv z)) (.cv t)
  have p0029 :=
    @g_eqeq2d (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (syn_copk (.cv t) (.cv u)) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z))) (.cv w) p0028
  have p0030 :=
    @g_anbi1d (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (.classEq (.cv w) (syn_copk (.cv t) (.cv u))) (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z)))) (.classMem (.cv t) (syn_cpw1 (syn_c1c))) p0029
  have p0031 :=
    @g_ceqsexv (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u))) (.classMem (.cv t) (syn_cpw1 (syn_c1c)))) (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z)))) (.classMem (.cv t) (syn_cpw1 (syn_c1c)))) u (syn_copk (.cv y) (.cv z)) (by exact (show u ∉ ((syn_copk (.cv y) (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show u ∉ (((Class.cv y)).fv) ∪ (((Class.cv z)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show u ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show u ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show u ≠ y from (by exact fresh_u_ne_y)))))) (show u ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show u ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show u ≠ z from (by exact fresh_u_ne_z))))))))))) (by exact (show u ∉ ((syn_wa (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z)))) (.classMem (.cv t) (syn_cpw1 (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show u ∉ (((Wff.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z))))).fv) ∪ (((Wff.classMem (.cv t) (syn_cpw1 (syn_c1c)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show u ∉ ((Wff.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show u ∉ (((Class.cv w)).fv) ∪ (((syn_copk (.cv t) (syn_copk (.cv y) (.cv z)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show u ∉ ((Class.cv w)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show u ∉ ({w} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show u ≠ w from (by exact fresh_u_ne_w)))))) (show u ∉ ((syn_copk (.cv t) (syn_copk (.cv y) (.cv z)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show u ∉ (((Class.cv t)).fv) ∪ (((syn_copk (.cv y) (.cv z))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show u ∉ ((Class.cv t)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show u ∉ ({t} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show u ≠ t from (by exact fresh_u_ne_t)))))) (show u ∉ ((syn_copk (.cv y) (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show u ∉ (((Class.cv y)).fv) ∪ (((Class.cv z)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show u ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show u ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show u ≠ y from (by exact fresh_u_ne_y)))))) (show u ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show u ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show u ≠ z from (by exact fresh_u_ne_z)))))))))))))))))) (show u ∉ ((Wff.classMem (.cv t) (syn_cpw1 (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show u ∉ (((Class.cv t)).fv) ∪ (((syn_cpw1 (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show u ∉ ((Class.cv t)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show u ∉ ({t} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show u ≠ t from (by exact fresh_u_ne_t)))))) (show u ∉ ((syn_cpw1 (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show u ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show u ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))))) p0027 p0030
  have p0032 :=
    @g_exbii (syn_wex u (syn_wa (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u))) (.classMem (.cv t) (syn_cpw1 (syn_c1c)))))) (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z)))) (.classMem (.cv t) (syn_cpw1 (syn_c1c)))) t p0031
  have p0033 :=
    @g_bitri (syn_wex t (syn_wex u (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u))) (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z))))))) (syn_wex t (syn_wex u (syn_wa (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u))) (.classMem (.cv t) (syn_cpw1 (syn_c1c))))))) (syn_wex t (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z)))) (.classMem (.cv t) (syn_cpw1 (syn_c1c))))) p0026 p0032
  have p0034 :=
    @g_snex (syn_csn (.cv x))
  have p0035 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))
  have p0036 :=
    @g_eqeq2d (.classEq (.cv t) (syn_csn (syn_csn (.cv x)))) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z))) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) (.cv w) p0035
  have p0037 :=
    @g_ceqsexv (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z)))) (.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))) t (syn_csn (syn_csn (.cv x))) (by exact (show t ∉ ((syn_csn (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ x from (by exact fresh_t_ne_x))))))))))) (by exact (show t ∉ ((Wff.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show t ∉ (((Class.cv w)).fv) ∪ (((syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((Class.cv w)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({w} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ w from (by exact fresh_t_ne_w)))))) (show t ∉ ((syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show t ∉ (((syn_csn (syn_csn (.cv x)))).fv) ∪ (((syn_copk (.cv y) (.cv z))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_csn (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ x from (by exact fresh_t_ne_x)))))))))) (show t ∉ ((syn_copk (.cv y) (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show t ∉ (((Class.cv y)).fv) ∪ (((Class.cv z)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ y from (by exact fresh_t_ne_y)))))) (show t ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ z from (by exact fresh_t_ne_z))))))))))))))))))) p0034 p0036
  have p0038 :=
    @g_exbii (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv x)))) (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z)))))) (.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))) x p0037
  have p0039 :=
    @g_excom (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv x)))) (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z))))) x t
  have p0040 :=
    @g_bitr3i (syn_wex x (.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))))) (syn_wex x (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv x)))) (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z))))))) (syn_wex t (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv x)))) (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z))))))) p0038 p0039
  have p0041 :=
    @g_n_3bitr4ri (syn_wex t (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z)))) (.classMem (.cv t) (syn_cpw1 (syn_c1c))))) (syn_wex t (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv x)))) (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z))))))) (syn_wex t (syn_wex u (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u))) (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z))))))) (syn_wex x (.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))))) p0021 p0033 p0040
  have p0042 :=
    @g_n_2exbii (syn_wex x (.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))))) (syn_wex t (syn_wex u (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u))) (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z))))))) y z p0041
  have p0043 :=
    @g_exrot4 (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u))) (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z))))) y z t u
  have p0044 :=
    @g_bitri (syn_wex y (syn_wex z (syn_wex x (.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))))))) (syn_wex y (syn_wex z (syn_wex t (syn_wex u (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u))) (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z))))))))) (syn_wex t (syn_wex u (syn_wex y (syn_wex z (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u))) (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z))))))))) p0042 p0043
  have p0045 :=
    @g_bitri (syn_wex x (syn_wex y (syn_wex z (.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))))))) (syn_wex y (syn_wex z (syn_wex x (.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))))))) (syn_wex t (syn_wex u (syn_wex y (syn_wex z (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u))) (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z))))))))) p0014 p0044
  have p0046 :=
    @g_n_3bitr4i (syn_wex t (syn_wex u (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u))) (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c))) (.classMem (.cv u) (syn_cxpk (syn_cvv) (syn_cvv))))))) (syn_wex t (syn_wex u (syn_wex y (syn_wex z (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u))) (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z))))))))) (.classMem (.cv w) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))) (syn_wex x (syn_wex y (syn_wex z (.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))))))) p0012 p0013 p0045
  have p0047 :=
    @g_imbi1i (.classMem (.cv w) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))) (syn_wex x (syn_wex y (syn_wex z (.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))))))) (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B)) p0046
  have p0048 :=
    @g_n_3bitr4ri (.all x (.imp (syn_wex y (syn_wex z (.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))))) (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B)))) (.imp (syn_wex x (syn_wex y (syn_wex z (.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))))))) (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B))) (.all x (.all y (.all z (.imp (.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))) (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B)))))) (.imp (.classMem (.cv w) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))) (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B))) p0002 p0004 p0047
  have p0049 :=
    @g_albii (.imp (.classMem (.cv w) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))) (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B))) (.all x (.all y (.all z (.imp (.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))) (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B)))))) w p0048
  have p0050 :=
    (by simpa [syn_wb, syn_wral] using (Nominal.biimpRefl (syn_wral w (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B)))))
  have p0051 :=
    @g_alcom (.all y (.all z (.imp (.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))) (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B))))) w x
  have p0052 :=
    @g_alrot3 (.imp (.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))) (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B))) w y z
  have p0053 :=
    @g_albii (.all w (.all y (.all z (.imp (.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))) (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B)))))) (.all y (.all z (.all w (.imp (.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))) (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B)))))) x p0052
  have p0054 :=
    @g_opkex (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))
  have p0055 :=
    @g_eleq1 (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) A
  have p0056 :=
    @g_eleq1 (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) B
  have p0057 :=
    @g_bibi12d (.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))) (.classMem (.cv w) A) (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) A) (.classMem (.cv w) B) (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) B) p0055 p0056
  have p0058 :=
    @g_ceqsalv (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B)) (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) A) (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) B)) w (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) (by exact (show w ∉ ((syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show w ∉ (((syn_csn (syn_csn (.cv x)))).fv) ∪ (((syn_copk (.cv y) (.cv z))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((syn_csn (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show w ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show w ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ x from (by exact fresh_w_ne_x)))))))))) (show w ∉ ((syn_copk (.cv y) (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show w ∉ (((Class.cv y)).fv) ∪ (((Class.cv z)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y)))))) (show w ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ z from (by exact fresh_w_ne_z))))))))))))))) (by exact (show w ∉ ((syn_wb (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) A) (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb]; exact (show w ∉ (((Wff.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) A)).fv) ∪ (((Wff.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Wff.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show w ∉ (((syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show w ∉ (((syn_csn (syn_csn (.cv x)))).fv) ∪ (((syn_copk (.cv y) (.cv z))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((syn_csn (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show w ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show w ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ x from (by exact fresh_w_ne_x)))))))))) (show w ∉ ((syn_copk (.cv y) (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show w ∉ (((Class.cv y)).fv) ∪ (((Class.cv z)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y)))))) (show w ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ z from (by exact fresh_w_ne_z)))))))))))))) (show w ∉ (A).fv from (by exact fresh_w_not_A)))))) (show w ∉ ((Wff.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show w ∉ (((syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show w ∉ (((syn_csn (syn_csn (.cv x)))).fv) ∪ (((syn_copk (.cv y) (.cv z))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((syn_csn (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show w ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show w ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ x from (by exact fresh_w_ne_x)))))))))) (show w ∉ ((syn_copk (.cv y) (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show w ∉ (((Class.cv y)).fv) ∪ (((Class.cv z)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y)))))) (show w ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ z from (by exact fresh_w_ne_z)))))))))))))) (show w ∉ (B).fv from (by exact fresh_w_not_B))))))))))) p0054 p0057
  have p0059 :=
    @g_albii (.all w (.imp (.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))) (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B)))) (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) A) (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) B)) z p0058
  have p0060 :=
    @g_n_2albii (.all z (.all w (.imp (.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))) (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B))))) (.all z (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) A) (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) B))) x y p0059
  have p0061 :=
    @g_n_3bitrri (.all w (.all x (.all y (.all z (.imp (.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))) (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B))))))) (.all x (.all w (.all y (.all z (.imp (.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))) (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B))))))) (.all x (.all y (.all z (.all w (.imp (.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))) (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B))))))) (.all x (.all y (.all z (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) A) (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) B))))) p0051 p0053 p0060
  have p0062 :=
    @g_n_3bitr4i (.all w (.imp (.classMem (.cv w) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))) (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B)))) (.all w (.all x (.all y (.all z (.imp (.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))) (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B))))))) (syn_wral w (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B))) (.all x (.all y (.all z (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) A) (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) B))))) p0049 p0050 p0061
  have p0063 :=
    @g_bitri (.classEq A B) (syn_wral w (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B))) (.all x (.all y (.all z (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) A) (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) B))))) p0001 p0062
  exact p0063



#print axioms g_insklem

end NFChoice.DirectNominalPrf.WPPReplay
