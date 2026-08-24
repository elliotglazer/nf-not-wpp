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
import NominalWPPReplayChunk009StructuralPart005


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

noncomputable def g_opkelins3kg
    (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_C_z : z ∉ C.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem B W)) (syn_wb (.classMem (syn_copk A B) (syn_cins3k C)) (syn_wex x (syn_wex y (syn_wex z (syn_w3a (.classEq A (syn_csn (syn_csn (.cv x)))) (.classEq B (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) C))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ V.fv ∪ W.fv
  let w : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  let t : Var := freshVar proofSupport 2
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))))
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))
  have fresh_y_ne_w : y ≠ w :=
    Ne.symm fresh_w_ne_y
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_z_ne_w : z ≠ w :=
    Ne.symm fresh_w_ne_z
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_w_not_C : w ∉ C.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_V : w ∉ V.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_W : w ∉ W.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_ne_x : u ≠ x := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))))
  have fresh_x_ne_u : x ≠ u :=
    Ne.symm fresh_u_ne_x
  have fresh_u_ne_y : u ≠ y := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))
  have fresh_y_ne_u : y ≠ u :=
    Ne.symm fresh_u_ne_y
  have fresh_u_ne_z : u ≠ z := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_z_ne_u : z ≠ u :=
    Ne.symm fresh_u_ne_z
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_not_V : u ∉ V.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_W : u ∉ W.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_t_ne_x : t ≠ x := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))))
  have fresh_x_ne_t : x ≠ t :=
    Ne.symm fresh_t_ne_x
  have fresh_t_ne_y : t ≠ y := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))
  have fresh_y_ne_t : y ≠ t :=
    Ne.symm fresh_t_ne_y
  have fresh_t_ne_z : t ≠ z := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_z_ne_t : z ≠ t :=
    Ne.symm fresh_t_ne_z
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_t_not_C : t ∉ C.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_t_not_V : t ∉ V.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_t_not_W : t ∉ W.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_w_ne_u : w ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_w : u ≠ w :=
    Ne.symm fresh_w_ne_u
  have fresh_w_ne_t : w ≠ t := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_t_ne_w : t ≠ w :=
    Ne.symm fresh_w_ne_t
  have fresh_u_ne_t : u ≠ t := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_t_ne_u : t ≠ u :=
    Ne.symm fresh_u_ne_t
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ins3k t w u z y x C (by exact (show x ∉ (C).fv from (by exact dv_C_x))) (by exact (show y ∉ (C).fv from (by exact dv_C_y))) (by exact (show z ∉ (C).fv from (by exact dv_C_z))) (by exact (show t ∉ (C).fv from (by exact fresh_t_not_C))) (by exact (show w ∉ (C).fv from (by exact fresh_w_not_C))) (by exact (show u ∉ (C).fv from (by exact fresh_u_not_C))) (show x ≠ y from (by exact dv_x_y)) (show x ≠ z from (by exact dv_x_z)) (show x ≠ t from (by exact fresh_x_ne_t)) (show x ≠ w from (by exact fresh_x_ne_w)) (show x ≠ u from (by exact fresh_x_ne_u)) (show y ≠ z from (by exact dv_y_z)) (show y ≠ t from (by exact fresh_y_ne_t)) (show y ≠ w from (by exact fresh_y_ne_w)) (show y ≠ u from (by exact fresh_y_ne_u)) (show z ≠ t from (by exact fresh_z_ne_t)) (show z ≠ w from (by exact fresh_z_ne_w)) (show z ≠ u from (by exact fresh_z_ne_u)) (show t ≠ w from (by exact fresh_t_ne_w)) (show t ≠ u from (by exact fresh_t_ne_u)) (show w ≠ u from (by exact fresh_w_ne_u))
  have p0001 :=
    @g_eqeq1 (.cv w) A (syn_csn (syn_csn (.cv x)))
  have p0002 :=
    @g_n_3anbi1d (.classEq (.cv w) A) (.classEq (.cv w) (syn_csn (syn_csn (.cv x)))) (.classEq A (syn_csn (syn_csn (.cv x)))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) C) p0001
  have p0003 :=
    @g_n_3exbidv (.classEq (.cv w) A) (syn_w3a (.classEq (.cv w) (syn_csn (syn_csn (.cv x)))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) C)) (syn_w3a (.classEq A (syn_csn (syn_csn (.cv x)))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) C)) x y z (by exact (show x ∉ ((Wff.classEq (.cv w) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ (((Class.cv w)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv w)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({w} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ w from (by exact fresh_x_ne_w)))))) (show x ∉ (A).fv from (by exact dv_A_x))))))) (by exact (show y ∉ ((Wff.classEq (.cv w) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ (((Class.cv w)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv w)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({w} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ w from (by exact fresh_y_ne_w)))))) (show y ∉ (A).fv from (by exact dv_A_y))))))) (by exact (show z ∉ ((Wff.classEq (.cv w) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show z ∉ (((Class.cv w)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv w)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({w} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ w from (by exact fresh_z_ne_w)))))) (show z ∉ (A).fv from (by exact dv_A_z))))))) p0002
  have p0004 :=
    @g_eqeq1 (.cv u) B (syn_copk (.cv y) (.cv z))
  have p0005 :=
    @g_n_3anbi2d (.classEq (.cv u) B) (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (.classEq B (syn_copk (.cv y) (.cv z))) (.classEq A (syn_csn (syn_csn (.cv x)))) (.classMem (syn_copk (.cv x) (.cv y)) C) p0004
  have p0006 :=
    @g_n_3exbidv (.classEq (.cv u) B) (syn_w3a (.classEq A (syn_csn (syn_csn (.cv x)))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) C)) (syn_w3a (.classEq A (syn_csn (syn_csn (.cv x)))) (.classEq B (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) C)) x y z (by exact (show x ∉ ((Wff.classEq (.cv u) B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ (((Class.cv u)).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv u)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({u} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ u from (by exact fresh_x_ne_u)))))) (show x ∉ (B).fv from (by exact dv_B_x))))))) (by exact (show y ∉ ((Wff.classEq (.cv u) B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ (((Class.cv u)).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv u)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({u} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ u from (by exact fresh_y_ne_u)))))) (show y ∉ (B).fv from (by exact dv_B_y))))))) (by exact (show z ∉ ((Wff.classEq (.cv u) B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show z ∉ (((Class.cv u)).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv u)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({u} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ u from (by exact fresh_z_ne_u)))))) (show z ∉ (B).fv from (by exact dv_B_z))))))) p0005
  have p0007 :=
    @g_opkelopkabg (syn_wex x (syn_wex y (syn_wex z (syn_w3a (.classEq (.cv w) (syn_csn (syn_csn (.cv x)))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) C))))) (syn_wex x (syn_wex y (syn_wex z (syn_w3a (.classEq A (syn_csn (syn_csn (.cv x)))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) C))))) (syn_wex x (syn_wex y (syn_wex z (syn_w3a (.classEq A (syn_csn (syn_csn (.cv x)))) (.classEq B (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) C))))) t w u (syn_cins3k C) A B V W (by exact (show w ∉ ((syn_cins3k C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k]; exact (show w ∉ (C).fv from (by exact fresh_w_not_C))))) (by exact (show u ∉ ((syn_cins3k C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k]; exact (show u ∉ (C).fv from (by exact fresh_u_not_C))))) (by exact (show t ∉ (A).fv from (by exact fresh_t_not_A))) (by exact (show w ∉ (A).fv from (by exact fresh_w_not_A))) (by exact (show u ∉ (A).fv from (by exact fresh_u_not_A))) (by exact (show t ∉ (B).fv from (by exact fresh_t_not_B))) (by exact (show w ∉ (B).fv from (by exact fresh_w_not_B))) (by exact (show u ∉ (B).fv from (by exact fresh_u_not_B))) (by exact (show u ∉ ((syn_wex x (syn_wex y (syn_wex z (syn_w3a (.classEq A (syn_csn (syn_csn (.cv x)))) (.classEq B (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) C)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex]; exact (show u ∉ (((syn_wex y (syn_wex z (syn_w3a (.classEq A (syn_csn (syn_csn (.cv x)))) (.classEq B (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) C))))).fv).erase x from (fun hmem => (show u ∉ ((syn_wex y (syn_wex z (syn_w3a (.classEq A (syn_csn (syn_csn (.cv x)))) (.classEq B (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) C))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex]; exact (show u ∉ (((syn_wex z (syn_w3a (.classEq A (syn_csn (syn_csn (.cv x)))) (.classEq B (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) C)))).fv).erase y from (fun hmem => (show u ∉ ((syn_wex z (syn_w3a (.classEq A (syn_csn (syn_csn (.cv x)))) (.classEq B (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) C)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex]; exact (show u ∉ (((syn_w3a (.classEq A (syn_csn (syn_csn (.cv x)))) (.classEq B (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) C))).fv).erase z from (fun hmem => (show u ∉ ((syn_w3a (.classEq A (syn_csn (syn_csn (.cv x)))) (.classEq B (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) C))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a]; exact (show u ∉ (((Wff.classMem (syn_copk (.cv x) (.cv y)) C)).fv) ∪ (((Wff.classEq A (syn_csn (syn_csn (.cv x))))).fv) ∪ (((Wff.classEq B (syn_copk (.cv y) (.cv z)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (fun hmem => (Finset.mem_union.mp hmem).elim (show u ∉ ((Wff.classMem (syn_copk (.cv x) (.cv y)) C)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show u ∉ (((syn_copk (.cv x) (.cv y))).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show u ∉ ((syn_copk (.cv x) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show u ∉ (((Class.cv x)).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show u ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show u ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show u ≠ x from (by exact fresh_u_ne_x)))))) (show u ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show u ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show u ≠ y from (by exact fresh_u_ne_y)))))))))) (show u ∉ (C).fv from (by exact fresh_u_not_C)))))) (show u ∉ ((Wff.classEq A (syn_csn (syn_csn (.cv x))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show u ∉ ((A).fv) ∪ (((syn_csn (syn_csn (.cv x)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show u ∉ (A).fv from (by exact fresh_u_not_A)) (show u ∉ ((syn_csn (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show u ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show u ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show u ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show u ≠ x from (by exact fresh_u_ne_x))))))))))))))) (show u ∉ ((Wff.classEq B (syn_copk (.cv y) (.cv z)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show u ∉ ((B).fv) ∪ (((syn_copk (.cv y) (.cv z))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show u ∉ (B).fv from (by exact fresh_u_not_B)) (show u ∉ ((syn_copk (.cv y) (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show u ∉ (((Class.cv y)).fv) ∪ (((Class.cv z)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show u ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show u ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show u ≠ y from (by exact fresh_u_ne_y)))))) (show u ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show u ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show u ≠ z from (by exact fresh_u_ne_z)))))))))))))))))) (Finset.mem_of_mem_erase hmem))))) (Finset.mem_of_mem_erase hmem))))) (Finset.mem_of_mem_erase hmem)))))) (by exact (show t ∉ ((syn_wex x (syn_wex y (syn_wex z (syn_w3a (.classEq (.cv w) (syn_csn (syn_csn (.cv x)))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) C)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex]; exact (show t ∉ (((syn_wex y (syn_wex z (syn_w3a (.classEq (.cv w) (syn_csn (syn_csn (.cv x)))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) C))))).fv).erase x from (fun hmem => (show t ∉ ((syn_wex y (syn_wex z (syn_w3a (.classEq (.cv w) (syn_csn (syn_csn (.cv x)))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) C))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex]; exact (show t ∉ (((syn_wex z (syn_w3a (.classEq (.cv w) (syn_csn (syn_csn (.cv x)))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) C)))).fv).erase y from (fun hmem => (show t ∉ ((syn_wex z (syn_w3a (.classEq (.cv w) (syn_csn (syn_csn (.cv x)))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) C)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex]; exact (show t ∉ (((syn_w3a (.classEq (.cv w) (syn_csn (syn_csn (.cv x)))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) C))).fv).erase z from (fun hmem => (show t ∉ ((syn_w3a (.classEq (.cv w) (syn_csn (syn_csn (.cv x)))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) C))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a]; exact (show t ∉ (((Wff.classMem (syn_copk (.cv x) (.cv y)) C)).fv) ∪ (((Wff.classEq (.cv w) (syn_csn (syn_csn (.cv x))))).fv) ∪ (((Wff.classEq (.cv u) (syn_copk (.cv y) (.cv z)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((Wff.classMem (syn_copk (.cv x) (.cv y)) C)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show t ∉ (((syn_copk (.cv x) (.cv y))).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_copk (.cv x) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show t ∉ (((Class.cv x)).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ x from (by exact fresh_t_ne_x)))))) (show t ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ y from (by exact fresh_t_ne_y)))))))))) (show t ∉ (C).fv from (by exact fresh_t_not_C)))))) (show t ∉ ((Wff.classEq (.cv w) (syn_csn (syn_csn (.cv x))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show t ∉ (((Class.cv w)).fv) ∪ (((syn_csn (syn_csn (.cv x)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((Class.cv w)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({w} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ w from (by exact fresh_t_ne_w)))))) (show t ∉ ((syn_csn (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ x from (by exact fresh_t_ne_x))))))))))))))) (show t ∉ ((Wff.classEq (.cv u) (syn_copk (.cv y) (.cv z)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show t ∉ (((Class.cv u)).fv) ∪ (((syn_copk (.cv y) (.cv z))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((Class.cv u)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({u} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ u from (by exact fresh_t_ne_u)))))) (show t ∉ ((syn_copk (.cv y) (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show t ∉ (((Class.cv y)).fv) ∪ (((Class.cv z)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ y from (by exact fresh_t_ne_y)))))) (show t ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ z from (by exact fresh_t_ne_z)))))))))))))))))) (Finset.mem_of_mem_erase hmem))))) (Finset.mem_of_mem_erase hmem))))) (Finset.mem_of_mem_erase hmem)))))) (by exact (show w ∉ ((syn_wex x (syn_wex y (syn_wex z (syn_w3a (.classEq A (syn_csn (syn_csn (.cv x)))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) C)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex]; exact (show w ∉ (((syn_wex y (syn_wex z (syn_w3a (.classEq A (syn_csn (syn_csn (.cv x)))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) C))))).fv).erase x from (fun hmem => (show w ∉ ((syn_wex y (syn_wex z (syn_w3a (.classEq A (syn_csn (syn_csn (.cv x)))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) C))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex]; exact (show w ∉ (((syn_wex z (syn_w3a (.classEq A (syn_csn (syn_csn (.cv x)))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) C)))).fv).erase y from (fun hmem => (show w ∉ ((syn_wex z (syn_w3a (.classEq A (syn_csn (syn_csn (.cv x)))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) C)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex]; exact (show w ∉ (((syn_w3a (.classEq A (syn_csn (syn_csn (.cv x)))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) C))).fv).erase z from (fun hmem => (show w ∉ ((syn_w3a (.classEq A (syn_csn (syn_csn (.cv x)))) (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) C))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a]; exact (show w ∉ (((Wff.classMem (syn_copk (.cv x) (.cv y)) C)).fv) ∪ (((Wff.classEq A (syn_csn (syn_csn (.cv x))))).fv) ∪ (((Wff.classEq (.cv u) (syn_copk (.cv y) (.cv z)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Wff.classMem (syn_copk (.cv x) (.cv y)) C)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show w ∉ (((syn_copk (.cv x) (.cv y))).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((syn_copk (.cv x) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show w ∉ (((Class.cv x)).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ x from (by exact fresh_w_ne_x)))))) (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y)))))))))) (show w ∉ (C).fv from (by exact fresh_w_not_C)))))) (show w ∉ ((Wff.classEq A (syn_csn (syn_csn (.cv x))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show w ∉ ((A).fv) ∪ (((syn_csn (syn_csn (.cv x)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ (A).fv from (by exact fresh_w_not_A)) (show w ∉ ((syn_csn (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show w ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show w ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ x from (by exact fresh_w_ne_x))))))))))))))) (show w ∉ ((Wff.classEq (.cv u) (syn_copk (.cv y) (.cv z)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show w ∉ (((Class.cv u)).fv) ∪ (((syn_copk (.cv y) (.cv z))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Class.cv u)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({u} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ u from (by exact fresh_w_ne_u)))))) (show w ∉ ((syn_copk (.cv y) (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show w ∉ (((Class.cv y)).fv) ∪ (((Class.cv z)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y)))))) (show w ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ z from (by exact fresh_w_ne_z)))))))))))))))))) (Finset.mem_of_mem_erase hmem))))) (Finset.mem_of_mem_erase hmem))))) (Finset.mem_of_mem_erase hmem)))))) (show t ≠ w from (by exact fresh_t_ne_w)) (show t ≠ u from (by exact fresh_t_ne_u)) (show w ≠ u from (by exact fresh_w_ne_u)) p0000 p0003 p0006
  exact p0007

noncomputable def g_otkelins2kg
    (A : Class) (B : Class) (C : Class) (D : Class) (T : Class) (V : Class) (W : Class) :
    Nominal.NPrf (.imp (syn_w3a (.classMem A V) (.classMem B W) (.classMem C T)) (syn_wb (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_cins2k D)) (.classMem (syn_copk A C) D))) := by
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
    @g_opkelins2kg x y z (syn_csn (syn_csn A)) (syn_copk B C) D (syn_cvv) (syn_cvv) (by exact (show x ∉ ((syn_csn (syn_csn A))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ ((syn_csn A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ (A).fv from (by exact fresh_x_not_A))))))) (by exact (show y ∉ ((syn_csn (syn_csn A))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ (A).fv from (by exact fresh_y_not_A))))))) (by exact (show z ∉ ((syn_csn (syn_csn A))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show z ∉ ((syn_csn A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show z ∉ (A).fv from (by exact fresh_z_not_A))))))) (by exact (show x ∉ ((syn_copk B C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show x ∉ ((B).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (B).fv from (by exact fresh_x_not_B)) (show x ∉ (C).fv from (by exact fresh_x_not_C))))))) (by exact (show y ∉ ((syn_copk B C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show y ∉ ((B).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (B).fv from (by exact fresh_y_not_B)) (show y ∉ (C).fv from (by exact fresh_y_not_C))))))) (by exact (show z ∉ ((syn_copk B C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show z ∉ ((B).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ (B).fv from (by exact fresh_z_not_B)) (show z ∉ (C).fv from (by exact fresh_z_not_C))))))) (by exact (show x ∉ (D).fv from (by exact fresh_x_not_D))) (by exact (show y ∉ (D).fv from (by exact fresh_y_not_D))) (by exact (show z ∉ (D).fv from (by exact fresh_z_not_D))) (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z)) (show y ≠ z from (by exact fresh_y_ne_z))
  have p0003 :=
    @g_mp2an (.classMem (syn_csn (syn_csn A)) (syn_cvv)) (.classMem (syn_copk B C) (syn_cvv)) (syn_wb (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_cins2k D)) (syn_wex x (syn_wex y (syn_wex z (syn_w3a (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x)))) (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv z)) D)))))) p0000 p0001 p0002
  have p0004 :=
    @g_n_3anass (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x)))) (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv z)) D)
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
    @g_anbi1i (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x)))) (.classEq (.cv x) A) (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv z)) D)) p0011
  have p0013 :=
    @g_bitri (syn_w3a (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x)))) (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv z)) D)) (syn_wa (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x)))) (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv z)) D))) (syn_wa (.classEq (.cv x) A) (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv z)) D))) p0004 p0012
  have p0014 :=
    @g_n_2exbii (syn_w3a (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x)))) (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv z)) D)) (syn_wa (.classEq (.cv x) A) (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv z)) D))) y z p0013
  have p0015 :=
    @g_n_19_42vv (.classEq (.cv x) A) (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv z)) D)) y z (by exact (show y ∉ ((Wff.classEq (.cv x) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ (((Class.cv x)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))) (show y ∉ (A).fv from (by exact fresh_y_not_A))))))) (by exact (show z ∉ ((Wff.classEq (.cv x) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show z ∉ (((Class.cv x)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))) (show z ∉ (A).fv from (by exact fresh_z_not_A)))))))
  have p0016 :=
    @g_bitri (syn_wex y (syn_wex z (syn_w3a (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x)))) (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv z)) D)))) (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) A) (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv z)) D))))) (syn_wa (.classEq (.cv x) A) (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv z)) D))))) p0014 p0015
  have p0017 :=
    @g_exbii (syn_wex y (syn_wex z (syn_w3a (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x)))) (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv z)) D)))) (syn_wa (.classEq (.cv x) A) (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv z)) D))))) x p0016
  have p0018 :=
    @g_bitri (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_cins2k D)) (syn_wex x (syn_wex y (syn_wex z (syn_w3a (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x)))) (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv z)) D))))) (syn_wex x (syn_wa (.classEq (.cv x) A) (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv z)) D)))))) p0003 p0017
  have p0019 :=
    @g_opkeq1 (.cv x) A (.cv z)
  have p0020 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_copk (.cv x) (.cv z)) (syn_copk A (.cv z)) D p0019
  have p0021 :=
    @g_anbi2d (.classEq (.cv x) A) (.classMem (syn_copk (.cv x) (.cv z)) D) (.classMem (syn_copk A (.cv z)) D) (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) p0020
  have p0022 :=
    @g_n_2exbidv (.classEq (.cv x) A) (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv z)) D)) (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk A (.cv z)) D)) y z (by exact (show y ∉ ((Wff.classEq (.cv x) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ (((Class.cv x)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))) (show y ∉ (A).fv from (by exact fresh_y_not_A))))))) (by exact (show z ∉ ((Wff.classEq (.cv x) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show z ∉ (((Class.cv x)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))) (show z ∉ (A).fv from (by exact fresh_z_not_A))))))) p0021
  have p0023 :=
    @g_ceqsexgv (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv z)) D)))) (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk A (.cv z)) D)))) x A V (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show x ∉ ((syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk A (.cv z)) D))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex]; exact (show x ∉ (((syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk A (.cv z)) D)))).fv).erase y from (fun hmem => (show x ∉ ((syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk A (.cv z)) D)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex]; exact (show x ∉ (((syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk A (.cv z)) D))).fv).erase z from (fun hmem => (show x ∉ ((syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk A (.cv z)) D))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show x ∉ (((Wff.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))).fv) ∪ (((Wff.classMem (syn_copk A (.cv z)) D)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Wff.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ (((syn_copk B C)).fv) ∪ (((syn_copk (.cv y) (.cv z))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_copk B C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show x ∉ ((B).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (B).fv from (by exact fresh_x_not_B)) (show x ∉ (C).fv from (by exact fresh_x_not_C)))))) (show x ∉ ((syn_copk (.cv y) (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show x ∉ (((Class.cv y)).fv) ∪ (((Class.cv z)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y)))))) (show x ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ z from (by exact fresh_x_ne_z)))))))))))))) (show x ∉ ((Wff.classMem (syn_copk A (.cv z)) D)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((syn_copk A (.cv z))).fv) ∪ ((D).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_copk A (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show x ∉ ((A).fv) ∪ (((Class.cv z)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ z from (by exact fresh_x_ne_z)))))))))) (show x ∉ (D).fv from (by exact fresh_x_not_D)))))))))) (Finset.mem_of_mem_erase hmem))))) (Finset.mem_of_mem_erase hmem)))))) p0022
  have p0024 :=
    @g_n_3ad2ant1 (.classMem A V) (.classMem B W) (syn_wb (syn_wex x (syn_wa (.classEq (.cv x) A) (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv z)) D)))))) (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk A (.cv z)) D))))) (.classMem C T) p0023
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
    @g_anbi1d (.classMem C T) (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (syn_wa (.classEq (.cv y) B) (.classEq (.cv z) C)) (.classMem (syn_copk A (.cv z)) D) p0030
  have p0032 :=
    @g_n_2exbidv (.classMem C T) (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk A (.cv z)) D)) (syn_wa (syn_wa (.classEq (.cv y) B) (.classEq (.cv z) C)) (.classMem (syn_copk A (.cv z)) D)) y z (by exact (show y ∉ ((Wff.classMem C T)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ ((C).fv) ∪ ((T).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (C).fv from (by exact fresh_y_not_C)) (show y ∉ (T).fv from (by exact fresh_y_not_T))))))) (by exact (show z ∉ ((Wff.classMem C T)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show z ∉ ((C).fv) ∪ ((T).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ (C).fv from (by exact fresh_z_not_C)) (show z ∉ (T).fv from (by exact fresh_z_not_T))))))) p0031
  have p0033 :=
    @g_anass (.classEq (.cv y) B) (.classEq (.cv z) C) (.classMem (syn_copk A (.cv z)) D)
  have p0034 :=
    @g_exbii (syn_wa (syn_wa (.classEq (.cv y) B) (.classEq (.cv z) C)) (.classMem (syn_copk A (.cv z)) D)) (syn_wa (.classEq (.cv y) B) (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv z)) D))) z p0033
  have p0035 :=
    @g_n_19_42v (.classEq (.cv y) B) (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv z)) D)) z (by exact (show z ∉ ((Wff.classEq (.cv y) B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show z ∉ (((Class.cv y)).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y)))))) (show z ∉ (B).fv from (by exact fresh_z_not_B)))))))
  have p0036 :=
    @g_bitri (syn_wex z (syn_wa (syn_wa (.classEq (.cv y) B) (.classEq (.cv z) C)) (.classMem (syn_copk A (.cv z)) D))) (syn_wex z (syn_wa (.classEq (.cv y) B) (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv z)) D)))) (syn_wa (.classEq (.cv y) B) (syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv z)) D)))) p0034 p0035
  have p0037 :=
    @g_exbii (syn_wex z (syn_wa (syn_wa (.classEq (.cv y) B) (.classEq (.cv z) C)) (.classMem (syn_copk A (.cv z)) D))) (syn_wa (.classEq (.cv y) B) (syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv z)) D)))) y p0036
  have p0038 :=
    @g_syl6bb (.classMem C T) (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk A (.cv z)) D)))) (syn_wex y (syn_wex z (syn_wa (syn_wa (.classEq (.cv y) B) (.classEq (.cv z) C)) (.classMem (syn_copk A (.cv z)) D)))) (syn_wex y (syn_wa (.classEq (.cv y) B) (syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv z)) D))))) p0032 p0037
  have p0039 :=
    @g_adantl (.classMem C T) (syn_wb (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk A (.cv z)) D)))) (syn_wex y (syn_wa (.classEq (.cv y) B) (syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv z)) D)))))) (.classMem B W) p0038
  have p0040 :=
    @g_biidd (.classEq (.cv y) B) (syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv z)) D)))
  have p0041 :=
    @g_ceqsexgv (syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv z)) D))) (syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv z)) D))) y B W (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B))) (by exact (show y ∉ ((syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv z)) D)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex]; exact (show y ∉ (((syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv z)) D))).fv).erase z from (fun hmem => (show y ∉ ((syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv z)) D))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show y ∉ (((Wff.classEq (.cv z) C)).fv) ∪ (((Wff.classMem (syn_copk A (.cv z)) D)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Wff.classEq (.cv z) C)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ (((Class.cv z)).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ z from (by exact fresh_y_ne_z)))))) (show y ∉ (C).fv from (by exact fresh_y_not_C)))))) (show y ∉ ((Wff.classMem (syn_copk A (.cv z)) D)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((syn_copk A (.cv z))).fv) ∪ ((D).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_copk A (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show y ∉ ((A).fv) ∪ (((Class.cv z)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ z from (by exact fresh_y_ne_z)))))))))) (show y ∉ (D).fv from (by exact fresh_y_not_D)))))))))) (Finset.mem_of_mem_erase hmem)))))) p0040
  have p0042 :=
    @g_opkeq2 (.cv z) C A
  have p0043 :=
    @g_eleq1d (.classEq (.cv z) C) (syn_copk A (.cv z)) (syn_copk A C) D p0042
  have p0044 :=
    @g_ceqsexgv (.classMem (syn_copk A (.cv z)) D) (.classMem (syn_copk A C) D) z C T (by exact (show z ∉ (C).fv from (by exact fresh_z_not_C))) (by exact (show z ∉ ((Wff.classMem (syn_copk A C) D)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show z ∉ (((syn_copk A C)).fv) ∪ ((D).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_copk A C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show z ∉ ((A).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ (A).fv from (by exact fresh_z_not_A)) (show z ∉ (C).fv from (by exact fresh_z_not_C)))))) (show z ∉ (D).fv from (by exact fresh_z_not_D))))))) p0043
  have p0045 :=
    @g_sylan9bb (.classMem B W) (syn_wex y (syn_wa (.classEq (.cv y) B) (syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv z)) D))))) (syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv z)) D))) (.classMem C T) (.classMem (syn_copk A C) D) p0041 p0044
  have p0046 :=
    @g_bitrd (syn_wa (.classMem B W) (.classMem C T)) (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk A (.cv z)) D)))) (syn_wex y (syn_wa (.classEq (.cv y) B) (syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv z)) D))))) (.classMem (syn_copk A C) D) p0039 p0045
  have p0047 :=
    @g_n_3adant1 (.classMem B W) (.classMem C T) (syn_wb (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk A (.cv z)) D)))) (.classMem (syn_copk A C) D)) (.classMem A V) p0046
  have p0048 :=
    @g_bitrd (syn_w3a (.classMem A V) (.classMem B W) (.classMem C T)) (syn_wex x (syn_wa (.classEq (.cv x) A) (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv z)) D)))))) (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk A (.cv z)) D)))) (.classMem (syn_copk A C) D) p0024 p0047
  have p0049 :=
    @g_syl5bb (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_cins2k D)) (syn_wex x (syn_wa (.classEq (.cv x) A) (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv z)) D)))))) (syn_w3a (.classMem A V) (.classMem B W) (.classMem C T)) (.classMem (syn_copk A C) D) p0018 p0048
  exact p0049



#print axioms g_otkelins2kg

end NFChoice.DirectNominalPrf.WPPReplay
