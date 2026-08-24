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
import NominalWPPReplayChunk009StructuralPart008


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

noncomputable def g_opkelsikg
    (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem B W)) (syn_wb (.classMem (syn_copk A B) (syn_csik C)) (syn_wex x (syn_wex y (syn_w3a (.classEq A (syn_csn (.cv x))) (.classEq B (syn_csn (.cv y))) (.classMem (syn_copk (.cv x) (.cv y)) C)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ V.fv ∪ W.fv
  let t : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_t_ne_x : t ≠ x := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_t : x ≠ t :=
    Ne.symm fresh_t_ne_x
  have fresh_t_ne_y : t ≠ y := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_y_ne_t : y ≠ t :=
    Ne.symm fresh_t_ne_y
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
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_ne_x : u ≠ x := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_u : x ≠ u :=
    Ne.symm fresh_u_ne_x
  have fresh_u_ne_y : u ≠ y := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_y_ne_u : y ≠ u :=
    Ne.symm fresh_u_ne_y
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
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_V : z ∉ V.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_W : z ∉ W.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_t_ne_u : t ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_t : u ≠ t :=
    Ne.symm fresh_t_ne_u
  have fresh_t_ne_z : t ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_t : z ≠ t :=
    Ne.symm fresh_t_ne_z
  have fresh_u_ne_z : u ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_u : z ≠ u :=
    Ne.symm fresh_u_ne_z
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sik z t u y x C (by exact (show x ∉ (C).fv from (by exact dv_C_x))) (by exact (show y ∉ (C).fv from (by exact dv_C_y))) (by exact (show z ∉ (C).fv from (by exact fresh_z_not_C))) (by exact (show t ∉ (C).fv from (by exact fresh_t_not_C))) (by exact (show u ∉ (C).fv from (by exact fresh_u_not_C))) (show x ≠ y from (by exact dv_x_y)) (show x ≠ z from (by exact fresh_x_ne_z)) (show x ≠ t from (by exact fresh_x_ne_t)) (show x ≠ u from (by exact fresh_x_ne_u)) (show y ≠ z from (by exact fresh_y_ne_z)) (show y ≠ t from (by exact fresh_y_ne_t)) (show y ≠ u from (by exact fresh_y_ne_u)) (show z ≠ t from (by exact fresh_z_ne_t)) (show z ≠ u from (by exact fresh_z_ne_u)) (show t ≠ u from (by exact fresh_t_ne_u))
  have p0001 :=
    @g_eqeq1 (.cv t) A (syn_csn (.cv x))
  have p0002 :=
    @g_n_3anbi1d (.classEq (.cv t) A) (.classEq (.cv t) (syn_csn (.cv x))) (.classEq A (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))) (.classMem (syn_copk (.cv x) (.cv y)) C) p0001
  have p0003 :=
    @g_n_2exbidv (.classEq (.cv t) A) (syn_w3a (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))) (.classMem (syn_copk (.cv x) (.cv y)) C)) (syn_w3a (.classEq A (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))) (.classMem (syn_copk (.cv x) (.cv y)) C)) x y (by exact (show x ∉ ((Wff.classEq (.cv t) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ (((Class.cv t)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv t)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({t} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ t from (by exact fresh_x_ne_t)))))) (show x ∉ (A).fv from (by exact dv_A_x))))))) (by exact (show y ∉ ((Wff.classEq (.cv t) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ (((Class.cv t)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv t)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({t} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ t from (by exact fresh_y_ne_t)))))) (show y ∉ (A).fv from (by exact dv_A_y))))))) p0002
  have p0004 :=
    @g_eqeq1 (.cv u) B (syn_csn (.cv y))
  have p0005 :=
    @g_n_3anbi2d (.classEq (.cv u) B) (.classEq (.cv u) (syn_csn (.cv y))) (.classEq B (syn_csn (.cv y))) (.classEq A (syn_csn (.cv x))) (.classMem (syn_copk (.cv x) (.cv y)) C) p0004
  have p0006 :=
    @g_n_2exbidv (.classEq (.cv u) B) (syn_w3a (.classEq A (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))) (.classMem (syn_copk (.cv x) (.cv y)) C)) (syn_w3a (.classEq A (syn_csn (.cv x))) (.classEq B (syn_csn (.cv y))) (.classMem (syn_copk (.cv x) (.cv y)) C)) x y (by exact (show x ∉ ((Wff.classEq (.cv u) B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ (((Class.cv u)).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv u)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({u} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ u from (by exact fresh_x_ne_u)))))) (show x ∉ (B).fv from (by exact dv_B_x))))))) (by exact (show y ∉ ((Wff.classEq (.cv u) B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ (((Class.cv u)).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv u)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({u} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ u from (by exact fresh_y_ne_u)))))) (show y ∉ (B).fv from (by exact dv_B_y))))))) p0005
  have p0007 :=
    @g_opkelopkabg (syn_wex x (syn_wex y (syn_w3a (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))) (.classMem (syn_copk (.cv x) (.cv y)) C)))) (syn_wex x (syn_wex y (syn_w3a (.classEq A (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))) (.classMem (syn_copk (.cv x) (.cv y)) C)))) (syn_wex x (syn_wex y (syn_w3a (.classEq A (syn_csn (.cv x))) (.classEq B (syn_csn (.cv y))) (.classMem (syn_copk (.cv x) (.cv y)) C)))) z t u (syn_csik C) A B V W (by exact (show t ∉ ((syn_csik C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik]; exact (show t ∉ (C).fv from (by exact fresh_t_not_C))))) (by exact (show u ∉ ((syn_csik C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik]; exact (show u ∉ (C).fv from (by exact fresh_u_not_C))))) (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A))) (by exact (show t ∉ (A).fv from (by exact fresh_t_not_A))) (by exact (show u ∉ (A).fv from (by exact fresh_u_not_A))) (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B))) (by exact (show t ∉ (B).fv from (by exact fresh_t_not_B))) (by exact (show u ∉ (B).fv from (by exact fresh_u_not_B))) (by exact (show u ∉ ((syn_wex x (syn_wex y (syn_w3a (.classEq A (syn_csn (.cv x))) (.classEq B (syn_csn (.cv y))) (.classMem (syn_copk (.cv x) (.cv y)) C))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex]; exact (show u ∉ (((syn_wex y (syn_w3a (.classEq A (syn_csn (.cv x))) (.classEq B (syn_csn (.cv y))) (.classMem (syn_copk (.cv x) (.cv y)) C)))).fv).erase x from (fun hmem => (show u ∉ ((syn_wex y (syn_w3a (.classEq A (syn_csn (.cv x))) (.classEq B (syn_csn (.cv y))) (.classMem (syn_copk (.cv x) (.cv y)) C)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex]; exact (show u ∉ (((syn_w3a (.classEq A (syn_csn (.cv x))) (.classEq B (syn_csn (.cv y))) (.classMem (syn_copk (.cv x) (.cv y)) C))).fv).erase y from (fun hmem => (show u ∉ ((syn_w3a (.classEq A (syn_csn (.cv x))) (.classEq B (syn_csn (.cv y))) (.classMem (syn_copk (.cv x) (.cv y)) C))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a]; exact (show u ∉ (((Wff.classMem (syn_copk (.cv x) (.cv y)) C)).fv) ∪ (((Wff.classEq A (syn_csn (.cv x)))).fv) ∪ (((Wff.classEq B (syn_csn (.cv y)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (fun hmem => (Finset.mem_union.mp hmem).elim (show u ∉ ((Wff.classMem (syn_copk (.cv x) (.cv y)) C)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show u ∉ (((syn_copk (.cv x) (.cv y))).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show u ∉ ((syn_copk (.cv x) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show u ∉ (((Class.cv x)).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show u ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show u ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show u ≠ x from (by exact fresh_u_ne_x)))))) (show u ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show u ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show u ≠ y from (by exact fresh_u_ne_y)))))))))) (show u ∉ (C).fv from (by exact fresh_u_not_C)))))) (show u ∉ ((Wff.classEq A (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show u ∉ ((A).fv) ∪ (((syn_csn (.cv x))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show u ∉ (A).fv from (by exact fresh_u_not_A)) (show u ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show u ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show u ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show u ≠ x from (by exact fresh_u_ne_x))))))))))))) (show u ∉ ((Wff.classEq B (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show u ∉ ((B).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show u ∉ (B).fv from (by exact fresh_u_not_B)) (show u ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show u ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show u ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show u ≠ y from (by exact fresh_u_ne_y)))))))))))))))) (Finset.mem_of_mem_erase hmem))))) (Finset.mem_of_mem_erase hmem)))))) (by exact (show z ∉ ((syn_wex x (syn_wex y (syn_w3a (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))) (.classMem (syn_copk (.cv x) (.cv y)) C))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex]; exact (show z ∉ (((syn_wex y (syn_w3a (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))) (.classMem (syn_copk (.cv x) (.cv y)) C)))).fv).erase x from (fun hmem => (show z ∉ ((syn_wex y (syn_w3a (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))) (.classMem (syn_copk (.cv x) (.cv y)) C)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex]; exact (show z ∉ (((syn_w3a (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))) (.classMem (syn_copk (.cv x) (.cv y)) C))).fv).erase y from (fun hmem => (show z ∉ ((syn_w3a (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))) (.classMem (syn_copk (.cv x) (.cv y)) C))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a]; exact (show z ∉ (((Wff.classMem (syn_copk (.cv x) (.cv y)) C)).fv) ∪ (((Wff.classEq (.cv t) (syn_csn (.cv x)))).fv) ∪ (((Wff.classEq (.cv u) (syn_csn (.cv y)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Wff.classMem (syn_copk (.cv x) (.cv y)) C)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show z ∉ (((syn_copk (.cv x) (.cv y))).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_copk (.cv x) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show z ∉ (((Class.cv x)).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))) (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y)))))))))) (show z ∉ (C).fv from (by exact fresh_z_not_C)))))) (show z ∉ ((Wff.classEq (.cv t) (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show z ∉ (((Class.cv t)).fv) ∪ (((syn_csn (.cv x))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv t)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({t} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ t from (by exact fresh_z_ne_t)))))) (show z ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x))))))))))))) (show z ∉ ((Wff.classEq (.cv u) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show z ∉ (((Class.cv u)).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv u)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({u} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ u from (by exact fresh_z_ne_u)))))) (show z ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y)))))))))))))))) (Finset.mem_of_mem_erase hmem))))) (Finset.mem_of_mem_erase hmem)))))) (by exact (show t ∉ ((syn_wex x (syn_wex y (syn_w3a (.classEq A (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))) (.classMem (syn_copk (.cv x) (.cv y)) C))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex]; exact (show t ∉ (((syn_wex y (syn_w3a (.classEq A (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))) (.classMem (syn_copk (.cv x) (.cv y)) C)))).fv).erase x from (fun hmem => (show t ∉ ((syn_wex y (syn_w3a (.classEq A (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))) (.classMem (syn_copk (.cv x) (.cv y)) C)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex]; exact (show t ∉ (((syn_w3a (.classEq A (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))) (.classMem (syn_copk (.cv x) (.cv y)) C))).fv).erase y from (fun hmem => (show t ∉ ((syn_w3a (.classEq A (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y))) (.classMem (syn_copk (.cv x) (.cv y)) C))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a]; exact (show t ∉ (((Wff.classMem (syn_copk (.cv x) (.cv y)) C)).fv) ∪ (((Wff.classEq A (syn_csn (.cv x)))).fv) ∪ (((Wff.classEq (.cv u) (syn_csn (.cv y)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((Wff.classMem (syn_copk (.cv x) (.cv y)) C)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show t ∉ (((syn_copk (.cv x) (.cv y))).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_copk (.cv x) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show t ∉ (((Class.cv x)).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ x from (by exact fresh_t_ne_x)))))) (show t ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ y from (by exact fresh_t_ne_y)))))))))) (show t ∉ (C).fv from (by exact fresh_t_not_C)))))) (show t ∉ ((Wff.classEq A (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show t ∉ ((A).fv) ∪ (((syn_csn (.cv x))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ (A).fv from (by exact fresh_t_not_A)) (show t ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ x from (by exact fresh_t_ne_x))))))))))))) (show t ∉ ((Wff.classEq (.cv u) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show t ∉ (((Class.cv u)).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((Class.cv u)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({u} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ u from (by exact fresh_t_ne_u)))))) (show t ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ y from (by exact fresh_t_ne_y)))))))))))))))) (Finset.mem_of_mem_erase hmem))))) (Finset.mem_of_mem_erase hmem)))))) (show z ≠ t from (by exact fresh_z_ne_t)) (show z ≠ u from (by exact fresh_z_ne_u)) (show t ≠ u from (by exact fresh_t_ne_u)) p0000 p0003 p0006
  exact p0007

noncomputable def g_opksnelsik
    (A : Class) (B : Class) (C : Class) (hyp_opksnelsik_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_opksnelsik_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem (syn_copk (syn_csn A) (syn_csn B)) (syn_csik C)) (.classMem (syn_copk A B) C)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
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
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have p0000 :=
    @g_snex A
  have p0001 :=
    @g_snex B
  have p0002 :=
    @g_opkelsikg x y (syn_csn A) (syn_csn B) C (syn_cvv) (syn_cvv) (by exact (show x ∉ ((syn_csn A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ (A).fv from (by exact fresh_x_not_A))))) (by exact (show y ∉ ((syn_csn A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ (A).fv from (by exact fresh_y_not_A))))) (by exact (show x ∉ ((syn_csn B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ (B).fv from (by exact fresh_x_not_B))))) (by exact (show y ∉ ((syn_csn B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ (B).fv from (by exact fresh_y_not_B))))) (by exact (show x ∉ (C).fv from (by exact fresh_x_not_C))) (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C))) (show x ≠ y from (by exact fresh_x_ne_y))
  have p0003 :=
    @g_mp2an (.classMem (syn_csn A) (syn_cvv)) (.classMem (syn_csn B) (syn_cvv)) (syn_wb (.classMem (syn_copk (syn_csn A) (syn_csn B)) (syn_csik C)) (syn_wex x (syn_wex y (syn_w3a (.classEq (syn_csn A) (syn_csn (.cv x))) (.classEq (syn_csn B) (syn_csn (.cv y))) (.classMem (syn_copk (.cv x) (.cv y)) C))))) p0000 p0001 p0002
  have p0004 :=
    @g_eqcom (syn_csn A) (syn_csn (.cv x))
  have p0005 :=
    @g_vex x
  have p0006 :=
    @g_sneqb (.cv x) A p0005
  have p0007 :=
    @g_bitri (.classEq (syn_csn A) (syn_csn (.cv x))) (.classEq (syn_csn (.cv x)) (syn_csn A)) (.classEq (.cv x) A) p0004 p0006
  have p0008 :=
    @g_eqcom (syn_csn B) (syn_csn (.cv y))
  have p0009 :=
    @g_vex y
  have p0010 :=
    @g_sneqb (.cv y) B p0009
  have p0011 :=
    @g_bitri (.classEq (syn_csn B) (syn_csn (.cv y))) (.classEq (syn_csn (.cv y)) (syn_csn B)) (.classEq (.cv y) B) p0008 p0010
  have p0012 :=
    @g_biid (.classMem (syn_copk (.cv x) (.cv y)) C)
  have p0013 :=
    @g_n_3anbi123i (.classEq (syn_csn A) (syn_csn (.cv x))) (.classEq (.cv x) A) (.classEq (syn_csn B) (syn_csn (.cv y))) (.classEq (.cv y) B) (.classMem (syn_copk (.cv x) (.cv y)) C) (.classMem (syn_copk (.cv x) (.cv y)) C) p0007 p0011 p0012
  have p0014 :=
    @g_n_2exbii (syn_w3a (.classEq (syn_csn A) (syn_csn (.cv x))) (.classEq (syn_csn B) (syn_csn (.cv y))) (.classMem (syn_copk (.cv x) (.cv y)) C)) (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classMem (syn_copk (.cv x) (.cv y)) C)) x y p0013
  have p0015 :=
    @g_opkeq1 (.cv x) A (.cv y)
  have p0016 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_copk (.cv x) (.cv y)) (syn_copk A (.cv y)) C p0015
  have p0017 :=
    @g_opkeq2 (.cv y) B A
  have p0018 :=
    @g_eleq1d (.classEq (.cv y) B) (syn_copk A (.cv y)) (syn_copk A B) C p0017
  have p0019 :=
    @g_ceqsex2v (.classMem (syn_copk (.cv x) (.cv y)) C) (.classMem (syn_copk A (.cv y)) C) (.classMem (syn_copk A B) C) x y A B (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B))) (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B))) (by exact (show y ∉ ((Wff.classMem (syn_copk A B) C)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((syn_copk A B)).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_copk A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show y ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ (B).fv from (by exact fresh_y_not_B)))))) (show y ∉ (C).fv from (by exact fresh_y_not_C))))))) (by exact (show x ∉ ((Wff.classMem (syn_copk A (.cv y)) C)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((syn_copk A (.cv y))).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_copk A (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show x ∉ ((A).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y)))))))))) (show x ∉ (C).fv from (by exact fresh_x_not_C))))))) (show x ≠ y from (by exact fresh_x_ne_y)) hyp_opksnelsik_1 hyp_opksnelsik_2 p0016 p0018
  have p0020 :=
    @g_bitri (syn_wex x (syn_wex y (syn_w3a (.classEq (syn_csn A) (syn_csn (.cv x))) (.classEq (syn_csn B) (syn_csn (.cv y))) (.classMem (syn_copk (.cv x) (.cv y)) C)))) (syn_wex x (syn_wex y (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classMem (syn_copk (.cv x) (.cv y)) C)))) (.classMem (syn_copk A B) C) p0014 p0019
  have p0021 :=
    @g_bitri (.classMem (syn_copk (syn_csn A) (syn_csn B)) (syn_csik C)) (syn_wex x (syn_wex y (syn_w3a (.classEq (syn_csn A) (syn_csn (.cv x))) (.classEq (syn_csn B) (syn_csn (.cv y))) (.classMem (syn_copk (.cv x) (.cv y)) C)))) (.classMem (syn_copk A B) C) p0003 p0020
  exact p0021

noncomputable def g_sikssvvk
    (A : Class) :
    Nominal.NPrf (syn_wss (syn_csik A) (syn_cxpk (syn_cvv) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv
  let y : Var := freshVar proofSupport 0
  let t : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let u : Var := freshVar proofSupport 3
  let x : Var := freshVar proofSupport 4
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (h)
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (h)
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y_ne_t : y ≠ t := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_t_ne_y : t ≠ y :=
    Ne.symm fresh_y_ne_t
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_y_ne_u : y ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_u_ne_y : u ≠ y :=
    Ne.symm fresh_y_ne_u
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_t_ne_z : t ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_t : z ≠ t :=
    Ne.symm fresh_t_ne_z
  have fresh_t_ne_u : t ≠ u := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_u_ne_t : u ≠ t :=
    Ne.symm fresh_t_ne_u
  have fresh_t_ne_x : t ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_x_ne_t : x ≠ t :=
    Ne.symm fresh_t_ne_x
  have fresh_z_ne_u : z ≠ u := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_u_ne_z : u ≠ z :=
    Ne.symm fresh_z_ne_u
  have fresh_z_ne_x : z ≠ x := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_u_ne_x : u ≠ x := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_x_ne_u : x ≠ u :=
    Ne.symm fresh_u_ne_x
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sik x y z u t A (by exact (show t ∉ (A).fv from (by exact fresh_t_not_A))) (by exact (show u ∉ (A).fv from (by exact fresh_u_not_A))) (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A))) (show t ≠ u from (by exact fresh_t_ne_u)) (show t ≠ x from (by exact fresh_t_ne_x)) (show t ≠ y from (by exact fresh_t_ne_y)) (show t ≠ z from (by exact fresh_t_ne_z)) (show u ≠ x from (by exact fresh_u_ne_x)) (show u ≠ y from (by exact fresh_u_ne_y)) (show u ≠ z from (by exact fresh_u_ne_z)) (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z)) (show y ≠ z from (by exact fresh_y_ne_z))
  have p0001 :=
    @g_opkabssvvki (syn_wex t (syn_wex u (syn_w3a (.classEq (.cv y) (syn_csn (.cv t))) (.classEq (.cv z) (syn_csn (.cv u))) (.classMem (syn_copk (.cv t) (.cv u)) A)))) x y z (syn_csik A) (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z)) p0000
  exact p0001



#print axioms g_sikssvvk

end NFChoice.DirectNominalPrf.WPPReplay
