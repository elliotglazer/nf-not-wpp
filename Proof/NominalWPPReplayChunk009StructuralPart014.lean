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
import NominalWPPReplayChunk009StructuralPart013


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

noncomputable def g_sikexlem
    (x : Var) (y : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) (hyp_sikexlem_1 : Nominal.NPrf (syn_wss A (syn_cxpk (syn_c1c) (syn_c1c)))) (hyp_sikexlem_2 : Nominal.NPrf (syn_wss B (syn_cxpk (syn_c1c) (syn_c1c)))) :
    Nominal.NPrf (syn_wb (.classEq A B) (.all x (.all y (syn_wb (.classMem (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) A) (.classMem (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) B))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv
  let z : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  let t : Var := freshVar proofSupport 2
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
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_w : y ≠ w :=
    Ne.symm fresh_w_ne_y
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_t_ne_x : t ≠ x := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_t : x ≠ t :=
    Ne.symm fresh_t_ne_x
  have fresh_t_ne_y : t ≠ y := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_t : y ≠ t :=
    Ne.symm fresh_t_ne_y
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have fresh_z_ne_t : z ≠ t := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_t_ne_z : t ≠ z :=
    Ne.symm fresh_z_ne_t
  have fresh_w_ne_t : w ≠ t := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_t_ne_w : t ≠ w :=
    Ne.symm fresh_w_ne_t
  have p0000 :=
    @g_ssofeq z A B (syn_cxpk (syn_c1c) (syn_c1c)) (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A))) (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B))) (by exact (show z ∉ ((syn_cxpk (syn_c1c) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show z ∉ (((syn_c1c)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show z ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))
  have p0001 :=
    @g_mp2an (syn_wss A (syn_cxpk (syn_c1c) (syn_c1c))) (syn_wss B (syn_cxpk (syn_c1c) (syn_c1c))) (syn_wb (.classEq A B) (syn_wral z (syn_cxpk (syn_c1c) (syn_c1c)) (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)))) hyp_sikexlem_1 hyp_sikexlem_2 p0000
  have p0002 :=
    (by simpa [syn_wb, syn_wral] using (Nominal.biimpRefl (syn_wral z (syn_cxpk (syn_c1c) (syn_c1c)) (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)))))
  have p0003 :=
    @g_elxpk w t (.cv z) (syn_c1c) (syn_c1c) (by exact (show w ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ z from (by exact fresh_w_ne_z))))))) (by exact (show t ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ z from (by exact fresh_t_ne_z))))))) (by exact (show w ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show t ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show w ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show t ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (show w ≠ t from (by exact fresh_w_ne_t))
  have p0004 :=
    @g_el1c x (.cv w) (by exact (show x ∉ ((Class.cv w)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({w} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ w from (by exact fresh_x_ne_w)))))))
  have p0005 :=
    @g_el1c y (.cv t) (by exact (show y ∉ ((Class.cv t)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({t} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ t from (by exact fresh_y_ne_t)))))))
  have p0006 :=
    @g_anbi12i (.classMem (.cv w) (syn_c1c)) (syn_wex x (.classEq (.cv w) (syn_csn (.cv x)))) (.classMem (.cv t) (syn_c1c)) (syn_wex y (.classEq (.cv t) (syn_csn (.cv y)))) p0004 p0005
  have p0007 :=
    @g_eeanv (.classEq (.cv w) (syn_csn (.cv x))) (.classEq (.cv t) (syn_csn (.cv y))) x y (by exact (show y ∉ ((Wff.classEq (.cv w) (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ (((Class.cv w)).fv) ∪ (((syn_csn (.cv x))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv w)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({w} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ w from (by exact fresh_y_ne_w)))))) (show y ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact Ne.symm dv_x_y))))))))))))) (by exact (show x ∉ ((Wff.classEq (.cv t) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ (((Class.cv t)).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv t)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({t} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ t from (by exact fresh_x_ne_t)))))) (show x ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact dv_x_y)))))))))))))
  have p0008 :=
    @g_bitr4i (syn_wa (.classMem (.cv w) (syn_c1c)) (.classMem (.cv t) (syn_c1c))) (syn_wa (syn_wex x (.classEq (.cv w) (syn_csn (.cv x)))) (syn_wex y (.classEq (.cv t) (syn_csn (.cv y))))) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_csn (.cv x))) (.classEq (.cv t) (syn_csn (.cv y)))))) p0006 p0007
  have p0009 :=
    @g_anbi2i (syn_wa (.classMem (.cv w) (syn_c1c)) (.classMem (.cv t) (syn_c1c))) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_csn (.cv x))) (.classEq (.cv t) (syn_csn (.cv y)))))) (.classEq (.cv z) (syn_copk (.cv w) (.cv t))) p0008
  have p0010 :=
    (by simpa [syn_wb, syn_w3a] using (Nominal.biimpRefl (syn_w3a (.classEq (.cv w) (syn_csn (.cv x))) (.classEq (.cv t) (syn_csn (.cv y))) (.classEq (.cv z) (syn_copk (.cv w) (.cv t))))))
  have p0011 :=
    @g_ancom (syn_wa (.classEq (.cv w) (syn_csn (.cv x))) (.classEq (.cv t) (syn_csn (.cv y)))) (.classEq (.cv z) (syn_copk (.cv w) (.cv t)))
  have p0012 :=
    @g_bitri (syn_w3a (.classEq (.cv w) (syn_csn (.cv x))) (.classEq (.cv t) (syn_csn (.cv y))) (.classEq (.cv z) (syn_copk (.cv w) (.cv t)))) (syn_wa (syn_wa (.classEq (.cv w) (syn_csn (.cv x))) (.classEq (.cv t) (syn_csn (.cv y)))) (.classEq (.cv z) (syn_copk (.cv w) (.cv t)))) (syn_wa (.classEq (.cv z) (syn_copk (.cv w) (.cv t))) (syn_wa (.classEq (.cv w) (syn_csn (.cv x))) (.classEq (.cv t) (syn_csn (.cv y))))) p0010 p0011
  have p0013 :=
    @g_n_2exbii (syn_w3a (.classEq (.cv w) (syn_csn (.cv x))) (.classEq (.cv t) (syn_csn (.cv y))) (.classEq (.cv z) (syn_copk (.cv w) (.cv t)))) (syn_wa (.classEq (.cv z) (syn_copk (.cv w) (.cv t))) (syn_wa (.classEq (.cv w) (syn_csn (.cv x))) (.classEq (.cv t) (syn_csn (.cv y))))) x y p0012
  have p0014 :=
    @g_n_19_42vv (.classEq (.cv z) (syn_copk (.cv w) (.cv t))) (syn_wa (.classEq (.cv w) (syn_csn (.cv x))) (.classEq (.cv t) (syn_csn (.cv y)))) x y (by exact (show x ∉ ((Wff.classEq (.cv z) (syn_copk (.cv w) (.cv t)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ (((Class.cv z)).fv) ∪ (((syn_copk (.cv w) (.cv t))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ z from (by exact fresh_x_ne_z)))))) (show x ∉ ((syn_copk (.cv w) (.cv t))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show x ∉ (((Class.cv w)).fv) ∪ (((Class.cv t)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv w)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({w} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ w from (by exact fresh_x_ne_w)))))) (show x ∉ ((Class.cv t)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({t} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ t from (by exact fresh_x_ne_t))))))))))))))) (by exact (show y ∉ ((Wff.classEq (.cv z) (syn_copk (.cv w) (.cv t)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ (((Class.cv z)).fv) ∪ (((syn_copk (.cv w) (.cv t))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ z from (by exact fresh_y_ne_z)))))) (show y ∉ ((syn_copk (.cv w) (.cv t))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show y ∉ (((Class.cv w)).fv) ∪ (((Class.cv t)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv w)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({w} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ w from (by exact fresh_y_ne_w)))))) (show y ∉ ((Class.cv t)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({t} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ t from (by exact fresh_y_ne_t)))))))))))))))
  have p0015 :=
    @g_bitri (syn_wex x (syn_wex y (syn_w3a (.classEq (.cv w) (syn_csn (.cv x))) (.classEq (.cv t) (syn_csn (.cv y))) (.classEq (.cv z) (syn_copk (.cv w) (.cv t)))))) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_copk (.cv w) (.cv t))) (syn_wa (.classEq (.cv w) (syn_csn (.cv x))) (.classEq (.cv t) (syn_csn (.cv y))))))) (syn_wa (.classEq (.cv z) (syn_copk (.cv w) (.cv t))) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_csn (.cv x))) (.classEq (.cv t) (syn_csn (.cv y))))))) p0013 p0014
  have p0016 :=
    @g_bitr4i (syn_wa (.classEq (.cv z) (syn_copk (.cv w) (.cv t))) (syn_wa (.classMem (.cv w) (syn_c1c)) (.classMem (.cv t) (syn_c1c)))) (syn_wa (.classEq (.cv z) (syn_copk (.cv w) (.cv t))) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_csn (.cv x))) (.classEq (.cv t) (syn_csn (.cv y))))))) (syn_wex x (syn_wex y (syn_w3a (.classEq (.cv w) (syn_csn (.cv x))) (.classEq (.cv t) (syn_csn (.cv y))) (.classEq (.cv z) (syn_copk (.cv w) (.cv t)))))) p0009 p0015
  have p0017 :=
    @g_n_2exbii (syn_wa (.classEq (.cv z) (syn_copk (.cv w) (.cv t))) (syn_wa (.classMem (.cv w) (syn_c1c)) (.classMem (.cv t) (syn_c1c)))) (syn_wex x (syn_wex y (syn_w3a (.classEq (.cv w) (syn_csn (.cv x))) (.classEq (.cv t) (syn_csn (.cv y))) (.classEq (.cv z) (syn_copk (.cv w) (.cv t)))))) w t p0016
  have p0018 :=
    @g_exrot4 (syn_w3a (.classEq (.cv w) (syn_csn (.cv x))) (.classEq (.cv t) (syn_csn (.cv y))) (.classEq (.cv z) (syn_copk (.cv w) (.cv t)))) x y w t
  have p0019 :=
    @g_bitr4i (syn_wex w (syn_wex t (syn_wa (.classEq (.cv z) (syn_copk (.cv w) (.cv t))) (syn_wa (.classMem (.cv w) (syn_c1c)) (.classMem (.cv t) (syn_c1c)))))) (syn_wex w (syn_wex t (syn_wex x (syn_wex y (syn_w3a (.classEq (.cv w) (syn_csn (.cv x))) (.classEq (.cv t) (syn_csn (.cv y))) (.classEq (.cv z) (syn_copk (.cv w) (.cv t)))))))) (syn_wex x (syn_wex y (syn_wex w (syn_wex t (syn_w3a (.classEq (.cv w) (syn_csn (.cv x))) (.classEq (.cv t) (syn_csn (.cv y))) (.classEq (.cv z) (syn_copk (.cv w) (.cv t)))))))) p0017 p0018
  have p0020 :=
    @g_snex (.cv x)
  have p0021 :=
    @g_snex (.cv y)
  have p0022 :=
    @g_opkeq1 (.cv w) (syn_csn (.cv x)) (.cv t)
  have p0023 :=
    @g_eqeq2d (.classEq (.cv w) (syn_csn (.cv x))) (syn_copk (.cv w) (.cv t)) (syn_copk (syn_csn (.cv x)) (.cv t)) (.cv z) p0022
  have p0024 :=
    @g_opkeq2 (.cv t) (syn_csn (.cv y)) (syn_csn (.cv x))
  have p0025 :=
    @g_eqeq2d (.classEq (.cv t) (syn_csn (.cv y))) (syn_copk (syn_csn (.cv x)) (.cv t)) (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) (.cv z) p0024
  have p0026 :=
    @g_ceqsex2v (.classEq (.cv z) (syn_copk (.cv w) (.cv t))) (.classEq (.cv z) (syn_copk (syn_csn (.cv x)) (.cv t))) (.classEq (.cv z) (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y)))) w t (syn_csn (.cv x)) (syn_csn (.cv y)) (by exact (show w ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show w ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ x from (by exact fresh_w_ne_x))))))))) (by exact (show t ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ x from (by exact fresh_t_ne_x))))))))) (by exact (show w ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y))))))))) (by exact (show t ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ y from (by exact fresh_t_ne_y))))))))) (by exact (show t ∉ ((Wff.classEq (.cv z) (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show t ∉ (((Class.cv z)).fv) ∪ (((syn_copk (syn_csn (.cv x)) (syn_csn (.cv y)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ z from (by exact fresh_t_ne_z)))))) (show t ∉ ((syn_copk (syn_csn (.cv x)) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show t ∉ (((syn_csn (.cv x))).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ x from (by exact fresh_t_ne_x)))))))) (show t ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ y from (by exact fresh_t_ne_y))))))))))))))))) (by exact (show w ∉ ((Wff.classEq (.cv z) (syn_copk (syn_csn (.cv x)) (.cv t)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show w ∉ (((Class.cv z)).fv) ∪ (((syn_copk (syn_csn (.cv x)) (.cv t))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ z from (by exact fresh_w_ne_z)))))) (show w ∉ ((syn_copk (syn_csn (.cv x)) (.cv t))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show w ∉ (((syn_csn (.cv x))).fv) ∪ (((Class.cv t)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show w ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ x from (by exact fresh_w_ne_x)))))))) (show w ∉ ((Class.cv t)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({t} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ t from (by exact fresh_w_ne_t))))))))))))))) (show w ≠ t from (by exact fresh_w_ne_t)) p0020 p0021 p0023 p0025
  have p0027 :=
    @g_n_2exbii (syn_wex w (syn_wex t (syn_w3a (.classEq (.cv w) (syn_csn (.cv x))) (.classEq (.cv t) (syn_csn (.cv y))) (.classEq (.cv z) (syn_copk (.cv w) (.cv t)))))) (.classEq (.cv z) (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y)))) x y p0026
  have p0028 :=
    @g_n_3bitri (.classMem (.cv z) (syn_cxpk (syn_c1c) (syn_c1c))) (syn_wex w (syn_wex t (syn_wa (.classEq (.cv z) (syn_copk (.cv w) (.cv t))) (syn_wa (.classMem (.cv w) (syn_c1c)) (.classMem (.cv t) (syn_c1c)))))) (syn_wex x (syn_wex y (syn_wex w (syn_wex t (syn_w3a (.classEq (.cv w) (syn_csn (.cv x))) (.classEq (.cv t) (syn_csn (.cv y))) (.classEq (.cv z) (syn_copk (.cv w) (.cv t)))))))) (syn_wex x (syn_wex y (.classEq (.cv z) (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y)))))) p0003 p0019 p0027
  have p0029 :=
    @g_imbi1i (.classMem (.cv z) (syn_cxpk (syn_c1c) (syn_c1c))) (syn_wex x (syn_wex y (.classEq (.cv z) (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y)))))) (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)) p0028
  have p0030 :=
    @g_n_19_23vv (.classEq (.cv z) (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y)))) (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)) x y (by exact (show x ∉ ((syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb]; exact (show x ∉ (((Wff.classMem (.cv z) A)).fv) ∪ (((Wff.classMem (.cv z) B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Wff.classMem (.cv z) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((Class.cv z)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ z from (by exact fresh_x_ne_z)))))) (show x ∉ (A).fv from (by exact dv_A_x)))))) (show x ∉ ((Wff.classMem (.cv z) B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((Class.cv z)).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ z from (by exact fresh_x_ne_z)))))) (show x ∉ (B).fv from (by exact dv_B_x))))))))))) (by exact (show y ∉ ((syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb]; exact (show y ∉ (((Wff.classMem (.cv z) A)).fv) ∪ (((Wff.classMem (.cv z) B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Wff.classMem (.cv z) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((Class.cv z)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ z from (by exact fresh_y_ne_z)))))) (show y ∉ (A).fv from (by exact dv_A_y)))))) (show y ∉ ((Wff.classMem (.cv z) B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((Class.cv z)).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ z from (by exact fresh_y_ne_z)))))) (show y ∉ (B).fv from (by exact dv_B_y)))))))))))
  have p0031 :=
    @g_bitr4i (.imp (.classMem (.cv z) (syn_cxpk (syn_c1c) (syn_c1c))) (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))) (.imp (syn_wex x (syn_wex y (.classEq (.cv z) (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y)))))) (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))) (.all x (.all y (.imp (.classEq (.cv z) (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y)))) (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))))) p0029 p0030
  have p0032 :=
    @g_albii (.imp (.classMem (.cv z) (syn_cxpk (syn_c1c) (syn_c1c))) (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))) (.all x (.all y (.imp (.classEq (.cv z) (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y)))) (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))))) z p0031
  have p0033 :=
    @g_alrot3 (.imp (.classEq (.cv z) (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y)))) (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))) z x y
  have p0034 :=
    @g_bitri (.all z (.imp (.classMem (.cv z) (syn_cxpk (syn_c1c) (syn_c1c))) (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)))) (.all z (.all x (.all y (.imp (.classEq (.cv z) (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y)))) (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)))))) (.all x (.all y (.all z (.imp (.classEq (.cv z) (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y)))) (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)))))) p0032 p0033
  have p0035 :=
    @g_opkex (syn_csn (.cv x)) (syn_csn (.cv y))
  have p0036 :=
    @g_eleq1 (.cv z) (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) A
  have p0037 :=
    @g_eleq1 (.cv z) (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) B
  have p0038 :=
    @g_bibi12d (.classEq (.cv z) (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y)))) (.classMem (.cv z) A) (.classMem (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) A) (.classMem (.cv z) B) (.classMem (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) B) p0036 p0037
  have p0039 :=
    @g_ceqsalv (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)) (syn_wb (.classMem (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) A) (.classMem (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) B)) z (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) (by exact (show z ∉ ((syn_copk (syn_csn (.cv x)) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show z ∉ (((syn_csn (.cv x))).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))))) (show z ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y))))))))))))) (by exact (show z ∉ ((syn_wb (.classMem (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) A) (.classMem (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb]; exact (show z ∉ (((Wff.classMem (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) A)).fv) ∪ (((Wff.classMem (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Wff.classMem (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show z ∉ (((syn_copk (syn_csn (.cv x)) (syn_csn (.cv y)))).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_copk (syn_csn (.cv x)) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show z ∉ (((syn_csn (.cv x))).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))))) (show z ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y)))))))))))) (show z ∉ (A).fv from (by exact fresh_z_not_A)))))) (show z ∉ ((Wff.classMem (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show z ∉ (((syn_copk (syn_csn (.cv x)) (syn_csn (.cv y)))).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_copk (syn_csn (.cv x)) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show z ∉ (((syn_csn (.cv x))).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))))) (show z ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y)))))))))))) (show z ∉ (B).fv from (by exact fresh_z_not_B))))))))))) p0035 p0038
  have p0040 :=
    @g_n_2albii (.all z (.imp (.classEq (.cv z) (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y)))) (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)))) (syn_wb (.classMem (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) A) (.classMem (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) B)) x y p0039
  have p0041 :=
    @g_n_3bitri (syn_wral z (syn_cxpk (syn_c1c) (syn_c1c)) (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))) (.all z (.imp (.classMem (.cv z) (syn_cxpk (syn_c1c) (syn_c1c))) (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)))) (.all x (.all y (.all z (.imp (.classEq (.cv z) (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y)))) (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)))))) (.all x (.all y (syn_wb (.classMem (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) A) (.classMem (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) B)))) p0002 p0034 p0040
  have p0042 :=
    @g_bitri (.classEq A B) (syn_wral z (syn_cxpk (syn_c1c) (syn_c1c)) (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))) (.all x (.all y (syn_wb (.classMem (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) A) (.classMem (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) B)))) p0001 p0041
  exact p0042

noncomputable def g_sikexg
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_csik A) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  let y : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_V : z ∉ V.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (h))
  have fresh_w_not_V : w ∉ V.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_V : y ∉ V.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_x_ne_w : x ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_w_ne_x : w ≠ x :=
    Ne.symm fresh_x_ne_w
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have fresh_z_ne_y : z ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_w_ne_y : w ≠ y := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_y_ne_w : y ≠ w :=
    Ne.symm fresh_w_ne_y
  have p0000 :=
    @g_sikeq (.cv x) A
  have p0001 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_csik (.cv x)) (syn_csik A) (syn_cvv) p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.Nominal.NFLiteralRemainingViaCompletenessDev001.axSi x y z w (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z)) (show x ≠ w from (by exact fresh_x_ne_w)) (show y ≠ z from (by exact fresh_y_ne_z)) (show y ≠ w from (by exact fresh_y_ne_w)) (show z ≠ w from (by exact fresh_z_ne_w))
  have p0003 :=
    @g_inss1 (syn_cxpk (syn_c1c) (syn_c1c)) (.cv y)
  have p0004 :=
    @g_sikss1c1c (.cv x)
  have p0005 :=
    @g_sikexlem z w (syn_cin (syn_cxpk (syn_c1c) (syn_c1c)) (.cv y)) (syn_csik (.cv x)) (by exact (show z ∉ ((syn_cin (syn_cxpk (syn_c1c) (syn_c1c)) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show z ∉ (((syn_cxpk (syn_c1c) (syn_c1c))).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_cxpk (syn_c1c) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show z ∉ (((syn_c1c)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show z ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y))))))))))) (by exact (show w ∉ ((syn_cin (syn_cxpk (syn_c1c) (syn_c1c)) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show w ∉ (((syn_cxpk (syn_c1c) (syn_c1c))).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((syn_cxpk (syn_c1c) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show w ∉ (((syn_c1c)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show w ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y))))))))))) (by exact (show z ∉ ((syn_csik (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik]; exact (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x))))))))) (by exact (show w ∉ ((syn_csik (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik]; exact (show w ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ x from (by exact fresh_w_ne_x))))))))) (show z ≠ w from (by exact fresh_z_ne_w)) p0003 p0004
  have p0006 :=
    @g_vex z
  have p0007 :=
    @g_snel1c (.cv z) p0006
  have p0008 :=
    @g_vex w
  have p0009 :=
    @g_snel1c (.cv w) p0008
  have p0010 :=
    @g_snex (.cv z)
  have p0011 :=
    @g_snex (.cv w)
  have p0012 :=
    @g_opkelxpk (syn_csn (.cv z)) (syn_csn (.cv w)) (syn_c1c) (syn_c1c) p0010 p0011
  have p0013 :=
    @g_mpbir2an (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w))) (syn_cxpk (syn_c1c) (syn_c1c))) (.classMem (syn_csn (.cv z)) (syn_c1c)) (.classMem (syn_csn (.cv w)) (syn_c1c)) p0007 p0009 p0012
  have p0014 :=
    @g_elin (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w))) (syn_cxpk (syn_c1c) (syn_c1c)) (.cv y)
  have p0015 :=
    @g_mpbiran (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w))) (syn_cin (syn_cxpk (syn_c1c) (syn_c1c)) (.cv y))) (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w))) (syn_cxpk (syn_c1c) (syn_c1c))) (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w))) (.cv y)) p0013 p0014
  have p0016 :=
    @g_opksnelsik (.cv z) (.cv w) (.cv x) p0006 p0008
  have p0017 :=
    @g_bibi12i (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w))) (syn_cin (syn_cxpk (syn_c1c) (syn_c1c)) (.cv y))) (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w))) (.cv y)) (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w))) (syn_csik (.cv x))) (.classMem (syn_copk (.cv z) (.cv w)) (.cv x)) p0015 p0016
  have p0018 :=
    @g_n_2albii (syn_wb (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w))) (syn_cin (syn_cxpk (syn_c1c) (syn_c1c)) (.cv y))) (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w))) (syn_csik (.cv x)))) (syn_wb (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w))) (.cv y)) (.classMem (syn_copk (.cv z) (.cv w)) (.cv x))) z w p0017
  have p0019 :=
    @g_bitri (.classEq (syn_cin (syn_cxpk (syn_c1c) (syn_c1c)) (.cv y)) (syn_csik (.cv x))) (.all z (.all w (syn_wb (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w))) (syn_cin (syn_cxpk (syn_c1c) (syn_c1c)) (.cv y))) (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w))) (syn_csik (.cv x)))))) (.all z (.all w (syn_wb (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w))) (.cv y)) (.classMem (syn_copk (.cv z) (.cv w)) (.cv x))))) p0005 p0018
  have p0020 :=
    @g_biimpri (.classEq (syn_cin (syn_cxpk (syn_c1c) (syn_c1c)) (.cv y)) (syn_csik (.cv x))) (.all z (.all w (syn_wb (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w))) (.cv y)) (.classMem (syn_copk (.cv z) (.cv w)) (.cv x))))) p0019
  have p0021 :=
    @g_n_1cex
  have p0022 :=
    @g_n_1cex
  have p0023 :=
    @g_xpkex (syn_c1c) (syn_c1c) p0021 p0022
  have p0024 :=
    @g_vex y
  have p0025 :=
    @g_inex (syn_cxpk (syn_c1c) (syn_c1c)) (.cv y) p0023 p0024
  have p0026 :=
    @g_syl6eqelr (.all z (.all w (syn_wb (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w))) (.cv y)) (.classMem (syn_copk (.cv z) (.cv w)) (.cv x))))) (syn_csik (.cv x)) (syn_cin (syn_cxpk (syn_c1c) (syn_c1c)) (.cv y)) (syn_cvv) p0020 p0025
  have p0027 :=
    @g_exlimiv (.all z (.all w (syn_wb (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w))) (.cv y)) (.classMem (syn_copk (.cv z) (.cv w)) (.cv x))))) (.classMem (syn_csik (.cv x)) (syn_cvv)) y (by exact (show y ∉ ((Wff.classMem (syn_csik (.cv x)) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((syn_csik (.cv x))).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_csik (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik]; exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))))) (show y ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0026
  have p0028 :=
    Nominal.mp p0002 p0027
  have p0029 :=
    @g_vtoclg (.classMem (syn_csik (.cv x)) (syn_cvv)) (.classMem (syn_csik A) (syn_cvv)) x A V (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show x ∉ ((Wff.classMem (syn_csik A) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((syn_csik A)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_csik A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik]; exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))) (show x ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0001 p0028
  exact p0029

noncomputable def g_sikex
    (A : Class) (hyp_sikex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_csik A) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_sikexg A (syn_cvv)
  have p0001 :=
    Nominal.mp hyp_sikex_1 p0000
  exact p0001



#print axioms g_sikex

end NFChoice.DirectNominalPrf.WPPReplay
