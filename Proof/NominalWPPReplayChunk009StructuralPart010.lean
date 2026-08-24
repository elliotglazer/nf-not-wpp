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
import NominalWPPReplayChunk009StructuralPart009


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

noncomputable def g_sikss1c1c
    (A : Class) :
    Nominal.NPrf (syn_wss (syn_csik A) (syn_cxpk (syn_c1c) (syn_c1c))) := by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let a : Var := freshVar proofSupport 2
  let b : Var := freshVar proofSupport 3
  let z : Var := freshVar proofSupport 4
  let w : Var := freshVar proofSupport 5
  let t : Var := freshVar proofSupport 6
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
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (h)
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (h)
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (h)
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (h)
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_a : x ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_a_ne_x : a ≠ x :=
    Ne.symm fresh_x_ne_a
  have fresh_x_ne_b : x ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_b_ne_x : b ≠ x :=
    Ne.symm fresh_x_ne_b
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_x_ne_w : x ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_w_ne_x : w ≠ x :=
    Ne.symm fresh_x_ne_w
  have fresh_x_ne_t : x ≠ t := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_t_ne_x : t ≠ x :=
    Ne.symm fresh_x_ne_t
  have fresh_y_ne_a : y ≠ a := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_a_ne_y : a ≠ y :=
    Ne.symm fresh_y_ne_a
  have fresh_y_ne_b : y ≠ b := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_b_ne_y : b ≠ y :=
    Ne.symm fresh_y_ne_b
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_y_ne_w : y ≠ w := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_w_ne_y : w ≠ y :=
    Ne.symm fresh_y_ne_w
  have fresh_y_ne_t : y ≠ t := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_t_ne_y : t ≠ y :=
    Ne.symm fresh_y_ne_t
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have fresh_a_ne_z : a ≠ z := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_z_ne_a : z ≠ a :=
    Ne.symm fresh_a_ne_z
  have fresh_a_ne_w : a ≠ w := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_w_ne_a : w ≠ a :=
    Ne.symm fresh_a_ne_w
  have fresh_a_ne_t : a ≠ t := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_t_ne_a : t ≠ a :=
    Ne.symm fresh_a_ne_t
  have fresh_b_ne_z : b ≠ z := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_z_ne_b : z ≠ b :=
    Ne.symm fresh_b_ne_z
  have fresh_b_ne_w : b ≠ w := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_w_ne_b : w ≠ b :=
    Ne.symm fresh_b_ne_w
  have fresh_b_ne_t : b ≠ t := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_t_ne_b : t ≠ b :=
    Ne.symm fresh_b_ne_t
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have fresh_z_ne_t : z ≠ t := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_t_ne_z : t ≠ z :=
    Ne.symm fresh_z_ne_t
  have fresh_w_ne_t : w ≠ t := by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_t_ne_w : t ≠ w :=
    Ne.symm fresh_w_ne_t
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sik t z w b a A (by exact (show a ∉ (A).fv from (by exact fresh_a_not_A))) (by exact (show b ∉ (A).fv from (by exact fresh_b_not_A))) (by exact (show t ∉ (A).fv from (by exact fresh_t_not_A))) (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A))) (by exact (show w ∉ (A).fv from (by exact fresh_w_not_A))) (show a ≠ b from (by exact fresh_a_ne_b)) (show a ≠ t from (by exact fresh_a_ne_t)) (show a ≠ z from (by exact fresh_a_ne_z)) (show a ≠ w from (by exact fresh_a_ne_w)) (show b ≠ t from (by exact fresh_b_ne_t)) (show b ≠ z from (by exact fresh_b_ne_z)) (show b ≠ w from (by exact fresh_b_ne_w)) (show t ≠ z from (by exact fresh_t_ne_z)) (show t ≠ w from (by exact fresh_t_ne_w)) (show z ≠ w from (by exact fresh_z_ne_w))
  have p0001 :=
    @g_eqeq1 (.cv z) (.cv x) (syn_csn (.cv a))
  have p0002_e00_recanon : Nominal.NPrf (.imp (.objEq z x) (syn_wb (.classEq (.cv z) (syn_csn (.cv a))) (.classEq (.cv x) (syn_csn (.cv a))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0001
  have p0002 :=
    @g_n_3anbi1d (.objEq z x) (.classEq (.cv z) (syn_csn (.cv a))) (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv w) (syn_csn (.cv b))) (.classMem (syn_copk (.cv a) (.cv b)) A) p0002_e00_recanon
  have p0003 :=
    @g_n_2exbidv (.objEq z x) (syn_w3a (.classEq (.cv z) (syn_csn (.cv a))) (.classEq (.cv w) (syn_csn (.cv b))) (.classMem (syn_copk (.cv a) (.cv b)) A)) (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv w) (syn_csn (.cv b))) (.classMem (syn_copk (.cv a) (.cv b)) A)) a b (by exact (show a ∉ ((Wff.objEq z x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]; exact (show a ∉ ({z, x} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show a ≠ z from (by exact fresh_a_ne_z)), (show a ≠ x from (by exact fresh_a_ne_x))⟩))))) (by exact (show b ∉ ((Wff.objEq z x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]; exact (show b ∉ ({z, x} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show b ≠ z from (by exact fresh_b_ne_z)), (show b ≠ x from (by exact fresh_b_ne_x))⟩))))) p0002
  have p0004 :=
    @g_eqeq1 (.cv w) (.cv y) (syn_csn (.cv b))
  have p0005_e00_recanon : Nominal.NPrf (.imp (.objEq w y) (syn_wb (.classEq (.cv w) (syn_csn (.cv b))) (.classEq (.cv y) (syn_csn (.cv b))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0004
  have p0005 :=
    @g_n_3anbi2d (.objEq w y) (.classEq (.cv w) (syn_csn (.cv b))) (.classEq (.cv y) (syn_csn (.cv b))) (.classEq (.cv x) (syn_csn (.cv a))) (.classMem (syn_copk (.cv a) (.cv b)) A) p0005_e00_recanon
  have p0006 :=
    @g_n_2exbidv (.objEq w y) (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv w) (syn_csn (.cv b))) (.classMem (syn_copk (.cv a) (.cv b)) A)) (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))) (.classMem (syn_copk (.cv a) (.cv b)) A)) a b (by exact (show a ∉ ((Wff.objEq w y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]; exact (show a ∉ ({w, y} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show a ≠ w from (by exact fresh_a_ne_w)), (show a ≠ y from (by exact fresh_a_ne_y))⟩))))) (by exact (show b ∉ ((Wff.objEq w y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]; exact (show b ∉ ({w, y} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show b ≠ w from (by exact fresh_b_ne_w)), (show b ≠ y from (by exact fresh_b_ne_y))⟩))))) p0005
  have p0007 :=
    @g_vex x
  have p0008 :=
    @g_vex y
  have p0009_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv z) (.cv x)) (syn_wb (syn_wex a (syn_wex b (syn_w3a (.classEq (.cv z) (syn_csn (.cv a))) (.classEq (.cv w) (syn_csn (.cv b))) (.classMem (syn_copk (.cv a) (.cv b)) A)))) (syn_wex a (syn_wex b (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv w) (syn_csn (.cv b))) (.classMem (syn_copk (.cv a) (.cv b)) A)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0003
  have p0009_e02_recanon : Nominal.NPrf (.imp (.classEq (.cv w) (.cv y)) (syn_wb (syn_wex a (syn_wex b (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv w) (syn_csn (.cv b))) (.classMem (syn_copk (.cv a) (.cv b)) A)))) (syn_wex a (syn_wex b (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))) (.classMem (syn_copk (.cv a) (.cv b)) A)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0006
  have p0009 :=
    @g_opkelopkab (syn_wex a (syn_wex b (syn_w3a (.classEq (.cv z) (syn_csn (.cv a))) (.classEq (.cv w) (syn_csn (.cv b))) (.classMem (syn_copk (.cv a) (.cv b)) A)))) (syn_wex a (syn_wex b (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv w) (syn_csn (.cv b))) (.classMem (syn_copk (.cv a) (.cv b)) A)))) (syn_wex a (syn_wex b (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))) (.classMem (syn_copk (.cv a) (.cv b)) A)))) t z w (syn_csik A) (.cv x) (.cv y) (by exact (show z ∉ ((syn_csik A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik]; exact (show z ∉ (A).fv from (by exact fresh_z_not_A))))) (by exact (show w ∉ ((syn_csik A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik]; exact (show w ∉ (A).fv from (by exact fresh_w_not_A))))) (by exact (show t ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ x from (by exact fresh_t_ne_x))))))) (by exact (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x))))))) (by exact (show w ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ x from (by exact fresh_w_ne_x))))))) (by exact (show t ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ y from (by exact fresh_t_ne_y))))))) (by exact (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y))))))) (by exact (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y))))))) (by exact (show w ∉ ((syn_wex a (syn_wex b (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))) (.classMem (syn_copk (.cv a) (.cv b)) A))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex]; exact (show w ∉ (((syn_wex b (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))) (.classMem (syn_copk (.cv a) (.cv b)) A)))).fv).erase a from (fun hmem => (show w ∉ ((syn_wex b (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))) (.classMem (syn_copk (.cv a) (.cv b)) A)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex]; exact (show w ∉ (((syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))) (.classMem (syn_copk (.cv a) (.cv b)) A))).fv).erase b from (fun hmem => (show w ∉ ((syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))) (.classMem (syn_copk (.cv a) (.cv b)) A))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a]; exact (show w ∉ (((Wff.classMem (syn_copk (.cv a) (.cv b)) A)).fv) ∪ (((Wff.classEq (.cv x) (syn_csn (.cv a)))).fv) ∪ (((Wff.classEq (.cv y) (syn_csn (.cv b)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Wff.classMem (syn_copk (.cv a) (.cv b)) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show w ∉ (((syn_copk (.cv a) (.cv b))).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((syn_copk (.cv a) (.cv b))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show w ∉ (((Class.cv a)).fv) ∪ (((Class.cv b)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ a from (by exact fresh_w_ne_a)))))) (show w ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ b from (by exact fresh_w_ne_b)))))))))) (show w ∉ (A).fv from (by exact fresh_w_not_A)))))) (show w ∉ ((Wff.classEq (.cv x) (syn_csn (.cv a)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show w ∉ (((Class.cv x)).fv) ∪ (((syn_csn (.cv a))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ x from (by exact fresh_w_ne_x)))))) (show w ∉ ((syn_csn (.cv a))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show w ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ a from (by exact fresh_w_ne_a))))))))))))) (show w ∉ ((Wff.classEq (.cv y) (syn_csn (.cv b)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show w ∉ (((Class.cv y)).fv) ∪ (((syn_csn (.cv b))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y)))))) (show w ∉ ((syn_csn (.cv b))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show w ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ b from (by exact fresh_w_ne_b)))))))))))))))) (Finset.mem_of_mem_erase hmem))))) (Finset.mem_of_mem_erase hmem)))))) (by exact (show t ∉ ((syn_wex a (syn_wex b (syn_w3a (.classEq (.cv z) (syn_csn (.cv a))) (.classEq (.cv w) (syn_csn (.cv b))) (.classMem (syn_copk (.cv a) (.cv b)) A))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex]; exact (show t ∉ (((syn_wex b (syn_w3a (.classEq (.cv z) (syn_csn (.cv a))) (.classEq (.cv w) (syn_csn (.cv b))) (.classMem (syn_copk (.cv a) (.cv b)) A)))).fv).erase a from (fun hmem => (show t ∉ ((syn_wex b (syn_w3a (.classEq (.cv z) (syn_csn (.cv a))) (.classEq (.cv w) (syn_csn (.cv b))) (.classMem (syn_copk (.cv a) (.cv b)) A)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex]; exact (show t ∉ (((syn_w3a (.classEq (.cv z) (syn_csn (.cv a))) (.classEq (.cv w) (syn_csn (.cv b))) (.classMem (syn_copk (.cv a) (.cv b)) A))).fv).erase b from (fun hmem => (show t ∉ ((syn_w3a (.classEq (.cv z) (syn_csn (.cv a))) (.classEq (.cv w) (syn_csn (.cv b))) (.classMem (syn_copk (.cv a) (.cv b)) A))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a]; exact (show t ∉ (((Wff.classMem (syn_copk (.cv a) (.cv b)) A)).fv) ∪ (((Wff.classEq (.cv z) (syn_csn (.cv a)))).fv) ∪ (((Wff.classEq (.cv w) (syn_csn (.cv b)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((Wff.classMem (syn_copk (.cv a) (.cv b)) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show t ∉ (((syn_copk (.cv a) (.cv b))).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_copk (.cv a) (.cv b))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show t ∉ (((Class.cv a)).fv) ∪ (((Class.cv b)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ a from (by exact fresh_t_ne_a)))))) (show t ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ b from (by exact fresh_t_ne_b)))))))))) (show t ∉ (A).fv from (by exact fresh_t_not_A)))))) (show t ∉ ((Wff.classEq (.cv z) (syn_csn (.cv a)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show t ∉ (((Class.cv z)).fv) ∪ (((syn_csn (.cv a))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ z from (by exact fresh_t_ne_z)))))) (show t ∉ ((syn_csn (.cv a))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ a from (by exact fresh_t_ne_a))))))))))))) (show t ∉ ((Wff.classEq (.cv w) (syn_csn (.cv b)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show t ∉ (((Class.cv w)).fv) ∪ (((syn_csn (.cv b))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((Class.cv w)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({w} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ w from (by exact fresh_t_ne_w)))))) (show t ∉ ((syn_csn (.cv b))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ b from (by exact fresh_t_ne_b)))))))))))))))) (Finset.mem_of_mem_erase hmem))))) (Finset.mem_of_mem_erase hmem)))))) (by exact (show z ∉ ((syn_wex a (syn_wex b (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv w) (syn_csn (.cv b))) (.classMem (syn_copk (.cv a) (.cv b)) A))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex]; exact (show z ∉ (((syn_wex b (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv w) (syn_csn (.cv b))) (.classMem (syn_copk (.cv a) (.cv b)) A)))).fv).erase a from (fun hmem => (show z ∉ ((syn_wex b (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv w) (syn_csn (.cv b))) (.classMem (syn_copk (.cv a) (.cv b)) A)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex]; exact (show z ∉ (((syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv w) (syn_csn (.cv b))) (.classMem (syn_copk (.cv a) (.cv b)) A))).fv).erase b from (fun hmem => (show z ∉ ((syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv w) (syn_csn (.cv b))) (.classMem (syn_copk (.cv a) (.cv b)) A))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a]; exact (show z ∉ (((Wff.classMem (syn_copk (.cv a) (.cv b)) A)).fv) ∪ (((Wff.classEq (.cv x) (syn_csn (.cv a)))).fv) ∪ (((Wff.classEq (.cv w) (syn_csn (.cv b)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Wff.classMem (syn_copk (.cv a) (.cv b)) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show z ∉ (((syn_copk (.cv a) (.cv b))).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_copk (.cv a) (.cv b))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show z ∉ (((Class.cv a)).fv) ∪ (((Class.cv b)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ a from (by exact fresh_z_ne_a)))))) (show z ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ b from (by exact fresh_z_ne_b)))))))))) (show z ∉ (A).fv from (by exact fresh_z_not_A)))))) (show z ∉ ((Wff.classEq (.cv x) (syn_csn (.cv a)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show z ∉ (((Class.cv x)).fv) ∪ (((syn_csn (.cv a))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))) (show z ∉ ((syn_csn (.cv a))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show z ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ a from (by exact fresh_z_ne_a))))))))))))) (show z ∉ ((Wff.classEq (.cv w) (syn_csn (.cv b)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show z ∉ (((Class.cv w)).fv) ∪ (((syn_csn (.cv b))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv w)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({w} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ w from (by exact fresh_z_ne_w)))))) (show z ∉ ((syn_csn (.cv b))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show z ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ b from (by exact fresh_z_ne_b)))))))))))))))) (Finset.mem_of_mem_erase hmem))))) (Finset.mem_of_mem_erase hmem)))))) (show t ≠ z from (by exact fresh_t_ne_z)) (show t ≠ w from (by exact fresh_t_ne_w)) (show z ≠ w from (by exact fresh_z_ne_w)) p0000 p0009_e01_recanon p0009_e02_recanon p0007 p0008
  have p0010 :=
    @g_opkeq12 (.cv x) (.cv y) (syn_csn (.cv a)) (syn_csn (.cv b))
  have p0011 :=
    @g_vex a
  have p0012 :=
    @g_snel1c (.cv a) p0011
  have p0013 :=
    @g_vex b
  have p0014 :=
    @g_snel1c (.cv b) p0013
  have p0015 :=
    @g_opkelxpkg (syn_csn (.cv a)) (syn_csn (.cv b)) (syn_c1c) (syn_c1c) (syn_c1c) (syn_c1c)
  have p0016 :=
    @g_mp2an (.classMem (syn_csn (.cv a)) (syn_c1c)) (.classMem (syn_csn (.cv b)) (syn_c1c)) (syn_wb (.classMem (syn_copk (syn_csn (.cv a)) (syn_csn (.cv b))) (syn_cxpk (syn_c1c) (syn_c1c))) (syn_wa (.classMem (syn_csn (.cv a)) (syn_c1c)) (.classMem (syn_csn (.cv b)) (syn_c1c)))) p0012 p0014 p0015
  have p0017 :=
    @g_mpbir2an (.classMem (syn_copk (syn_csn (.cv a)) (syn_csn (.cv b))) (syn_cxpk (syn_c1c) (syn_c1c))) (.classMem (syn_csn (.cv a)) (syn_c1c)) (.classMem (syn_csn (.cv b)) (syn_c1c)) p0012 p0014 p0016
  have p0018 :=
    @g_syl6eqel (syn_wa (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b)))) (syn_copk (.cv x) (.cv y)) (syn_copk (syn_csn (.cv a)) (syn_csn (.cv b))) (syn_cxpk (syn_c1c) (syn_c1c)) p0010 p0017
  have p0019 :=
    @g_n_3adant3 (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))) (.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk (syn_c1c) (syn_c1c))) (.classMem (syn_copk (.cv a) (.cv b)) A) p0018
  have p0020 :=
    @g_exlimivv (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))) (.classMem (syn_copk (.cv a) (.cv b)) A)) (.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk (syn_c1c) (syn_c1c))) a b (by exact (show a ∉ ((Wff.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk (syn_c1c) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show a ∉ (((syn_copk (.cv x) (.cv y))).fv) ∪ (((syn_cxpk (syn_c1c) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((syn_copk (.cv x) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show a ∉ (((Class.cv x)).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ x from (by exact fresh_a_ne_x)))))) (show a ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ y from (by exact fresh_a_ne_y)))))))))) (show a ∉ ((syn_cxpk (syn_c1c) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show a ∉ (((syn_c1c)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show a ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (by exact (show b ∉ ((Wff.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk (syn_c1c) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ (((syn_copk (.cv x) (.cv y))).fv) ∪ (((syn_cxpk (syn_c1c) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_copk (.cv x) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show b ∉ (((Class.cv x)).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ x from (by exact fresh_b_ne_x)))))) (show b ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ y from (by exact fresh_b_ne_y)))))))))) (show b ∉ ((syn_cxpk (syn_c1c) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show b ∉ (((syn_c1c)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show b ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) p0019
  have p0021 :=
    @g_sylbi (.classMem (syn_copk (.cv x) (.cv y)) (syn_csik A)) (syn_wex a (syn_wex b (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))) (.classMem (syn_copk (.cv a) (.cv b)) A)))) (.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk (syn_c1c) (syn_c1c))) p0009 p0020
  have p0022 :=
    @g_gen2 (.imp (.classMem (syn_copk (.cv x) (.cv y)) (syn_csik A)) (.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk (syn_c1c) (syn_c1c)))) x y p0021
  have p0023 :=
    @g_sikssvvk A
  have p0024 :=
    @g_ssrelk x y (syn_csik A) (syn_cxpk (syn_c1c) (syn_c1c)) (by exact (show x ∉ ((syn_csik A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik]; exact (show x ∉ (A).fv from (by exact fresh_x_not_A))))) (by exact (show y ∉ ((syn_csik A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik]; exact (show y ∉ (A).fv from (by exact fresh_y_not_A))))) (by exact (show x ∉ ((syn_cxpk (syn_c1c) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show x ∉ (((syn_c1c)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show x ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) (by exact (show y ∉ ((syn_cxpk (syn_c1c) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show y ∉ (((syn_c1c)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show y ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) (show x ≠ y from (by exact fresh_x_ne_y))
  have p0025 :=
    Nominal.mp p0023 p0024
  have p0026 :=
    @g_mpbir (syn_wss (syn_csik A) (syn_cxpk (syn_c1c) (syn_c1c))) (.all x (.all y (.imp (.classMem (syn_copk (.cv x) (.cv y)) (syn_csik A)) (.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk (syn_c1c) (syn_c1c)))))) p0022 p0025
  exact p0026

noncomputable def g_opkelssetkg
    (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem B W)) (syn_wb (.classMem (syn_copk A B) (syn_cssetk)) (syn_wss A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
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
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_V : z ∉ V.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_W : z ∉ W.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ssetk x y z (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z)) (show y ≠ z from (by exact fresh_y_ne_z))
  have p0001 :=
    @g_sseq1 (.cv y) A (.cv z)
  have p0002 :=
    @g_sseq2 (.cv z) B A
  have p0003 :=
    @g_opkelopkabg (syn_wss (.cv y) (.cv z)) (syn_wss A (.cv z)) (syn_wss A B) x y z (syn_cssetk) A B V W (by exact (show y ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show z ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A))) (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B))) (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B))) (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B))) (by exact (show z ∉ ((syn_wss A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss]; exact (show z ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ (A).fv from (by exact fresh_z_not_A)) (show z ∉ (B).fv from (by exact fresh_z_not_B))))))) (by exact (show x ∉ ((syn_wss (.cv y) (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss]; exact (show x ∉ (((Class.cv y)).fv) ∪ (((Class.cv z)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y)))))) (show x ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ z from (by exact fresh_x_ne_z))))))))))) (by exact (show y ∉ ((syn_wss A (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss]; exact (show y ∉ ((A).fv) ∪ (((Class.cv z)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ z from (by exact fresh_y_ne_z))))))))))) (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z)) (show y ≠ z from (by exact fresh_y_ne_z)) p0000 p0001 p0002
  exact p0003

noncomputable def g_elssetkg
    (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem B W)) (syn_wb (.classMem (syn_copk (syn_csn A) B) (syn_cssetk)) (.classMem A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  have p0000 :=
    @g_snex A
  have p0001 :=
    @g_opkelssetkg (syn_csn A) B (syn_cvv) W
  have p0002 :=
    @g_mpan (.classMem (syn_csn A) (syn_cvv)) (.classMem B W) (syn_wb (.classMem (syn_copk (syn_csn A) B) (syn_cssetk)) (syn_wss (syn_csn A) B)) p0000 p0001
  have p0003 :=
    @g_snssg A B V
  have p0004 :=
    @g_bicomd (.classMem A V) (.classMem A B) (syn_wss (syn_csn A) B) p0003
  have p0005 :=
    @g_sylan9bbr (.classMem B W) (.classMem (syn_copk (syn_csn A) B) (syn_cssetk)) (syn_wss (syn_csn A) B) (.classMem A V) (.classMem A B) p0002 p0004
  exact p0005

noncomputable def g_elssetk
    (A : Class) (B : Class) (hyp_elssetk_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_elssetk_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem (syn_copk (syn_csn A) B) (syn_cssetk)) (.classMem A B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_elssetkg A B (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (syn_wb (.classMem (syn_copk (syn_csn A) B) (syn_cssetk)) (.classMem A B)) hyp_elssetk_1 hyp_elssetk_2 p0000
  exact p0001



#print axioms g_elssetk

end NFChoice.DirectNominalPrf.WPPReplay
