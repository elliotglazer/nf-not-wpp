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
import NominalWPPReplayChunk009StructuralPart012


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

noncomputable def g_xpkvexg
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_cxpk (syn_cvv) A) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  let a : Var := freshVar proofSupport 3
  let b : Var := freshVar proofSupport 4
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
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_V : y ∉ V.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (h))
  have fresh_a_not_V : a ∉ V.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (h))
  have fresh_b_not_V : b ∉ V.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_a : x ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_a_ne_x : a ≠ x :=
    Ne.symm fresh_x_ne_a
  have fresh_x_ne_b : x ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_b_ne_x : b ≠ x :=
    Ne.symm fresh_x_ne_b
  have fresh_z_ne_y : z ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_ne_a : z ≠ a := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_a_ne_z : a ≠ z :=
    Ne.symm fresh_z_ne_a
  have fresh_z_ne_b : z ≠ b := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_b_ne_z : b ≠ z :=
    Ne.symm fresh_z_ne_b
  have fresh_y_ne_a : y ≠ a := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_a_ne_y : a ≠ y :=
    Ne.symm fresh_y_ne_a
  have fresh_y_ne_b : y ≠ b := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_b_ne_y : b ≠ y :=
    Ne.symm fresh_y_ne_b
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have p0000 :=
    @g_xpkeq2 (.cv x) A (syn_cvv)
  have p0001 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_cxpk (syn_cvv) (.cv x)) (syn_cxpk (syn_cvv) A) (syn_cvv) p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.Nominal.NFLiteralXpViaCompletenessDev003.axXp x y z a b (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z)) (show x ≠ a from (by exact fresh_x_ne_a)) (show x ≠ b from (by exact fresh_x_ne_b)) (show y ≠ z from (by exact fresh_y_ne_z)) (show y ≠ a from (by exact fresh_y_ne_a)) (show y ≠ b from (by exact fresh_y_ne_b)) (show z ≠ a from (by exact fresh_z_ne_a)) (show z ≠ b from (by exact fresh_z_ne_b)) (show a ≠ b from (by exact fresh_a_ne_b))
  have p0003 :=
    @g_isset y (syn_cxpk (syn_cvv) (.cv x)) (by exact (show y ∉ ((syn_cxpk (syn_cvv) (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show y ∉ (((syn_cvv)).fv) ∪ (((Class.cv x)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))))))))
  have p0004 :=
    @g_dfcleq z (.cv y) (syn_cxpk (syn_cvv) (.cv x)) (by exact (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y))))))) (by exact (show z ∉ ((syn_cxpk (syn_cvv) (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show z ∉ (((syn_cvv)).fv) ∪ (((Class.cv x)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))))))))
  have p0005 :=
    @g_elxpk a b (.cv z) (syn_cvv) (.cv x) (by exact (show a ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ z from (by exact fresh_a_ne_z))))))) (by exact (show b ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ z from (by exact fresh_b_ne_z))))))) (by exact (show a ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show b ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show a ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ x from (by exact fresh_a_ne_x))))))) (by exact (show b ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ x from (by exact fresh_b_ne_x))))))) (show a ≠ b from (by exact fresh_a_ne_b))
  have p0006 :=
    @g_vex a
  have p0007 :=
    @g_biantrur (.classMem (.cv a) (syn_cvv)) (.objMem b x) p0006
  have p0008 :=
    @g_anbi2i (.objMem b x) (syn_wa (.classMem (.cv a) (syn_cvv)) (.objMem b x)) (.classEq (.cv z) (syn_copk (.cv a) (.cv b))) p0007
  have p0009 :=
    @g_n_2exbii (syn_wa (.classEq (.cv z) (syn_copk (.cv a) (.cv b))) (.objMem b x)) (syn_wa (.classEq (.cv z) (syn_copk (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) (syn_cvv)) (.objMem b x))) a b p0008
  have p0010_e00_recanon : Nominal.NPrf (syn_wb (.classMem (.cv z) (syn_cxpk (syn_cvv) (.cv x))) (syn_wex a (syn_wex b (syn_wa (.classEq (.cv z) (syn_copk (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) (syn_cvv)) (.objMem b x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cxpk syn_wex syn_cvv
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
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
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                apply Nominal.RecanonTransportDev.TRecanonWff.neg
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0005
  have p0010 :=
    @g_bitr4i (.classMem (.cv z) (syn_cxpk (syn_cvv) (.cv x))) (syn_wex a (syn_wex b (syn_wa (.classEq (.cv z) (syn_copk (.cv a) (.cv b))) (syn_wa (.classMem (.cv a) (syn_cvv)) (.objMem b x))))) (syn_wex a (syn_wex b (syn_wa (.classEq (.cv z) (syn_copk (.cv a) (.cv b))) (.objMem b x)))) p0010_e00_recanon p0009
  have p0011 :=
    @g_bibi2i (.classMem (.cv z) (syn_cxpk (syn_cvv) (.cv x))) (syn_wex a (syn_wex b (syn_wa (.classEq (.cv z) (syn_copk (.cv a) (.cv b))) (.objMem b x)))) (.objMem z y) p0010
  have p0012 :=
    @g_albii (syn_wb (.objMem z y) (.classMem (.cv z) (syn_cxpk (syn_cvv) (.cv x)))) (syn_wb (.objMem z y) (syn_wex a (syn_wex b (syn_wa (.classEq (.cv z) (syn_copk (.cv a) (.cv b))) (.objMem b x))))) z p0011
  have p0013_e00_recanon : Nominal.NPrf (syn_wb (.classEq (.cv y) (syn_cxpk (syn_cvv) (.cv x))) (.all z (syn_wb (.objMem z y) (.classMem (.cv z) (syn_cxpk (syn_cvv) (.cv x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cxpk syn_wex syn_cvv
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0004
  have p0013 :=
    @g_bitri (.classEq (.cv y) (syn_cxpk (syn_cvv) (.cv x))) (.all z (syn_wb (.objMem z y) (.classMem (.cv z) (syn_cxpk (syn_cvv) (.cv x))))) (.all z (syn_wb (.objMem z y) (syn_wex a (syn_wex b (syn_wa (.classEq (.cv z) (syn_copk (.cv a) (.cv b))) (.objMem b x)))))) p0013_e00_recanon p0012
  have p0014 :=
    @g_exbii (.classEq (.cv y) (syn_cxpk (syn_cvv) (.cv x))) (.all z (syn_wb (.objMem z y) (syn_wex a (syn_wex b (syn_wa (.classEq (.cv z) (syn_copk (.cv a) (.cv b))) (.objMem b x)))))) y p0013
  have p0015 :=
    @g_bitri (.classMem (syn_cxpk (syn_cvv) (.cv x)) (syn_cvv)) (syn_wex y (.classEq (.cv y) (syn_cxpk (syn_cvv) (.cv x)))) (syn_wex y (.all z (syn_wb (.objMem z y) (syn_wex a (syn_wex b (syn_wa (.classEq (.cv z) (syn_copk (.cv a) (.cv b))) (.objMem b x))))))) p0003 p0014
  have p0016 :=
    @g_mpbir (.classMem (syn_cxpk (syn_cvv) (.cv x)) (syn_cvv)) (syn_wex y (.all z (syn_wb (.objMem z y) (syn_wex a (syn_wex b (syn_wa (.classEq (.cv z) (syn_copk (.cv a) (.cv b))) (.objMem b x))))))) p0002 p0015
  have p0017 :=
    @g_vtoclg (.classMem (syn_cxpk (syn_cvv) (.cv x)) (syn_cvv)) (.classMem (syn_cxpk (syn_cvv) A) (syn_cvv)) x A V (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show x ∉ ((Wff.classMem (syn_cxpk (syn_cvv) A) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((syn_cxpk (syn_cvv) A)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cxpk (syn_cvv) A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show x ∉ (((syn_cvv)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show x ∉ (A).fv from (by exact fresh_x_not_A)))))) (show x ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0001 p0016
  exact p0017

noncomputable def g_cnvkexg
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_ccnvk A) (syn_cvv))) := by
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
    @g_cnvkeq (.cv x) A
  have p0001 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_ccnvk (.cv x)) (syn_ccnvk A) (syn_cvv) p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.Nominal.NFLiteralRemainingViaCompletenessDev001.axCnv x y z w (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z)) (show x ≠ w from (by exact fresh_x_ne_w)) (show y ≠ z from (by exact fresh_y_ne_z)) (show y ≠ w from (by exact fresh_y_ne_w)) (show z ≠ w from (by exact fresh_z_ne_w))
  have p0003 :=
    @g_inss1 (syn_cxpk (syn_cvv) (syn_cvv)) (.cv y)
  have p0004 :=
    @g_cnvkssvvk (.cv x)
  have p0005 :=
    @g_eqrelk z w (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv y)) (syn_ccnvk (.cv x)) (by exact (show z ∉ ((syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show z ∉ (((syn_cxpk (syn_cvv) (syn_cvv))).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_cxpk (syn_cvv) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show z ∉ (((syn_cvv)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show z ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y))))))))))) (by exact (show w ∉ ((syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show w ∉ (((syn_cxpk (syn_cvv) (syn_cvv))).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((syn_cxpk (syn_cvv) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show w ∉ (((syn_cvv)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show w ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y))))))))))) (by exact (show z ∉ ((syn_ccnvk (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk]; exact (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x))))))))) (by exact (show w ∉ ((syn_ccnvk (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk]; exact (show w ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ x from (by exact fresh_w_ne_x))))))))) (show z ≠ w from (by exact fresh_z_ne_w))
  have p0006 :=
    @g_mp2an (syn_wss (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv y)) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_wss (syn_ccnvk (.cv x)) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_wb (.classEq (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv y)) (syn_ccnvk (.cv x))) (.all z (.all w (syn_wb (.classMem (syn_copk (.cv z) (.cv w)) (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv y))) (.classMem (syn_copk (.cv z) (.cv w)) (syn_ccnvk (.cv x))))))) p0003 p0004 p0005
  have p0007 :=
    @g_vex z
  have p0008 :=
    @g_vex w
  have p0009 :=
    @g_opkelxpk (.cv z) (.cv w) (syn_cvv) (syn_cvv) p0007 p0008
  have p0010 :=
    @g_mpbir2an (.classMem (syn_copk (.cv z) (.cv w)) (syn_cxpk (syn_cvv) (syn_cvv))) (.classMem (.cv z) (syn_cvv)) (.classMem (.cv w) (syn_cvv)) p0007 p0008 p0009
  have p0011 :=
    @g_elin (syn_copk (.cv z) (.cv w)) (syn_cxpk (syn_cvv) (syn_cvv)) (.cv y)
  have p0012 :=
    @g_mpbiran (.classMem (syn_copk (.cv z) (.cv w)) (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv y))) (.classMem (syn_copk (.cv z) (.cv w)) (syn_cxpk (syn_cvv) (syn_cvv))) (.classMem (syn_copk (.cv z) (.cv w)) (.cv y)) p0010 p0011
  have p0013 :=
    @g_opkelcnvk (.cv z) (.cv w) (.cv x) p0007 p0008
  have p0014 :=
    @g_bibi12i (.classMem (syn_copk (.cv z) (.cv w)) (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv y))) (.classMem (syn_copk (.cv z) (.cv w)) (.cv y)) (.classMem (syn_copk (.cv z) (.cv w)) (syn_ccnvk (.cv x))) (.classMem (syn_copk (.cv w) (.cv z)) (.cv x)) p0012 p0013
  have p0015 :=
    @g_n_2albii (syn_wb (.classMem (syn_copk (.cv z) (.cv w)) (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv y))) (.classMem (syn_copk (.cv z) (.cv w)) (syn_ccnvk (.cv x)))) (syn_wb (.classMem (syn_copk (.cv z) (.cv w)) (.cv y)) (.classMem (syn_copk (.cv w) (.cv z)) (.cv x))) z w p0014
  have p0016 :=
    @g_bitri (.classEq (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv y)) (syn_ccnvk (.cv x))) (.all z (.all w (syn_wb (.classMem (syn_copk (.cv z) (.cv w)) (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv y))) (.classMem (syn_copk (.cv z) (.cv w)) (syn_ccnvk (.cv x)))))) (.all z (.all w (syn_wb (.classMem (syn_copk (.cv z) (.cv w)) (.cv y)) (.classMem (syn_copk (.cv w) (.cv z)) (.cv x))))) p0006 p0015
  have p0017 :=
    @g_biimpri (.classEq (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv y)) (syn_ccnvk (.cv x))) (.all z (.all w (syn_wb (.classMem (syn_copk (.cv z) (.cv w)) (.cv y)) (.classMem (syn_copk (.cv w) (.cv z)) (.cv x))))) p0016
  have p0018 :=
    @g_vvex
  have p0019 :=
    @g_xpkvexg (syn_cvv) (syn_cvv)
  have p0020 :=
    Nominal.mp p0018 p0019
  have p0021 :=
    @g_vex y
  have p0022 :=
    @g_inex (syn_cxpk (syn_cvv) (syn_cvv)) (.cv y) p0020 p0021
  have p0023 :=
    @g_syl6eqelr (.all z (.all w (syn_wb (.classMem (syn_copk (.cv z) (.cv w)) (.cv y)) (.classMem (syn_copk (.cv w) (.cv z)) (.cv x))))) (syn_ccnvk (.cv x)) (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv y)) (syn_cvv) p0017 p0022
  have p0024 :=
    @g_exlimiv (.all z (.all w (syn_wb (.classMem (syn_copk (.cv z) (.cv w)) (.cv y)) (.classMem (syn_copk (.cv w) (.cv z)) (.cv x))))) (.classMem (syn_ccnvk (.cv x)) (syn_cvv)) y (by exact (show y ∉ ((Wff.classMem (syn_ccnvk (.cv x)) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((syn_ccnvk (.cv x))).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_ccnvk (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk]; exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))))) (show y ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0023
  have p0025 :=
    Nominal.mp p0002 p0024
  have p0026 :=
    @g_vtoclg (.classMem (syn_ccnvk (.cv x)) (syn_cvv)) (.classMem (syn_ccnvk A) (syn_cvv)) x A V (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show x ∉ ((Wff.classMem (syn_ccnvk A) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((syn_ccnvk A)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_ccnvk A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk]; exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))) (show x ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0001 p0025
  exact p0026

noncomputable def g_cnvkex
    (A : Class) (hyp_cnvkex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_ccnvk A) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_cnvkexg A (syn_cvv)
  have p0001 :=
    Nominal.mp hyp_cnvkex_1 p0000
  exact p0001

noncomputable def g_xpkexg
    (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem B W)) (.classMem (syn_cxpk A B) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  have p0000 :=
    @g_cnvkxpk (syn_cvv) A
  have p0001 :=
    @g_xpkvexg A V
  have p0002 :=
    @g_cnvkexg (syn_cxpk (syn_cvv) A) (syn_cvv)
  have p0003 :=
    @g_syl (.classMem A V) (.classMem (syn_cxpk (syn_cvv) A) (syn_cvv)) (.classMem (syn_ccnvk (syn_cxpk (syn_cvv) A)) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_syl5eqelr (.classMem A V) (syn_cxpk A (syn_cvv)) (syn_ccnvk (syn_cxpk (syn_cvv) A)) (syn_cvv) p0000 p0003
  have p0005 :=
    @g_xpkvexg B W
  have p0006 :=
    @g_inxpk A (syn_cvv) (syn_cvv) B
  have p0007 :=
    @g_inv1 A
  have p0008 :=
    @g_incom (syn_cvv) B
  have p0009 :=
    @g_inv1 B
  have p0010 :=
    @g_eqtri (syn_cin (syn_cvv) B) (syn_cin B (syn_cvv)) B p0008 p0009
  have p0011 :=
    @g_xpkeq12i (syn_cin A (syn_cvv)) A (syn_cin (syn_cvv) B) B p0007 p0010
  have p0012 :=
    @g_eqtri (syn_cin (syn_cxpk A (syn_cvv)) (syn_cxpk (syn_cvv) B)) (syn_cxpk (syn_cin A (syn_cvv)) (syn_cin (syn_cvv) B)) (syn_cxpk A B) p0006 p0011
  have p0013 :=
    @g_inexg (syn_cxpk A (syn_cvv)) (syn_cxpk (syn_cvv) B) (syn_cvv) (syn_cvv)
  have p0014 :=
    @g_syl5eqelr (syn_wa (.classMem (syn_cxpk A (syn_cvv)) (syn_cvv)) (.classMem (syn_cxpk (syn_cvv) B) (syn_cvv))) (syn_cxpk A B) (syn_cin (syn_cxpk A (syn_cvv)) (syn_cxpk (syn_cvv) B)) (syn_cvv) p0012 p0013
  have p0015 :=
    @g_syl2an (.classMem A V) (.classMem (syn_cxpk A (syn_cvv)) (syn_cvv)) (.classMem (syn_cxpk (syn_cvv) B) (syn_cvv)) (.classMem (syn_cxpk A B) (syn_cvv)) (.classMem B W) p0004 p0005 p0014
  exact p0015

noncomputable def g_xpkex
    (A : Class) (B : Class) (hyp_xpkex_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_xpkex_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cxpk A B) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_xpkexg A B (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem (syn_cxpk A B) (syn_cvv)) hyp_xpkex_1 hyp_xpkex_2 p0000
  exact p0001

noncomputable def g_p6exg
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_cp6 A) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
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
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_V : y ∉ V.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (h))
  have fresh_w_not_V : w ∉ V.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_w : x ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_w_ne_x : w ≠ x :=
    Ne.symm fresh_x_ne_w
  have fresh_z_ne_y : z ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have fresh_y_ne_w : y ≠ w := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_y : w ≠ y :=
    Ne.symm fresh_y_ne_w
  have p0000 :=
    @g_p6eq (.cv x) A
  have p0001 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_cp6 (.cv x)) (syn_cp6 A) (syn_cvv) p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.Nominal.NFLiteralRemainingViaCompletenessDev001.axTypeLower x y z w (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z)) (show x ≠ w from (by exact fresh_x_ne_w)) (show y ≠ z from (by exact fresh_y_ne_z)) (show y ≠ w from (by exact fresh_y_ne_w)) (show z ≠ w from (by exact fresh_z_ne_w))
  have p0003 :=
    @g_dfcleq z (.cv y) (syn_cp6 (.cv x)) (by exact (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y))))))) (by exact (show z ∉ ((syn_cp6 (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cp6]; exact (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))))))
  have p0004 :=
    @g_vex z
  have p0005 :=
    @g_elp6 w (.cv z) (.cv x) (syn_cvv) (by exact (show w ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ z from (by exact fresh_w_ne_z))))))) (by exact (show w ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ x from (by exact fresh_w_ne_x)))))))
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_bibi2i (.classMem (.cv z) (syn_cp6 (.cv x))) (.all w (.classMem (syn_copk (.cv w) (syn_csn (.cv z))) (.cv x))) (.objMem z y) p0006
  have p0008 :=
    @g_albii (syn_wb (.objMem z y) (.classMem (.cv z) (syn_cp6 (.cv x)))) (syn_wb (.objMem z y) (.all w (.classMem (syn_copk (.cv w) (syn_csn (.cv z))) (.cv x)))) z p0007
  have p0009_e00_recanon : Nominal.NPrf (syn_wb (.classEq (.cv y) (syn_cp6 (.cv x))) (.all z (syn_wb (.objMem z y) (.classMem (.cv z) (syn_cp6 (.cv x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cp6 syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cxpk syn_wex syn_cvv syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cp6, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0003
  have p0009 :=
    @g_bitri (.classEq (.cv y) (syn_cp6 (.cv x))) (.all z (syn_wb (.objMem z y) (.classMem (.cv z) (syn_cp6 (.cv x))))) (.all z (syn_wb (.objMem z y) (.all w (.classMem (syn_copk (.cv w) (syn_csn (.cv z))) (.cv x))))) p0009_e00_recanon p0008
  have p0010 :=
    @g_biimpri (.classEq (.cv y) (syn_cp6 (.cv x))) (.all z (syn_wb (.objMem z y) (.all w (.classMem (syn_copk (.cv w) (syn_csn (.cv z))) (.cv x))))) p0009
  have p0011 :=
    @g_vex y
  have p0012 :=
    @g_syl6eqelr (.all z (syn_wb (.objMem z y) (.all w (.classMem (syn_copk (.cv w) (syn_csn (.cv z))) (.cv x))))) (syn_cp6 (.cv x)) (.cv y) (syn_cvv) p0010 p0011
  have p0013 :=
    @g_exlimiv (.all z (syn_wb (.objMem z y) (.all w (.classMem (syn_copk (.cv w) (syn_csn (.cv z))) (.cv x))))) (.classMem (syn_cp6 (.cv x)) (syn_cvv)) y (by exact (show y ∉ ((Wff.classMem (syn_cp6 (.cv x)) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((syn_cp6 (.cv x))).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cp6 (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cp6]; exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))))) (show y ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0012
  have p0014 :=
    Nominal.mp p0002 p0013
  have p0015 :=
    @g_vtoclg (.classMem (syn_cp6 (.cv x)) (syn_cvv)) (.classMem (syn_cp6 A) (syn_cvv)) x A V (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show x ∉ ((Wff.classMem (syn_cp6 A) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((syn_cp6 A)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cp6 A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cp6]; exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))) (show x ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0001 p0014
  exact p0015

noncomputable def g_dfuni12
    (A : Class) :
    Nominal.NPrf (.classEq (syn_cuni1 A) (syn_cp6 (syn_cxpk (syn_cvv) A))) := by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have p0000 :=
    @g_n_19_27v (.classMem (.cv z) (syn_cvv)) (.classMem (syn_csn (.cv x)) A) z (by exact (show z ∉ ((Wff.classMem (syn_csn (.cv x)) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show z ∉ (((syn_csn (.cv x))).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))))) (show z ∉ (A).fv from (by exact fresh_z_not_A)))))))
  have p0001 :=
    @g_vex z
  have p0002 :=
    @g_snex (.cv x)
  have p0003 :=
    @g_opkelxpk (.cv z) (syn_csn (.cv x)) (syn_cvv) A p0001 p0002
  have p0004 :=
    @g_albii (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_cxpk (syn_cvv) A)) (syn_wa (.classMem (.cv z) (syn_cvv)) (.classMem (syn_csn (.cv x)) A)) z p0003
  have p0005 :=
    Nominal.gen p0001 z
  have p0006 :=
    @g_biantrur (.all z (.classMem (.cv z) (syn_cvv))) (.classMem (syn_csn (.cv x)) A) p0005
  have p0007 :=
    @g_n_3bitr4ri (.all z (syn_wa (.classMem (.cv z) (syn_cvv)) (.classMem (syn_csn (.cv x)) A))) (syn_wa (.all z (.classMem (.cv z) (syn_cvv))) (.classMem (syn_csn (.cv x)) A)) (.all z (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_cxpk (syn_cvv) A))) (.classMem (syn_csn (.cv x)) A) p0000 p0004 p0006
  have p0008 :=
    @g_vex x
  have p0009 :=
    @g_eluni1 (.cv x) A p0008
  have p0010 :=
    @g_elp6 z (.cv x) (syn_cxpk (syn_cvv) A) (syn_cvv) (by exact (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x))))))) (by exact (show z ∉ ((syn_cxpk (syn_cvv) A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show z ∉ (((syn_cvv)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show z ∉ (A).fv from (by exact fresh_z_not_A)))))))
  have p0011 :=
    Nominal.mp p0008 p0010
  have p0012 :=
    @g_n_3bitr4i (.classMem (syn_csn (.cv x)) A) (.all z (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_cxpk (syn_cvv) A))) (.classMem (.cv x) (syn_cuni1 A)) (.classMem (.cv x) (syn_cp6 (syn_cxpk (syn_cvv) A))) p0007 p0009 p0011
  have p0013 :=
    @g_eqriv x (syn_cuni1 A) (syn_cp6 (syn_cxpk (syn_cvv) A)) (by exact (show x ∉ ((syn_cuni1 A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni1]; exact (show x ∉ (A).fv from (by exact fresh_x_not_A))))) (by exact (show x ∉ ((syn_cp6 (syn_cxpk (syn_cvv) A))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cp6]; exact (show x ∉ ((syn_cxpk (syn_cvv) A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show x ∉ (((syn_cvv)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show x ∉ (A).fv from (by exact fresh_x_not_A))))))))) p0012
  exact p0013

noncomputable def g_uni1exg
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_cuni1 A) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  have p0000 :=
    @g_dfuni12 A
  have p0001 :=
    @g_vvex
  have p0002 :=
    @g_xpkexg (syn_cvv) A (syn_cvv) V
  have p0003 :=
    @g_mpan (.classMem (syn_cvv) (syn_cvv)) (.classMem A V) (.classMem (syn_cxpk (syn_cvv) A) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_p6exg (syn_cxpk (syn_cvv) A) (syn_cvv)
  have p0005 :=
    @g_syl (.classMem A V) (.classMem (syn_cxpk (syn_cvv) A) (syn_cvv)) (.classMem (syn_cp6 (syn_cxpk (syn_cvv) A)) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_syl5eqel (.classMem A V) (syn_cuni1 A) (syn_cp6 (syn_cxpk (syn_cvv) A)) (syn_cvv) p0000 p0005
  exact p0006

noncomputable def g_uni1ex
    (A : Class) (hyp_uni1ex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cuni1 A) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_uni1exg A (syn_cvv)
  have p0001 :=
    Nominal.mp hyp_uni1ex_1 p0000
  exact p0001

noncomputable def g_ssetkex
     :
    Nominal.NPrf (.classMem (syn_cssetk) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
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
  have fresh_y_ne_w : y ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_w_ne_y : w ≠ y :=
    Ne.symm fresh_y_ne_w
  have fresh_z_ne_x : z ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have fresh_x_ne_w : x ≠ w := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_x : w ≠ x :=
    Ne.symm fresh_x_ne_w
  have p0000 :=
    NFChoice.DirectNominalPrf.Nominal.NFLiteralRemainingViaCompletenessDev001.axSset x y z w (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z)) (show x ≠ w from (by exact fresh_x_ne_w)) (show y ≠ z from (by exact fresh_y_ne_z)) (show y ≠ w from (by exact fresh_y_ne_w)) (show z ≠ w from (by exact fresh_z_ne_w))
  have p0001 :=
    @g_inss1 (syn_cxpk (syn_cvv) (syn_cvv)) (.cv x)
  have p0002 :=
    @g_ssetkssvvk
  have p0003 :=
    @g_eqrelk y z (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv x)) (syn_cssetk) (by exact (show y ∉ ((syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show y ∉ (((syn_cxpk (syn_cvv) (syn_cvv))).fv) ∪ (((Class.cv x)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cxpk (syn_cvv) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show y ∉ (((syn_cvv)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show y ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))))))) (by exact (show z ∉ ((syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show z ∉ (((syn_cxpk (syn_cvv) (syn_cvv))).fv) ∪ (((Class.cv x)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_cxpk (syn_cvv) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show z ∉ (((syn_cvv)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show z ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x))))))))))) (by exact (show y ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show z ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (show y ≠ z from (by exact fresh_y_ne_z))
  have p0004 :=
    @g_mp2an (syn_wss (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv x)) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_wss (syn_cssetk) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_wb (.classEq (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv x)) (syn_cssetk)) (.all y (.all z (syn_wb (.classMem (syn_copk (.cv y) (.cv z)) (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv x))) (.classMem (syn_copk (.cv y) (.cv z)) (syn_cssetk)))))) p0001 p0002 p0003
  have p0005 :=
    @g_vex y
  have p0006 :=
    @g_vex z
  have p0007 :=
    @g_opkelxpk (.cv y) (.cv z) (syn_cvv) (syn_cvv) p0005 p0006
  have p0008 :=
    @g_mpbir2an (.classMem (syn_copk (.cv y) (.cv z)) (syn_cxpk (syn_cvv) (syn_cvv))) (.classMem (.cv y) (syn_cvv)) (.classMem (.cv z) (syn_cvv)) p0005 p0006 p0007
  have p0009 :=
    @g_elin (syn_copk (.cv y) (.cv z)) (syn_cxpk (syn_cvv) (syn_cvv)) (.cv x)
  have p0010 :=
    @g_mpbiran (.classMem (syn_copk (.cv y) (.cv z)) (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv x))) (.classMem (syn_copk (.cv y) (.cv z)) (syn_cxpk (syn_cvv) (syn_cvv))) (.classMem (syn_copk (.cv y) (.cv z)) (.cv x)) p0008 p0009
  have p0011 :=
    @g_opkelssetkg (.cv y) (.cv z) (syn_cvv) (syn_cvv)
  have p0012 :=
    @g_mp2an (.classMem (.cv y) (syn_cvv)) (.classMem (.cv z) (syn_cvv)) (syn_wb (.classMem (syn_copk (.cv y) (.cv z)) (syn_cssetk)) (syn_wss (.cv y) (.cv z))) p0005 p0006 p0011
  have p0013 :=
    @g_dfss2 w (.cv y) (.cv z) (by exact (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y))))))) (by exact (show w ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ z from (by exact fresh_w_ne_z)))))))
  have p0014_e01_recanon : Nominal.NPrf (syn_wb (syn_wss (.cv y) (.cv z)) (.all w (.imp (.objMem w y) (.objMem w z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0013
  have p0014 :=
    @g_bitri (.classMem (syn_copk (.cv y) (.cv z)) (syn_cssetk)) (syn_wss (.cv y) (.cv z)) (.all w (.imp (.objMem w y) (.objMem w z))) p0012 p0014_e01_recanon
  have p0015 :=
    @g_bibi12i (.classMem (syn_copk (.cv y) (.cv z)) (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv x))) (.classMem (syn_copk (.cv y) (.cv z)) (.cv x)) (.classMem (syn_copk (.cv y) (.cv z)) (syn_cssetk)) (.all w (.imp (.objMem w y) (.objMem w z))) p0010 p0014
  have p0016 :=
    @g_n_2albii (syn_wb (.classMem (syn_copk (.cv y) (.cv z)) (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv x))) (.classMem (syn_copk (.cv y) (.cv z)) (syn_cssetk))) (syn_wb (.classMem (syn_copk (.cv y) (.cv z)) (.cv x)) (.all w (.imp (.objMem w y) (.objMem w z)))) y z p0015
  have p0017 :=
    @g_bitri (.classEq (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv x)) (syn_cssetk)) (.all y (.all z (syn_wb (.classMem (syn_copk (.cv y) (.cv z)) (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv x))) (.classMem (syn_copk (.cv y) (.cv z)) (syn_cssetk))))) (.all y (.all z (syn_wb (.classMem (syn_copk (.cv y) (.cv z)) (.cv x)) (.all w (.imp (.objMem w y) (.objMem w z)))))) p0004 p0016
  have p0018 :=
    @g_biimpri (.classEq (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv x)) (syn_cssetk)) (.all y (.all z (syn_wb (.classMem (syn_copk (.cv y) (.cv z)) (.cv x)) (.all w (.imp (.objMem w y) (.objMem w z)))))) p0017
  have p0019 :=
    @g_vvex
  have p0020 :=
    @g_xpkvexg (syn_cvv) (syn_cvv)
  have p0021 :=
    Nominal.mp p0019 p0020
  have p0022 :=
    @g_vex x
  have p0023 :=
    @g_inex (syn_cxpk (syn_cvv) (syn_cvv)) (.cv x) p0021 p0022
  have p0024 :=
    @g_syl6eqelr (.all y (.all z (syn_wb (.classMem (syn_copk (.cv y) (.cv z)) (.cv x)) (.all w (.imp (.objMem w y) (.objMem w z)))))) (syn_cssetk) (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv x)) (syn_cvv) p0018 p0023
  have p0025 :=
    @g_exlimiv (.all y (.all z (syn_wb (.classMem (syn_copk (.cv y) (.cv z)) (.cv x)) (.all w (.imp (.objMem w y) (.objMem w z)))))) (.classMem (syn_cssetk) (syn_cvv)) x (by exact (show x ∉ ((Wff.classMem (syn_cssetk) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((syn_cssetk)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show x ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0024
  have p0026 :=
    Nominal.mp p0000 p0025
  exact p0026



#print axioms g_ssetkex

end NFChoice.DirectNominalPrf.WPPReplay
