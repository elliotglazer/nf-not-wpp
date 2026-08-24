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
import NominalWPPReplayChunk009StructuralPart017


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

noncomputable def g_dfuni3
    (A : Class) :
    Nominal.NPrf (.classEq (syn_cuni A) (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cssetk)) A))) := by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
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
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have p0000 :=
    @g_vex y
  have p0001 :=
    @g_snex (.cv x)
  have p0002 :=
    @g_opkelcnvk (.cv y) (syn_csn (.cv x)) (syn_cssetk) p0000 p0001
  have p0003 :=
    @g_vex x
  have p0004 :=
    @g_elssetk (.cv x) (.cv y) p0003 p0000
  have p0005_e01_recanon : Nominal.NPrf (syn_wb (.classMem (syn_copk (syn_csn (.cv x)) (.cv y)) (syn_cssetk)) (.objMem x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn syn_cssetk syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0004
  have p0005 :=
    @g_bitri (.classMem (syn_copk (.cv y) (syn_csn (.cv x))) (syn_ccnvk (syn_cssetk))) (.classMem (syn_copk (syn_csn (.cv x)) (.cv y)) (syn_cssetk)) (.objMem x y) p0002 p0005_e01_recanon
  have p0006 :=
    @g_rexbii (.classMem (syn_copk (.cv y) (syn_csn (.cv x))) (syn_ccnvk (syn_cssetk))) (.objMem x y) y A p0005
  have p0007 :=
    @g_eluni1 (.cv x) (syn_cimak (syn_ccnvk (syn_cssetk)) A) p0003
  have p0008 :=
    @g_elimak y (syn_ccnvk (syn_cssetk)) A (syn_csn (.cv x)) (by exact (show y ∉ ((syn_ccnvk (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk]; exact (show y ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show y ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))))) p0001
  have p0009 :=
    @g_bitri (.classMem (.cv x) (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cssetk)) A))) (.classMem (syn_csn (.cv x)) (syn_cimak (syn_ccnvk (syn_cssetk)) A)) (syn_wrex y A (.classMem (syn_copk (.cv y) (syn_csn (.cv x))) (syn_ccnvk (syn_cssetk)))) p0007 p0008
  have p0010 :=
    @g_eluni2 y (.cv x) A (by exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
  have p0011_e02_recanon : Nominal.NPrf (syn_wb (.classMem (.cv x) (syn_cuni A)) (syn_wrex y A (.objMem x y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cuni syn_wex syn_wa syn_wrex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0010
  have p0011 :=
    @g_n_3bitr4ri (syn_wrex y A (.classMem (syn_copk (.cv y) (syn_csn (.cv x))) (syn_ccnvk (syn_cssetk)))) (syn_wrex y A (.objMem x y)) (.classMem (.cv x) (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cssetk)) A))) (.classMem (.cv x) (syn_cuni A)) p0006 p0009 p0011_e02_recanon
  have p0012 :=
    @g_eqriv x (syn_cuni A) (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cssetk)) A)) (by exact (show x ∉ ((syn_cuni A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show x ∉ (A).fv from (by exact fresh_x_not_A))))) (by exact (show x ∉ ((syn_cuni1 (syn_cimak (syn_ccnvk (syn_cssetk)) A))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni1]; exact (show x ∉ ((syn_cimak (syn_ccnvk (syn_cssetk)) A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak]; exact (show x ∉ (((syn_ccnvk (syn_cssetk))).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_ccnvk (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk]; exact (show x ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))) (show x ∉ (A).fv from (by exact fresh_x_not_A))))))))) p0011
  exact p0012

noncomputable def g_uniexg
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_cuni A) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  have p0000 :=
    @g_dfuni3 A
  have p0001 :=
    @g_ssetkex
  have p0002 :=
    @g_cnvkex (syn_cssetk) p0001
  have p0003 :=
    @g_imakexg (syn_ccnvk (syn_cssetk)) A (syn_cvv) V
  have p0004 :=
    @g_mpan (.classMem (syn_ccnvk (syn_cssetk)) (syn_cvv)) (.classMem A V) (.classMem (syn_cimak (syn_ccnvk (syn_cssetk)) A) (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_uni1exg (syn_cimak (syn_ccnvk (syn_cssetk)) A) (syn_cvv)
  have p0006 :=
    @g_syl (.classMem A V) (.classMem (syn_cimak (syn_ccnvk (syn_cssetk)) A) (syn_cvv)) (.classMem (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cssetk)) A)) (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_syl5eqel (.classMem A V) (syn_cuni A) (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cssetk)) A)) (syn_cvv) p0000 p0006
  exact p0007

noncomputable def g_uniex
    (A : Class) (hyp_uniex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cuni A) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_uniexg A (syn_cvv)
  have p0001 :=
    Nominal.mp hyp_uniex_1 p0000
  exact p0001

noncomputable def g_dfint3
    (A : Class) :
    Nominal.NPrf (.classEq (syn_cint A) (syn_ccompl (syn_cuni1 (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A)))) := by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
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
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have p0000 :=
    @g_vex x
  have p0001 :=
    @g_eluni1 (.cv x) (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A) p0000
  have p0002 :=
    @g_snex (.cv x)
  have p0003 :=
    @g_elimak y (syn_ccnvk (syn_ccompl (syn_cssetk))) A (syn_csn (.cv x)) (by exact (show y ∉ ((syn_ccnvk (syn_ccompl (syn_cssetk)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk]; exact (show y ∉ ((syn_ccompl (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl]; exact (show y ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show y ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))))) p0002
  have p0004 :=
    @g_bitri (.classMem (.cv x) (syn_cuni1 (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A))) (.classMem (syn_csn (.cv x)) (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A)) (syn_wrex y A (.classMem (syn_copk (.cv y) (syn_csn (.cv x))) (syn_ccnvk (syn_ccompl (syn_cssetk))))) p0001 p0003
  have p0005 :=
    @g_vex y
  have p0006 :=
    @g_opkelcnvk (.cv y) (syn_csn (.cv x)) (syn_ccompl (syn_cssetk)) p0005 p0002
  have p0007 :=
    @g_opkex (syn_csn (.cv x)) (.cv y)
  have p0008 :=
    @g_elcompl (syn_copk (syn_csn (.cv x)) (.cv y)) (syn_cssetk) p0007
  have p0009 :=
    @g_elssetk (.cv x) (.cv y) p0000 p0005
  have p0010_e00_recanon : Nominal.NPrf (syn_wb (.classMem (syn_copk (syn_csn (.cv x)) (.cv y)) (syn_cssetk)) (.objMem x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn syn_cssetk syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0009
  have p0010 :=
    @g_notbii (.classMem (syn_copk (syn_csn (.cv x)) (.cv y)) (syn_cssetk)) (.objMem x y) p0010_e00_recanon
  have p0011 :=
    @g_n_3bitri (.classMem (syn_copk (.cv y) (syn_csn (.cv x))) (syn_ccnvk (syn_ccompl (syn_cssetk)))) (.classMem (syn_copk (syn_csn (.cv x)) (.cv y)) (syn_ccompl (syn_cssetk))) (.neg (.classMem (syn_copk (syn_csn (.cv x)) (.cv y)) (syn_cssetk))) (.neg (.objMem x y)) p0006 p0008 p0010
  have p0012 :=
    @g_rexbii (.classMem (syn_copk (.cv y) (syn_csn (.cv x))) (syn_ccnvk (syn_ccompl (syn_cssetk)))) (.neg (.objMem x y)) y A p0011
  have p0013 :=
    @g_rexnal (.objMem x y) y A
  have p0014 :=
    @g_n_3bitri (.classMem (.cv x) (syn_cuni1 (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A))) (syn_wrex y A (.classMem (syn_copk (.cv y) (syn_csn (.cv x))) (syn_ccnvk (syn_ccompl (syn_cssetk))))) (syn_wrex y A (.neg (.objMem x y))) (.neg (syn_wral y A (.objMem x y))) p0004 p0012 p0013
  have p0015 :=
    @g_con2bii (.classMem (.cv x) (syn_cuni1 (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A))) (syn_wral y A (.objMem x y)) p0014
  have p0016 :=
    @g_elint2 y (.cv x) A (by exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) p0000
  have p0017 :=
    @g_elcompl (.cv x) (syn_cuni1 (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A)) p0000
  have p0018_e01_recanon : Nominal.NPrf (syn_wb (.classMem (.cv x) (syn_cint A)) (syn_wral y A (.objMem x y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cint syn_wral
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cint, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0016
  have p0018 :=
    @g_n_3bitr4i (syn_wral y A (.objMem x y)) (.neg (.classMem (.cv x) (syn_cuni1 (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A)))) (.classMem (.cv x) (syn_cint A)) (.classMem (.cv x) (syn_ccompl (syn_cuni1 (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A)))) p0015 p0018_e01_recanon p0017
  have p0019 :=
    @g_eqriv x (syn_cint A) (syn_ccompl (syn_cuni1 (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A))) (by exact (show x ∉ ((syn_cint A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cint]; exact (show x ∉ (A).fv from (by exact fresh_x_not_A))))) (by exact (show x ∉ ((syn_ccompl (syn_cuni1 (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl]; exact (show x ∉ ((syn_cuni1 (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni1]; exact (show x ∉ ((syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak]; exact (show x ∉ (((syn_ccnvk (syn_ccompl (syn_cssetk)))).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_ccnvk (syn_ccompl (syn_cssetk)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk]; exact (show x ∉ ((syn_ccompl (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl]; exact (show x ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show x ∉ (A).fv from (by exact fresh_x_not_A))))))))))) p0018
  exact p0019

noncomputable def g_intexg
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_cint A) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  have p0000 :=
    @g_dfint3 A
  have p0001 :=
    @g_ssetkex
  have p0002 :=
    @g_complex (syn_cssetk) p0001
  have p0003 :=
    @g_cnvkex (syn_ccompl (syn_cssetk)) p0002
  have p0004 :=
    @g_imakexg (syn_ccnvk (syn_ccompl (syn_cssetk))) A (syn_cvv) V
  have p0005 :=
    @g_mpan (.classMem (syn_ccnvk (syn_ccompl (syn_cssetk))) (syn_cvv)) (.classMem A V) (.classMem (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_uni1exg (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A) (syn_cvv)
  have p0007 :=
    @g_complexg (syn_cuni1 (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A)) (syn_cvv)
  have p0008 :=
    @g_n_3syl (.classMem A V) (.classMem (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A) (syn_cvv)) (.classMem (syn_cuni1 (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A)) (syn_cvv)) (.classMem (syn_ccompl (syn_cuni1 (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A))) (syn_cvv)) p0005 p0006 p0007
  have p0009 :=
    @g_syl5eqel (.classMem A V) (syn_cint A) (syn_ccompl (syn_cuni1 (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A))) (syn_cvv) p0000 p0008
  exact p0009

noncomputable def g_intex
    (A : Class) (hyp_intex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cint A) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_intexg A (syn_cvv)
  have p0001 :=
    Nominal.mp hyp_intex_1 p0000
  exact p0001

noncomputable def g_setswith
    (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.classEq (.cab x (.classMem A (.cv x))) (syn_cif (.classMem A (syn_cvv)) (syn_cimak (syn_cssetk) (syn_csn (syn_csn A))) (syn_c0))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_snex A
  have p0001 :=
    @g_opkeq1 (.cv y) (syn_csn A) (.cv x)
  have p0002 :=
    @g_eleq1d (.classEq (.cv y) (syn_csn A)) (syn_copk (.cv y) (.cv x)) (syn_copk (syn_csn A) (.cv x)) (syn_cssetk) p0001
  have p0003 :=
    @g_rexsn (.classMem (syn_copk (.cv y) (.cv x)) (syn_cssetk)) (.classMem (syn_copk (syn_csn A) (.cv x)) (syn_cssetk)) y (syn_csn A) (by exact (show y ∉ ((syn_csn A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ (A).fv from (by exact fresh_y_not_A))))) (by exact (show y ∉ ((Wff.classMem (syn_copk (syn_csn A) (.cv x)) (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((syn_copk (syn_csn A) (.cv x))).fv) ∪ (((syn_cssetk)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_copk (syn_csn A) (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show y ∉ (((syn_csn A)).fv) ∪ (((Class.cv x)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_csn A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))) (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))))))) (show y ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0000 p0002
  have p0004 :=
    @g_vex x
  have p0005 :=
    @g_elssetkg A (.cv x) (syn_cvv) (syn_cvv)
  have p0006 :=
    @g_mpan2 (.classMem A (syn_cvv)) (.classMem (.cv x) (syn_cvv)) (syn_wb (.classMem (syn_copk (syn_csn A) (.cv x)) (syn_cssetk)) (.classMem A (.cv x))) p0004 p0005
  have p0007 :=
    @g_syl5rbb (syn_wrex y (syn_csn (syn_csn A)) (.classMem (syn_copk (.cv y) (.cv x)) (syn_cssetk))) (.classMem (syn_copk (syn_csn A) (.cv x)) (syn_cssetk)) (.classMem A (syn_cvv)) (.classMem A (.cv x)) p0003 p0006
  have p0008 :=
    @g_abbidv (.classMem A (syn_cvv)) (.classMem A (.cv x)) (syn_wrex y (syn_csn (syn_csn A)) (.classMem (syn_copk (.cv y) (.cv x)) (syn_cssetk))) x (by exact (show x ∉ ((Wff.classMem A (syn_cvv))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ ((A).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact dv_A_x)) (show x ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0007
  have p0009 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_imak x y (syn_cssetk) (syn_csn (syn_csn A)) (by exact (show x ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show y ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show x ∉ ((syn_csn (syn_csn A))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ ((syn_csn A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ (A).fv from (by exact dv_A_x))))))) (by exact (show y ∉ ((syn_csn (syn_csn A))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ (A).fv from (by exact fresh_y_not_A))))))) (show x ≠ y from (by exact fresh_x_ne_y))
  have p0010 :=
    @g_syl6eqr (.classMem A (syn_cvv)) (.cab x (.classMem A (.cv x))) (.cab x (syn_wrex y (syn_csn (syn_csn A)) (.classMem (syn_copk (.cv y) (.cv x)) (syn_cssetk)))) (syn_cimak (syn_cssetk) (syn_csn (syn_csn A))) p0008 p0009
  have p0011 :=
    @g_iftrue (.classMem A (syn_cvv)) (syn_cimak (syn_cssetk) (syn_csn (syn_csn A))) (syn_c0)
  have p0012 :=
    @g_eqtr4d (.classMem A (syn_cvv)) (.cab x (.classMem A (.cv x))) (syn_cimak (syn_cssetk) (syn_csn (syn_csn A))) (syn_cif (.classMem A (syn_cvv)) (syn_cimak (syn_cssetk) (syn_csn (syn_csn A))) (syn_c0)) p0010 p0011
  have p0013 :=
    @g_elex A (.cv x)
  have p0014 :=
    @g_con3i (.classMem A (.cv x)) (.classMem A (syn_cvv)) p0013
  have p0015 :=
    @g_alrimiv (.neg (.classMem A (syn_cvv))) (.neg (.classMem A (.cv x))) x (by exact (show x ∉ ((Wff.neg (.classMem A (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_neg]; exact (show x ∉ ((Wff.classMem A (syn_cvv))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ ((A).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact dv_A_x)) (show x ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))) p0014
  have p0016 :=
    @g_ab0 (.classMem A (.cv x)) x
  have p0017 :=
    @g_sylibr (.neg (.classMem A (syn_cvv))) (.all x (.neg (.classMem A (.cv x)))) (.classEq (.cab x (.classMem A (.cv x))) (syn_c0)) p0015 p0016
  have p0018 :=
    @g_iffalse (.classMem A (syn_cvv)) (syn_cimak (syn_cssetk) (syn_csn (syn_csn A))) (syn_c0)
  have p0019 :=
    @g_eqtr4d (.neg (.classMem A (syn_cvv))) (.cab x (.classMem A (.cv x))) (syn_c0) (syn_cif (.classMem A (syn_cvv)) (syn_cimak (syn_cssetk) (syn_csn (syn_csn A))) (syn_c0)) p0017 p0018
  have p0020 :=
    @g_pm2_61i (.classMem A (syn_cvv)) (.classEq (.cab x (.classMem A (.cv x))) (syn_cif (.classMem A (syn_cvv)) (syn_cimak (syn_cssetk) (syn_csn (syn_csn A))) (syn_c0))) p0012 p0019
  exact p0020

noncomputable def g_setswithex
    (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.classMem (.cab x (.classMem A (.cv x))) (syn_cvv)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv
  have p0000 :=
    @g_setswith x A (by exact (show x ∉ (A).fv from (by exact dv_A_x)))
  have p0001 :=
    @g_ssetkex
  have p0002 :=
    @g_snex (syn_csn A)
  have p0003 :=
    @g_imakex (syn_cssetk) (syn_csn (syn_csn A)) p0001 p0002
  have p0004 :=
    @g_n_0ex
  have p0005 :=
    @g_ifex (.classMem A (syn_cvv)) (syn_cimak (syn_cssetk) (syn_csn (syn_csn A))) (syn_c0) p0003 p0004
  have p0006 :=
    @g_eqeltri (.cab x (.classMem A (.cv x))) (syn_cif (.classMem A (syn_cvv)) (syn_cimak (syn_cssetk) (syn_csn (syn_csn A))) (syn_c0)) (syn_cvv) p0000 p0005
  exact p0006

noncomputable def g_ndisjrelk
    (A : Class) (B : Class) (hyp_ndisjrelk_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_ndisjrelk_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem (syn_copk A B) (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_wne (syn_cin A B) (syn_c0))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let t : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (h))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_t_ne_x : t ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_t : x ≠ t :=
    Ne.symm fresh_t_ne_x
  have p0000 :=
    @g_snex (syn_csn (syn_csn (.cv x)))
  have p0001 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B)
  have p0002 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_copk (.cv t) (syn_copk A B)) (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) p0001
  have p0003 :=
    @g_ceqsexv (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))) t (syn_csn (syn_csn (syn_csn (.cv x)))) (by exact (show t ∉ ((syn_csn (syn_csn (syn_csn (.cv x))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((syn_csn (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ x from (by exact fresh_t_ne_x))))))))))))) (by exact (show t ∉ ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show t ∉ (((syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B))).fv) ∪ (((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show t ∉ (((syn_csn (syn_csn (syn_csn (.cv x))))).fv) ∪ (((syn_copk A B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_csn (syn_csn (syn_csn (.cv x))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((syn_csn (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ x from (by exact fresh_t_ne_x)))))))))))) (show t ∉ ((syn_copk A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show t ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ (A).fv from (by exact fresh_t_not_A)) (show t ∉ (B).fv from (by exact fresh_t_not_B)))))))))) (show t ∉ ((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show t ∉ (((syn_cins3k (syn_cssetk))).fv) ∪ (((syn_cins2k (syn_cssetk))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_cins3k (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k]; exact (show t ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))) (show t ∉ ((syn_cins2k (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k]; exact (show t ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))))) p0000 p0002
  have p0004 :=
    @g_elin (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B)) (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))
  have p0005 :=
    @g_snex (.cv x)
  have p0006 :=
    @g_otkelins3k (syn_csn (.cv x)) A B (syn_cssetk) p0005 hyp_ndisjrelk_1 hyp_ndisjrelk_2
  have p0007 :=
    @g_vex x
  have p0008 :=
    @g_elssetk (.cv x) A p0007 hyp_ndisjrelk_1
  have p0009 :=
    @g_bitri (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B)) (syn_cins3k (syn_cssetk))) (.classMem (syn_copk (syn_csn (.cv x)) A) (syn_cssetk)) (.classMem (.cv x) A) p0006 p0008
  have p0010 :=
    @g_otkelins2k (syn_csn (.cv x)) A B (syn_cssetk) p0005 hyp_ndisjrelk_1 hyp_ndisjrelk_2
  have p0011 :=
    @g_elssetk (.cv x) B p0007 hyp_ndisjrelk_2
  have p0012 :=
    @g_bitri (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B)) (syn_cins2k (syn_cssetk))) (.classMem (syn_copk (syn_csn (.cv x)) B) (syn_cssetk)) (.classMem (.cv x) B) p0010 p0011
  have p0013 :=
    @g_anbi12i (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B)) (syn_cins3k (syn_cssetk))) (.classMem (.cv x) A) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B)) (syn_cins2k (syn_cssetk))) (.classMem (.cv x) B) p0009 p0012
  have p0014 :=
    @g_bitri (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))) (syn_wa (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B)) (syn_cins3k (syn_cssetk))) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B)) (syn_cins2k (syn_cssetk)))) (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)) p0004 p0013
  have p0015 :=
    @g_bitri (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))) (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))))) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))) (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)) p0003 p0014
  have p0016 :=
    @g_exbii (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))) (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))))) (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)) x p0015
  have p0017 :=
    @g_opkex A B
  have p0018 :=
    @g_elimak t (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))) (syn_copk A B) (by exact (show t ∉ ((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show t ∉ (((syn_cins3k (syn_cssetk))).fv) ∪ (((syn_cins2k (syn_cssetk))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_cins3k (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k]; exact (show t ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))) (show t ∉ ((syn_cins2k (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k]; exact (show t ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))) (by exact (show t ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show t ∉ ((syn_cpw1 (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show t ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) (by exact (show t ∉ ((syn_copk A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show t ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ (A).fv from (by exact fresh_t_not_A)) (show t ∉ (B).fv from (by exact fresh_t_not_B))))))) p0017
  have p0019 :=
    @g_elpw121c x (.cv t) (by exact (show x ∉ ((Class.cv t)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({t} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ t from (by exact fresh_x_ne_t)))))))
  have p0020 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))) (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))) p0019
  have p0021 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))) (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))) x (by exact (show x ∉ ((Wff.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((syn_copk (.cv t) (syn_copk A B))).fv) ∪ (((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_copk (.cv t) (syn_copk A B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show x ∉ (((Class.cv t)).fv) ∪ (((syn_copk A B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv t)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({t} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ t from (by exact fresh_x_ne_t)))))) (show x ∉ ((syn_copk A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show x ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ (B).fv from (by exact fresh_x_not_B)))))))))) (show x ∉ ((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show x ∉ (((syn_cins3k (syn_cssetk))).fv) ∪ (((syn_cins2k (syn_cssetk))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cins3k (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k]; exact (show x ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))) (show x ∉ ((syn_cins2k (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k]; exact (show x ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))))
  have p0022 :=
    @g_bitr4i (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))))) (syn_wa (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))) (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))))) (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))) (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))))) p0020 p0021
  have p0023 :=
    @g_exbii (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))))) (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))) (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))))) t p0022
  have p0024 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c))) (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))))))
  have p0025 :=
    @g_excom (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))) (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))))) x t
  have p0026 :=
    @g_n_3bitr4i (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))))) (syn_wex t (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))) (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))))))) (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c))) (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))))) (syn_wex x (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))) (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))))))) p0023 p0024 p0025
  have p0027 :=
    @g_bitri (.classMem (syn_copk A B) (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c))) (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))))) (syn_wex x (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))) (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))))))) p0018 p0026
  have p0028 :=
    @g_n0 x (syn_cin A B) (by exact (show x ∉ ((syn_cin A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show x ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ (B).fv from (by exact fresh_x_not_B)))))))
  have p0029 :=
    @g_elin (.cv x) A B
  have p0030 :=
    @g_exbii (.classMem (.cv x) (syn_cin A B)) (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)) x p0029
  have p0031 :=
    @g_bitri (syn_wne (syn_cin A B) (syn_c0)) (syn_wex x (.classMem (.cv x) (syn_cin A B))) (syn_wex x (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B))) p0028 p0030
  have p0032 :=
    @g_n_3bitr4i (syn_wex x (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))) (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))))))) (syn_wex x (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B))) (.classMem (syn_copk A B) (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_wne (syn_cin A B) (syn_c0)) p0016 p0027 p0031
  exact p0032

noncomputable def g_abexv
    (ph : Wff) (x : Var) (dv_ph_x : x ∉ ph.fv) :
    Nominal.NPrf (.classMem (.cab x ph) (syn_cvv)) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var)
  have p0000 :=
    @g_abvor0 ph x (by exact (show x ∉ (ph).fv from (by exact dv_ph_x)))
  have p0001 :=
    @g_vvex
  have p0002 :=
    @g_eleq1 (.cab x ph) (syn_cvv) (syn_cvv)
  have p0003 :=
    @g_mpbiri (.classEq (.cab x ph) (syn_cvv)) (.classMem (.cab x ph) (syn_cvv)) (.classMem (syn_cvv) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_n_0ex
  have p0005 :=
    @g_eleq1 (.cab x ph) (syn_c0) (syn_cvv)
  have p0006 :=
    @g_mpbiri (.classEq (.cab x ph) (syn_c0)) (.classMem (.cab x ph) (syn_cvv)) (.classMem (syn_c0) (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_jaoi (.classEq (.cab x ph) (syn_cvv)) (.classMem (.cab x ph) (syn_cvv)) (.classEq (.cab x ph) (syn_c0)) p0003 p0006
  have p0008 :=
    Nominal.mp p0000 p0007
  exact p0008

noncomputable def g_unipw1
    (A : Class) :
    Nominal.NPrf (.classEq (syn_cuni (syn_cpw1 A)) A) := by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
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
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
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
    @g_eluni y (.cv x) (syn_cpw1 A) (by exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))) (by exact (show y ∉ ((syn_cpw1 A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))))
  have p0001 :=
    @g_elpw1 z (.cv y) A (by exact (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y))))))) (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
  have p0002 :=
    @g_anbi1i (.classMem (.cv y) (syn_cpw1 A)) (syn_wrex z A (.classEq (.cv y) (syn_csn (.cv z)))) (.objMem x y) p0001
  have p0003 :=
    @g_ancom (.objMem x y) (.classMem (.cv y) (syn_cpw1 A))
  have p0004 :=
    @g_r19_41v (.classEq (.cv y) (syn_csn (.cv z))) (.objMem x y) z A (by exact (show z ∉ ((Wff.objMem x y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show z ∉ ({x, y} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show z ≠ x from (by exact fresh_z_ne_x)), (show z ≠ y from (by exact fresh_z_ne_y))⟩)))))
  have p0005 :=
    @g_n_3bitr4i (syn_wa (.classMem (.cv y) (syn_cpw1 A)) (.objMem x y)) (syn_wa (syn_wrex z A (.classEq (.cv y) (syn_csn (.cv z)))) (.objMem x y)) (syn_wa (.objMem x y) (.classMem (.cv y) (syn_cpw1 A))) (syn_wrex z A (syn_wa (.classEq (.cv y) (syn_csn (.cv z))) (.objMem x y))) p0002 p0003 p0004
  have p0006 :=
    @g_exbii (syn_wa (.objMem x y) (.classMem (.cv y) (syn_cpw1 A))) (syn_wrex z A (syn_wa (.classEq (.cv y) (syn_csn (.cv z))) (.objMem x y))) y p0005
  have p0007 :=
    @g_risset z (.cv x) A (by exact (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x))))))) (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
  have p0008 :=
    @g_snex (.cv z)
  have p0009 :=
    @g_eleq2 (.cv y) (syn_csn (.cv z)) (.cv x)
  have p0010_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv y) (syn_csn (.cv z))) (syn_wb (.objMem x y) (.classMem (.cv x) (syn_csn (.cv z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_csn syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
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
      )
      p0009
  have p0010 :=
    @g_ceqsexv (.objMem x y) (.classMem (.cv x) (syn_csn (.cv z))) y (syn_csn (.cv z)) (by exact (show y ∉ ((syn_csn (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ z from (by exact fresh_y_ne_z))))))))) (by exact (show y ∉ ((Wff.classMem (.cv x) (syn_csn (.cv z)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((Class.cv x)).fv) ∪ (((syn_csn (.cv z))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))) (show y ∉ ((syn_csn (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ z from (by exact fresh_y_ne_z))))))))))))) p0008 p0010_e01_recanon
  have p0011 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sn x (.cv z) (by exact (show x ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ z from (by exact fresh_x_ne_z)))))))
  have p0012_e00_recanon : Nominal.NPrf (.classEq (syn_csn (.cv z)) (.cab x (.objEq x z))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.classEq
        ·
          exact Nominal.RecanonTransportDev.TRecanonClass.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonClass.cab
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0011
  have p0012 :=
    @g_eqabri (.objEq x z) x (syn_csn (.cv z)) p0012_e00_recanon
  have p0013 :=
    @g_equcom x z
  have p0014 :=
    @g_n_3bitri (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (.cv z))) (.objMem x y))) (.classMem (.cv x) (syn_csn (.cv z))) (.objEq x z) (.objEq z x) p0010 p0012 p0013
  have p0015 :=
    @g_rexbii (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (.cv z))) (.objMem x y))) (.objEq z x) z A p0014
  have p0016 :=
    @g_rexcom4 (syn_wa (.classEq (.cv y) (syn_csn (.cv z))) (.objMem x y)) z y A (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (show z ≠ y from (by exact fresh_z_ne_y))
  have p0017_e00_recanon : Nominal.NPrf (syn_wb (.classMem (.cv x) A) (syn_wrex z A (.objEq z x))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wrex syn_wex syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0007
  have p0017 :=
    @g_n_3bitr2ri (.classMem (.cv x) A) (syn_wrex z A (.objEq z x)) (syn_wrex z A (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (.cv z))) (.objMem x y)))) (syn_wex y (syn_wrex z A (syn_wa (.classEq (.cv y) (syn_csn (.cv z))) (.objMem x y)))) p0017_e00_recanon p0015 p0016
  have p0018_e00_recanon : Nominal.NPrf (syn_wb (.classMem (.cv x) (syn_cuni (syn_cpw1 A))) (syn_wex y (syn_wa (.objMem x y) (.classMem (.cv y) (syn_cpw1 A))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cuni syn_wex syn_wa syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_cpw syn_wss syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0000
  have p0018 :=
    @g_n_3bitri (.classMem (.cv x) (syn_cuni (syn_cpw1 A))) (syn_wex y (syn_wa (.objMem x y) (.classMem (.cv y) (syn_cpw1 A)))) (syn_wex y (syn_wrex z A (syn_wa (.classEq (.cv y) (syn_csn (.cv z))) (.objMem x y)))) (.classMem (.cv x) A) p0018_e00_recanon p0006 p0017
  have p0019 :=
    @g_eqriv x (syn_cuni (syn_cpw1 A)) A (by exact (show x ∉ ((syn_cuni (syn_cpw1 A))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show x ∉ ((syn_cpw1 A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show x ∉ (A).fv from (by exact fresh_x_not_A))))))) (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) p0018
  exact p0019

noncomputable def g_pw1exb
    (A : Class) :
    Nominal.NPrf (syn_wb (.classMem (syn_cpw1 A) (syn_cvv)) (.classMem A (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_unipw1 A
  have p0001 :=
    @g_uniexg (syn_cpw1 A) (syn_cvv)
  have p0002 :=
    @g_syl5eqelr (.classMem (syn_cpw1 A) (syn_cvv)) A (syn_cuni (syn_cpw1 A)) (syn_cvv) p0000 p0001
  have p0003 :=
    @g_pw1exg A (syn_cvv)
  have p0004 :=
    @g_impbii (.classMem (syn_cpw1 A) (syn_cvv)) (.classMem A (syn_cvv)) p0002 p0003
  exact p0004



#print axioms g_pw1exb

end NFChoice.DirectNominalPrf.WPPReplay
