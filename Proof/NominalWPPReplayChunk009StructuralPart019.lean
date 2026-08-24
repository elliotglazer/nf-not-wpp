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
import NominalWPPReplayChunk009StructuralPart018


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

noncomputable def g_dfpw2
    (A : Class) :
    Nominal.NPrf (.classEq (syn_cpw A) (syn_ccompl (syn_cimak (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (syn_c1c)))) := by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let t : Var := freshVar proofSupport 2
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
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (h)
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_t : x ≠ t := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_t_ne_x : t ≠ x :=
    Ne.symm fresh_x_ne_t
  have fresh_y_ne_t : y ≠ t := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_t_ne_y : t ≠ y :=
    Ne.symm fresh_y_ne_t
  have p0000 :=
    @g_vex x
  have p0001 :=
    @g_elimak t (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (syn_c1c) (.cv x) (by exact (show t ∉ ((syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif]; exact (show t ∉ (((syn_cssetk)).fv) ∪ (((syn_cxpk (syn_cpw1 A) (syn_cvv))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show t ∉ ((syn_cxpk (syn_cpw1 A) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show t ∉ (((syn_cpw1 A)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_cpw1 A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show t ∉ (A).fv from (by exact fresh_t_not_A)))) (show t ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (by exact (show t ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show t ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ x from (by exact fresh_t_ne_x))))))) p0000
  have p0002 :=
    @g_el1c y (.cv t) (by exact (show y ∉ ((Class.cv t)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({t} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ t from (by exact fresh_y_ne_t)))))))
  have p0003 :=
    @g_anbi1i (.classMem (.cv t) (syn_c1c)) (syn_wex y (.classEq (.cv t) (syn_csn (.cv y)))) (.classMem (syn_copk (.cv t) (.cv x)) (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv)))) p0002
  have p0004 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (.cv y))) (.classMem (syn_copk (.cv t) (.cv x)) (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv)))) y (by exact (show y ∉ ((Wff.classMem (syn_copk (.cv t) (.cv x)) (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((syn_copk (.cv t) (.cv x))).fv) ∪ (((syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_copk (.cv t) (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show y ∉ (((Class.cv t)).fv) ∪ (((Class.cv x)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv t)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({t} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ t from (by exact fresh_y_ne_t)))))) (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))))))) (show y ∉ ((syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif]; exact (show y ∉ (((syn_cssetk)).fv) ∪ (((syn_cxpk (syn_cpw1 A) (syn_cvv))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show y ∉ ((syn_cxpk (syn_cpw1 A) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show y ∉ (((syn_cpw1 A)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cpw1 A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))) (show y ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))))))
  have p0005 :=
    @g_bitr4i (syn_wa (.classMem (.cv t) (syn_c1c)) (.classMem (syn_copk (.cv t) (.cv x)) (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))))) (syn_wa (syn_wex y (.classEq (.cv t) (syn_csn (.cv y)))) (.classMem (syn_copk (.cv t) (.cv x)) (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))))) (syn_wex y (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) (.classMem (syn_copk (.cv t) (.cv x)) (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv)))))) p0003 p0004
  have p0006 :=
    @g_exbii (syn_wa (.classMem (.cv t) (syn_c1c)) (.classMem (syn_copk (.cv t) (.cv x)) (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))))) (syn_wex y (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) (.classMem (syn_copk (.cv t) (.cv x)) (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv)))))) t p0005
  have p0007 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex t (syn_c1c) (.classMem (syn_copk (.cv t) (.cv x)) (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv)))))))
  have p0008 :=
    @g_excom (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) (.classMem (syn_copk (.cv t) (.cv x)) (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))))) y t
  have p0009 :=
    @g_n_3bitr4i (syn_wex t (syn_wa (.classMem (.cv t) (syn_c1c)) (.classMem (syn_copk (.cv t) (.cv x)) (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv)))))) (syn_wex t (syn_wex y (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) (.classMem (syn_copk (.cv t) (.cv x)) (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))))))) (syn_wrex t (syn_c1c) (.classMem (syn_copk (.cv t) (.cv x)) (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))))) (syn_wex y (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) (.classMem (syn_copk (.cv t) (.cv x)) (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))))))) p0006 p0007 p0008
  have p0010 :=
    @g_bitri (.classMem (.cv x) (syn_cimak (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (syn_c1c))) (syn_wrex t (syn_c1c) (.classMem (syn_copk (.cv t) (.cv x)) (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))))) (syn_wex y (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) (.classMem (syn_copk (.cv t) (.cv x)) (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))))))) p0001 p0009
  have p0011 :=
    @g_snex (.cv y)
  have p0012 :=
    @g_opkeq1 (.cv t) (syn_csn (.cv y)) (.cv x)
  have p0013 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (.cv y))) (syn_copk (.cv t) (.cv x)) (syn_copk (syn_csn (.cv y)) (.cv x)) (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) p0012
  have p0014 :=
    @g_ceqsexv (.classMem (syn_copk (.cv t) (.cv x)) (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv)))) (.classMem (syn_copk (syn_csn (.cv y)) (.cv x)) (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv)))) t (syn_csn (.cv y)) (by exact (show t ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ y from (by exact fresh_t_ne_y))))))))) (by exact (show t ∉ ((Wff.classMem (syn_copk (syn_csn (.cv y)) (.cv x)) (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show t ∉ (((syn_copk (syn_csn (.cv y)) (.cv x))).fv) ∪ (((syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_copk (syn_csn (.cv y)) (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show t ∉ (((syn_csn (.cv y))).fv) ∪ (((Class.cv x)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ y from (by exact fresh_t_ne_y)))))))) (show t ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ x from (by exact fresh_t_ne_x)))))))))) (show t ∉ ((syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif]; exact (show t ∉ (((syn_cssetk)).fv) ∪ (((syn_cxpk (syn_cpw1 A) (syn_cvv))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show t ∉ ((syn_cxpk (syn_cpw1 A) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show t ∉ (((syn_cpw1 A)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_cpw1 A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show t ∉ (A).fv from (by exact fresh_t_not_A)))) (show t ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))))))) p0011 p0013
  have p0015 :=
    @g_eldif (syn_copk (syn_csn (.cv y)) (.cv x)) (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))
  have p0016 :=
    @g_vex y
  have p0017 :=
    @g_elssetk (.cv y) (.cv x) p0016 p0000
  have p0018 :=
    @g_opkelxpk (syn_csn (.cv y)) (.cv x) (syn_cpw1 A) (syn_cvv) p0011 p0000
  have p0019 :=
    @g_mpbiran2 (.classMem (syn_copk (syn_csn (.cv y)) (.cv x)) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (.classMem (syn_csn (.cv y)) (syn_cpw1 A)) (.classMem (.cv x) (syn_cvv)) p0000 p0018
  have p0020 :=
    @g_snelpw1 (.cv y) A
  have p0021 :=
    @g_bitri (.classMem (syn_copk (syn_csn (.cv y)) (.cv x)) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (.classMem (syn_csn (.cv y)) (syn_cpw1 A)) (.classMem (.cv y) A) p0019 p0020
  have p0022 :=
    @g_notbii (.classMem (syn_copk (syn_csn (.cv y)) (.cv x)) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (.classMem (.cv y) A) p0021
  have p0023_e00_recanon : Nominal.NPrf (syn_wb (.classMem (syn_copk (syn_csn (.cv y)) (.cv x)) (syn_cssetk)) (.objMem y x)) :=
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
      p0017
  have p0023 :=
    @g_anbi12i (.classMem (syn_copk (syn_csn (.cv y)) (.cv x)) (syn_cssetk)) (.objMem y x) (.neg (.classMem (syn_copk (syn_csn (.cv y)) (.cv x)) (syn_cxpk (syn_cpw1 A) (syn_cvv)))) (.neg (.classMem (.cv y) A)) p0023_e00_recanon p0022
  have p0024 :=
    @g_annim (.objMem y x) (.classMem (.cv y) A)
  have p0025 :=
    @g_n_3bitri (.classMem (syn_copk (syn_csn (.cv y)) (.cv x)) (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv)))) (syn_wa (.classMem (syn_copk (syn_csn (.cv y)) (.cv x)) (syn_cssetk)) (.neg (.classMem (syn_copk (syn_csn (.cv y)) (.cv x)) (syn_cxpk (syn_cpw1 A) (syn_cvv))))) (syn_wa (.objMem y x) (.neg (.classMem (.cv y) A))) (.neg (.imp (.objMem y x) (.classMem (.cv y) A))) p0015 p0023 p0024
  have p0026 :=
    @g_bitri (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) (.classMem (syn_copk (.cv t) (.cv x)) (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv)))))) (.classMem (syn_copk (syn_csn (.cv y)) (.cv x)) (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv)))) (.neg (.imp (.objMem y x) (.classMem (.cv y) A))) p0014 p0025
  have p0027 :=
    @g_exbii (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) (.classMem (syn_copk (.cv t) (.cv x)) (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv)))))) (.neg (.imp (.objMem y x) (.classMem (.cv y) A))) y p0026
  have p0028 :=
    @g_exnal (.imp (.objMem y x) (.classMem (.cv y) A)) y
  have p0029 :=
    @g_n_3bitri (.classMem (.cv x) (syn_cimak (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (syn_c1c))) (syn_wex y (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) (.classMem (syn_copk (.cv t) (.cv x)) (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))))))) (syn_wex y (.neg (.imp (.objMem y x) (.classMem (.cv y) A)))) (.neg (.all y (.imp (.objMem y x) (.classMem (.cv y) A)))) p0010 p0027 p0028
  have p0030 :=
    @g_con2bii (.classMem (.cv x) (syn_cimak (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (syn_c1c))) (.all y (.imp (.objMem y x) (.classMem (.cv y) A))) p0029
  have p0031 :=
    @g_elpw (.cv x) A p0000
  have p0032 :=
    @g_dfss2 y (.cv x) A (by exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
  have p0033_e01_recanon : Nominal.NPrf (syn_wb (syn_wss (.cv x) A) (.all y (.imp (.objMem y x) (.classMem (.cv y) A)))) :=
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
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0032
  have p0033 :=
    @g_bitri (.classMem (.cv x) (syn_cpw A)) (syn_wss (.cv x) A) (.all y (.imp (.objMem y x) (.classMem (.cv y) A))) p0031 p0033_e01_recanon
  have p0034 :=
    @g_elcompl (.cv x) (syn_cimak (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (syn_c1c)) p0000
  have p0035 :=
    @g_n_3bitr4i (.all y (.imp (.objMem y x) (.classMem (.cv y) A))) (.neg (.classMem (.cv x) (syn_cimak (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (syn_c1c)))) (.classMem (.cv x) (syn_cpw A)) (.classMem (.cv x) (syn_ccompl (syn_cimak (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (syn_c1c)))) p0030 p0033 p0034
  have p0036 :=
    @g_eqriv x (syn_cpw A) (syn_ccompl (syn_cimak (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (syn_c1c))) (by exact (show x ∉ ((syn_cpw A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw]; exact (show x ∉ (A).fv from (by exact fresh_x_not_A))))) (by exact (show x ∉ ((syn_ccompl (syn_cimak (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl]; exact (show x ∉ ((syn_cimak (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak]; exact (show x ∉ (((syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv)))).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif]; exact (show x ∉ (((syn_cssetk)).fv) ∪ (((syn_cxpk (syn_cpw1 A) (syn_cvv))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show x ∉ ((syn_cxpk (syn_cpw1 A) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show x ∉ (((syn_cpw1 A)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cpw1 A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))) (show x ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (show x ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))) p0035
  exact p0036

noncomputable def g_pwexg
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_cpw A) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  have p0000 :=
    @g_dfpw2 A
  have p0001 :=
    @g_ssetkex
  have p0002 :=
    @g_pw1exg A V
  have p0003 :=
    @g_vvex
  have p0004 :=
    @g_xpkexg (syn_cpw1 A) (syn_cvv) (syn_cvv) (syn_cvv)
  have p0005 :=
    @g_sylancl (.classMem A V) (.classMem (syn_cpw1 A) (syn_cvv)) (.classMem (syn_cvv) (syn_cvv)) (.classMem (syn_cxpk (syn_cpw1 A) (syn_cvv)) (syn_cvv)) p0002 p0003 p0004
  have p0006 :=
    @g_difexg (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv)) (syn_cvv) (syn_cvv)
  have p0007 :=
    @g_sylancr (.classMem A V) (.classMem (syn_cssetk) (syn_cvv)) (.classMem (syn_cxpk (syn_cpw1 A) (syn_cvv)) (syn_cvv)) (.classMem (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (syn_cvv)) p0001 p0005 p0006
  have p0008 :=
    @g_n_1cex
  have p0009 :=
    @g_imakexg (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (syn_c1c) (syn_cvv) (syn_cvv)
  have p0010 :=
    @g_sylancl (.classMem A V) (.classMem (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (syn_cvv)) (.classMem (syn_c1c) (syn_cvv)) (.classMem (syn_cimak (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (syn_c1c)) (syn_cvv)) p0007 p0008 p0009
  have p0011 :=
    @g_complexg (syn_cimak (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (syn_c1c)) (syn_cvv)
  have p0012 :=
    @g_syl (.classMem A V) (.classMem (syn_cimak (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (syn_c1c)) (syn_cvv)) (.classMem (syn_ccompl (syn_cimak (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (syn_c1c))) (syn_cvv)) p0010 p0011
  have p0013 :=
    @g_syl5eqel (.classMem A V) (syn_cpw A) (syn_ccompl (syn_cimak (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (syn_c1c))) (syn_cvv) p0000 p0012
  exact p0013

noncomputable def g_pwex
    (A : Class) (hyp_pwex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cpw A) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_pwexg A (syn_cvv)
  have p0001 :=
    Nominal.mp hyp_pwex_1 p0000
  exact p0001

noncomputable def g_eqpw1uni
    (A : Class) :
    Nominal.NPrf (.imp (syn_wss A (syn_c1c)) (.classEq A (syn_cpw1 (syn_cuni A)))) := by
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
    @g_ssel A (syn_c1c) (.cv x)
  have p0001 :=
    @g_pw1ss1c (syn_cuni A)
  have p0002 :=
    @g_sseli (syn_cpw1 (syn_cuni A)) (syn_c1c) (.cv x) p0001
  have p0003 :=
    @g_a1i (.imp (.classMem (.cv x) (syn_cpw1 (syn_cuni A))) (.classMem (.cv x) (syn_c1c))) (syn_wss A (syn_c1c)) p0002
  have p0004 :=
    @g_el1c y (.cv x) (by exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))))
  have p0005 :=
    @g_vex y
  have p0006 :=
    @g_snid (.cv y) p0005
  have p0007 :=
    @g_eleq2 (.cv x) (syn_csn (.cv y)) (.cv y)
  have p0008_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv x) (syn_csn (.cv y))) (syn_wb (.objMem y x) (.classMem (.cv y) (syn_csn (.cv y))))) :=
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
      p0007
  have p0008 :=
    @g_rspcev (.objMem y x) (.classMem (.cv y) (syn_csn (.cv y))) x (syn_csn (.cv y)) A (by exact (show x ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y))))))))) (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show x ∉ ((Wff.classMem (.cv y) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((Class.cv y)).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y)))))) (show x ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y))))))))))))) p0008_e00_recanon
  have p0009 :=
    @g_mpan2 (.classMem (syn_csn (.cv y)) A) (.classMem (.cv y) (syn_csn (.cv y))) (syn_wrex x A (.objMem y x)) p0006 p0008
  have p0010 :=
    @g_el1c z (.cv x) (by exact (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))))
  have p0011 :=
    @g_elsn y (.cv z) (by exact (show y ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ z from (by exact fresh_y_ne_z)))))))
  have p0012 :=
    @g_sneq (.cv y) (.cv z)
  have p0013_e00_recanon : Nominal.NPrf (.imp (.objEq y z) (.classEq (syn_csn (.cv y)) (syn_csn (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0012
  have p0013 :=
    @g_eleq1d (.objEq y z) (syn_csn (.cv y)) (syn_csn (.cv z)) A p0013_e00_recanon
  have p0014_e00_recanon : Nominal.NPrf (syn_wb (.classMem (.cv y) (syn_csn (.cv z))) (.objEq y z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0011
  have p0014 :=
    @g_sylbi (.classMem (.cv y) (syn_csn (.cv z))) (.objEq y z) (syn_wb (.classMem (syn_csn (.cv y)) A) (.classMem (syn_csn (.cv z)) A)) p0014_e00_recanon p0013
  have p0015 :=
    @g_biimprcd (.classMem (.cv y) (syn_csn (.cv z))) (.classMem (syn_csn (.cv y)) A) (.classMem (syn_csn (.cv z)) A) p0014
  have p0016 :=
    @g_eleq1 (.cv x) (syn_csn (.cv z)) A
  have p0017 :=
    @g_eleq2 (.cv x) (syn_csn (.cv z)) (.cv y)
  have p0018_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv x) (syn_csn (.cv z))) (syn_wb (.objMem y x) (.classMem (.cv y) (syn_csn (.cv z))))) :=
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
      p0017
  have p0018 :=
    @g_imbi1d (.classEq (.cv x) (syn_csn (.cv z))) (.objMem y x) (.classMem (.cv y) (syn_csn (.cv z))) (.classMem (syn_csn (.cv y)) A) p0018_e00_recanon
  have p0019 :=
    @g_imbi12d (.classEq (.cv x) (syn_csn (.cv z))) (.classMem (.cv x) A) (.classMem (syn_csn (.cv z)) A) (.imp (.objMem y x) (.classMem (syn_csn (.cv y)) A)) (.imp (.classMem (.cv y) (syn_csn (.cv z))) (.classMem (syn_csn (.cv y)) A)) p0016 p0018
  have p0020 :=
    @g_mpbiri (.classEq (.cv x) (syn_csn (.cv z))) (.imp (.classMem (.cv x) A) (.imp (.objMem y x) (.classMem (syn_csn (.cv y)) A))) (.imp (.classMem (syn_csn (.cv z)) A) (.imp (.classMem (.cv y) (syn_csn (.cv z))) (.classMem (syn_csn (.cv y)) A))) p0015 p0019
  have p0021 :=
    @g_exlimiv (.classEq (.cv x) (syn_csn (.cv z))) (.imp (.classMem (.cv x) A) (.imp (.objMem y x) (.classMem (syn_csn (.cv y)) A))) z (by exact (show z ∉ ((Wff.imp (.classMem (.cv x) A) (.imp (.objMem y x) (.classMem (syn_csn (.cv y)) A)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show z ∉ (((Wff.classMem (.cv x) A)).fv) ∪ (((Wff.imp (.objMem y x) (.classMem (syn_csn (.cv y)) A))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Wff.classMem (.cv x) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show z ∉ (((Class.cv x)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))) (show z ∉ (A).fv from (by exact fresh_z_not_A)))))) (show z ∉ ((Wff.imp (.objMem y x) (.classMem (syn_csn (.cv y)) A))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show z ∉ (((Wff.objMem y x)).fv) ∪ (((Wff.classMem (syn_csn (.cv y)) A)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Wff.objMem y x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show z ∉ ({y, x} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show z ≠ y from (by exact fresh_z_ne_y)), (show z ≠ x from (by exact fresh_z_ne_x))⟩)))) (show z ∉ ((Wff.classMem (syn_csn (.cv y)) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show z ∉ (((syn_csn (.cv y))).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y)))))))) (show z ∉ (A).fv from (by exact fresh_z_not_A))))))))))))))) p0020
  have p0022 :=
    @g_sylbi (.classMem (.cv x) (syn_c1c)) (syn_wex z (.classEq (.cv x) (syn_csn (.cv z)))) (.imp (.classMem (.cv x) A) (.imp (.objMem y x) (.classMem (syn_csn (.cv y)) A))) p0010 p0021
  have p0023 :=
    @g_syli (.classMem (.cv x) A) (syn_wss A (syn_c1c)) (.classMem (.cv x) (syn_c1c)) (.imp (.objMem y x) (.classMem (syn_csn (.cv y)) A)) p0000 p0022
  have p0024 :=
    @g_rexlimdv (syn_wss A (syn_c1c)) (.objMem y x) (.classMem (syn_csn (.cv y)) A) x A (by exact (show x ∉ ((Wff.classMem (syn_csn (.cv y)) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((syn_csn (.cv y))).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y)))))))) (show x ∉ (A).fv from (by exact fresh_x_not_A))))))) (by exact (show x ∉ ((syn_wss A (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss]; exact (show x ∉ ((A).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0023
  have p0025 :=
    @g_impbid2 (syn_wss A (syn_c1c)) (.classMem (syn_csn (.cv y)) A) (syn_wrex x A (.objMem y x)) p0009 p0024
  have p0026 :=
    @g_eluni2 x (.cv y) A (by exact (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y))))))) (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
  have p0027_e01_recanon : Nominal.NPrf (syn_wb (.classMem (.cv y) (syn_cuni A)) (syn_wrex x A (.objMem y x))) :=
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
      p0026
  have p0027 :=
    @g_syl6bbr (syn_wss A (syn_c1c)) (.classMem (syn_csn (.cv y)) A) (syn_wrex x A (.objMem y x)) (.classMem (.cv y) (syn_cuni A)) p0025 p0027_e01_recanon
  have p0028 :=
    @g_eleq1 (.cv x) (syn_csn (.cv y)) A
  have p0029 :=
    @g_eleq1 (.cv x) (syn_csn (.cv y)) (syn_cpw1 (syn_cuni A))
  have p0030 :=
    @g_snelpw1 (.cv y) (syn_cuni A)
  have p0031 :=
    @g_syl6bb (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) (syn_cpw1 (syn_cuni A))) (.classMem (syn_csn (.cv y)) (syn_cpw1 (syn_cuni A))) (.classMem (.cv y) (syn_cuni A)) p0029 p0030
  have p0032 :=
    @g_bibi12d (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) A) (.classMem (syn_csn (.cv y)) A) (.classMem (.cv x) (syn_cpw1 (syn_cuni A))) (.classMem (.cv y) (syn_cuni A)) p0028 p0031
  have p0033 :=
    @g_syl5ibrcom (syn_wss A (syn_c1c)) (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) (syn_cpw1 (syn_cuni A)))) (.classEq (.cv x) (syn_csn (.cv y))) (syn_wb (.classMem (syn_csn (.cv y)) A) (.classMem (.cv y) (syn_cuni A))) p0027 p0032
  have p0034 :=
    @g_exlimdv (syn_wss A (syn_c1c)) (.classEq (.cv x) (syn_csn (.cv y))) (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) (syn_cpw1 (syn_cuni A)))) y (by exact (show y ∉ ((syn_wb (.classMem (.cv x) A) (.classMem (.cv x) (syn_cpw1 (syn_cuni A))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb]; exact (show y ∉ (((Wff.classMem (.cv x) A)).fv) ∪ (((Wff.classMem (.cv x) (syn_cpw1 (syn_cuni A)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Wff.classMem (.cv x) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((Class.cv x)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))) (show y ∉ (A).fv from (by exact fresh_y_not_A)))))) (show y ∉ ((Wff.classMem (.cv x) (syn_cpw1 (syn_cuni A)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((Class.cv x)).fv) ∪ (((syn_cpw1 (syn_cuni A))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))) (show y ∉ ((syn_cpw1 (syn_cuni A))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show y ∉ ((syn_cuni A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show y ∉ (A).fv from (by exact fresh_y_not_A))))))))))))))) (by exact (show y ∉ ((syn_wss A (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss]; exact (show y ∉ ((A).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0033
  have p0035 :=
    @g_syl5bi (.classMem (.cv x) (syn_c1c)) (syn_wex y (.classEq (.cv x) (syn_csn (.cv y)))) (syn_wss A (syn_c1c)) (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) (syn_cpw1 (syn_cuni A)))) p0004 p0034
  have p0036 :=
    @g_pm5_21ndd (syn_wss A (syn_c1c)) (.classMem (.cv x) (syn_c1c)) (.classMem (.cv x) A) (.classMem (.cv x) (syn_cpw1 (syn_cuni A))) p0000 p0003 p0035
  have p0037 :=
    @g_eqrdv (syn_wss A (syn_c1c)) x A (syn_cpw1 (syn_cuni A)) (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show x ∉ ((syn_cpw1 (syn_cuni A))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show x ∉ ((syn_cuni A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show x ∉ (A).fv from (by exact fresh_x_not_A))))))) (by exact (show x ∉ ((syn_wss A (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss]; exact (show x ∉ ((A).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0036
  exact p0037

noncomputable def g_pw1equn
    (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_x_y : x ≠ y) (hyp_pw1equn_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_pw1equn_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classEq (syn_cpw1 C) (syn_cun A B)) (syn_wex x (syn_wex y (syn_w3a (.classEq C (syn_cun (.cv x) (.cv y))) (.classEq A (syn_cpw1 (.cv x))) (.classEq B (syn_cpw1 (.cv y))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_unipw1 C
  have p0001 :=
    @g_unieq (syn_cpw1 C) (syn_cun A B)
  have p0002 :=
    @g_syl5eqr (.classEq (syn_cpw1 C) (syn_cun A B)) C (syn_cuni (syn_cpw1 C)) (syn_cuni (syn_cun A B)) p0000 p0001
  have p0003 :=
    @g_ssun1 A B
  have p0004 :=
    @g_sseq2 (syn_cpw1 C) (syn_cun A B) A
  have p0005 :=
    @g_mpbiri (.classEq (syn_cpw1 C) (syn_cun A B)) (syn_wss A (syn_cpw1 C)) (syn_wss A (syn_cun A B)) p0003 p0004
  have p0006 :=
    @g_pw1ss1c C
  have p0007 :=
    @g_syl6ss (.classEq (syn_cpw1 C) (syn_cun A B)) A (syn_cpw1 C) (syn_c1c) p0005 p0006
  have p0008 :=
    @g_eqpw1uni A
  have p0009 :=
    @g_syl (.classEq (syn_cpw1 C) (syn_cun A B)) (syn_wss A (syn_c1c)) (.classEq A (syn_cpw1 (syn_cuni A))) p0007 p0008
  have p0010 :=
    @g_ssun2 B A
  have p0011 :=
    @g_sseq2 (syn_cpw1 C) (syn_cun A B) B
  have p0012 :=
    @g_mpbiri (.classEq (syn_cpw1 C) (syn_cun A B)) (syn_wss B (syn_cpw1 C)) (syn_wss B (syn_cun A B)) p0010 p0011
  have p0013 :=
    @g_syl6ss (.classEq (syn_cpw1 C) (syn_cun A B)) B (syn_cpw1 C) (syn_c1c) p0012 p0006
  have p0014 :=
    @g_eqpw1uni B
  have p0015 :=
    @g_syl (.classEq (syn_cpw1 C) (syn_cun A B)) (syn_wss B (syn_c1c)) (.classEq B (syn_cpw1 (syn_cuni B))) p0013 p0014
  have p0016 :=
    @g_uniex A hyp_pw1equn_1
  have p0017 :=
    @g_uniex B hyp_pw1equn_2
  have p0018 :=
    @g_uneq12 (.cv x) (syn_cuni A) (.cv y) (syn_cuni B)
  have p0019 :=
    @g_uniun A B
  have p0020 :=
    @g_syl6eqr (syn_wa (.classEq (.cv x) (syn_cuni A)) (.classEq (.cv y) (syn_cuni B))) (syn_cun (.cv x) (.cv y)) (syn_cun (syn_cuni A) (syn_cuni B)) (syn_cuni (syn_cun A B)) p0018 p0019
  have p0021 :=
    @g_eqeq2d (syn_wa (.classEq (.cv x) (syn_cuni A)) (.classEq (.cv y) (syn_cuni B))) (syn_cun (.cv x) (.cv y)) (syn_cuni (syn_cun A B)) C p0020
  have p0022 :=
    @g_pw1eq (.cv x) (syn_cuni A)
  have p0023 :=
    @g_eqeq2d (.classEq (.cv x) (syn_cuni A)) (syn_cpw1 (.cv x)) (syn_cpw1 (syn_cuni A)) A p0022
  have p0024 :=
    @g_adantr (.classEq (.cv x) (syn_cuni A)) (syn_wb (.classEq A (syn_cpw1 (.cv x))) (.classEq A (syn_cpw1 (syn_cuni A)))) (.classEq (.cv y) (syn_cuni B)) p0023
  have p0025 :=
    @g_pw1eq (.cv y) (syn_cuni B)
  have p0026 :=
    @g_eqeq2d (.classEq (.cv y) (syn_cuni B)) (syn_cpw1 (.cv y)) (syn_cpw1 (syn_cuni B)) B p0025
  have p0027 :=
    @g_adantl (.classEq (.cv y) (syn_cuni B)) (syn_wb (.classEq B (syn_cpw1 (.cv y))) (.classEq B (syn_cpw1 (syn_cuni B)))) (.classEq (.cv x) (syn_cuni A)) p0026
  have p0028 :=
    @g_n_3anbi123d (syn_wa (.classEq (.cv x) (syn_cuni A)) (.classEq (.cv y) (syn_cuni B))) (.classEq C (syn_cun (.cv x) (.cv y))) (.classEq C (syn_cuni (syn_cun A B))) (.classEq A (syn_cpw1 (.cv x))) (.classEq A (syn_cpw1 (syn_cuni A))) (.classEq B (syn_cpw1 (.cv y))) (.classEq B (syn_cpw1 (syn_cuni B))) p0021 p0024 p0027
  have p0029 :=
    @g_spc2ev (syn_w3a (.classEq C (syn_cun (.cv x) (.cv y))) (.classEq A (syn_cpw1 (.cv x))) (.classEq B (syn_cpw1 (.cv y)))) (syn_w3a (.classEq C (syn_cuni (syn_cun A B))) (.classEq A (syn_cpw1 (syn_cuni A))) (.classEq B (syn_cpw1 (syn_cuni B)))) x y (syn_cuni A) (syn_cuni B) (by exact (show x ∉ ((syn_cuni A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show x ∉ (A).fv from (by exact dv_A_x))))) (by exact (show y ∉ ((syn_cuni A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show y ∉ (A).fv from (by exact dv_A_y))))) (by exact (show x ∉ ((syn_cuni B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show x ∉ (B).fv from (by exact dv_B_x))))) (by exact (show y ∉ ((syn_cuni B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show y ∉ (B).fv from (by exact dv_B_y))))) (by exact (show x ∉ ((syn_w3a (.classEq C (syn_cuni (syn_cun A B))) (.classEq A (syn_cpw1 (syn_cuni A))) (.classEq B (syn_cpw1 (syn_cuni B))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a]; exact (show x ∉ (((Wff.classEq B (syn_cpw1 (syn_cuni B)))).fv) ∪ (((Wff.classEq C (syn_cuni (syn_cun A B)))).fv) ∪ (((Wff.classEq A (syn_cpw1 (syn_cuni A)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Wff.classEq B (syn_cpw1 (syn_cuni B)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ ((B).fv) ∪ (((syn_cpw1 (syn_cuni B))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (B).fv from (by exact dv_B_x)) (show x ∉ ((syn_cpw1 (syn_cuni B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show x ∉ ((syn_cuni B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show x ∉ (B).fv from (by exact dv_B_x)))))))))) (show x ∉ ((Wff.classEq C (syn_cuni (syn_cun A B)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ ((C).fv) ∪ (((syn_cuni (syn_cun A B))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (C).fv from (by exact dv_C_x)) (show x ∉ ((syn_cuni (syn_cun A B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show x ∉ ((syn_cun A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show x ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact dv_A_x)) (show x ∉ (B).fv from (by exact dv_B_x))))))))))))) (show x ∉ ((Wff.classEq A (syn_cpw1 (syn_cuni A)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ ((A).fv) ∪ (((syn_cpw1 (syn_cuni A))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact dv_A_x)) (show x ∉ ((syn_cpw1 (syn_cuni A))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show x ∉ ((syn_cuni A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show x ∉ (A).fv from (by exact dv_A_x))))))))))))))) (by exact (show y ∉ ((syn_w3a (.classEq C (syn_cuni (syn_cun A B))) (.classEq A (syn_cpw1 (syn_cuni A))) (.classEq B (syn_cpw1 (syn_cuni B))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a]; exact (show y ∉ (((Wff.classEq B (syn_cpw1 (syn_cuni B)))).fv) ∪ (((Wff.classEq C (syn_cuni (syn_cun A B)))).fv) ∪ (((Wff.classEq A (syn_cpw1 (syn_cuni A)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Wff.classEq B (syn_cpw1 (syn_cuni B)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ ((B).fv) ∪ (((syn_cpw1 (syn_cuni B))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (B).fv from (by exact dv_B_y)) (show y ∉ ((syn_cpw1 (syn_cuni B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show y ∉ ((syn_cuni B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show y ∉ (B).fv from (by exact dv_B_y)))))))))) (show y ∉ ((Wff.classEq C (syn_cuni (syn_cun A B)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ ((C).fv) ∪ (((syn_cuni (syn_cun A B))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (C).fv from (by exact dv_C_y)) (show y ∉ ((syn_cuni (syn_cun A B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show y ∉ ((syn_cun A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show y ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact dv_A_y)) (show y ∉ (B).fv from (by exact dv_B_y))))))))))))) (show y ∉ ((Wff.classEq A (syn_cpw1 (syn_cuni A)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ ((A).fv) ∪ (((syn_cpw1 (syn_cuni A))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact dv_A_y)) (show y ∉ ((syn_cpw1 (syn_cuni A))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show y ∉ ((syn_cuni A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni]; exact (show y ∉ (A).fv from (by exact dv_A_y))))))))))))))) (show x ≠ y from (by exact dv_x_y)) p0016 p0017 p0028
  have p0030 :=
    @g_syl3anc (.classEq (syn_cpw1 C) (syn_cun A B)) (.classEq C (syn_cuni (syn_cun A B))) (.classEq A (syn_cpw1 (syn_cuni A))) (.classEq B (syn_cpw1 (syn_cuni B))) (syn_wex x (syn_wex y (syn_w3a (.classEq C (syn_cun (.cv x) (.cv y))) (.classEq A (syn_cpw1 (.cv x))) (.classEq B (syn_cpw1 (.cv y)))))) p0002 p0009 p0015 p0029
  have p0031 :=
    @g_pw1un (.cv x) (.cv y)
  have p0032 :=
    @g_pw1eq C (syn_cun (.cv x) (.cv y))
  have p0033 :=
    @g_uneq12 A (syn_cpw1 (.cv x)) B (syn_cpw1 (.cv y))
  have p0034 :=
    @g_eqeqan12d (.classEq C (syn_cun (.cv x) (.cv y))) (syn_wa (.classEq A (syn_cpw1 (.cv x))) (.classEq B (syn_cpw1 (.cv y)))) (syn_cpw1 C) (syn_cpw1 (syn_cun (.cv x) (.cv y))) (syn_cun A B) (syn_cun (syn_cpw1 (.cv x)) (syn_cpw1 (.cv y))) p0032 p0033
  have p0035 :=
    @g_n_3impb (.classEq C (syn_cun (.cv x) (.cv y))) (.classEq A (syn_cpw1 (.cv x))) (.classEq B (syn_cpw1 (.cv y))) (syn_wb (.classEq (syn_cpw1 C) (syn_cun A B)) (.classEq (syn_cpw1 (syn_cun (.cv x) (.cv y))) (syn_cun (syn_cpw1 (.cv x)) (syn_cpw1 (.cv y))))) p0034
  have p0036 :=
    @g_mpbiri (syn_w3a (.classEq C (syn_cun (.cv x) (.cv y))) (.classEq A (syn_cpw1 (.cv x))) (.classEq B (syn_cpw1 (.cv y)))) (.classEq (syn_cpw1 C) (syn_cun A B)) (.classEq (syn_cpw1 (syn_cun (.cv x) (.cv y))) (syn_cun (syn_cpw1 (.cv x)) (syn_cpw1 (.cv y)))) p0031 p0035
  have p0037 :=
    @g_exlimivv (syn_w3a (.classEq C (syn_cun (.cv x) (.cv y))) (.classEq A (syn_cpw1 (.cv x))) (.classEq B (syn_cpw1 (.cv y)))) (.classEq (syn_cpw1 C) (syn_cun A B)) x y (by exact (show x ∉ ((Wff.classEq (syn_cpw1 C) (syn_cun A B))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ (((syn_cpw1 C)).fv) ∪ (((syn_cun A B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cpw1 C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show x ∉ (C).fv from (by exact dv_C_x)))) (show x ∉ ((syn_cun A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show x ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact dv_A_x)) (show x ∉ (B).fv from (by exact dv_B_x))))))))))) (by exact (show y ∉ ((Wff.classEq (syn_cpw1 C) (syn_cun A B))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ (((syn_cpw1 C)).fv) ∪ (((syn_cun A B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cpw1 C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show y ∉ (C).fv from (by exact dv_C_y)))) (show y ∉ ((syn_cun A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show y ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact dv_A_y)) (show y ∉ (B).fv from (by exact dv_B_y))))))))))) p0036
  have p0038 :=
    @g_impbii (.classEq (syn_cpw1 C) (syn_cun A B)) (syn_wex x (syn_wex y (syn_w3a (.classEq C (syn_cun (.cv x) (.cv y))) (.classEq A (syn_cpw1 (.cv x))) (.classEq B (syn_cpw1 (.cv y)))))) p0030 p0037
  exact p0038



#print axioms g_pw1equn

end NFChoice.DirectNominalPrf.WPPReplay
