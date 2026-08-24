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
import NominalWPPReplayChunk009StructuralPart014


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

noncomputable def g_dfimak2
    (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cimak A B) (syn_ccompl (syn_cp6 (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_B : z ∉ B.fv := by
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
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex y B (.classMem (syn_copk (.cv y) (.cv x)) A))))
  have p0001 :=
    @g_exancom (.classMem (.cv y) B) (.classMem (syn_copk (.cv y) (.cv x)) A) y
  have p0002 :=
    @g_vex x
  have p0003 :=
    @g_elp6 z (.cv x) (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))) (syn_cvv) (by exact (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x))))))) (by exact (show z ∉ ((syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show z ∉ (((syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv)))).fv) ∪ (((syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl]; exact (show z ∉ ((syn_cxpk (syn_c1c) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show z ∉ (((syn_c1c)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show z ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))) (show z ∉ ((syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik]; exact (show z ∉ ((syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl]; exact (show z ∉ ((syn_cin A (syn_cxpk B (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show z ∉ ((A).fv) ∪ (((syn_cxpk B (syn_cvv))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ (A).fv from (by exact fresh_z_not_A)) (show z ∉ ((syn_cxpk B (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show z ∉ ((B).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ (B).fv from (by exact fresh_z_not_B)) (show z ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))))))))))
  have p0004 :=
    Nominal.mp p0002 p0003
  have p0005 :=
    @g_elun (syn_copk (.cv z) (syn_csn (.cv x))) (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))
  have p0006 :=
    @g_opkex (.cv z) (syn_csn (.cv x))
  have p0007 :=
    @g_elcompl (syn_copk (.cv z) (syn_csn (.cv x))) (syn_cxpk (syn_c1c) (syn_cvv)) p0006
  have p0008 :=
    @g_snex (.cv x)
  have p0009 :=
    @g_vex z
  have p0010 :=
    @g_opkelxpk (.cv z) (syn_csn (.cv x)) (syn_c1c) (syn_cvv) p0009 p0008
  have p0011 :=
    @g_mpbiran2 (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_cxpk (syn_c1c) (syn_cvv))) (.classMem (.cv z) (syn_c1c)) (.classMem (syn_csn (.cv x)) (syn_cvv)) p0008 p0010
  have p0012 :=
    @g_xchbinx (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv)))) (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_cxpk (syn_c1c) (syn_cvv))) (.classMem (.cv z) (syn_c1c)) p0007 p0011
  have p0013 :=
    @g_orbi1i (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv)))) (.neg (.classMem (.cv z) (syn_c1c))) (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))) p0012
  have p0014 :=
    @g_iman (.classMem (.cv z) (syn_c1c)) (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))
  have p0015 :=
    @g_imor (.classMem (.cv z) (syn_c1c)) (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))
  have p0016 :=
    @g_el1c y (.cv z) (by exact (show y ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ z from (by exact fresh_y_ne_z)))))))
  have p0017 :=
    @g_anbi1i (.classMem (.cv z) (syn_c1c)) (syn_wex y (.classEq (.cv z) (syn_csn (.cv y)))) (.neg (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))) p0016
  have p0018 :=
    @g_n_19_41v (.classEq (.cv z) (syn_csn (.cv y))) (.neg (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))) y (by exact (show y ∉ ((Wff.neg (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_neg]; exact (show y ∉ ((Wff.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((syn_copk (.cv z) (syn_csn (.cv x)))).fv) ∪ (((syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_copk (.cv z) (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show y ∉ (((Class.cv z)).fv) ∪ (((syn_csn (.cv x))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ z from (by exact fresh_y_ne_z)))))) (show y ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))))))))) (show y ∉ ((syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik]; exact (show y ∉ ((syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl]; exact (show y ∉ ((syn_cin A (syn_cxpk B (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show y ∉ ((A).fv) ∪ (((syn_cxpk B (syn_cvv))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ ((syn_cxpk B (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show y ∉ ((B).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (B).fv from (by exact fresh_y_not_B)) (show y ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))))))))))))
  have p0019 :=
    @g_bitr4i (syn_wa (.classMem (.cv z) (syn_c1c)) (.neg (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))) (syn_wa (syn_wex y (.classEq (.cv z) (syn_csn (.cv y)))) (.neg (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))) (syn_wex y (syn_wa (.classEq (.cv z) (syn_csn (.cv y))) (.neg (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))))) p0017 p0018
  have p0020 :=
    @g_notbii (syn_wa (.classMem (.cv z) (syn_c1c)) (.neg (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))) (syn_wex y (syn_wa (.classEq (.cv z) (syn_csn (.cv y))) (.neg (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))))) p0019
  have p0021 :=
    @g_n_3bitr3i (.imp (.classMem (.cv z) (syn_c1c)) (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))) (.neg (syn_wa (.classMem (.cv z) (syn_c1c)) (.neg (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))))) (syn_wo (.neg (.classMem (.cv z) (syn_c1c))) (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))) (.neg (syn_wex y (syn_wa (.classEq (.cv z) (syn_csn (.cv y))) (.neg (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))))) p0014 p0015 p0020
  have p0022 :=
    @g_n_3bitri (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))) (syn_wo (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv)))) (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))) (syn_wo (.neg (.classMem (.cv z) (syn_c1c))) (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))) (.neg (syn_wex y (syn_wa (.classEq (.cv z) (syn_csn (.cv y))) (.neg (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))))) p0005 p0013 p0021
  have p0023 :=
    @g_albii (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))) (.neg (syn_wex y (syn_wa (.classEq (.cv z) (syn_csn (.cv y))) (.neg (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))))) z p0022
  have p0024 :=
    @g_alnex (syn_wex y (syn_wa (.classEq (.cv z) (syn_csn (.cv y))) (.neg (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))))) z
  have p0025 :=
    @g_excom (syn_wa (.classEq (.cv z) (syn_csn (.cv y))) (.neg (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))) z y
  have p0026 :=
    @g_snex (.cv y)
  have p0027 :=
    @g_opkeq1 (.cv z) (syn_csn (.cv y)) (syn_csn (.cv x))
  have p0028 :=
    @g_eleq1d (.classEq (.cv z) (syn_csn (.cv y))) (syn_copk (.cv z) (syn_csn (.cv x))) (syn_copk (syn_csn (.cv y)) (syn_csn (.cv x))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))) p0027
  have p0029 :=
    @g_vex y
  have p0030 :=
    @g_opksnelsik (.cv y) (.cv x) (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))) p0029 p0002
  have p0031 :=
    @g_opkex (.cv y) (.cv x)
  have p0032 :=
    @g_elcompl (syn_copk (.cv y) (.cv x)) (syn_cin A (syn_cxpk B (syn_cvv))) p0031
  have p0033 :=
    @g_bitri (.classMem (syn_copk (syn_csn (.cv y)) (syn_csn (.cv x))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))) (.classMem (syn_copk (.cv y) (.cv x)) (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))) (.neg (.classMem (syn_copk (.cv y) (.cv x)) (syn_cin A (syn_cxpk B (syn_cvv))))) p0030 p0032
  have p0034 :=
    @g_syl6bb (.classEq (.cv z) (syn_csn (.cv y))) (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))) (.classMem (syn_copk (syn_csn (.cv y)) (syn_csn (.cv x))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))) (.neg (.classMem (syn_copk (.cv y) (.cv x)) (syn_cin A (syn_cxpk B (syn_cvv))))) p0028 p0033
  have p0035 :=
    @g_notbid (.classEq (.cv z) (syn_csn (.cv y))) (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))) (.neg (.classMem (syn_copk (.cv y) (.cv x)) (syn_cin A (syn_cxpk B (syn_cvv))))) p0034
  have p0036 :=
    @g_ceqsexv (.neg (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))) (.neg (.neg (.classMem (syn_copk (.cv y) (.cv x)) (syn_cin A (syn_cxpk B (syn_cvv)))))) z (syn_csn (.cv y)) (by exact (show z ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y))))))))) (by exact (show z ∉ ((Wff.neg (.neg (.classMem (syn_copk (.cv y) (.cv x)) (syn_cin A (syn_cxpk B (syn_cvv))))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_neg]; exact (show z ∉ ((Wff.neg (.classMem (syn_copk (.cv y) (.cv x)) (syn_cin A (syn_cxpk B (syn_cvv)))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_neg]; exact (show z ∉ ((Wff.classMem (syn_copk (.cv y) (.cv x)) (syn_cin A (syn_cxpk B (syn_cvv))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show z ∉ (((syn_copk (.cv y) (.cv x))).fv) ∪ (((syn_cin A (syn_cxpk B (syn_cvv)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_copk (.cv y) (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show z ∉ (((Class.cv y)).fv) ∪ (((Class.cv x)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y)))))) (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))))))) (show z ∉ ((syn_cin A (syn_cxpk B (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show z ∉ ((A).fv) ∪ (((syn_cxpk B (syn_cvv))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ (A).fv from (by exact fresh_z_not_A)) (show z ∉ ((syn_cxpk B (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show z ∉ ((B).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ (B).fv from (by exact fresh_z_not_B)) (show z ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))))))))))) p0026 p0035
  have p0037 :=
    @g_elin (syn_copk (.cv y) (.cv x)) A (syn_cxpk B (syn_cvv))
  have p0038 :=
    @g_notnot (.classMem (syn_copk (.cv y) (.cv x)) (syn_cin A (syn_cxpk B (syn_cvv))))
  have p0039 :=
    @g_opkelxpk (.cv y) (.cv x) B (syn_cvv) p0029 p0002
  have p0040 :=
    @g_mpbiran2 (.classMem (syn_copk (.cv y) (.cv x)) (syn_cxpk B (syn_cvv))) (.classMem (.cv y) B) (.classMem (.cv x) (syn_cvv)) p0002 p0039
  have p0041 :=
    @g_anbi2i (.classMem (syn_copk (.cv y) (.cv x)) (syn_cxpk B (syn_cvv))) (.classMem (.cv y) B) (.classMem (syn_copk (.cv y) (.cv x)) A) p0040
  have p0042 :=
    @g_n_3bitr3i (.classMem (syn_copk (.cv y) (.cv x)) (syn_cin A (syn_cxpk B (syn_cvv)))) (syn_wa (.classMem (syn_copk (.cv y) (.cv x)) A) (.classMem (syn_copk (.cv y) (.cv x)) (syn_cxpk B (syn_cvv)))) (.neg (.neg (.classMem (syn_copk (.cv y) (.cv x)) (syn_cin A (syn_cxpk B (syn_cvv)))))) (syn_wa (.classMem (syn_copk (.cv y) (.cv x)) A) (.classMem (.cv y) B)) p0037 p0038 p0041
  have p0043 :=
    @g_bitri (syn_wex z (syn_wa (.classEq (.cv z) (syn_csn (.cv y))) (.neg (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))))) (.neg (.neg (.classMem (syn_copk (.cv y) (.cv x)) (syn_cin A (syn_cxpk B (syn_cvv)))))) (syn_wa (.classMem (syn_copk (.cv y) (.cv x)) A) (.classMem (.cv y) B)) p0036 p0042
  have p0044 :=
    @g_exbii (syn_wex z (syn_wa (.classEq (.cv z) (syn_csn (.cv y))) (.neg (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))))) (syn_wa (.classMem (syn_copk (.cv y) (.cv x)) A) (.classMem (.cv y) B)) y p0043
  have p0045 :=
    @g_bitri (syn_wex z (syn_wex y (syn_wa (.classEq (.cv z) (syn_csn (.cv y))) (.neg (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))))) (syn_wex y (syn_wex z (syn_wa (.classEq (.cv z) (syn_csn (.cv y))) (.neg (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))))) (syn_wex y (syn_wa (.classMem (syn_copk (.cv y) (.cv x)) A) (.classMem (.cv y) B))) p0025 p0044
  have p0046 :=
    @g_xchbinx (.all z (.neg (syn_wex y (syn_wa (.classEq (.cv z) (syn_csn (.cv y))) (.neg (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))))))) (syn_wex z (syn_wex y (syn_wa (.classEq (.cv z) (syn_csn (.cv y))) (.neg (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))))) (syn_wex y (syn_wa (.classMem (syn_copk (.cv y) (.cv x)) A) (.classMem (.cv y) B))) p0024 p0045
  have p0047 :=
    @g_n_3bitri (.classMem (.cv x) (syn_cp6 (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))) (.all z (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))) (.all z (.neg (syn_wex y (syn_wa (.classEq (.cv z) (syn_csn (.cv y))) (.neg (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))))))) (.neg (syn_wex y (syn_wa (.classMem (syn_copk (.cv y) (.cv x)) A) (.classMem (.cv y) B)))) p0004 p0023 p0046
  have p0048 :=
    @g_con2bii (.classMem (.cv x) (syn_cp6 (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))) (syn_wex y (syn_wa (.classMem (syn_copk (.cv y) (.cv x)) A) (.classMem (.cv y) B))) p0047
  have p0049 :=
    @g_n_3bitri (syn_wrex y B (.classMem (syn_copk (.cv y) (.cv x)) A)) (syn_wex y (syn_wa (.classMem (.cv y) B) (.classMem (syn_copk (.cv y) (.cv x)) A))) (syn_wex y (syn_wa (.classMem (syn_copk (.cv y) (.cv x)) A) (.classMem (.cv y) B))) (.neg (.classMem (.cv x) (syn_cp6 (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))))) p0000 p0001 p0048
  have p0050 :=
    @g_elimak y A B (.cv x) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B))) (by exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))) p0002
  have p0051 :=
    @g_elcompl (.cv x) (syn_cp6 (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))) p0002
  have p0052 :=
    @g_n_3bitr4i (syn_wrex y B (.classMem (syn_copk (.cv y) (.cv x)) A)) (.neg (.classMem (.cv x) (syn_cp6 (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))))) (.classMem (.cv x) (syn_cimak A B)) (.classMem (.cv x) (syn_ccompl (syn_cp6 (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))))) p0049 p0050 p0051
  have p0053 :=
    @g_eqriv x (syn_cimak A B) (syn_ccompl (syn_cp6 (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))) (by exact (show x ∉ ((syn_cimak A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak]; exact (show x ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ (B).fv from (by exact fresh_x_not_B))))))) (by exact (show x ∉ ((syn_ccompl (syn_cp6 (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl]; exact (show x ∉ ((syn_cp6 (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cp6]; exact (show x ∉ ((syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show x ∉ (((syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv)))).fv) ∪ (((syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl]; exact (show x ∉ ((syn_cxpk (syn_c1c) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show x ∉ (((syn_c1c)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show x ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))) (show x ∉ ((syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik]; exact (show x ∉ ((syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl]; exact (show x ∉ ((syn_cin A (syn_cxpk B (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show x ∉ ((A).fv) ∪ (((syn_cxpk B (syn_cvv))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ ((syn_cxpk B (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show x ∉ ((B).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (B).fv from (by exact fresh_x_not_B)) (show x ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))))))))))))))) p0052
  exact p0053

noncomputable def g_imakexg
    (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem B W)) (.classMem (syn_cimak A B) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  have p0000 :=
    @g_dfimak2 A B
  have p0001 :=
    @g_n_1cex
  have p0002 :=
    @g_vvex
  have p0003 :=
    @g_xpkex (syn_c1c) (syn_cvv) p0001 p0002
  have p0004 :=
    @g_complex (syn_cxpk (syn_c1c) (syn_cvv)) p0003
  have p0005 :=
    @g_vvex
  have p0006 :=
    @g_xpkexg B (syn_cvv) W (syn_cvv)
  have p0007 :=
    @g_mpan2 (.classMem B W) (.classMem (syn_cvv) (syn_cvv)) (.classMem (syn_cxpk B (syn_cvv)) (syn_cvv)) p0005 p0006
  have p0008 :=
    @g_inexg A (syn_cxpk B (syn_cvv)) V (syn_cvv)
  have p0009 :=
    @g_sylan2 (.classMem B W) (.classMem A V) (.classMem (syn_cxpk B (syn_cvv)) (syn_cvv)) (.classMem (syn_cin A (syn_cxpk B (syn_cvv))) (syn_cvv)) p0007 p0008
  have p0010 :=
    @g_complexg (syn_cin A (syn_cxpk B (syn_cvv))) (syn_cvv)
  have p0011 :=
    @g_sikexg (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))) (syn_cvv)
  have p0012 :=
    @g_n_3syl (syn_wa (.classMem A V) (.classMem B W)) (.classMem (syn_cin A (syn_cxpk B (syn_cvv))) (syn_cvv)) (.classMem (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))) (syn_cvv)) (.classMem (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))) (syn_cvv)) p0009 p0010 p0011
  have p0013 :=
    @g_unexg (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))) (syn_cvv) (syn_cvv)
  have p0014 :=
    @g_sylancr (syn_wa (.classMem A V) (.classMem B W)) (.classMem (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv))) (syn_cvv)) (.classMem (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))) (syn_cvv)) (.classMem (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))) (syn_cvv)) p0004 p0012 p0013
  have p0015 :=
    @g_p6exg (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))) (syn_cvv)
  have p0016 :=
    @g_complexg (syn_cp6 (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))) (syn_cvv)
  have p0017 :=
    @g_n_3syl (syn_wa (.classMem A V) (.classMem B W)) (.classMem (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))) (syn_cvv)) (.classMem (syn_cp6 (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))) (syn_cvv)) (.classMem (syn_ccompl (syn_cp6 (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))) (syn_cvv)) p0014 p0015 p0016
  have p0018 :=
    @g_syl5eqel (syn_wa (.classMem A V) (.classMem B W)) (syn_cimak A B) (syn_ccompl (syn_cp6 (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv))) (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))) (syn_cvv) p0000 p0017
  exact p0018

noncomputable def g_imakex
    (A : Class) (B : Class) (hyp_imakex_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_imakex_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cimak A B) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_imakexg A B (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem (syn_cimak A B) (syn_cvv)) hyp_imakex_1 hyp_imakex_2 p0000
  exact p0001

noncomputable def g_dfpw12
    (A : Class) :
    Nominal.NPrf (.classEq (syn_cpw1 A) (syn_cimak (syn_csik (syn_cxpk A A)) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
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
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (h)
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
  have fresh_x_ne_w : x ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_w_ne_x : w ≠ x :=
    Ne.symm fresh_x_ne_w
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_y_ne_w : y ≠ w := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_w_ne_y : w ≠ y :=
    Ne.symm fresh_y_ne_w
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have p0000 :=
    @g_elpw1 y (.cv x) A (by exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
  have p0001 :=
    @g_vex x
  have p0002 :=
    @g_elimakv z (syn_csik (syn_cxpk A A)) (.cv x) (by exact (show z ∉ ((syn_csik (syn_cxpk A A))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik]; exact (show z ∉ ((syn_cxpk A A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show z ∉ ((A).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ (A).fv from (by exact fresh_z_not_A)) (show z ∉ (A).fv from (by exact fresh_z_not_A))))))))) (by exact (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x))))))) p0001
  have p0003 :=
    @g_vex z
  have p0004 :=
    @g_opkelsikg w y (.cv z) (.cv x) (syn_cxpk A A) (syn_cvv) (syn_cvv) (by exact (show w ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ z from (by exact fresh_w_ne_z))))))) (by exact (show y ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ z from (by exact fresh_y_ne_z))))))) (by exact (show w ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ x from (by exact fresh_w_ne_x))))))) (by exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))) (by exact (show w ∉ ((syn_cxpk A A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show w ∉ ((A).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ (A).fv from (by exact fresh_w_not_A)) (show w ∉ (A).fv from (by exact fresh_w_not_A))))))) (by exact (show y ∉ ((syn_cxpk A A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show y ∉ ((A).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ (A).fv from (by exact fresh_y_not_A))))))) (show w ≠ y from (by exact fresh_w_ne_y))
  have p0005 :=
    @g_mp2an (.classMem (.cv z) (syn_cvv)) (.classMem (.cv x) (syn_cvv)) (syn_wb (.classMem (syn_copk (.cv z) (.cv x)) (syn_csik (syn_cxpk A A))) (syn_wex w (syn_wex y (syn_w3a (.classEq (.cv z) (syn_csn (.cv w))) (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (syn_copk (.cv w) (.cv y)) (syn_cxpk A A)))))) p0003 p0001 p0004
  have p0006 :=
    @g_exbii (.classMem (syn_copk (.cv z) (.cv x)) (syn_csik (syn_cxpk A A))) (syn_wex w (syn_wex y (syn_w3a (.classEq (.cv z) (syn_csn (.cv w))) (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (syn_copk (.cv w) (.cv y)) (syn_cxpk A A))))) z p0005
  have p0007 :=
    @g_exrot3 (syn_w3a (.classEq (.cv z) (syn_csn (.cv w))) (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (syn_copk (.cv w) (.cv y)) (syn_cxpk A A))) y z w
  have p0008 :=
    @g_bitr4i (syn_wex z (.classMem (syn_copk (.cv z) (.cv x)) (syn_csik (syn_cxpk A A)))) (syn_wex z (syn_wex w (syn_wex y (syn_w3a (.classEq (.cv z) (syn_csn (.cv w))) (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (syn_copk (.cv w) (.cv y)) (syn_cxpk A A)))))) (syn_wex y (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv z) (syn_csn (.cv w))) (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (syn_copk (.cv w) (.cv y)) (syn_cxpk A A)))))) p0006 p0007
  have p0009 :=
    (by simpa [syn_wb, syn_w3a] using (Nominal.biimpRefl (syn_w3a (.classEq (.cv z) (syn_csn (.cv w))) (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (syn_copk (.cv w) (.cv y)) (syn_cxpk A A)))))
  have p0010 :=
    @g_vex w
  have p0011 :=
    @g_vex y
  have p0012 :=
    @g_opkelxpk (.cv w) (.cv y) A A p0010 p0011
  have p0013 :=
    @g_anbi2i (.classMem (syn_copk (.cv w) (.cv y)) (syn_cxpk A A)) (syn_wa (.classMem (.cv w) A) (.classMem (.cv y) A)) (syn_wa (.classEq (.cv z) (syn_csn (.cv w))) (.classEq (.cv x) (syn_csn (.cv y)))) p0012
  have p0014 :=
    @g_an4 (.classEq (.cv z) (syn_csn (.cv w))) (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv w) A) (.classMem (.cv y) A)
  have p0015 :=
    @g_n_3bitri (syn_w3a (.classEq (.cv z) (syn_csn (.cv w))) (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (syn_copk (.cv w) (.cv y)) (syn_cxpk A A))) (syn_wa (syn_wa (.classEq (.cv z) (syn_csn (.cv w))) (.classEq (.cv x) (syn_csn (.cv y)))) (.classMem (syn_copk (.cv w) (.cv y)) (syn_cxpk A A))) (syn_wa (syn_wa (.classEq (.cv z) (syn_csn (.cv w))) (.classEq (.cv x) (syn_csn (.cv y)))) (syn_wa (.classMem (.cv w) A) (.classMem (.cv y) A))) (syn_wa (syn_wa (.classEq (.cv z) (syn_csn (.cv w))) (.classMem (.cv w) A)) (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv y) A))) p0009 p0013 p0014
  have p0016 :=
    @g_n_2exbii (syn_w3a (.classEq (.cv z) (syn_csn (.cv w))) (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (syn_copk (.cv w) (.cv y)) (syn_cxpk A A))) (syn_wa (syn_wa (.classEq (.cv z) (syn_csn (.cv w))) (.classMem (.cv w) A)) (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv y) A))) z w p0015
  have p0017 :=
    @g_n_19_41vv (syn_wa (.classEq (.cv z) (syn_csn (.cv w))) (.classMem (.cv w) A)) (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv y) A)) z w (by exact (show z ∉ ((syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv y) A))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show z ∉ (((Wff.classEq (.cv x) (syn_csn (.cv y)))).fv) ∪ (((Wff.classMem (.cv y) A)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Wff.classEq (.cv x) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show z ∉ (((Class.cv x)).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))) (show z ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y)))))))))))) (show z ∉ ((Wff.classMem (.cv y) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show z ∉ (((Class.cv y)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y)))))) (show z ∉ (A).fv from (by exact fresh_z_not_A))))))))))) (by exact (show w ∉ ((syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv y) A))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show w ∉ (((Wff.classEq (.cv x) (syn_csn (.cv y)))).fv) ∪ (((Wff.classMem (.cv y) A)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Wff.classEq (.cv x) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show w ∉ (((Class.cv x)).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ x from (by exact fresh_w_ne_x)))))) (show w ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y)))))))))))) (show w ∉ ((Wff.classMem (.cv y) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show w ∉ (((Class.cv y)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y)))))) (show w ∉ (A).fv from (by exact fresh_w_not_A)))))))))))
  have p0018 :=
    @g_sneq (.cv w) (.cv y)
  have p0019 :=
    @g_eqeq12 (.cv z) (.cv x) (syn_csn (.cv w)) (syn_csn (.cv y))
  have p0020_e00_recanon : Nominal.NPrf (.imp (.objEq w y) (.classEq (syn_csn (.cv w)) (syn_csn (.cv y)))) :=
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
      p0018
  have p0020_e01_recanon : Nominal.NPrf (.imp (syn_wa (.objEq z x) (.classEq (syn_csn (.cv w)) (syn_csn (.cv y)))) (syn_wb (.classEq (.cv z) (syn_csn (.cv w))) (.classEq (.cv x) (syn_csn (.cv y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_csn syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0019
  have p0020 :=
    @g_sylan2 (.objEq w y) (.objEq z x) (.classEq (syn_csn (.cv w)) (syn_csn (.cv y))) (syn_wb (.classEq (.cv z) (syn_csn (.cv w))) (.classEq (.cv x) (syn_csn (.cv y)))) p0020_e00_recanon p0020_e01_recanon
  have p0021 :=
    @g_eleq1 (.cv w) (.cv y) A
  have p0022_e00_recanon : Nominal.NPrf (.imp (.objEq w y) (syn_wb (.classMem (.cv w) A) (.classMem (.cv y) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0021
  have p0022 :=
    @g_adantl (.objEq w y) (syn_wb (.classMem (.cv w) A) (.classMem (.cv y) A)) (.objEq z x) p0022_e00_recanon
  have p0023 :=
    @g_anbi12d (syn_wa (.objEq z x) (.objEq w y)) (.classEq (.cv z) (syn_csn (.cv w))) (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv w) A) (.classMem (.cv y) A) p0020 p0022
  have p0024_e02_recanon : Nominal.NPrf (.imp (syn_wa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y))) (syn_wb (syn_wa (.classEq (.cv z) (syn_csn (.cv w))) (.classMem (.cv w) A)) (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv y) A)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0023
  have p0024 :=
    @g_spc2ev (syn_wa (.classEq (.cv z) (syn_csn (.cv w))) (.classMem (.cv w) A)) (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv y) A)) z w (.cv x) (.cv y) (by exact (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x))))))) (by exact (show w ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ x from (by exact fresh_w_ne_x))))))) (by exact (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y))))))) (by exact (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y))))))) (by exact (show z ∉ ((syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv y) A))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show z ∉ (((Wff.classEq (.cv x) (syn_csn (.cv y)))).fv) ∪ (((Wff.classMem (.cv y) A)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Wff.classEq (.cv x) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show z ∉ (((Class.cv x)).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))) (show z ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y)))))))))))) (show z ∉ ((Wff.classMem (.cv y) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show z ∉ (((Class.cv y)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y)))))) (show z ∉ (A).fv from (by exact fresh_z_not_A))))))))))) (by exact (show w ∉ ((syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv y) A))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show w ∉ (((Wff.classEq (.cv x) (syn_csn (.cv y)))).fv) ∪ (((Wff.classMem (.cv y) A)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Wff.classEq (.cv x) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show w ∉ (((Class.cv x)).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ x from (by exact fresh_w_ne_x)))))) (show w ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y)))))))))))) (show w ∉ ((Wff.classMem (.cv y) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show w ∉ (((Class.cv y)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y)))))) (show w ∉ (A).fv from (by exact fresh_w_not_A))))))))))) (show z ≠ w from (by exact fresh_z_ne_w)) p0001 p0011 p0024_e02_recanon
  have p0025 :=
    @g_pm4_71ri (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv y) A)) (syn_wex z (syn_wex w (syn_wa (.classEq (.cv z) (syn_csn (.cv w))) (.classMem (.cv w) A)))) p0024
  have p0026 :=
    @g_ancom (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv y) A)
  have p0027 :=
    @g_bitr3i (syn_wa (syn_wex z (syn_wex w (syn_wa (.classEq (.cv z) (syn_csn (.cv w))) (.classMem (.cv w) A)))) (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv y) A))) (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv y) A)) (syn_wa (.classMem (.cv y) A) (.classEq (.cv x) (syn_csn (.cv y)))) p0025 p0026
  have p0028 :=
    @g_n_3bitri (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv z) (syn_csn (.cv w))) (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (syn_copk (.cv w) (.cv y)) (syn_cxpk A A))))) (syn_wex z (syn_wex w (syn_wa (syn_wa (.classEq (.cv z) (syn_csn (.cv w))) (.classMem (.cv w) A)) (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv y) A))))) (syn_wa (syn_wex z (syn_wex w (syn_wa (.classEq (.cv z) (syn_csn (.cv w))) (.classMem (.cv w) A)))) (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv y) A))) (syn_wa (.classMem (.cv y) A) (.classEq (.cv x) (syn_csn (.cv y)))) p0016 p0017 p0027
  have p0029 :=
    @g_exbii (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv z) (syn_csn (.cv w))) (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (syn_copk (.cv w) (.cv y)) (syn_cxpk A A))))) (syn_wa (.classMem (.cv y) A) (.classEq (.cv x) (syn_csn (.cv y)))) y p0028
  have p0030 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex y A (.classEq (.cv x) (syn_csn (.cv y))))))
  have p0031 :=
    @g_bitr4i (syn_wex y (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv z) (syn_csn (.cv w))) (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (syn_copk (.cv w) (.cv y)) (syn_cxpk A A)))))) (syn_wex y (syn_wa (.classMem (.cv y) A) (.classEq (.cv x) (syn_csn (.cv y))))) (syn_wrex y A (.classEq (.cv x) (syn_csn (.cv y)))) p0029 p0030
  have p0032 :=
    @g_n_3bitri (.classMem (.cv x) (syn_cimak (syn_csik (syn_cxpk A A)) (syn_cvv))) (syn_wex z (.classMem (syn_copk (.cv z) (.cv x)) (syn_csik (syn_cxpk A A)))) (syn_wex y (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv z) (syn_csn (.cv w))) (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (syn_copk (.cv w) (.cv y)) (syn_cxpk A A)))))) (syn_wrex y A (.classEq (.cv x) (syn_csn (.cv y)))) p0002 p0008 p0031
  have p0033 :=
    @g_bitr4i (.classMem (.cv x) (syn_cpw1 A)) (syn_wrex y A (.classEq (.cv x) (syn_csn (.cv y)))) (.classMem (.cv x) (syn_cimak (syn_csik (syn_cxpk A A)) (syn_cvv))) p0000 p0032
  have p0034 :=
    @g_eqriv x (syn_cpw1 A) (syn_cimak (syn_csik (syn_cxpk A A)) (syn_cvv)) (by exact (show x ∉ ((syn_cpw1 A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show x ∉ (A).fv from (by exact fresh_x_not_A))))) (by exact (show x ∉ ((syn_cimak (syn_csik (syn_cxpk A A)) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak]; exact (show x ∉ (((syn_csik (syn_cxpk A A))).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_csik (syn_cxpk A A))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik]; exact (show x ∉ ((syn_cxpk A A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show x ∉ ((A).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ (A).fv from (by exact fresh_x_not_A)))))))) (show x ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0033
  exact p0034

noncomputable def g_pw1exg
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_cpw1 A) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  have p0000 :=
    @g_dfpw12 A
  have p0001 :=
    @g_xpkexg A A V V
  have p0002 :=
    @g_anidms (.classMem A V) (.classMem (syn_cxpk A A) (syn_cvv)) p0001
  have p0003 :=
    @g_sikexg (syn_cxpk A A) (syn_cvv)
  have p0004 :=
    @g_syl (.classMem A V) (.classMem (syn_cxpk A A) (syn_cvv)) (.classMem (syn_csik (syn_cxpk A A)) (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_vvex
  have p0006 :=
    @g_imakexg (syn_csik (syn_cxpk A A)) (syn_cvv) (syn_cvv) (syn_cvv)
  have p0007 :=
    @g_sylancl (.classMem A V) (.classMem (syn_csik (syn_cxpk A A)) (syn_cvv)) (.classMem (syn_cvv) (syn_cvv)) (.classMem (syn_cimak (syn_csik (syn_cxpk A A)) (syn_cvv)) (syn_cvv)) p0004 p0005 p0006
  have p0008 :=
    @g_syl5eqel (.classMem A V) (syn_cpw1 A) (syn_cimak (syn_csik (syn_cxpk A A)) (syn_cvv)) (syn_cvv) p0000 p0007
  exact p0008

noncomputable def g_pw1ex
    (A : Class) (hyp_pw1ex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cpw1 A) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_pw1exg A (syn_cvv)
  have p0001 :=
    Nominal.mp hyp_pw1ex_1 p0000
  exact p0001



#print axioms g_pw1ex

end NFChoice.DirectNominalPrf.WPPReplay
