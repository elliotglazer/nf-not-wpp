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
import NominalWPPReplayChunk009StructuralPart010


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

noncomputable def g_opkelimagekg
    (A : Class) (B : Class) (C : Class) (V : Class) (W : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem B W)) (syn_wb (.classMem (syn_copk A B) (syn_cimagek C)) (.classEq B (syn_cimak C A)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ V.fv ∪ W.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_C : x ∉ C.fv := by
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
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_C : y ∉ C.fv := by
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
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
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
    @g_elex A V
  have p0001 :=
    @g_elex B W
  have p0002 :=
    @g_opkelxpkg A B (syn_cvv) (syn_cvv) (syn_cvv) (syn_cvv)
  have p0003 :=
    @g_ibir (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (.classMem (syn_copk A B) (syn_cxpk (syn_cvv) (syn_cvv))) p0002
  have p0004 :=
    @g_biantrurd (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (.classMem (syn_copk A B) (syn_cxpk (syn_cvv) (syn_cvv))) (.neg (.classMem (syn_copk A B) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0003
  have p0005 :=
    @g_exnal (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) (syn_cimak C A))) x
  have p0006 :=
    @g_opkex A B
  have p0007 :=
    @g_elimak y (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))) (syn_cpw1 (syn_cpw1 (syn_c1c))) (syn_copk A B) (by exact (show y ∉ ((syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif]; exact (show y ∉ (((syn_cins2k (syn_cssetk))).fv) ∪ (((syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cins2k (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k]; exact (show y ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))) (show y ∉ ((syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k]; exact (show y ∉ ((syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk]; exact (show y ∉ (((syn_cssetk)).fv) ∪ (((syn_ccnvk (syn_csik C))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show y ∉ ((syn_ccnvk (syn_csik C))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk]; exact (show y ∉ ((syn_csik C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik]; exact (show y ∉ (C).fv from (by exact fresh_y_not_C))))))))))))))))) (by exact (show y ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show y ∉ ((syn_cpw1 (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show y ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) (by exact (show y ∉ ((syn_copk A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show y ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ (B).fv from (by exact fresh_y_not_B))))))) p0006
  have p0008 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_c1c))) (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))))))
  have p0009 :=
    @g_elpw121c x (.cv y) (by exact (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y)))))))
  have p0010 :=
    @g_anbi1i (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x)))))) (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))) p0009
  have p0011 :=
    @g_n_19_41v (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x))))) (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))) x (by exact (show x ∉ ((Wff.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((syn_copk (.cv y) (syn_copk A B))).fv) ∪ (((syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_copk (.cv y) (syn_copk A B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show x ∉ (((Class.cv y)).fv) ∪ (((syn_copk A B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y)))))) (show x ∉ ((syn_copk A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show x ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ (B).fv from (by exact fresh_x_not_B)))))))))) (show x ∉ ((syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif]; exact (show x ∉ (((syn_cins2k (syn_cssetk))).fv) ∪ (((syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cins2k (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k]; exact (show x ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))) (show x ∉ ((syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k]; exact (show x ∉ ((syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk]; exact (show x ∉ (((syn_cssetk)).fv) ∪ (((syn_ccnvk (syn_csik C))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show x ∉ ((syn_ccnvk (syn_csik C))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk]; exact (show x ∉ ((syn_csik C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik]; exact (show x ∉ (C).fv from (by exact fresh_x_not_C)))))))))))))))))))))
  have p0012 :=
    @g_bitr4i (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))))) (syn_wa (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x)))))) (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))))) (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x))))) (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))))) p0010 p0011
  have p0013 :=
    @g_exbii (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))))) (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x))))) (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))))) y p0012
  have p0014 :=
    @g_excom (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x))))) (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))))) y x
  have p0015 :=
    @g_snex (syn_csn (syn_csn (.cv x)))
  have p0016 :=
    @g_opkeq1 (.cv y) (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B)
  have p0017 :=
    @g_eleq1d (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_copk (.cv y) (syn_copk A B)) (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))) p0016
  have p0018 :=
    @g_ceqsexv (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))) y (syn_csn (syn_csn (syn_csn (.cv x)))) (by exact (show y ∉ ((syn_csn (syn_csn (syn_csn (.cv x))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))))))))) (by exact (show y ∉ ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B))).fv) ∪ (((syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show y ∉ (((syn_csn (syn_csn (syn_csn (.cv x))))).fv) ∪ (((syn_copk A B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_csn (syn_csn (syn_csn (.cv x))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))))))))) (show y ∉ ((syn_copk A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show y ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ (B).fv from (by exact fresh_y_not_B)))))))))) (show y ∉ ((syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif]; exact (show y ∉ (((syn_cins2k (syn_cssetk))).fv) ∪ (((syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cins2k (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k]; exact (show y ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))) (show y ∉ ((syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k]; exact (show y ∉ ((syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk]; exact (show y ∉ (((syn_cssetk)).fv) ∪ (((syn_ccnvk (syn_csik C))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show y ∉ ((syn_ccnvk (syn_csik C))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk]; exact (show y ∉ ((syn_csik C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik]; exact (show y ∉ (C).fv from (by exact fresh_y_not_C))))))))))))))))))))) p0015 p0017
  have p0019 :=
    @g_exbii (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x))))) (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))))) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))) x p0018
  have p0020 :=
    @g_n_3bitri (syn_wex y (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))))) (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x))))) (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))))))) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x))))) (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))))))) (syn_wex x (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))))) p0013 p0014 p0019
  have p0021 :=
    @g_n_3bitri (.classMem (syn_copk A B) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_c1c))) (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))))) (syn_wex y (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))))) (syn_wex x (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))))) p0007 p0008 p0020
  have p0022 :=
    @g_elsymdif (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B)) (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))
  have p0023 :=
    @g_snex (.cv x)
  have p0024 :=
    @g_otkelins2kg (syn_csn (.cv x)) A B (syn_cssetk) (syn_cvv) (syn_cvv) (syn_cvv)
  have p0025 :=
    @g_mp3an1 (.classMem (syn_csn (.cv x)) (syn_cvv)) (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B)) (syn_cins2k (syn_cssetk))) (.classMem (syn_copk (syn_csn (.cv x)) B) (syn_cssetk))) p0023 p0024
  have p0026 :=
    @g_vex x
  have p0027 :=
    @g_elssetkg (.cv x) B (syn_cvv) (syn_cvv)
  have p0028 :=
    @g_mpan (.classMem (.cv x) (syn_cvv)) (.classMem B (syn_cvv)) (syn_wb (.classMem (syn_copk (syn_csn (.cv x)) B) (syn_cssetk)) (.classMem (.cv x) B)) p0026 p0027
  have p0029 :=
    @g_adantl (.classMem B (syn_cvv)) (syn_wb (.classMem (syn_copk (syn_csn (.cv x)) B) (syn_cssetk)) (.classMem (.cv x) B)) (.classMem A (syn_cvv)) p0028
  have p0030 :=
    @g_bitrd (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B)) (syn_cins2k (syn_cssetk))) (.classMem (syn_copk (syn_csn (.cv x)) B) (syn_cssetk)) (.classMem (.cv x) B) p0025 p0029
  have p0031 :=
    @g_otkelins3kg (syn_csn (.cv x)) A B (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))) (syn_cvv) (syn_cvv) (syn_cvv)
  have p0032 :=
    @g_mp3an1 (.classMem (syn_csn (.cv x)) (syn_cvv)) (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))) (.classMem (syn_copk (syn_csn (.cv x)) A) (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))) p0023 p0031
  have p0033 :=
    @g_opkelcokg z (syn_csn (.cv x)) A (syn_cssetk) (syn_ccnvk (syn_csik C)) (syn_cvv) (syn_cvv) (by exact (show z ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x))))))))) (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A))) (by exact (show z ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show z ∉ ((syn_ccnvk (syn_csik C))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk]; exact (show z ∉ ((syn_csik C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik]; exact (show z ∉ (C).fv from (by exact fresh_z_not_C)))))))
  have p0034 :=
    @g_mpan (.classMem (syn_csn (.cv x)) (syn_cvv)) (.classMem A (syn_cvv)) (syn_wb (.classMem (syn_copk (syn_csn (.cv x)) A) (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))) (syn_wex z (syn_wa (.classMem (syn_copk (syn_csn (.cv x)) (.cv z)) (syn_ccnvk (syn_csik C))) (.classMem (syn_copk (.cv z) A) (syn_cssetk))))) p0023 p0033
  have p0035 :=
    @g_vex y
  have p0036 :=
    @g_elssetkg (.cv y) A (syn_cvv) (syn_cvv)
  have p0037 :=
    @g_mpan (.classMem (.cv y) (syn_cvv)) (.classMem A (syn_cvv)) (syn_wb (.classMem (syn_copk (syn_csn (.cv y)) A) (syn_cssetk)) (.classMem (.cv y) A)) p0035 p0036
  have p0038 :=
    @g_anbi1d (.classMem A (syn_cvv)) (.classMem (syn_copk (syn_csn (.cv y)) A) (syn_cssetk)) (.classMem (.cv y) A) (.classMem (syn_copk (.cv y) (.cv x)) C) p0037
  have p0039 :=
    @g_exbidv (.classMem A (syn_cvv)) (syn_wa (.classMem (syn_copk (syn_csn (.cv y)) A) (syn_cssetk)) (.classMem (syn_copk (.cv y) (.cv x)) C)) (syn_wa (.classMem (.cv y) A) (.classMem (syn_copk (.cv y) (.cv x)) C)) y (by exact (show y ∉ ((Wff.classMem A (syn_cvv))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ ((A).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0038
  have p0040 :=
    @g_vex z
  have p0041 :=
    @g_opkelcnvk (syn_csn (.cv x)) (.cv z) (syn_csik C) p0023 p0040
  have p0042 :=
    @g_sikss1c1c C
  have p0043 :=
    @g_sseli (syn_csik C) (syn_cxpk (syn_c1c) (syn_c1c)) (syn_copk (.cv z) (syn_csn (.cv x))) p0042
  have p0044 :=
    @g_opkelxpk (.cv z) (syn_csn (.cv x)) (syn_c1c) (syn_c1c) p0040 p0023
  have p0045 :=
    @g_el1c y (.cv z) (by exact (show y ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ z from (by exact fresh_y_ne_z)))))))
  have p0046 :=
    @g_biimpi (.classMem (.cv z) (syn_c1c)) (syn_wex y (.classEq (.cv z) (syn_csn (.cv y)))) p0045
  have p0047 :=
    @g_adantr (.classMem (.cv z) (syn_c1c)) (syn_wex y (.classEq (.cv z) (syn_csn (.cv y)))) (.classMem (syn_csn (.cv x)) (syn_c1c)) p0046
  have p0048 :=
    @g_sylbi (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_cxpk (syn_c1c) (syn_c1c))) (syn_wa (.classMem (.cv z) (syn_c1c)) (.classMem (syn_csn (.cv x)) (syn_c1c))) (syn_wex y (.classEq (.cv z) (syn_csn (.cv y)))) p0044 p0047
  have p0049 :=
    @g_syl (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C)) (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_cxpk (syn_c1c) (syn_c1c))) (syn_wex y (.classEq (.cv z) (syn_csn (.cv y)))) p0043 p0048
  have p0050 :=
    @g_pm4_71ri (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C)) (syn_wex y (.classEq (.cv z) (syn_csn (.cv y)))) p0049
  have p0051 :=
    @g_bitri (.classMem (syn_copk (syn_csn (.cv x)) (.cv z)) (syn_ccnvk (syn_csik C))) (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C)) (syn_wa (syn_wex y (.classEq (.cv z) (syn_csn (.cv y)))) (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C))) p0041 p0050
  have p0052 :=
    @g_anbi1i (.classMem (syn_copk (syn_csn (.cv x)) (.cv z)) (syn_ccnvk (syn_csik C))) (syn_wa (syn_wex y (.classEq (.cv z) (syn_csn (.cv y)))) (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C))) (.classMem (syn_copk (.cv z) A) (syn_cssetk)) p0051
  have p0053 :=
    @g_anass (syn_wex y (.classEq (.cv z) (syn_csn (.cv y)))) (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C)) (.classMem (syn_copk (.cv z) A) (syn_cssetk))
  have p0054 :=
    @g_n_19_41v (.classEq (.cv z) (syn_csn (.cv y))) (syn_wa (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C)) (.classMem (syn_copk (.cv z) A) (syn_cssetk))) y (by exact (show y ∉ ((syn_wa (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C)) (.classMem (syn_copk (.cv z) A) (syn_cssetk)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show y ∉ (((Wff.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C))).fv) ∪ (((Wff.classMem (syn_copk (.cv z) A) (syn_cssetk))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Wff.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((syn_copk (.cv z) (syn_csn (.cv x)))).fv) ∪ (((syn_csik C)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_copk (.cv z) (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show y ∉ (((Class.cv z)).fv) ∪ (((syn_csn (.cv x))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ z from (by exact fresh_y_ne_z)))))) (show y ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))))))))) (show y ∉ ((syn_csik C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik]; exact (show y ∉ (C).fv from (by exact fresh_y_not_C)))))))) (show y ∉ ((Wff.classMem (syn_copk (.cv z) A) (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((syn_copk (.cv z) A)).fv) ∪ (((syn_cssetk)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_copk (.cv z) A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show y ∉ (((Class.cv z)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ z from (by exact fresh_y_ne_z)))))) (show y ∉ (A).fv from (by exact fresh_y_not_A)))))) (show y ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))
  have p0055 :=
    @g_bitr4i (syn_wa (syn_wa (syn_wex y (.classEq (.cv z) (syn_csn (.cv y)))) (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C))) (.classMem (syn_copk (.cv z) A) (syn_cssetk))) (syn_wa (syn_wex y (.classEq (.cv z) (syn_csn (.cv y)))) (syn_wa (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C)) (.classMem (syn_copk (.cv z) A) (syn_cssetk)))) (syn_wex y (syn_wa (.classEq (.cv z) (syn_csn (.cv y))) (syn_wa (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C)) (.classMem (syn_copk (.cv z) A) (syn_cssetk))))) p0053 p0054
  have p0056 :=
    @g_bitri (syn_wa (.classMem (syn_copk (syn_csn (.cv x)) (.cv z)) (syn_ccnvk (syn_csik C))) (.classMem (syn_copk (.cv z) A) (syn_cssetk))) (syn_wa (syn_wa (syn_wex y (.classEq (.cv z) (syn_csn (.cv y)))) (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C))) (.classMem (syn_copk (.cv z) A) (syn_cssetk))) (syn_wex y (syn_wa (.classEq (.cv z) (syn_csn (.cv y))) (syn_wa (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C)) (.classMem (syn_copk (.cv z) A) (syn_cssetk))))) p0052 p0055
  have p0057 :=
    @g_exbii (syn_wa (.classMem (syn_copk (syn_csn (.cv x)) (.cv z)) (syn_ccnvk (syn_csik C))) (.classMem (syn_copk (.cv z) A) (syn_cssetk))) (syn_wex y (syn_wa (.classEq (.cv z) (syn_csn (.cv y))) (syn_wa (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C)) (.classMem (syn_copk (.cv z) A) (syn_cssetk))))) z p0056
  have p0058 :=
    @g_excom (syn_wa (.classEq (.cv z) (syn_csn (.cv y))) (syn_wa (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C)) (.classMem (syn_copk (.cv z) A) (syn_cssetk)))) z y
  have p0059 :=
    @g_snex (.cv y)
  have p0060 :=
    @g_opkeq1 (.cv z) (syn_csn (.cv y)) (syn_csn (.cv x))
  have p0061 :=
    @g_eleq1d (.classEq (.cv z) (syn_csn (.cv y))) (syn_copk (.cv z) (syn_csn (.cv x))) (syn_copk (syn_csn (.cv y)) (syn_csn (.cv x))) (syn_csik C) p0060
  have p0062 :=
    @g_opkeq1 (.cv z) (syn_csn (.cv y)) A
  have p0063 :=
    @g_eleq1d (.classEq (.cv z) (syn_csn (.cv y))) (syn_copk (.cv z) A) (syn_copk (syn_csn (.cv y)) A) (syn_cssetk) p0062
  have p0064 :=
    @g_anbi12d (.classEq (.cv z) (syn_csn (.cv y))) (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C)) (.classMem (syn_copk (syn_csn (.cv y)) (syn_csn (.cv x))) (syn_csik C)) (.classMem (syn_copk (.cv z) A) (syn_cssetk)) (.classMem (syn_copk (syn_csn (.cv y)) A) (syn_cssetk)) p0061 p0063
  have p0065 :=
    @g_ancom (.classMem (syn_copk (syn_csn (.cv y)) (syn_csn (.cv x))) (syn_csik C)) (.classMem (syn_copk (syn_csn (.cv y)) A) (syn_cssetk))
  have p0066 :=
    @g_opksnelsik (.cv y) (.cv x) C p0035 p0026
  have p0067 :=
    @g_anbi2i (.classMem (syn_copk (syn_csn (.cv y)) (syn_csn (.cv x))) (syn_csik C)) (.classMem (syn_copk (.cv y) (.cv x)) C) (.classMem (syn_copk (syn_csn (.cv y)) A) (syn_cssetk)) p0066
  have p0068 :=
    @g_bitri (syn_wa (.classMem (syn_copk (syn_csn (.cv y)) (syn_csn (.cv x))) (syn_csik C)) (.classMem (syn_copk (syn_csn (.cv y)) A) (syn_cssetk))) (syn_wa (.classMem (syn_copk (syn_csn (.cv y)) A) (syn_cssetk)) (.classMem (syn_copk (syn_csn (.cv y)) (syn_csn (.cv x))) (syn_csik C))) (syn_wa (.classMem (syn_copk (syn_csn (.cv y)) A) (syn_cssetk)) (.classMem (syn_copk (.cv y) (.cv x)) C)) p0065 p0067
  have p0069 :=
    @g_syl6bb (.classEq (.cv z) (syn_csn (.cv y))) (syn_wa (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C)) (.classMem (syn_copk (.cv z) A) (syn_cssetk))) (syn_wa (.classMem (syn_copk (syn_csn (.cv y)) (syn_csn (.cv x))) (syn_csik C)) (.classMem (syn_copk (syn_csn (.cv y)) A) (syn_cssetk))) (syn_wa (.classMem (syn_copk (syn_csn (.cv y)) A) (syn_cssetk)) (.classMem (syn_copk (.cv y) (.cv x)) C)) p0064 p0068
  have p0070 :=
    @g_ceqsexv (syn_wa (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C)) (.classMem (syn_copk (.cv z) A) (syn_cssetk))) (syn_wa (.classMem (syn_copk (syn_csn (.cv y)) A) (syn_cssetk)) (.classMem (syn_copk (.cv y) (.cv x)) C)) z (syn_csn (.cv y)) (by exact (show z ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y))))))))) (by exact (show z ∉ ((syn_wa (.classMem (syn_copk (syn_csn (.cv y)) A) (syn_cssetk)) (.classMem (syn_copk (.cv y) (.cv x)) C))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show z ∉ (((Wff.classMem (syn_copk (syn_csn (.cv y)) A) (syn_cssetk))).fv) ∪ (((Wff.classMem (syn_copk (.cv y) (.cv x)) C)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Wff.classMem (syn_copk (syn_csn (.cv y)) A) (syn_cssetk))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show z ∉ (((syn_copk (syn_csn (.cv y)) A)).fv) ∪ (((syn_cssetk)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_copk (syn_csn (.cv y)) A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show z ∉ (((syn_csn (.cv y))).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y)))))))) (show z ∉ (A).fv from (by exact fresh_z_not_A)))))) (show z ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show z ∉ ((Wff.classMem (syn_copk (.cv y) (.cv x)) C)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show z ∉ (((syn_copk (.cv y) (.cv x))).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_copk (.cv y) (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show z ∉ (((Class.cv y)).fv) ∪ (((Class.cv x)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y)))))) (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))))))) (show z ∉ (C).fv from (by exact fresh_z_not_C))))))))))) p0059 p0069
  have p0071 :=
    @g_exbii (syn_wex z (syn_wa (.classEq (.cv z) (syn_csn (.cv y))) (syn_wa (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C)) (.classMem (syn_copk (.cv z) A) (syn_cssetk))))) (syn_wa (.classMem (syn_copk (syn_csn (.cv y)) A) (syn_cssetk)) (.classMem (syn_copk (.cv y) (.cv x)) C)) y p0070
  have p0072 :=
    @g_n_3bitri (syn_wex z (syn_wa (.classMem (syn_copk (syn_csn (.cv x)) (.cv z)) (syn_ccnvk (syn_csik C))) (.classMem (syn_copk (.cv z) A) (syn_cssetk)))) (syn_wex z (syn_wex y (syn_wa (.classEq (.cv z) (syn_csn (.cv y))) (syn_wa (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C)) (.classMem (syn_copk (.cv z) A) (syn_cssetk)))))) (syn_wex y (syn_wex z (syn_wa (.classEq (.cv z) (syn_csn (.cv y))) (syn_wa (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C)) (.classMem (syn_copk (.cv z) A) (syn_cssetk)))))) (syn_wex y (syn_wa (.classMem (syn_copk (syn_csn (.cv y)) A) (syn_cssetk)) (.classMem (syn_copk (.cv y) (.cv x)) C))) p0057 p0058 p0071
  have p0073 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex y A (.classMem (syn_copk (.cv y) (.cv x)) C))))
  have p0074 :=
    @g_n_3bitr4g (.classMem A (syn_cvv)) (syn_wex y (syn_wa (.classMem (syn_copk (syn_csn (.cv y)) A) (syn_cssetk)) (.classMem (syn_copk (.cv y) (.cv x)) C))) (syn_wex y (syn_wa (.classMem (.cv y) A) (.classMem (syn_copk (.cv y) (.cv x)) C))) (syn_wex z (syn_wa (.classMem (syn_copk (syn_csn (.cv x)) (.cv z)) (syn_ccnvk (syn_csik C))) (.classMem (syn_copk (.cv z) A) (syn_cssetk)))) (syn_wrex y A (.classMem (syn_copk (.cv y) (.cv x)) C)) p0039 p0072 p0073
  have p0075 :=
    @g_bitrd (.classMem A (syn_cvv)) (.classMem (syn_copk (syn_csn (.cv x)) A) (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))) (syn_wex z (syn_wa (.classMem (syn_copk (syn_csn (.cv x)) (.cv z)) (syn_ccnvk (syn_csik C))) (.classMem (syn_copk (.cv z) A) (syn_cssetk)))) (syn_wrex y A (.classMem (syn_copk (.cv y) (.cv x)) C)) p0034 p0074
  have p0076 :=
    @g_elimak y C A (.cv x) (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C))) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))) p0026
  have p0077 :=
    @g_syl6bbr (.classMem A (syn_cvv)) (.classMem (syn_copk (syn_csn (.cv x)) A) (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))) (syn_wrex y A (.classMem (syn_copk (.cv y) (.cv x)) C)) (.classMem (.cv x) (syn_cimak C A)) p0075 p0076
  have p0078 :=
    @g_adantr (.classMem A (syn_cvv)) (syn_wb (.classMem (syn_copk (syn_csn (.cv x)) A) (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))) (.classMem (.cv x) (syn_cimak C A))) (.classMem B (syn_cvv)) p0077
  have p0079 :=
    @g_bitrd (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))) (.classMem (syn_copk (syn_csn (.cv x)) A) (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))) (.classMem (.cv x) (syn_cimak C A)) p0032 p0078
  have p0080 :=
    @g_bibi12d (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B)) (syn_cins2k (syn_cssetk))) (.classMem (.cv x) B) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))) (.classMem (.cv x) (syn_cimak C A)) p0030 p0079
  have p0081 :=
    @g_notbid (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B)) (syn_cins2k (syn_cssetk))) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))) (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) (syn_cimak C A))) p0080
  have p0082 :=
    @g_syl5bb (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))) (.neg (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B)) (syn_cins2k (syn_cssetk))) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))))) (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (.neg (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) (syn_cimak C A)))) p0022 p0081
  have p0083 :=
    @g_exbidv (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))) (.neg (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) (syn_cimak C A)))) x (by exact (show x ∉ ((syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show x ∉ (((Wff.classMem A (syn_cvv))).fv) ∪ (((Wff.classMem B (syn_cvv))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Wff.classMem A (syn_cvv))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ ((A).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show x ∉ ((Wff.classMem B (syn_cvv))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ ((B).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (B).fv from (by exact fresh_x_not_B)) (show x ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) p0082
  have p0084 :=
    @g_syl5rbb (.classMem (syn_copk A B) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_wex x (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))))) (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (syn_wex x (.neg (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) (syn_cimak C A))))) p0021 p0083
  have p0085 :=
    @g_syl5bbr (.neg (.all x (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) (syn_cimak C A))))) (syn_wex x (.neg (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) (syn_cimak C A))))) (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (.classMem (syn_copk A B) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0005 p0084
  have p0086 :=
    @g_con1bid (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (.all x (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) (syn_cimak C A)))) (.classMem (syn_copk A B) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0085
  have p0087 :=
    @g_bitr3d (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (.neg (.classMem (syn_copk A B) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_wa (.classMem (syn_copk A B) (syn_cxpk (syn_cvv) (syn_cvv))) (.neg (.classMem (syn_copk A B) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (.all x (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) (syn_cimak C A)))) p0004 p0086
  have p0088 :=
    (by simpa [syn_cimagek] using (Nominal.classEqRefl (syn_cimagek C)))
  have p0089 :=
    @g_eleq2i (syn_cimagek C) (syn_cdif (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_copk A B) p0088
  have p0090 :=
    @g_eldif (syn_copk A B) (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))
  have p0091 :=
    @g_bitri (.classMem (syn_copk A B) (syn_cimagek C)) (.classMem (syn_copk A B) (syn_cdif (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_wa (.classMem (syn_copk A B) (syn_cxpk (syn_cvv) (syn_cvv))) (.neg (.classMem (syn_copk A B) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) p0089 p0090
  have p0092 :=
    @g_dfcleq x B (syn_cimak C A) (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B))) (by exact (show x ∉ ((syn_cimak C A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak]; exact (show x ∉ ((C).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (C).fv from (by exact fresh_x_not_C)) (show x ∉ (A).fv from (by exact fresh_x_not_A)))))))
  have p0093 :=
    @g_n_3bitr4g (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (syn_wa (.classMem (syn_copk A B) (syn_cxpk (syn_cvv) (syn_cvv))) (.neg (.classMem (syn_copk A B) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (.all x (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) (syn_cimak C A)))) (.classMem (syn_copk A B) (syn_cimagek C)) (.classEq B (syn_cimak C A)) p0087 p0091 p0092
  have p0094 :=
    @g_syl2an (.classMem A V) (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (syn_wb (.classMem (syn_copk A B) (syn_cimagek C)) (.classEq B (syn_cimak C A))) (.classMem B W) p0000 p0001 p0093
  exact p0094

noncomputable def g_opkelimagek
    (A : Class) (B : Class) (C : Class) (hyp_opkelimagek_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_opkelimagek_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem (syn_copk A B) (syn_cimagek C)) (.classEq B (syn_cimak C A))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_opkelimagekg A B C (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (syn_wb (.classMem (syn_copk A B) (syn_cimagek C)) (.classEq B (syn_cimak C A))) hyp_opkelimagek_1 hyp_opkelimagek_2 p0000
  exact p0001

noncomputable def g_opkelidkg
    (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem B W)) (syn_wb (.classMem (syn_copk A B) (syn_cidk)) (.classEq A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
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
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_idk z x y (show z ≠ x from (by exact fresh_z_ne_x)) (show z ≠ y from (by exact fresh_z_ne_y)) (show x ≠ y from (by exact fresh_x_ne_y))
  have p0001 :=
    @g_eqeq1 (.cv x) A (.cv y)
  have p0002 :=
    @g_eqeq2 (.cv y) B A
  have p0003_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb (.objEq x y) (.classEq A (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0001
  have p0003 :=
    @g_opkelopkabg (.objEq x y) (.classEq A (.cv y)) (.classEq A B) z x y (syn_cidk) A B V W (by exact (show x ∉ ((syn_cidk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show y ∉ ((syn_cidk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A))) (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B))) (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B))) (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B))) (by exact (show y ∉ ((Wff.classEq A B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ (B).fv from (by exact fresh_y_not_B))))))) (by exact (show z ∉ ((Wff.objEq x y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]; exact (show z ∉ ({x, y} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show z ≠ x from (by exact fresh_z_ne_x)), (show z ≠ y from (by exact fresh_z_ne_y))⟩))))) (by exact (show x ∉ ((Wff.classEq A (.cv y))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ ((A).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y))))))))))) (show z ≠ x from (by exact fresh_z_ne_x)) (show z ≠ y from (by exact fresh_z_ne_y)) (show x ≠ y from (by exact fresh_x_ne_y)) p0000 p0003_e01_recanon p0002
  exact p0003

noncomputable def g_cnvkssvvk
    (A : Class) :
    Nominal.NPrf (syn_wss (syn_ccnvk A) (syn_cxpk (syn_cvv) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv
  let z : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_z_ne_y : z ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_ne_x : z ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_cnvk x y z A (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A))) (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z)) (show y ≠ z from (by exact fresh_y_ne_z))
  have p0001 :=
    @g_opkabssvvki (.classMem (syn_copk (.cv z) (.cv y)) A) x y z (syn_ccnvk A) (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z)) p0000
  exact p0001

noncomputable def g_cnvkxpk
    (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_ccnvk (syn_cxpk A B)) (syn_cxpk B A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
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
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have p0000 :=
    @g_cnvkssvvk (syn_cxpk A B)
  have p0001 :=
    @g_xpkssvvk B A
  have p0002 :=
    @g_ancom (.classMem (.cv y) A) (.classMem (.cv x) B)
  have p0003 :=
    @g_vex x
  have p0004 :=
    @g_vex y
  have p0005 :=
    @g_opkelcnvk (.cv x) (.cv y) (syn_cxpk A B) p0003 p0004
  have p0006 :=
    @g_opkelxpk (.cv y) (.cv x) A B p0004 p0003
  have p0007 :=
    @g_bitri (.classMem (syn_copk (.cv x) (.cv y)) (syn_ccnvk (syn_cxpk A B))) (.classMem (syn_copk (.cv y) (.cv x)) (syn_cxpk A B)) (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) B)) p0005 p0006
  have p0008 :=
    @g_opkelxpk (.cv x) (.cv y) B A p0003 p0004
  have p0009 :=
    @g_n_3bitr4i (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) B)) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) A)) (.classMem (syn_copk (.cv x) (.cv y)) (syn_ccnvk (syn_cxpk A B))) (.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk B A)) p0002 p0007 p0008
  have p0010 :=
    @g_eqrelkriiv x y (syn_ccnvk (syn_cxpk A B)) (syn_cxpk B A) (by exact (show x ∉ ((syn_ccnvk (syn_cxpk A B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk]; exact (show x ∉ ((syn_cxpk A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show x ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ (B).fv from (by exact fresh_x_not_B))))))))) (by exact (show y ∉ ((syn_ccnvk (syn_cxpk A B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk]; exact (show y ∉ ((syn_cxpk A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show y ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ (B).fv from (by exact fresh_y_not_B))))))))) (by exact (show x ∉ ((syn_cxpk B A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show x ∉ ((B).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (B).fv from (by exact fresh_x_not_B)) (show x ∉ (A).fv from (by exact fresh_x_not_A))))))) (by exact (show y ∉ ((syn_cxpk B A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show y ∉ ((B).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (B).fv from (by exact fresh_y_not_B)) (show y ∉ (A).fv from (by exact fresh_y_not_A))))))) (show x ≠ y from (by exact fresh_x_ne_y)) p0000 p0001 p0009
  exact p0010



#print axioms g_cnvkxpk

end NFChoice.DirectNominalPrf.WPPReplay
