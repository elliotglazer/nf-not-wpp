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
import NominalWPPReplayChunk009StructuralPart001


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

noncomputable def g_df1c2
     :
    Nominal.NPrf (.classEq (syn_c1c) (syn_cpw1 (syn_cvv))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have p0000 :=
    @g_rexv (.classEq (.cv x) (syn_csn (.cv y))) y
  have p0001 :=
    @g_elpw1 y (.cv x) (syn_cvv) (by exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))) (by exact (show y ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0002 :=
    @g_el1c y (.cv x) (by exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))))
  have p0003 :=
    @g_n_3bitr4ri (syn_wrex y (syn_cvv) (.classEq (.cv x) (syn_csn (.cv y)))) (syn_wex y (.classEq (.cv x) (syn_csn (.cv y)))) (.classMem (.cv x) (syn_cpw1 (syn_cvv))) (.classMem (.cv x) (syn_c1c)) p0000 p0001 p0002
  have p0004 :=
    @g_eqriv x (syn_c1c) (syn_cpw1 (syn_cvv)) (by exact (show x ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show x ∉ ((syn_cpw1 (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show x ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))) p0003
  exact p0004

noncomputable def g_pw1ss
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wss A B) (syn_wss (syn_cpw1 A) (syn_cpw1 B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_sspwb A B
  have p0001 :=
    @g_ssrin (syn_cpw A) (syn_cpw B) (syn_c1c)
  have p0002 :=
    @g_sylbi (syn_wss A B) (syn_wss (syn_cpw A) (syn_cpw B)) (syn_wss (syn_cin (syn_cpw A) (syn_c1c)) (syn_cin (syn_cpw B) (syn_c1c))) p0000 p0001
  have p0003 :=
    (by simpa [syn_cpw1] using (Nominal.classEqRefl (syn_cpw1 A)))
  have p0004 :=
    (by simpa [syn_cpw1] using (Nominal.classEqRefl (syn_cpw1 B)))
  have p0005 :=
    @g_n_3sstr4g (syn_wss A B) (syn_cin (syn_cpw A) (syn_c1c)) (syn_cin (syn_cpw B) (syn_c1c)) (syn_cpw1 A) (syn_cpw1 B) p0002 p0003 p0004
  exact p0005

noncomputable def g_pw111
    (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (.classEq (syn_cpw1 A) (syn_cpw1 B)) (.classEq A B)) := by
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
    @g_snex (.cv x)
  have p0001 :=
    @g_eleq1 (.cv t) (syn_csn (.cv x)) (syn_cpw1 A)
  have p0002 :=
    @g_eleq1 (.cv t) (syn_csn (.cv x)) (syn_cpw1 B)
  have p0003 :=
    @g_bibi12d (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (.cv t) (syn_cpw1 A)) (.classMem (syn_csn (.cv x)) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B)) (.classMem (syn_csn (.cv x)) (syn_cpw1 B)) p0001 p0002
  have p0004 :=
    @g_ceqsalv (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B))) (syn_wb (.classMem (syn_csn (.cv x)) (syn_cpw1 A)) (.classMem (syn_csn (.cv x)) (syn_cpw1 B))) t (syn_csn (.cv x)) (by exact (show t ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ x from (by exact fresh_t_ne_x))))))))) (by exact (show t ∉ ((syn_wb (.classMem (syn_csn (.cv x)) (syn_cpw1 A)) (.classMem (syn_csn (.cv x)) (syn_cpw1 B)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb]; exact (show t ∉ (((Wff.classMem (syn_csn (.cv x)) (syn_cpw1 A))).fv) ∪ (((Wff.classMem (syn_csn (.cv x)) (syn_cpw1 B))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((Wff.classMem (syn_csn (.cv x)) (syn_cpw1 A))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show t ∉ (((syn_csn (.cv x))).fv) ∪ (((syn_cpw1 A)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ x from (by exact fresh_t_ne_x)))))))) (show t ∉ ((syn_cpw1 A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show t ∉ (A).fv from (by exact fresh_t_not_A)))))))) (show t ∉ ((Wff.classMem (syn_csn (.cv x)) (syn_cpw1 B))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show t ∉ (((syn_csn (.cv x))).fv) ∪ (((syn_cpw1 B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ x from (by exact fresh_t_ne_x)))))))) (show t ∉ ((syn_cpw1 B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show t ∉ (B).fv from (by exact fresh_t_not_B))))))))))))) p0000 p0003
  have p0005 :=
    @g_snelpw1 (.cv x) A
  have p0006 :=
    @g_snelpw1 (.cv x) B
  have p0007 :=
    @g_bibi12i (.classMem (syn_csn (.cv x)) (syn_cpw1 A)) (.classMem (.cv x) A) (.classMem (syn_csn (.cv x)) (syn_cpw1 B)) (.classMem (.cv x) B) p0005 p0006
  have p0008 :=
    @g_bitri (.all t (.imp (.classEq (.cv t) (syn_csn (.cv x))) (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B))))) (syn_wb (.classMem (syn_csn (.cv x)) (syn_cpw1 A)) (.classMem (syn_csn (.cv x)) (syn_cpw1 B))) (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B)) p0004 p0007
  have p0009 :=
    @g_albii (.all t (.imp (.classEq (.cv t) (syn_csn (.cv x))) (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B))))) (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B)) x p0008
  have p0010 :=
    @g_pw1ss1c A
  have p0011 :=
    @g_pw1ss1c B
  have p0012 :=
    @g_ssofeq t (syn_cpw1 A) (syn_cpw1 B) (syn_c1c) (by exact (show t ∉ ((syn_cpw1 A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show t ∉ (A).fv from (by exact fresh_t_not_A))))) (by exact (show t ∉ ((syn_cpw1 B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show t ∉ (B).fv from (by exact fresh_t_not_B))))) (by exact (show t ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0013 :=
    @g_mp2an (syn_wss (syn_cpw1 A) (syn_c1c)) (syn_wss (syn_cpw1 B) (syn_c1c)) (syn_wb (.classEq (syn_cpw1 A) (syn_cpw1 B)) (syn_wral t (syn_c1c) (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B))))) p0010 p0011 p0012
  have p0014 :=
    (by simpa [syn_wb, syn_wral] using (Nominal.biimpRefl (syn_wral t (syn_c1c) (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B))))))
  have p0015 :=
    @g_el1c x (.cv t) (by exact (show x ∉ ((Class.cv t)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({t} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ t from (by exact fresh_x_ne_t)))))))
  have p0016 :=
    @g_imbi1i (.classMem (.cv t) (syn_c1c)) (syn_wex x (.classEq (.cv t) (syn_csn (.cv x)))) (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B))) p0015
  have p0017 :=
    @g_n_19_23v (.classEq (.cv t) (syn_csn (.cv x))) (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B))) x (by exact (show x ∉ ((syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb]; exact (show x ∉ (((Wff.classMem (.cv t) (syn_cpw1 A))).fv) ∪ (((Wff.classMem (.cv t) (syn_cpw1 B))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Wff.classMem (.cv t) (syn_cpw1 A))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((Class.cv t)).fv) ∪ (((syn_cpw1 A)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv t)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({t} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ t from (by exact fresh_x_ne_t)))))) (show x ∉ ((syn_cpw1 A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))))))) (show x ∉ ((Wff.classMem (.cv t) (syn_cpw1 B))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((Class.cv t)).fv) ∪ (((syn_cpw1 B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv t)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({t} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ t from (by exact fresh_x_ne_t)))))) (show x ∉ ((syn_cpw1 B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))))))))))))
  have p0018 :=
    @g_bitr4i (.imp (.classMem (.cv t) (syn_c1c)) (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B)))) (.imp (syn_wex x (.classEq (.cv t) (syn_csn (.cv x)))) (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B)))) (.all x (.imp (.classEq (.cv t) (syn_csn (.cv x))) (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B))))) p0016 p0017
  have p0019 :=
    @g_albii (.imp (.classMem (.cv t) (syn_c1c)) (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B)))) (.all x (.imp (.classEq (.cv t) (syn_csn (.cv x))) (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B))))) t p0018
  have p0020 :=
    @g_alcom (.imp (.classEq (.cv t) (syn_csn (.cv x))) (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B)))) t x
  have p0021 :=
    @g_bitri (.all t (.imp (.classMem (.cv t) (syn_c1c)) (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B))))) (.all t (.all x (.imp (.classEq (.cv t) (syn_csn (.cv x))) (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B)))))) (.all x (.all t (.imp (.classEq (.cv t) (syn_csn (.cv x))) (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B)))))) p0019 p0020
  have p0022 :=
    @g_bitri (syn_wral t (syn_c1c) (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B)))) (.all t (.imp (.classMem (.cv t) (syn_c1c)) (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B))))) (.all x (.all t (.imp (.classEq (.cv t) (syn_csn (.cv x))) (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B)))))) p0014 p0021
  have p0023 :=
    @g_bitri (.classEq (syn_cpw1 A) (syn_cpw1 B)) (syn_wral t (syn_c1c) (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B)))) (.all x (.all t (.imp (.classEq (.cv t) (syn_csn (.cv x))) (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B)))))) p0013 p0022
  have p0024 :=
    @g_dfcleq x A B (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
  have p0025 :=
    @g_n_3bitr4i (.all x (.all t (.imp (.classEq (.cv t) (syn_csn (.cv x))) (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B)))))) (.all x (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B))) (.classEq (syn_cpw1 A) (syn_cpw1 B)) (.classEq A B) p0009 p0023 p0024
  exact p0025

noncomputable def g_eluni1g
    (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (syn_wb (.classMem A (syn_cuni1 B)) (.classMem (syn_csn A) B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_V : y ∉ V.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have p0000 :=
    (by simpa [syn_cuni1] using (Nominal.classEqRefl (syn_cuni1 B)))
  have p0001 :=
    @g_eleq2i (syn_cuni1 B) (syn_cuni (syn_cin B (syn_c1c))) A p0000
  have p0002 :=
    @g_eluni x A (syn_cin B (syn_c1c)) (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show x ∉ ((syn_cin B (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show x ∉ ((B).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (B).fv from (by exact fresh_x_not_B)) (show x ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))
  have p0003 :=
    @g_elin (.cv x) B (syn_c1c)
  have p0004 :=
    @g_ancom (.classMem (.cv x) B) (.classMem (.cv x) (syn_c1c))
  have p0005 :=
    @g_el1c y (.cv x) (by exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))))
  have p0006 :=
    @g_anbi1i (.classMem (.cv x) (syn_c1c)) (syn_wex y (.classEq (.cv x) (syn_csn (.cv y)))) (.classMem (.cv x) B) p0005
  have p0007 :=
    @g_n_19_41v (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) B) y (by exact (show y ∉ ((Wff.classMem (.cv x) B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((Class.cv x)).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))) (show y ∉ (B).fv from (by exact fresh_y_not_B)))))))
  have p0008 :=
    @g_bitr4i (syn_wa (.classMem (.cv x) (syn_c1c)) (.classMem (.cv x) B)) (syn_wa (syn_wex y (.classEq (.cv x) (syn_csn (.cv y)))) (.classMem (.cv x) B)) (syn_wex y (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) B))) p0006 p0007
  have p0009 :=
    @g_n_3bitri (.classMem (.cv x) (syn_cin B (syn_c1c))) (syn_wa (.classMem (.cv x) B) (.classMem (.cv x) (syn_c1c))) (syn_wa (.classMem (.cv x) (syn_c1c)) (.classMem (.cv x) B)) (syn_wex y (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) B))) p0003 p0004 p0008
  have p0010 :=
    @g_anbi2i (.classMem (.cv x) (syn_cin B (syn_c1c))) (syn_wex y (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) B))) (.classMem A (.cv x)) p0009
  have p0011 :=
    @g_n_19_42v (.classMem A (.cv x)) (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) B)) y (by exact (show y ∉ ((Wff.classMem A (.cv x))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ ((A).fv) ∪ (((Class.cv x)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))))))))
  have p0012 :=
    @g_bitr4i (syn_wa (.classMem A (.cv x)) (.classMem (.cv x) (syn_cin B (syn_c1c)))) (syn_wa (.classMem A (.cv x)) (syn_wex y (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) B)))) (syn_wex y (syn_wa (.classMem A (.cv x)) (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) B)))) p0010 p0011
  have p0013 :=
    @g_exbii (syn_wa (.classMem A (.cv x)) (.classMem (.cv x) (syn_cin B (syn_c1c)))) (syn_wex y (syn_wa (.classMem A (.cv x)) (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) B)))) x p0012
  have p0014 :=
    @g_excom (syn_wa (.classMem A (.cv x)) (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) B))) x y
  have p0015 :=
    @g_an12 (.classMem A (.cv x)) (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) B)
  have p0016 :=
    @g_exbii (syn_wa (.classMem A (.cv x)) (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) B))) (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (syn_wa (.classMem A (.cv x)) (.classMem (.cv x) B))) x p0015
  have p0017 :=
    @g_snex (.cv y)
  have p0018 :=
    @g_eleq2 (.cv x) (syn_csn (.cv y)) A
  have p0019 :=
    @g_vex y
  have p0020 :=
    @g_elsnc2 A (.cv y) p0019
  have p0021 :=
    @g_syl6bb (.classEq (.cv x) (syn_csn (.cv y))) (.classMem A (.cv x)) (.classMem A (syn_csn (.cv y))) (.classEq A (.cv y)) p0018 p0020
  have p0022 :=
    @g_eleq1 (.cv x) (syn_csn (.cv y)) B
  have p0023 :=
    @g_anbi12d (.classEq (.cv x) (syn_csn (.cv y))) (.classMem A (.cv x)) (.classEq A (.cv y)) (.classMem (.cv x) B) (.classMem (syn_csn (.cv y)) B) p0021 p0022
  have p0024 :=
    @g_ceqsexv (syn_wa (.classMem A (.cv x)) (.classMem (.cv x) B)) (syn_wa (.classEq A (.cv y)) (.classMem (syn_csn (.cv y)) B)) x (syn_csn (.cv y)) (by exact (show x ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y))))))))) (by exact (show x ∉ ((syn_wa (.classEq A (.cv y)) (.classMem (syn_csn (.cv y)) B))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show x ∉ (((Wff.classEq A (.cv y))).fv) ∪ (((Wff.classMem (syn_csn (.cv y)) B)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Wff.classEq A (.cv y))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ ((A).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y)))))))))) (show x ∉ ((Wff.classMem (syn_csn (.cv y)) B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((syn_csn (.cv y))).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y)))))))) (show x ∉ (B).fv from (by exact fresh_x_not_B))))))))))) p0017 p0023
  have p0025 :=
    @g_eqcom A (.cv y)
  have p0026 :=
    @g_anbi1i (.classEq A (.cv y)) (.classEq (.cv y) A) (.classMem (syn_csn (.cv y)) B) p0025
  have p0027 :=
    @g_n_3bitri (syn_wex x (syn_wa (.classMem A (.cv x)) (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) B)))) (syn_wex x (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (syn_wa (.classMem A (.cv x)) (.classMem (.cv x) B)))) (syn_wa (.classEq A (.cv y)) (.classMem (syn_csn (.cv y)) B)) (syn_wa (.classEq (.cv y) A) (.classMem (syn_csn (.cv y)) B)) p0016 p0024 p0026
  have p0028 :=
    @g_exbii (syn_wex x (syn_wa (.classMem A (.cv x)) (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) B)))) (syn_wa (.classEq (.cv y) A) (.classMem (syn_csn (.cv y)) B)) y p0027
  have p0029 :=
    @g_n_3bitri (syn_wex x (syn_wa (.classMem A (.cv x)) (.classMem (.cv x) (syn_cin B (syn_c1c))))) (syn_wex x (syn_wex y (syn_wa (.classMem A (.cv x)) (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) B))))) (syn_wex y (syn_wex x (syn_wa (.classMem A (.cv x)) (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) B))))) (syn_wex y (syn_wa (.classEq (.cv y) A) (.classMem (syn_csn (.cv y)) B))) p0013 p0014 p0028
  have p0030 :=
    @g_n_3bitri (.classMem A (syn_cuni1 B)) (.classMem A (syn_cuni (syn_cin B (syn_c1c)))) (syn_wex x (syn_wa (.classMem A (.cv x)) (.classMem (.cv x) (syn_cin B (syn_c1c))))) (syn_wex y (syn_wa (.classEq (.cv y) A) (.classMem (syn_csn (.cv y)) B))) p0001 p0002 p0029
  have p0031 :=
    @g_sneq (.cv y) A
  have p0032 :=
    @g_eleq1d (.classEq (.cv y) A) (syn_csn (.cv y)) (syn_csn A) B p0031
  have p0033 :=
    @g_ceqsexgv (.classMem (syn_csn (.cv y)) B) (.classMem (syn_csn A) B) y A V (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show y ∉ ((Wff.classMem (syn_csn A) B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((syn_csn A)).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_csn A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))) (show y ∉ (B).fv from (by exact fresh_y_not_B))))))) p0032
  have p0034 :=
    @g_syl5bb (.classMem A (syn_cuni1 B)) (syn_wex y (syn_wa (.classEq (.cv y) A) (.classMem (syn_csn (.cv y)) B))) (.classMem A V) (.classMem (syn_csn A) B) p0030 p0033
  exact p0034

noncomputable def g_eluni1
    (A : Class) (B : Class) (hyp_eluni1_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cuni1 B)) (.classMem (syn_csn A) B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_eluni1g A B (syn_cvv)
  have p0001 :=
    Nominal.mp hyp_eluni1_1 p0000
  exact p0001

noncomputable def g_elxpk
    (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cxpk B C)) (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  let w : Var := freshVar proofSupport 0
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
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_C : w ∉ C.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_elex A (syn_cxpk B C)
  have p0001 :=
    @g_opkex (.cv x) (.cv y)
  have p0002 :=
    @g_eleq1 A (syn_copk (.cv x) (.cv y)) (syn_cvv)
  have p0003 :=
    @g_mpbiri (.classEq A (syn_copk (.cv x) (.cv y))) (.classMem A (syn_cvv)) (.classMem (syn_copk (.cv x) (.cv y)) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_adantr (.classEq A (syn_copk (.cv x) (.cv y))) (.classMem A (syn_cvv)) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C)) p0003
  have p0005 :=
    @g_exlimivv (syn_wa (.classEq A (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C))) (.classMem A (syn_cvv)) x y (by exact (show x ∉ ((Wff.classMem A (syn_cvv))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ ((A).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact dv_A_x)) (show x ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) (by exact (show y ∉ ((Wff.classMem A (syn_cvv))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ ((A).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact dv_A_y)) (show y ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0004
  have p0006 :=
    @g_eqeq1 (.cv w) A (syn_copk (.cv x) (.cv y))
  have p0007 :=
    @g_anbi1d (.classEq (.cv w) A) (.classEq (.cv w) (syn_copk (.cv x) (.cv y))) (.classEq A (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C)) p0006
  have p0008 :=
    @g_n_2exbidv (.classEq (.cv w) A) (syn_wa (.classEq (.cv w) (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C))) (syn_wa (.classEq A (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C))) x y (by exact (show x ∉ ((Wff.classEq (.cv w) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ (((Class.cv w)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv w)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({w} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ w from (by exact fresh_x_ne_w)))))) (show x ∉ (A).fv from (by exact dv_A_x))))))) (by exact (show y ∉ ((Wff.classEq (.cv w) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ (((Class.cv w)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv w)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({w} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ w from (by exact fresh_y_ne_w)))))) (show y ∉ (A).fv from (by exact dv_A_y))))))) p0007
  have p0009 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xpk w x y B C (by exact (show w ∉ (B).fv from (by exact fresh_w_not_B))) (by exact (show x ∉ (B).fv from (by exact dv_B_x))) (by exact (show y ∉ (B).fv from (by exact dv_B_y))) (by exact (show w ∉ (C).fv from (by exact fresh_w_not_C))) (by exact (show x ∉ (C).fv from (by exact dv_C_x))) (by exact (show y ∉ (C).fv from (by exact dv_C_y))) (show w ≠ x from (by exact fresh_w_ne_x)) (show w ≠ y from (by exact fresh_w_ne_y)) (show x ≠ y from (by exact dv_x_y))
  have p0010 :=
    @g_elab2g (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C))))) (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C))))) w A (syn_cxpk B C) (syn_cvv) (by exact (show w ∉ (A).fv from (by exact fresh_w_not_A))) (by exact (show w ∉ ((syn_wex x (syn_wex y (syn_wa (.classEq A (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex]; exact (show w ∉ (((syn_wex y (syn_wa (.classEq A (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C))))).fv).erase x from (fun hmem => (show w ∉ ((syn_wex y (syn_wa (.classEq A (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex]; exact (show w ∉ (((syn_wa (.classEq A (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C)))).fv).erase y from (fun hmem => (show w ∉ ((syn_wa (.classEq A (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show w ∉ (((Wff.classEq A (syn_copk (.cv x) (.cv y)))).fv) ∪ (((syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Wff.classEq A (syn_copk (.cv x) (.cv y)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show w ∉ ((A).fv) ∪ (((syn_copk (.cv x) (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ (A).fv from (by exact fresh_w_not_A)) (show w ∉ ((syn_copk (.cv x) (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show w ∉ (((Class.cv x)).fv) ∪ (((Class.cv y)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ x from (by exact fresh_w_ne_x)))))) (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y)))))))))))))) (show w ∉ ((syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show w ∉ (((Wff.classMem (.cv x) B)).fv) ∪ (((Wff.classMem (.cv y) C)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Wff.classMem (.cv x) B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show w ∉ (((Class.cv x)).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ x from (by exact fresh_w_ne_x)))))) (show w ∉ (B).fv from (by exact fresh_w_not_B)))))) (show w ∉ ((Wff.classMem (.cv y) C)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show w ∉ (((Class.cv y)).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y)))))) (show w ∉ (C).fv from (by exact fresh_w_not_C)))))))))))))) (Finset.mem_of_mem_erase hmem))))) (Finset.mem_of_mem_erase hmem)))))) p0008 p0009
  have p0011 :=
    @g_pm5_21nii (.classMem A (syn_cxpk B C)) (.classMem A (syn_cvv)) (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C))))) p0000 p0005 p0010
  exact p0011

noncomputable def g_elxpk2
    (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cxpk B C)) (syn_wrex x B (syn_wrex y C (.classEq A (syn_copk (.cv x) (.cv y)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_ancom (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C)) (.classEq A (syn_copk (.cv x) (.cv y)))
  have p0001 :=
    @g_n_2exbii (syn_wa (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C)) (.classEq A (syn_copk (.cv x) (.cv y)))) (syn_wa (.classEq A (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C))) x y p0000
  have p0002 :=
    @g_r2ex (.classEq A (syn_copk (.cv x) (.cv y))) x y B C (by exact (show y ∉ (B).fv from (by exact dv_B_y))) (show x ≠ y from (by exact dv_x_y))
  have p0003 :=
    @g_elxpk x y A B C (by exact (show x ∉ (A).fv from (by exact dv_A_x))) (by exact (show y ∉ (A).fv from (by exact dv_A_y))) (by exact (show x ∉ (B).fv from (by exact dv_B_x))) (by exact (show y ∉ (B).fv from (by exact dv_B_y))) (by exact (show x ∉ (C).fv from (by exact dv_C_x))) (by exact (show y ∉ (C).fv from (by exact dv_C_y))) (show x ≠ y from (by exact dv_x_y))
  have p0004 :=
    @g_n_3bitr4ri (syn_wex x (syn_wex y (syn_wa (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C)) (.classEq A (syn_copk (.cv x) (.cv y)))))) (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C))))) (syn_wrex x B (syn_wrex y C (.classEq A (syn_copk (.cv x) (.cv y))))) (.classMem A (syn_cxpk B C)) p0001 p0002 p0003
  exact p0004

noncomputable def g_xpkeq1
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cxpk A C) (syn_cxpk B C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
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
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_C : z ∉ C.fv := by
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
    @g_rexeq (syn_wrex z C (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))) y A B (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
  have p0001 :=
    @g_elxpk2 y z (.cv x) A C (by exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))) (by exact (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x))))))) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A))) (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C))) (by exact (show z ∉ (C).fv from (by exact fresh_z_not_C))) (show y ≠ z from (by exact fresh_y_ne_z))
  have p0002 :=
    @g_elxpk2 y z (.cv x) B C (by exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))) (by exact (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x))))))) (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B))) (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B))) (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C))) (by exact (show z ∉ (C).fv from (by exact fresh_z_not_C))) (show y ≠ z from (by exact fresh_y_ne_z))
  have p0003 :=
    @g_n_3bitr4g (.classEq A B) (syn_wrex y A (syn_wrex z C (.classEq (.cv x) (syn_copk (.cv y) (.cv z))))) (syn_wrex y B (syn_wrex z C (.classEq (.cv x) (syn_copk (.cv y) (.cv z))))) (.classMem (.cv x) (syn_cxpk A C)) (.classMem (.cv x) (syn_cxpk B C)) p0000 p0001 p0002
  have p0004 :=
    @g_eqrdv (.classEq A B) x (syn_cxpk A C) (syn_cxpk B C) (by exact (show x ∉ ((syn_cxpk A C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show x ∉ ((A).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ (C).fv from (by exact fresh_x_not_C))))))) (by exact (show x ∉ ((syn_cxpk B C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show x ∉ ((B).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (B).fv from (by exact fresh_x_not_B)) (show x ∉ (C).fv from (by exact fresh_x_not_C))))))) (by exact (show x ∉ ((Wff.classEq A B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ (B).fv from (by exact fresh_x_not_B))))))) p0003
  exact p0004

noncomputable def g_xpkeq2
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cxpk C A) (syn_cxpk C B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
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
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_C : z ∉ C.fv := by
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
    @g_rexeq (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) z A B (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A))) (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B)))
  have p0001 :=
    @g_rexbidv (.classEq A B) (syn_wrex z A (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))) (syn_wrex z B (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))) y C (by exact (show y ∉ ((Wff.classEq A B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ (B).fv from (by exact fresh_y_not_B))))))) p0000
  have p0002 :=
    @g_elxpk2 y z (.cv x) C A (by exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))) (by exact (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x))))))) (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C))) (by exact (show z ∉ (C).fv from (by exact fresh_z_not_C))) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A))) (show y ≠ z from (by exact fresh_y_ne_z))
  have p0003 :=
    @g_elxpk2 y z (.cv x) C B (by exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))) (by exact (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x))))))) (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C))) (by exact (show z ∉ (C).fv from (by exact fresh_z_not_C))) (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B))) (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B))) (show y ≠ z from (by exact fresh_y_ne_z))
  have p0004 :=
    @g_n_3bitr4g (.classEq A B) (syn_wrex y C (syn_wrex z A (.classEq (.cv x) (syn_copk (.cv y) (.cv z))))) (syn_wrex y C (syn_wrex z B (.classEq (.cv x) (syn_copk (.cv y) (.cv z))))) (.classMem (.cv x) (syn_cxpk C A)) (.classMem (.cv x) (syn_cxpk C B)) p0001 p0002 p0003
  have p0005 :=
    @g_eqrdv (.classEq A B) x (syn_cxpk C A) (syn_cxpk C B) (by exact (show x ∉ ((syn_cxpk C A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show x ∉ ((C).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (C).fv from (by exact fresh_x_not_C)) (show x ∉ (A).fv from (by exact fresh_x_not_A))))))) (by exact (show x ∉ ((syn_cxpk C B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show x ∉ ((C).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (C).fv from (by exact fresh_x_not_C)) (show x ∉ (B).fv from (by exact fresh_x_not_B))))))) (by exact (show x ∉ ((Wff.classEq A B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ (B).fv from (by exact fresh_x_not_B))))))) p0004
  exact p0005

noncomputable def g_xpkeq12
    (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf (.imp (syn_wa (.classEq A B) (.classEq C D)) (.classEq (syn_cxpk A C) (syn_cxpk B D))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  have p0000 :=
    @g_xpkeq1 A B C
  have p0001 :=
    @g_xpkeq2 C D B
  have p0002 :=
    @g_sylan9eq (.classEq A B) (.classEq C D) (syn_cxpk A C) (syn_cxpk B C) (syn_cxpk B D) p0000 p0001
  exact p0002

noncomputable def g_xpkeq12i
    (A : Class) (B : Class) (C : Class) (D : Class) (hyp_xpkeq12i_1 : Nominal.NPrf (.classEq A B)) (hyp_xpkeq12i_2 : Nominal.NPrf (.classEq C D)) :
    Nominal.NPrf (.classEq (syn_cxpk A C) (syn_cxpk B D)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  have p0000 :=
    @g_xpkeq12 A B C D
  have p0001 :=
    @g_mp2an (.classEq A B) (.classEq C D) (.classEq (syn_cxpk A C) (syn_cxpk B D)) hyp_xpkeq12i_1 hyp_xpkeq12i_2 p0000
  exact p0001

noncomputable def g_xpkeq2d
    (ph : Wff) (A : Class) (B : Class) (C : Class) (hyp_xpkeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cxpk C A) (syn_cxpk C B))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_xpkeq2 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cxpk C A) (syn_cxpk C B)) hyp_xpkeq1d_1 p0000
  exact p0001

noncomputable def g_elvvk
    (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cxpk (syn_cvv) (syn_cvv))) (syn_wex x (syn_wex y (.classEq A (syn_copk (.cv x) (.cv y)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv
  have p0000 :=
    @g_elxpk x y A (syn_cvv) (syn_cvv) (by exact (show x ∉ (A).fv from (by exact dv_A_x))) (by exact (show y ∉ (A).fv from (by exact dv_A_y))) (by exact (show x ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show y ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show x ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show y ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (show x ≠ y from (by exact dv_x_y))
  have p0001 :=
    @g_vex x
  have p0002 :=
    @g_vex y
  have p0003 :=
    @g_pm3_2i (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_biantru (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))) (.classEq A (syn_copk (.cv x) (.cv y))) p0003
  have p0005 :=
    @g_n_2exbii (.classEq A (syn_copk (.cv x) (.cv y))) (syn_wa (.classEq A (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))) x y p0004
  have p0006 :=
    @g_bitr4i (.classMem A (syn_cxpk (syn_cvv) (syn_cvv))) (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_copk (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))))) (syn_wex x (syn_wex y (.classEq A (syn_copk (.cv x) (.cv y))))) p0000 p0005
  exact p0006



#print axioms g_elvvk

end NFChoice.DirectNominalPrf.WPPReplay
