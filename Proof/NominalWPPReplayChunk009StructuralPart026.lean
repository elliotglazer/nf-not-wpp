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
import NominalWPPReplayChunk009StructuralPart025


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

noncomputable def g_addccom
    (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cplc A B) (syn_cplc B A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
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
    @g_incom (.cv y) (.cv z)
  have p0001 :=
    @g_eqeq1i (syn_cin (.cv y) (.cv z)) (syn_cin (.cv z) (.cv y)) (syn_c0) p0000
  have p0002 :=
    @g_uncom (.cv y) (.cv z)
  have p0003 :=
    @g_eqeq2i (syn_cun (.cv y) (.cv z)) (syn_cun (.cv z) (.cv y)) (.cv x) p0002
  have p0004 :=
    @g_anbi12i (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0)) (.classEq (syn_cin (.cv z) (.cv y)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv y) (.cv z))) (.classEq (.cv x) (syn_cun (.cv z) (.cv y))) p0001 p0003
  have p0005 :=
    @g_n_2rexbii (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv y) (.cv z)))) (syn_wa (.classEq (syn_cin (.cv z) (.cv y)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv z) (.cv y)))) y z A B p0004
  have p0006 :=
    @g_rexcom (syn_wa (.classEq (syn_cin (.cv z) (.cv y)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv z) (.cv y)))) y z A B (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A))) (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B))) (show y ≠ z from (by exact fresh_y_ne_z))
  have p0007 :=
    @g_bitri (syn_wrex y A (syn_wrex z B (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv y) (.cv z)))))) (syn_wrex y A (syn_wrex z B (syn_wa (.classEq (syn_cin (.cv z) (.cv y)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv z) (.cv y)))))) (syn_wrex z B (syn_wrex y A (syn_wa (.classEq (syn_cin (.cv z) (.cv y)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv z) (.cv y)))))) p0005 p0006
  have p0008 :=
    @g_abbii (syn_wrex y A (syn_wrex z B (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv y) (.cv z)))))) (syn_wrex z B (syn_wrex y A (syn_wa (.classEq (syn_cin (.cv z) (.cv y)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv z) (.cv y)))))) x p0007
  have p0009 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_addc x y z A B (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A))) (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B))) (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B))) (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B))) (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z)) (show y ≠ z from (by exact fresh_y_ne_z))
  have p0010 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_addc x z y B A (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B))) (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B))) (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B))) (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A))) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (show x ≠ z from (by exact fresh_x_ne_z)) (show x ≠ y from (by exact fresh_x_ne_y)) (show z ≠ y from (by exact fresh_z_ne_y))
  have p0011 :=
    @g_n_3eqtr4i (.cab x (syn_wrex y A (syn_wrex z B (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv y) (.cv z))))))) (.cab x (syn_wrex z B (syn_wrex y A (syn_wa (.classEq (syn_cin (.cv z) (.cv y)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv z) (.cv y))))))) (syn_cplc A B) (syn_cplc B A) p0008 p0009 p0010
  exact p0011

noncomputable def g_addcid2
    (A : Class) :
    Nominal.NPrf (.classEq (syn_cplc (syn_c0c) A) A) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_addccom (syn_c0c) A
  have p0001 :=
    @g_addcid1 A
  have p0002 :=
    @g_eqtri (syn_cplc (syn_c0c) A) (syn_cplc A (syn_c0c)) A p0000 p0001
  exact p0002

noncomputable def g_n_1cnnc
     :
    Nominal.NPrf (.classMem (syn_c1c) (syn_cnnc)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_addcid1 (syn_c1c)
  have p0001 :=
    @g_addccom (syn_c1c) (syn_c0c)
  have p0002 :=
    @g_eqtr3i (syn_cplc (syn_c1c) (syn_c0c)) (syn_c1c) (syn_cplc (syn_c0c) (syn_c1c)) p0000 p0001
  have p0003 :=
    @g_peano1
  have p0004 :=
    @g_peano2 (syn_c0c)
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_eqeltri (syn_c1c) (syn_cplc (syn_c0c) (syn_c1c)) (syn_cnnc) p0002 p0005
  exact p0006

noncomputable def g_peano5
    (x : Var) (A : Class) (V : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.imp (syn_w3a (.classMem A V) (.classMem (syn_c0c) A) (syn_wral x (syn_cnnc) (.imp (.classMem (.cv x) A) (.classMem (syn_cplc (.cv x) (syn_c1c)) A)))) (syn_wss (syn_cnnc) A)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ V.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_V : y ∉ V.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_nncex
  have p0001 :=
    @g_inexg (syn_cnnc) A (syn_cvv) V
  have p0002 :=
    @g_mpan (.classMem (syn_cnnc) (syn_cvv)) (.classMem A V) (.classMem (syn_cin (syn_cnnc) A) (syn_cvv)) p0000 p0001
  have p0003 :=
    @g_peano1
  have p0004 :=
    @g_elin (syn_c0c) (syn_cnnc) A
  have p0005 :=
    @g_biimpri (.classMem (syn_c0c) (syn_cin (syn_cnnc) A)) (syn_wa (.classMem (syn_c0c) (syn_cnnc)) (.classMem (syn_c0c) A)) p0004
  have p0006 :=
    @g_mpan (.classMem (syn_c0c) (syn_cnnc)) (.classMem (syn_c0c) A) (.classMem (syn_c0c) (syn_cin (syn_cnnc) A)) p0003 p0005
  have p0007 :=
    @g_elin (.cv x) (syn_cnnc) A
  have p0008 :=
    @g_imbi1i (.classMem (.cv x) (syn_cin (syn_cnnc) A)) (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv x) A)) (.classMem (syn_cplc (.cv x) (syn_c1c)) A) p0007
  have p0009 :=
    @g_impexp (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv x) A) (.classMem (syn_cplc (.cv x) (syn_c1c)) A)
  have p0010 :=
    @g_bitri (.imp (.classMem (.cv x) (syn_cin (syn_cnnc) A)) (.classMem (syn_cplc (.cv x) (syn_c1c)) A)) (.imp (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv x) A)) (.classMem (syn_cplc (.cv x) (syn_c1c)) A)) (.imp (.classMem (.cv x) (syn_cnnc)) (.imp (.classMem (.cv x) A) (.classMem (syn_cplc (.cv x) (syn_c1c)) A))) p0008 p0009
  have p0011 :=
    @g_inss1 (syn_cnnc) A
  have p0012 :=
    @g_sseli (syn_cin (syn_cnnc) A) (syn_cnnc) (.cv x) p0011
  have p0013 :=
    @g_peano2 (.cv x)
  have p0014 :=
    @g_syl (.classMem (.cv x) (syn_cin (syn_cnnc) A)) (.classMem (.cv x) (syn_cnnc)) (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cnnc)) p0012 p0013
  have p0015 :=
    @g_elin (syn_cplc (.cv x) (syn_c1c)) (syn_cnnc) A
  have p0016 :=
    @g_biimpri (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A)) (syn_wa (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cnnc)) (.classMem (syn_cplc (.cv x) (syn_c1c)) A)) p0015
  have p0017 :=
    @g_a1i (.imp (syn_wa (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cnnc)) (.classMem (syn_cplc (.cv x) (syn_c1c)) A)) (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A))) (.classMem (.cv x) (syn_cin (syn_cnnc) A)) p0016
  have p0018 :=
    @g_mpand (.classMem (.cv x) (syn_cin (syn_cnnc) A)) (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cnnc)) (.classMem (syn_cplc (.cv x) (syn_c1c)) A) (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A)) p0014 p0017
  have p0019 :=
    @g_a2i (.classMem (.cv x) (syn_cin (syn_cnnc) A)) (.classMem (syn_cplc (.cv x) (syn_c1c)) A) (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A)) p0018
  have p0020 :=
    @g_sylbir (.imp (.classMem (.cv x) (syn_cnnc)) (.imp (.classMem (.cv x) A) (.classMem (syn_cplc (.cv x) (syn_c1c)) A))) (.imp (.classMem (.cv x) (syn_cin (syn_cnnc) A)) (.classMem (syn_cplc (.cv x) (syn_c1c)) A)) (.imp (.classMem (.cv x) (syn_cin (syn_cnnc) A)) (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A))) p0010 p0019
  have p0021 :=
    @g_ralimi2 (.imp (.classMem (.cv x) A) (.classMem (syn_cplc (.cv x) (syn_c1c)) A)) (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A)) x (syn_cnnc) (syn_cin (syn_cnnc) A) p0020
  have p0022 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_nnc x y (show y ≠ x from (by exact fresh_y_ne_x))
  have p0023 :=
    @g_eleq2 (.cv y) (syn_cin (syn_cnnc) A) (syn_c0c)
  have p0024 :=
    @g_eleq2 (.cv y) (syn_cin (syn_cnnc) A) (syn_cplc (.cv x) (syn_c1c))
  have p0025 :=
    @g_raleqbi1dv (.classMem (syn_cplc (.cv x) (syn_c1c)) (.cv y)) (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A)) x (.cv y) (syn_cin (syn_cnnc) A) (by exact (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact fresh_x_ne_y))))))) (by exact (show x ∉ ((syn_cin (syn_cnnc) A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show x ∉ (((syn_cnnc)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show x ∉ (A).fv from (by exact dv_A_x))))))) p0024
  have p0026 :=
    @g_anbi12d (.classEq (.cv y) (syn_cin (syn_cnnc) A)) (.classMem (syn_c0c) (.cv y)) (.classMem (syn_c0c) (syn_cin (syn_cnnc) A)) (syn_wral x (.cv y) (.classMem (syn_cplc (.cv x) (syn_c1c)) (.cv y))) (syn_wral x (syn_cin (syn_cnnc) A) (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A))) p0023 p0025
  have p0027 :=
    @g_elabg (syn_wa (.classMem (syn_c0c) (.cv y)) (syn_wral x (.cv y) (.classMem (syn_cplc (.cv x) (syn_c1c)) (.cv y)))) (syn_wa (.classMem (syn_c0c) (syn_cin (syn_cnnc) A)) (syn_wral x (syn_cin (syn_cnnc) A) (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A)))) y (syn_cin (syn_cnnc) A) (syn_cvv) (by exact (show y ∉ ((syn_cin (syn_cnnc) A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show y ∉ (((syn_cnnc)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show y ∉ (A).fv from (by exact fresh_y_not_A))))))) (by exact (show y ∉ ((syn_wa (.classMem (syn_c0c) (syn_cin (syn_cnnc) A)) (syn_wral x (syn_cin (syn_cnnc) A) (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show y ∉ (((Wff.classMem (syn_c0c) (syn_cin (syn_cnnc) A))).fv) ∪ (((syn_wral x (syn_cin (syn_cnnc) A) (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Wff.classMem (syn_c0c) (syn_cin (syn_cnnc) A))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((syn_c0c)).fv) ∪ (((syn_cin (syn_cnnc) A)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_c0c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show y ∉ ((syn_cin (syn_cnnc) A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show y ∉ (((syn_cnnc)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show y ∉ (A).fv from (by exact fresh_y_not_A)))))))))) (show y ∉ ((syn_wral x (syn_cin (syn_cnnc) A) (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral]; exact (show y ∉ ((((syn_cin (syn_cnnc) A)).fv).erase x) ∪ ((((Wff.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A))).fv).erase x) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (((syn_cin (syn_cnnc) A)).fv).erase x from (fun hmem => (show y ∉ ((syn_cin (syn_cnnc) A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show y ∉ (((syn_cnnc)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show y ∉ (A).fv from (by exact fresh_y_not_A)))))) (Finset.mem_of_mem_erase hmem))) (show y ∉ (((Wff.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A))).fv).erase x from (fun hmem => (show y ∉ ((Wff.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((syn_cplc (.cv x) (syn_c1c))).fv) ∪ (((syn_cin (syn_cnnc) A)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cplc (.cv x) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show y ∉ (((Class.cv x)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))) (show y ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show y ∉ ((syn_cin (syn_cnnc) A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show y ∉ (((syn_cnnc)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show y ∉ (A).fv from (by exact fresh_y_not_A)))))))))) (Finset.mem_of_mem_erase hmem)))))))))))) p0026
  have p0028 :=
    @g_biimprd (.classMem (syn_cin (syn_cnnc) A) (syn_cvv)) (.classMem (syn_cin (syn_cnnc) A) (.cab y (syn_wa (.classMem (syn_c0c) (.cv y)) (syn_wral x (.cv y) (.classMem (syn_cplc (.cv x) (syn_c1c)) (.cv y)))))) (syn_wa (.classMem (syn_c0c) (syn_cin (syn_cnnc) A)) (syn_wral x (syn_cin (syn_cnnc) A) (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A)))) p0027
  have p0029 :=
    @g_n_3impib (.classMem (syn_cin (syn_cnnc) A) (syn_cvv)) (.classMem (syn_c0c) (syn_cin (syn_cnnc) A)) (syn_wral x (syn_cin (syn_cnnc) A) (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A))) (.classMem (syn_cin (syn_cnnc) A) (.cab y (syn_wa (.classMem (syn_c0c) (.cv y)) (syn_wral x (.cv y) (.classMem (syn_cplc (.cv x) (syn_c1c)) (.cv y)))))) p0028
  have p0030 :=
    @g_intss1 (syn_cin (syn_cnnc) A) (.cab y (syn_wa (.classMem (syn_c0c) (.cv y)) (syn_wral x (.cv y) (.classMem (syn_cplc (.cv x) (syn_c1c)) (.cv y)))))
  have p0031 :=
    @g_syl (syn_w3a (.classMem (syn_cin (syn_cnnc) A) (syn_cvv)) (.classMem (syn_c0c) (syn_cin (syn_cnnc) A)) (syn_wral x (syn_cin (syn_cnnc) A) (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A)))) (.classMem (syn_cin (syn_cnnc) A) (.cab y (syn_wa (.classMem (syn_c0c) (.cv y)) (syn_wral x (.cv y) (.classMem (syn_cplc (.cv x) (syn_c1c)) (.cv y)))))) (syn_wss (syn_cint (.cab y (syn_wa (.classMem (syn_c0c) (.cv y)) (syn_wral x (.cv y) (.classMem (syn_cplc (.cv x) (syn_c1c)) (.cv y)))))) (syn_cin (syn_cnnc) A)) p0029 p0030
  have p0032 :=
    @g_syl5eqss (syn_w3a (.classMem (syn_cin (syn_cnnc) A) (syn_cvv)) (.classMem (syn_c0c) (syn_cin (syn_cnnc) A)) (syn_wral x (syn_cin (syn_cnnc) A) (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A)))) (syn_cnnc) (syn_cint (.cab y (syn_wa (.classMem (syn_c0c) (.cv y)) (syn_wral x (.cv y) (.classMem (syn_cplc (.cv x) (syn_c1c)) (.cv y)))))) (syn_cin (syn_cnnc) A) p0022 p0031
  have p0033 :=
    @g_inss2 (syn_cnnc) A
  have p0034 :=
    @g_syl6ss (syn_w3a (.classMem (syn_cin (syn_cnnc) A) (syn_cvv)) (.classMem (syn_c0c) (syn_cin (syn_cnnc) A)) (syn_wral x (syn_cin (syn_cnnc) A) (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A)))) (syn_cnnc) (syn_cin (syn_cnnc) A) A p0032 p0033
  have p0035 :=
    @g_syl3an (.classMem A V) (.classMem (syn_cin (syn_cnnc) A) (syn_cvv)) (.classMem (syn_c0c) A) (.classMem (syn_c0c) (syn_cin (syn_cnnc) A)) (syn_wral x (syn_cnnc) (.imp (.classMem (.cv x) A) (.classMem (syn_cplc (.cv x) (syn_c1c)) A))) (syn_wral x (syn_cin (syn_cnnc) A) (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A))) (syn_wss (syn_cnnc) A) p0002 p0006 p0021 p0034
  exact p0035

noncomputable def g_findsd
    (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) (et : Wff) (x : Var) (y : Var) (A : Class) (V : Class) (dv_A_x : x ∉ A.fv) (dv_ch_x : x ∉ ch.fv) (dv_et_y : y ∉ et.fv) (dv_ph_y : y ∉ ph.fv) (dv_ps_x : x ∉ ps.fv) (dv_ta_x : x ∉ ta.fv) (dv_th_x : x ∉ th.fv) (dv_x_y : x ≠ y) (hyp_findsd_1 : Nominal.NPrf (.imp et (.classMem (.cab x ph) V))) (hyp_findsd_2 : Nominal.NPrf (.imp (.classEq (.cv x) (syn_c0c)) (syn_wb ph ps))) (hyp_findsd_3 : Nominal.NPrf (.imp (.objEq x y) (syn_wb ph ch))) (hyp_findsd_4 : Nominal.NPrf (.imp (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (syn_wb ph th))) (hyp_findsd_5 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ta))) (hyp_findsd_6 : Nominal.NPrf (.imp et ps)) (hyp_findsd_7 : Nominal.NPrf (.imp (syn_wa (.classMem (.cv y) (syn_cnnc)) et) (.imp ch th))) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_cnnc)) et) ta) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ th.fv ∪ ta.fv ∪ et.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ V.fv
  have p0000 :=
    @g_n_0cex
  have p0001 :=
    @g_elab ph ps x (syn_c0c) (by exact (show x ∉ ((syn_c0c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show x ∉ (ps).fv from (by exact dv_ps_x))) p0000 hyp_findsd_2
  have p0002 :=
    @g_sylibr et ps (.classMem (syn_c0c) (.cab x ph)) hyp_findsd_6 p0001
  have p0003 :=
    @g_vex y
  have p0004_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv x) (.cv y)) (syn_wb ph ch)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      hyp_findsd_3
  have p0004 :=
    @g_elab ph ch x (.cv y) (by exact (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact dv_x_y))))))) (by exact (show x ∉ (ch).fv from (by exact dv_ch_x))) p0003 p0004_e01_recanon
  have p0005 :=
    @g_n_1cex
  have p0006 :=
    @g_addcex (.cv y) (syn_c1c) p0003 p0005
  have p0007 :=
    @g_elab ph th x (syn_cplc (.cv y) (syn_c1c)) (by exact (show x ∉ ((syn_cplc (.cv y) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ (((Class.cv y)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact dv_x_y)))))) (show x ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) (by exact (show x ∉ (th).fv from (by exact dv_th_x))) p0006 hyp_findsd_4
  have p0008 :=
    @g_n_3imtr4g (syn_wa (.classMem (.cv y) (syn_cnnc)) et) ch th (.classMem (.cv y) (.cab x ph)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cab x ph)) hyp_findsd_7 p0004 p0007
  have p0009 :=
    @g_ancoms (.classMem (.cv y) (syn_cnnc)) et (.imp (.classMem (.cv y) (.cab x ph)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cab x ph))) p0008
  have p0010 :=
    @g_ralrimiva et (.imp (.classMem (.cv y) (.cab x ph)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cab x ph))) y (syn_cnnc) (by exact (show y ∉ (et).fv from (by exact dv_et_y))) p0009
  have p0011 :=
    @g_peano5 y (.cab x ph) V (by exact (show y ∉ ((Class.cab x ph)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cab]; exact (show y ∉ ((ph).fv).erase x from (fun hmem => (show y ∉ (ph).fv from (by exact dv_ph_y)) (Finset.mem_of_mem_erase hmem))))))
  have p0012 :=
    @g_syl3anc et (.classMem (.cab x ph) V) (.classMem (syn_c0c) (.cab x ph)) (syn_wral y (syn_cnnc) (.imp (.classMem (.cv y) (.cab x ph)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cab x ph)))) (syn_wss (syn_cnnc) (.cab x ph)) hyp_findsd_1 p0002 p0010 p0011
  have p0013 :=
    @g_sseld et (syn_cnnc) (.cab x ph) A p0012
  have p0014 :=
    @g_impcom et (.classMem A (syn_cnnc)) (.classMem A (.cab x ph)) p0013
  have p0015 :=
    @g_elabg ph ta x A (syn_cnnc) (by exact (show x ∉ (A).fv from (by exact dv_A_x))) (by exact (show x ∉ (ta).fv from (by exact dv_ta_x))) hyp_findsd_5
  have p0016 :=
    @g_adantr (.classMem A (syn_cnnc)) (syn_wb (.classMem A (.cab x ph)) ta) et p0015
  have p0017 :=
    @g_mpbid (syn_wa (.classMem A (syn_cnnc)) et) (.classMem A (.cab x ph)) ta p0014 p0016
  exact p0017

noncomputable def g_finds
    (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv) (dv_ch_x : x ∉ ch.fv) (dv_ph_y : y ∉ ph.fv) (dv_ps_x : x ∉ ps.fv) (dv_ta_x : x ∉ ta.fv) (dv_th_x : x ∉ th.fv) (dv_x_y : x ≠ y) (hyp_finds_1 : Nominal.NPrf (.classMem (.cab x ph) (syn_cvv))) (hyp_finds_2 : Nominal.NPrf (.imp (.classEq (.cv x) (syn_c0c)) (syn_wb ph ps))) (hyp_finds_3 : Nominal.NPrf (.imp (.objEq x y) (syn_wb ph ch))) (hyp_finds_4 : Nominal.NPrf (.imp (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (syn_wb ph th))) (hyp_finds_5 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ta))) (hyp_finds_6 : Nominal.NPrf ps) (hyp_finds_7 : Nominal.NPrf (.imp (.classMem (.cv y) (syn_cnnc)) (.imp ch th))) :
    Nominal.NPrf (.imp (.classMem A (syn_cnnc)) ta) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ th.fv ∪ ta.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv
  have p0000 :=
    @g_tru
  have p0001 :=
    @g_a1i (.classMem (.cab x ph) (syn_cvv)) syn_wtru hyp_finds_1
  have p0002 :=
    @g_a1i ps syn_wtru hyp_finds_6
  have p0003 :=
    @g_adantr (.classMem (.cv y) (syn_cnnc)) (.imp ch th) syn_wtru hyp_finds_7
  have p0004 :=
    @g_findsd ph ps ch th ta syn_wtru x y A (syn_cvv) (by exact (show x ∉ (A).fv from (by exact dv_A_x))) (by exact (show x ∉ (ch).fv from (by exact dv_ch_x))) (by exact (show y ∉ (syn_wtru).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show y ∉ (ph).fv from (by exact dv_ph_y))) (by exact (show x ∉ (ps).fv from (by exact dv_ps_x))) (by exact (show x ∉ (ta).fv from (by exact dv_ta_x))) (by exact (show x ∉ (th).fv from (by exact dv_th_x))) (show x ≠ y from (by exact dv_x_y)) p0001 hyp_finds_2 hyp_finds_3 hyp_finds_4 hyp_finds_5 p0002 p0003
  have p0005 :=
    @g_mpan2 (.classMem A (syn_cnnc)) syn_wtru ta p0000 p0004
  exact p0005



#print axioms g_finds

end NFChoice.DirectNominalPrf.WPPReplay
