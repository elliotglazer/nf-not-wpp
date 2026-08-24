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
import NominalWPPReplayChunk009StructuralPart011


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

noncomputable def g_inxpk
    (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf (.classEq (syn_cin (syn_cxpk A B) (syn_cxpk C D)) (syn_cxpk (syn_cin A C) (syn_cin B D))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_D : x ∉ D.fv := by
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
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have p0000 :=
    @g_inss1 (syn_cxpk A B) (syn_cxpk C D)
  have p0001 :=
    @g_xpkssvvk A B
  have p0002 :=
    @g_sstri (syn_cin (syn_cxpk A B) (syn_cxpk C D)) (syn_cxpk A B) (syn_cxpk (syn_cvv) (syn_cvv)) p0000 p0001
  have p0003 :=
    @g_xpkssvvk (syn_cin A C) (syn_cin B D)
  have p0004 :=
    @g_an4 (.classMem (.cv x) A) (.classMem (.cv y) B) (.classMem (.cv x) C) (.classMem (.cv y) D)
  have p0005 :=
    @g_elin (syn_copk (.cv x) (.cv y)) (syn_cxpk A B) (syn_cxpk C D)
  have p0006 :=
    @g_vex x
  have p0007 :=
    @g_vex y
  have p0008 :=
    @g_opkelxpk (.cv x) (.cv y) A B p0006 p0007
  have p0009 :=
    @g_opkelxpk (.cv x) (.cv y) C D p0006 p0007
  have p0010 :=
    @g_anbi12i (.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk A B)) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk C D)) (syn_wa (.classMem (.cv x) C) (.classMem (.cv y) D)) p0008 p0009
  have p0011 :=
    @g_bitri (.classMem (syn_copk (.cv x) (.cv y)) (syn_cin (syn_cxpk A B) (syn_cxpk C D))) (syn_wa (.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk A B)) (.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk C D))) (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (syn_wa (.classMem (.cv x) C) (.classMem (.cv y) D))) p0005 p0010
  have p0012 :=
    @g_opkelxpk (.cv x) (.cv y) (syn_cin A C) (syn_cin B D) p0006 p0007
  have p0013 :=
    @g_elin (.cv x) A C
  have p0014 :=
    @g_elin (.cv y) B D
  have p0015 :=
    @g_anbi12i (.classMem (.cv x) (syn_cin A C)) (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) C)) (.classMem (.cv y) (syn_cin B D)) (syn_wa (.classMem (.cv y) B) (.classMem (.cv y) D)) p0013 p0014
  have p0016 :=
    @g_bitri (.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk (syn_cin A C) (syn_cin B D))) (syn_wa (.classMem (.cv x) (syn_cin A C)) (.classMem (.cv y) (syn_cin B D))) (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) C)) (syn_wa (.classMem (.cv y) B) (.classMem (.cv y) D))) p0012 p0015
  have p0017 :=
    @g_n_3bitr4i (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (syn_wa (.classMem (.cv x) C) (.classMem (.cv y) D))) (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) C)) (syn_wa (.classMem (.cv y) B) (.classMem (.cv y) D))) (.classMem (syn_copk (.cv x) (.cv y)) (syn_cin (syn_cxpk A B) (syn_cxpk C D))) (.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk (syn_cin A C) (syn_cin B D))) p0004 p0011 p0016
  have p0018 :=
    @g_eqrelkriiv x y (syn_cin (syn_cxpk A B) (syn_cxpk C D)) (syn_cxpk (syn_cin A C) (syn_cin B D)) (by exact (show x ∉ ((syn_cin (syn_cxpk A B) (syn_cxpk C D))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show x ∉ (((syn_cxpk A B)).fv) ∪ (((syn_cxpk C D)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cxpk A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show x ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ (B).fv from (by exact fresh_x_not_B)))))) (show x ∉ ((syn_cxpk C D)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show x ∉ ((C).fv) ∪ ((D).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (C).fv from (by exact fresh_x_not_C)) (show x ∉ (D).fv from (by exact fresh_x_not_D))))))))))) (by exact (show y ∉ ((syn_cin (syn_cxpk A B) (syn_cxpk C D))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show y ∉ (((syn_cxpk A B)).fv) ∪ (((syn_cxpk C D)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cxpk A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show y ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ (B).fv from (by exact fresh_y_not_B)))))) (show y ∉ ((syn_cxpk C D)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show y ∉ ((C).fv) ∪ ((D).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (C).fv from (by exact fresh_y_not_C)) (show y ∉ (D).fv from (by exact fresh_y_not_D))))))))))) (by exact (show x ∉ ((syn_cxpk (syn_cin A C) (syn_cin B D))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show x ∉ (((syn_cin A C)).fv) ∪ (((syn_cin B D)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cin A C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show x ∉ ((A).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ (C).fv from (by exact fresh_x_not_C)))))) (show x ∉ ((syn_cin B D)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show x ∉ ((B).fv) ∪ ((D).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (B).fv from (by exact fresh_x_not_B)) (show x ∉ (D).fv from (by exact fresh_x_not_D))))))))))) (by exact (show y ∉ ((syn_cxpk (syn_cin A C) (syn_cin B D))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show y ∉ (((syn_cin A C)).fv) ∪ (((syn_cin B D)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cin A C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show y ∉ ((A).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ (C).fv from (by exact fresh_y_not_C)))))) (show y ∉ ((syn_cin B D)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show y ∉ ((B).fv) ∪ ((D).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (B).fv from (by exact fresh_y_not_B)) (show y ∉ (D).fv from (by exact fresh_y_not_D))))))))))) (show x ≠ y from (by exact fresh_x_ne_y)) p0002 p0003 p0017
  exact p0018

noncomputable def g_ssetkssvvk
     :
    Nominal.NPrf (syn_wss (syn_cssetk) (syn_cxpk (syn_cvv) (syn_cvv))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
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
    @g_opkabssvvki (syn_wss (.cv y) (.cv z)) x y z (syn_cssetk) (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z)) p0000
  exact p0001

noncomputable def g_ins2kss
    (A : Class) :
    Nominal.NPrf (syn_wss (syn_cins2k A) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))) := by
  let proofSupport : Finset Var := A.fv
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  let t : Var := freshVar proofSupport 3
  let u : Var := freshVar proofSupport 4
  let x : Var := freshVar proofSupport 5
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (h)
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (h)
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (h)
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_y_ne_w : y ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_w_ne_y : w ≠ y :=
    Ne.symm fresh_y_ne_w
  have fresh_y_ne_t : y ≠ t := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_t_ne_y : t ≠ y :=
    Ne.symm fresh_y_ne_t
  have fresh_y_ne_u : y ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_u_ne_y : u ≠ y :=
    Ne.symm fresh_y_ne_u
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have fresh_z_ne_t : z ≠ t := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_t_ne_z : t ≠ z :=
    Ne.symm fresh_z_ne_t
  have fresh_z_ne_u : z ≠ u := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_u_ne_z : u ≠ z :=
    Ne.symm fresh_z_ne_u
  have fresh_z_ne_x : z ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_w_ne_t : w ≠ t := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_t_ne_w : t ≠ w :=
    Ne.symm fresh_w_ne_t
  have fresh_w_ne_u : w ≠ u := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_u_ne_w : u ≠ w :=
    Ne.symm fresh_w_ne_u
  have fresh_w_ne_x : w ≠ x := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_t_ne_u : t ≠ u := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_u_ne_t : u ≠ t :=
    Ne.symm fresh_t_ne_u
  have fresh_t_ne_x : t ≠ x := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_x_ne_t : x ≠ t :=
    Ne.symm fresh_t_ne_x
  have fresh_u_ne_x : u ≠ x := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_x_ne_u : x ≠ u :=
    Ne.symm fresh_u_ne_x
  have p0000 :=
    @g_vex y
  have p0001 :=
    @g_vex z
  have p0002 :=
    @g_opkelins2kg w t u (.cv y) (.cv z) A (syn_cvv) (syn_cvv) (by exact (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y))))))) (by exact (show t ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ y from (by exact fresh_t_ne_y))))))) (by exact (show u ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show u ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show u ≠ y from (by exact fresh_u_ne_y))))))) (by exact (show w ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ z from (by exact fresh_w_ne_z))))))) (by exact (show t ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ z from (by exact fresh_t_ne_z))))))) (by exact (show u ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show u ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show u ≠ z from (by exact fresh_u_ne_z))))))) (by exact (show w ∉ (A).fv from (by exact fresh_w_not_A))) (by exact (show t ∉ (A).fv from (by exact fresh_t_not_A))) (by exact (show u ∉ (A).fv from (by exact fresh_u_not_A))) (show w ≠ t from (by exact fresh_w_ne_t)) (show w ≠ u from (by exact fresh_w_ne_u)) (show t ≠ u from (by exact fresh_t_ne_u))
  have p0003 :=
    @g_mp2an (.classMem (.cv y) (syn_cvv)) (.classMem (.cv z) (syn_cvv)) (syn_wb (.classMem (syn_copk (.cv y) (.cv z)) (syn_cins2k A)) (syn_wex w (syn_wex t (syn_wex u (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w)))) (.classEq (.cv z) (syn_copk (.cv t) (.cv u))) (.classMem (syn_copk (.cv w) (.cv u)) A)))))) p0000 p0001 p0002
  have p0004 :=
    @g_opkeq12 (.cv y) (.cv z) (syn_csn (syn_csn (.cv w))) (syn_copk (.cv t) (.cv u))
  have p0005 :=
    @g_vex w
  have p0006 :=
    @g_snel1c (.cv w) p0005
  have p0007 :=
    @g_snelpw1 (syn_csn (.cv w)) (syn_c1c)
  have p0008 :=
    @g_mpbir (.classMem (syn_csn (syn_csn (.cv w))) (syn_cpw1 (syn_c1c))) (.classMem (syn_csn (.cv w)) (syn_c1c)) p0006 p0007
  have p0009 :=
    @g_vex t
  have p0010 :=
    @g_vex u
  have p0011 :=
    @g_opkelxpk (.cv t) (.cv u) (syn_cvv) (syn_cvv) p0009 p0010
  have p0012 :=
    @g_mpbir2an (.classMem (syn_copk (.cv t) (.cv u)) (syn_cxpk (syn_cvv) (syn_cvv))) (.classMem (.cv t) (syn_cvv)) (.classMem (.cv u) (syn_cvv)) p0009 p0010 p0011
  have p0013 :=
    @g_snex (syn_csn (.cv w))
  have p0014 :=
    @g_opkex (.cv t) (.cv u)
  have p0015 :=
    @g_opkelxpk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv t) (.cv u)) (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)) p0013 p0014
  have p0016 :=
    @g_mpbir2an (.classMem (syn_copk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv t) (.cv u))) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))) (.classMem (syn_csn (syn_csn (.cv w))) (syn_cpw1 (syn_c1c))) (.classMem (syn_copk (.cv t) (.cv u)) (syn_cxpk (syn_cvv) (syn_cvv))) p0008 p0012 p0015
  have p0017 :=
    @g_syl6eqel (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv w)))) (.classEq (.cv z) (syn_copk (.cv t) (.cv u)))) (syn_copk (.cv y) (.cv z)) (syn_copk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv t) (.cv u))) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) p0004 p0016
  have p0018 :=
    @g_n_3adant3 (.classEq (.cv y) (syn_csn (syn_csn (.cv w)))) (.classEq (.cv z) (syn_copk (.cv t) (.cv u))) (.classMem (syn_copk (.cv y) (.cv z)) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))) (.classMem (syn_copk (.cv w) (.cv u)) A) p0017
  have p0019 :=
    @g_exlimiv (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w)))) (.classEq (.cv z) (syn_copk (.cv t) (.cv u))) (.classMem (syn_copk (.cv w) (.cv u)) A)) (.classMem (syn_copk (.cv y) (.cv z)) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))) u (by exact (show u ∉ ((Wff.classMem (syn_copk (.cv y) (.cv z)) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show u ∉ (((syn_copk (.cv y) (.cv z))).fv) ∪ (((syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show u ∉ ((syn_copk (.cv y) (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show u ∉ (((Class.cv y)).fv) ∪ (((Class.cv z)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show u ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show u ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show u ≠ y from (by exact fresh_u_ne_y)))))) (show u ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show u ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show u ≠ z from (by exact fresh_u_ne_z)))))))))) (show u ∉ ((syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show u ∉ (((syn_cpw1 (syn_c1c))).fv) ∪ (((syn_cxpk (syn_cvv) (syn_cvv))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show u ∉ ((syn_cpw1 (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show u ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show u ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))) (show u ∉ ((syn_cxpk (syn_cvv) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show u ∉ (((syn_cvv)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show u ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show u ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show u ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show u ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))))))) p0018
  have p0020 :=
    @g_exlimivv (syn_wex u (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w)))) (.classEq (.cv z) (syn_copk (.cv t) (.cv u))) (.classMem (syn_copk (.cv w) (.cv u)) A))) (.classMem (syn_copk (.cv y) (.cv z)) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))) w t (by exact (show w ∉ ((Wff.classMem (syn_copk (.cv y) (.cv z)) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show w ∉ (((syn_copk (.cv y) (.cv z))).fv) ∪ (((syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((syn_copk (.cv y) (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show w ∉ (((Class.cv y)).fv) ∪ (((Class.cv z)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y)))))) (show w ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ z from (by exact fresh_w_ne_z)))))))))) (show w ∉ ((syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show w ∉ (((syn_cpw1 (syn_c1c))).fv) ∪ (((syn_cxpk (syn_cvv) (syn_cvv))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((syn_cpw1 (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show w ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))) (show w ∉ ((syn_cxpk (syn_cvv) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show w ∉ (((syn_cvv)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show w ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))))))) (by exact (show t ∉ ((Wff.classMem (syn_copk (.cv y) (.cv z)) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show t ∉ (((syn_copk (.cv y) (.cv z))).fv) ∪ (((syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_copk (.cv y) (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show t ∉ (((Class.cv y)).fv) ∪ (((Class.cv z)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ y from (by exact fresh_t_ne_y)))))) (show t ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ z from (by exact fresh_t_ne_z)))))))))) (show t ∉ ((syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show t ∉ (((syn_cpw1 (syn_c1c))).fv) ∪ (((syn_cxpk (syn_cvv) (syn_cvv))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_cpw1 (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show t ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))) (show t ∉ ((syn_cxpk (syn_cvv) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show t ∉ (((syn_cvv)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show t ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))))))) p0019
  have p0021 :=
    @g_sylbi (.classMem (syn_copk (.cv y) (.cv z)) (syn_cins2k A)) (syn_wex w (syn_wex t (syn_wex u (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w)))) (.classEq (.cv z) (syn_copk (.cv t) (.cv u))) (.classMem (syn_copk (.cv w) (.cv u)) A))))) (.classMem (syn_copk (.cv y) (.cv z)) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))) p0003 p0020
  have p0022 :=
    @g_gen2 (.imp (.classMem (syn_copk (.cv y) (.cv z)) (syn_cins2k A)) (.classMem (syn_copk (.cv y) (.cv z)) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))) y z p0021
  have p0023 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ins2k x y z w u t A (by exact (show t ∉ (A).fv from (by exact fresh_t_not_A))) (by exact (show u ∉ (A).fv from (by exact fresh_u_not_A))) (by exact (show w ∉ (A).fv from (by exact fresh_w_not_A))) (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A))) (show t ≠ u from (by exact fresh_t_ne_u)) (show t ≠ w from (by exact fresh_t_ne_w)) (show t ≠ x from (by exact fresh_t_ne_x)) (show t ≠ y from (by exact fresh_t_ne_y)) (show t ≠ z from (by exact fresh_t_ne_z)) (show u ≠ w from (by exact fresh_u_ne_w)) (show u ≠ x from (by exact fresh_u_ne_x)) (show u ≠ y from (by exact fresh_u_ne_y)) (show u ≠ z from (by exact fresh_u_ne_z)) (show w ≠ x from (by exact fresh_w_ne_x)) (show w ≠ y from (by exact fresh_w_ne_y)) (show w ≠ z from (by exact fresh_w_ne_z)) (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z)) (show y ≠ z from (by exact fresh_y_ne_z))
  have p0024 :=
    @g_opkabssvvki (syn_wex t (syn_wex u (syn_wex w (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv t)))) (.classEq (.cv z) (syn_copk (.cv u) (.cv w))) (.classMem (syn_copk (.cv t) (.cv w)) A))))) x y z (syn_cins2k A) (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z)) p0023
  have p0025 :=
    @g_ssrelk y z (syn_cins2k A) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (by exact (show y ∉ ((syn_cins2k A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k]; exact (show y ∉ (A).fv from (by exact fresh_y_not_A))))) (by exact (show z ∉ ((syn_cins2k A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k]; exact (show z ∉ (A).fv from (by exact fresh_z_not_A))))) (by exact (show y ∉ ((syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show y ∉ (((syn_cpw1 (syn_c1c))).fv) ∪ (((syn_cxpk (syn_cvv) (syn_cvv))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cpw1 (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show y ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))) (show y ∉ ((syn_cxpk (syn_cvv) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show y ∉ (((syn_cvv)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show y ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (by exact (show z ∉ ((syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show z ∉ (((syn_cpw1 (syn_c1c))).fv) ∪ (((syn_cxpk (syn_cvv) (syn_cvv))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_cpw1 (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show z ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))) (show z ∉ ((syn_cxpk (syn_cvv) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show z ∉ (((syn_cvv)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show z ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (show y ≠ z from (by exact fresh_y_ne_z))
  have p0026 :=
    Nominal.mp p0024 p0025
  have p0027 :=
    @g_mpbir (syn_wss (syn_cins2k A) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))) (.all y (.all z (.imp (.classMem (syn_copk (.cv y) (.cv z)) (syn_cins2k A)) (.classMem (syn_copk (.cv y) (.cv z)) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))))) p0022 p0026
  exact p0027

noncomputable def g_ins3kss
    (A : Class) :
    Nominal.NPrf (syn_wss (syn_cins3k A) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))) := by
  let proofSupport : Finset Var := A.fv
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let t : Var := freshVar proofSupport 2
  let u : Var := freshVar proofSupport 3
  let w : Var := freshVar proofSupport 4
  let x : Var := freshVar proofSupport 5
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (h)
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (h)
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (h)
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_y_ne_t : y ≠ t := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_t_ne_y : t ≠ y :=
    Ne.symm fresh_y_ne_t
  have fresh_y_ne_u : y ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_u_ne_y : u ≠ y :=
    Ne.symm fresh_y_ne_u
  have fresh_y_ne_w : y ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_w_ne_y : w ≠ y :=
    Ne.symm fresh_y_ne_w
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_z_ne_t : z ≠ t := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_t_ne_z : t ≠ z :=
    Ne.symm fresh_z_ne_t
  have fresh_z_ne_u : z ≠ u := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_u_ne_z : u ≠ z :=
    Ne.symm fresh_z_ne_u
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have fresh_z_ne_x : z ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_t_ne_u : t ≠ u := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_u_ne_t : u ≠ t :=
    Ne.symm fresh_t_ne_u
  have fresh_t_ne_w : t ≠ w := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_w_ne_t : w ≠ t :=
    Ne.symm fresh_t_ne_w
  have fresh_t_ne_x : t ≠ x := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_x_ne_t : x ≠ t :=
    Ne.symm fresh_t_ne_x
  have fresh_u_ne_w : u ≠ w := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_w_ne_u : w ≠ u :=
    Ne.symm fresh_u_ne_w
  have fresh_u_ne_x : u ≠ x := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_x_ne_u : x ≠ u :=
    Ne.symm fresh_u_ne_x
  have fresh_w_ne_x : w ≠ x := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have p0000 :=
    @g_vex y
  have p0001 :=
    @g_vex z
  have p0002 :=
    @g_opkelins3kg t u w (.cv y) (.cv z) A (syn_cvv) (syn_cvv) (by exact (show t ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ y from (by exact fresh_t_ne_y))))))) (by exact (show u ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show u ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show u ≠ y from (by exact fresh_u_ne_y))))))) (by exact (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y))))))) (by exact (show t ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ z from (by exact fresh_t_ne_z))))))) (by exact (show u ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show u ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show u ≠ z from (by exact fresh_u_ne_z))))))) (by exact (show w ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ z from (by exact fresh_w_ne_z))))))) (by exact (show t ∉ (A).fv from (by exact fresh_t_not_A))) (by exact (show u ∉ (A).fv from (by exact fresh_u_not_A))) (by exact (show w ∉ (A).fv from (by exact fresh_w_not_A))) (show t ≠ u from (by exact fresh_t_ne_u)) (show t ≠ w from (by exact fresh_t_ne_w)) (show u ≠ w from (by exact fresh_u_ne_w))
  have p0003 :=
    @g_mp2an (.classMem (.cv y) (syn_cvv)) (.classMem (.cv z) (syn_cvv)) (syn_wb (.classMem (syn_copk (.cv y) (.cv z)) (syn_cins3k A)) (syn_wex t (syn_wex u (syn_wex w (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv t)))) (.classEq (.cv z) (syn_copk (.cv u) (.cv w))) (.classMem (syn_copk (.cv t) (.cv u)) A)))))) p0000 p0001 p0002
  have p0004 :=
    @g_opkeq12 (.cv y) (.cv z) (syn_csn (syn_csn (.cv t))) (syn_copk (.cv u) (.cv w))
  have p0005 :=
    @g_vex t
  have p0006 :=
    @g_snel1c (.cv t) p0005
  have p0007 :=
    @g_snelpw1 (syn_csn (.cv t)) (syn_c1c)
  have p0008 :=
    @g_mpbir (.classMem (syn_csn (syn_csn (.cv t))) (syn_cpw1 (syn_c1c))) (.classMem (syn_csn (.cv t)) (syn_c1c)) p0006 p0007
  have p0009 :=
    @g_vex u
  have p0010 :=
    @g_vex w
  have p0011 :=
    @g_opkelxpk (.cv u) (.cv w) (syn_cvv) (syn_cvv) p0009 p0010
  have p0012 :=
    @g_mpbir2an (.classMem (syn_copk (.cv u) (.cv w)) (syn_cxpk (syn_cvv) (syn_cvv))) (.classMem (.cv u) (syn_cvv)) (.classMem (.cv w) (syn_cvv)) p0009 p0010 p0011
  have p0013 :=
    @g_snex (syn_csn (.cv t))
  have p0014 :=
    @g_opkex (.cv u) (.cv w)
  have p0015 :=
    @g_opkelxpk (syn_csn (syn_csn (.cv t))) (syn_copk (.cv u) (.cv w)) (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)) p0013 p0014
  have p0016 :=
    @g_mpbir2an (.classMem (syn_copk (syn_csn (syn_csn (.cv t))) (syn_copk (.cv u) (.cv w))) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))) (.classMem (syn_csn (syn_csn (.cv t))) (syn_cpw1 (syn_c1c))) (.classMem (syn_copk (.cv u) (.cv w)) (syn_cxpk (syn_cvv) (syn_cvv))) p0008 p0012 p0015
  have p0017 :=
    @g_syl6eqel (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv t)))) (.classEq (.cv z) (syn_copk (.cv u) (.cv w)))) (syn_copk (.cv y) (.cv z)) (syn_copk (syn_csn (syn_csn (.cv t))) (syn_copk (.cv u) (.cv w))) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) p0004 p0016
  have p0018 :=
    @g_n_3adant3 (.classEq (.cv y) (syn_csn (syn_csn (.cv t)))) (.classEq (.cv z) (syn_copk (.cv u) (.cv w))) (.classMem (syn_copk (.cv y) (.cv z)) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))) (.classMem (syn_copk (.cv t) (.cv u)) A) p0017
  have p0019 :=
    @g_exlimiv (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv t)))) (.classEq (.cv z) (syn_copk (.cv u) (.cv w))) (.classMem (syn_copk (.cv t) (.cv u)) A)) (.classMem (syn_copk (.cv y) (.cv z)) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))) w (by exact (show w ∉ ((Wff.classMem (syn_copk (.cv y) (.cv z)) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show w ∉ (((syn_copk (.cv y) (.cv z))).fv) ∪ (((syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((syn_copk (.cv y) (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show w ∉ (((Class.cv y)).fv) ∪ (((Class.cv z)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y)))))) (show w ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ z from (by exact fresh_w_ne_z)))))))))) (show w ∉ ((syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show w ∉ (((syn_cpw1 (syn_c1c))).fv) ∪ (((syn_cxpk (syn_cvv) (syn_cvv))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((syn_cpw1 (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show w ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))) (show w ∉ ((syn_cxpk (syn_cvv) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show w ∉ (((syn_cvv)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show w ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))))))) p0018
  have p0020 :=
    @g_exlimivv (syn_wex w (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv t)))) (.classEq (.cv z) (syn_copk (.cv u) (.cv w))) (.classMem (syn_copk (.cv t) (.cv u)) A))) (.classMem (syn_copk (.cv y) (.cv z)) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))) t u (by exact (show t ∉ ((Wff.classMem (syn_copk (.cv y) (.cv z)) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show t ∉ (((syn_copk (.cv y) (.cv z))).fv) ∪ (((syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_copk (.cv y) (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show t ∉ (((Class.cv y)).fv) ∪ (((Class.cv z)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ y from (by exact fresh_t_ne_y)))))) (show t ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ z from (by exact fresh_t_ne_z)))))))))) (show t ∉ ((syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show t ∉ (((syn_cpw1 (syn_c1c))).fv) ∪ (((syn_cxpk (syn_cvv) (syn_cvv))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_cpw1 (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show t ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))) (show t ∉ ((syn_cxpk (syn_cvv) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show t ∉ (((syn_cvv)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show t ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))))))) (by exact (show u ∉ ((Wff.classMem (syn_copk (.cv y) (.cv z)) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show u ∉ (((syn_copk (.cv y) (.cv z))).fv) ∪ (((syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show u ∉ ((syn_copk (.cv y) (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show u ∉ (((Class.cv y)).fv) ∪ (((Class.cv z)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show u ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show u ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show u ≠ y from (by exact fresh_u_ne_y)))))) (show u ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show u ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show u ≠ z from (by exact fresh_u_ne_z)))))))))) (show u ∉ ((syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show u ∉ (((syn_cpw1 (syn_c1c))).fv) ∪ (((syn_cxpk (syn_cvv) (syn_cvv))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show u ∉ ((syn_cpw1 (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show u ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show u ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))) (show u ∉ ((syn_cxpk (syn_cvv) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show u ∉ (((syn_cvv)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show u ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show u ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show u ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show u ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))))))) p0019
  have p0021 :=
    @g_sylbi (.classMem (syn_copk (.cv y) (.cv z)) (syn_cins3k A)) (syn_wex t (syn_wex u (syn_wex w (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv t)))) (.classEq (.cv z) (syn_copk (.cv u) (.cv w))) (.classMem (syn_copk (.cv t) (.cv u)) A))))) (.classMem (syn_copk (.cv y) (.cv z)) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))) p0003 p0020
  have p0022 :=
    @g_gen2 (.imp (.classMem (syn_copk (.cv y) (.cv z)) (syn_cins3k A)) (.classMem (syn_copk (.cv y) (.cv z)) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))) y z p0021
  have p0023 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ins3k x y z w u t A (by exact (show t ∉ (A).fv from (by exact fresh_t_not_A))) (by exact (show u ∉ (A).fv from (by exact fresh_u_not_A))) (by exact (show w ∉ (A).fv from (by exact fresh_w_not_A))) (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A))) (show t ≠ u from (by exact fresh_t_ne_u)) (show t ≠ w from (by exact fresh_t_ne_w)) (show t ≠ x from (by exact fresh_t_ne_x)) (show t ≠ y from (by exact fresh_t_ne_y)) (show t ≠ z from (by exact fresh_t_ne_z)) (show u ≠ w from (by exact fresh_u_ne_w)) (show u ≠ x from (by exact fresh_u_ne_x)) (show u ≠ y from (by exact fresh_u_ne_y)) (show u ≠ z from (by exact fresh_u_ne_z)) (show w ≠ x from (by exact fresh_w_ne_x)) (show w ≠ y from (by exact fresh_w_ne_y)) (show w ≠ z from (by exact fresh_w_ne_z)) (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z)) (show y ≠ z from (by exact fresh_y_ne_z))
  have p0024 :=
    @g_opkabssvvki (syn_wex t (syn_wex u (syn_wex w (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv t)))) (.classEq (.cv z) (syn_copk (.cv u) (.cv w))) (.classMem (syn_copk (.cv t) (.cv u)) A))))) x y z (syn_cins3k A) (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z)) p0023
  have p0025 :=
    @g_ssrelk y z (syn_cins3k A) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (by exact (show y ∉ ((syn_cins3k A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k]; exact (show y ∉ (A).fv from (by exact fresh_y_not_A))))) (by exact (show z ∉ ((syn_cins3k A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k]; exact (show z ∉ (A).fv from (by exact fresh_z_not_A))))) (by exact (show y ∉ ((syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show y ∉ (((syn_cpw1 (syn_c1c))).fv) ∪ (((syn_cxpk (syn_cvv) (syn_cvv))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cpw1 (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show y ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))) (show y ∉ ((syn_cxpk (syn_cvv) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show y ∉ (((syn_cvv)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show y ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (by exact (show z ∉ ((syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show z ∉ (((syn_cpw1 (syn_c1c))).fv) ∪ (((syn_cxpk (syn_cvv) (syn_cvv))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_cpw1 (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show z ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))) (show z ∉ ((syn_cxpk (syn_cvv) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show z ∉ (((syn_cvv)).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show z ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (show y ≠ z from (by exact fresh_y_ne_z))
  have p0026 :=
    Nominal.mp p0024 p0025
  have p0027 :=
    @g_mpbir (syn_wss (syn_cins3k A) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))) (.all y (.all z (.imp (.classMem (syn_copk (.cv y) (.cv z)) (syn_cins3k A)) (.classMem (syn_copk (.cv y) (.cv z)) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))))) p0022 p0026
  exact p0027

noncomputable def g_idkssvvk
     :
    Nominal.NPrf (syn_wss (syn_cidk) (syn_cxpk (syn_cvv) (syn_cvv))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_idk x y z (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z)) (show y ≠ z from (by exact fresh_y_ne_z))
  have p0001 :=
    @g_opkabssvvki (.objEq y z) x y z (syn_cidk) (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z)) p0000
  exact p0001

noncomputable def g_elimaksn
    (A : Class) (B : Class) (C : Class) (hyp_elimaksn_1 : Nominal.NPrf (.classMem B (syn_cvv))) (hyp_elimaksn_2 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem C (syn_cimak A (syn_csn B))) (.classMem (syn_copk B C) A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
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
  have p0000 :=
    @g_elimak x A (syn_csn B) C (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show x ∉ ((syn_csn B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ (B).fv from (by exact fresh_x_not_B))))) (by exact (show x ∉ (C).fv from (by exact fresh_x_not_C))) hyp_elimaksn_2
  have p0001 :=
    @g_opkeq1 (.cv x) B C
  have p0002 :=
    @g_eleq1d (.classEq (.cv x) B) (syn_copk (.cv x) C) (syn_copk B C) A p0001
  have p0003 :=
    @g_rexsn (.classMem (syn_copk (.cv x) C) A) (.classMem (syn_copk B C) A) x B (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B))) (by exact (show x ∉ ((Wff.classMem (syn_copk B C) A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((syn_copk B C)).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_copk B C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show x ∉ ((B).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (B).fv from (by exact fresh_x_not_B)) (show x ∉ (C).fv from (by exact fresh_x_not_C)))))) (show x ∉ (A).fv from (by exact fresh_x_not_A))))))) hyp_elimaksn_1 p0002
  have p0004 :=
    @g_bitri (.classMem C (syn_cimak A (syn_csn B))) (syn_wrex x (syn_csn B) (.classMem (syn_copk (.cv x) C) A)) (.classMem (syn_copk B C) A) p0000 p0003
  exact p0004



#print axioms g_elimaksn

end NFChoice.DirectNominalPrf.WPPReplay
