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
import NominalWPPReplayChunk009StructuralPart003


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

noncomputable def g_ins2keq
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cins2k A) (syn_cins2k B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  let t : Var := freshVar proofSupport 4
  let u : Var := freshVar proofSupport 5
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
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (h))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (h))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
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
  have fresh_x_ne_t : x ≠ t := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_t_ne_x : t ≠ x :=
    Ne.symm fresh_x_ne_t
  have fresh_x_ne_u : x ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_u_ne_x : u ≠ x :=
    Ne.symm fresh_x_ne_u
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
  have fresh_y_ne_t : y ≠ t := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_t_ne_y : t ≠ y :=
    Ne.symm fresh_y_ne_t
  have fresh_y_ne_u : y ≠ u := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_u_ne_y : u ≠ y :=
    Ne.symm fresh_y_ne_u
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have fresh_z_ne_t : z ≠ t := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_t_ne_z : t ≠ z :=
    Ne.symm fresh_z_ne_t
  have fresh_z_ne_u : z ≠ u := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_u_ne_z : u ≠ z :=
    Ne.symm fresh_z_ne_u
  have fresh_w_ne_t : w ≠ t := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_t_ne_w : t ≠ w :=
    Ne.symm fresh_w_ne_t
  have fresh_w_ne_u : w ≠ u := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_u_ne_w : u ≠ w :=
    Ne.symm fresh_w_ne_u
  have fresh_t_ne_u : t ≠ u := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_u_ne_t : u ≠ t :=
    Ne.symm fresh_t_ne_u
  have p0000 :=
    @g_eleq2 A B (syn_copk (.cv w) (.cv u))
  have p0001 :=
    @g_n_3anbi3d (.classEq A B) (.classMem (syn_copk (.cv w) (.cv u)) A) (.classMem (syn_copk (.cv w) (.cv u)) B) (.classEq (.cv y) (syn_csn (syn_csn (.cv w)))) (.classEq (.cv z) (syn_copk (.cv t) (.cv u))) p0000
  have p0002 :=
    @g_n_3exbidv (.classEq A B) (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w)))) (.classEq (.cv z) (syn_copk (.cv t) (.cv u))) (.classMem (syn_copk (.cv w) (.cv u)) A)) (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w)))) (.classEq (.cv z) (syn_copk (.cv t) (.cv u))) (.classMem (syn_copk (.cv w) (.cv u)) B)) w t u (by exact (show w ∉ ((Wff.classEq A B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show w ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ (A).fv from (by exact fresh_w_not_A)) (show w ∉ (B).fv from (by exact fresh_w_not_B))))))) (by exact (show t ∉ ((Wff.classEq A B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show t ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ (A).fv from (by exact fresh_t_not_A)) (show t ∉ (B).fv from (by exact fresh_t_not_B))))))) (by exact (show u ∉ ((Wff.classEq A B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show u ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show u ∉ (A).fv from (by exact fresh_u_not_A)) (show u ∉ (B).fv from (by exact fresh_u_not_B))))))) p0001
  have p0003 :=
    @g_anbi2d (.classEq A B) (syn_wex w (syn_wex t (syn_wex u (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w)))) (.classEq (.cv z) (syn_copk (.cv t) (.cv u))) (.classMem (syn_copk (.cv w) (.cv u)) A))))) (syn_wex w (syn_wex t (syn_wex u (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w)))) (.classEq (.cv z) (syn_copk (.cv t) (.cv u))) (.classMem (syn_copk (.cv w) (.cv u)) B))))) (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) p0002
  have p0004 :=
    @g_n_2exbidv (.classEq A B) (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (syn_wex w (syn_wex t (syn_wex u (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w)))) (.classEq (.cv z) (syn_copk (.cv t) (.cv u))) (.classMem (syn_copk (.cv w) (.cv u)) A)))))) (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (syn_wex w (syn_wex t (syn_wex u (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w)))) (.classEq (.cv z) (syn_copk (.cv t) (.cv u))) (.classMem (syn_copk (.cv w) (.cv u)) B)))))) y z (by exact (show y ∉ ((Wff.classEq A B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ (B).fv from (by exact fresh_y_not_B))))))) (by exact (show z ∉ ((Wff.classEq A B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show z ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ (A).fv from (by exact fresh_z_not_A)) (show z ∉ (B).fv from (by exact fresh_z_not_B))))))) p0003
  have p0005 :=
    @g_abbidv (.classEq A B) (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (syn_wex w (syn_wex t (syn_wex u (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w)))) (.classEq (.cv z) (syn_copk (.cv t) (.cv u))) (.classMem (syn_copk (.cv w) (.cv u)) A)))))))) (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (syn_wex w (syn_wex t (syn_wex u (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w)))) (.classEq (.cv z) (syn_copk (.cv t) (.cv u))) (.classMem (syn_copk (.cv w) (.cv u)) B)))))))) x (by exact (show x ∉ ((Wff.classEq A B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ (B).fv from (by exact fresh_x_not_B))))))) p0004
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ins2k x y z u t w A (by exact (show w ∉ (A).fv from (by exact fresh_w_not_A))) (by exact (show t ∉ (A).fv from (by exact fresh_t_not_A))) (by exact (show u ∉ (A).fv from (by exact fresh_u_not_A))) (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A))) (show w ≠ t from (by exact fresh_w_ne_t)) (show w ≠ u from (by exact fresh_w_ne_u)) (show w ≠ x from (by exact fresh_w_ne_x)) (show w ≠ y from (by exact fresh_w_ne_y)) (show w ≠ z from (by exact fresh_w_ne_z)) (show t ≠ u from (by exact fresh_t_ne_u)) (show t ≠ x from (by exact fresh_t_ne_x)) (show t ≠ y from (by exact fresh_t_ne_y)) (show t ≠ z from (by exact fresh_t_ne_z)) (show u ≠ x from (by exact fresh_u_ne_x)) (show u ≠ y from (by exact fresh_u_ne_y)) (show u ≠ z from (by exact fresh_u_ne_z)) (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z)) (show y ≠ z from (by exact fresh_y_ne_z))
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ins2k x y z u t w B (by exact (show w ∉ (B).fv from (by exact fresh_w_not_B))) (by exact (show t ∉ (B).fv from (by exact fresh_t_not_B))) (by exact (show u ∉ (B).fv from (by exact fresh_u_not_B))) (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B))) (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B))) (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B))) (show w ≠ t from (by exact fresh_w_ne_t)) (show w ≠ u from (by exact fresh_w_ne_u)) (show w ≠ x from (by exact fresh_w_ne_x)) (show w ≠ y from (by exact fresh_w_ne_y)) (show w ≠ z from (by exact fresh_w_ne_z)) (show t ≠ u from (by exact fresh_t_ne_u)) (show t ≠ x from (by exact fresh_t_ne_x)) (show t ≠ y from (by exact fresh_t_ne_y)) (show t ≠ z from (by exact fresh_t_ne_z)) (show u ≠ x from (by exact fresh_u_ne_x)) (show u ≠ y from (by exact fresh_u_ne_y)) (show u ≠ z from (by exact fresh_u_ne_z)) (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z)) (show y ≠ z from (by exact fresh_y_ne_z))
  have p0008 :=
    @g_n_3eqtr4g (.classEq A B) (.cab x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (syn_wex w (syn_wex t (syn_wex u (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w)))) (.classEq (.cv z) (syn_copk (.cv t) (.cv u))) (.classMem (syn_copk (.cv w) (.cv u)) A))))))))) (.cab x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (syn_wex w (syn_wex t (syn_wex u (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w)))) (.classEq (.cv z) (syn_copk (.cv t) (.cv u))) (.classMem (syn_copk (.cv w) (.cv u)) B))))))))) (syn_cins2k A) (syn_cins2k B) p0005 p0006 p0007
  exact p0008

noncomputable def g_ins3keq
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cins3k A) (syn_cins3k B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  let t : Var := freshVar proofSupport 4
  let u : Var := freshVar proofSupport 5
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
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (h))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (h))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
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
  have fresh_x_ne_t : x ≠ t := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_t_ne_x : t ≠ x :=
    Ne.symm fresh_x_ne_t
  have fresh_x_ne_u : x ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_u_ne_x : u ≠ x :=
    Ne.symm fresh_x_ne_u
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
  have fresh_y_ne_t : y ≠ t := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_t_ne_y : t ≠ y :=
    Ne.symm fresh_y_ne_t
  have fresh_y_ne_u : y ≠ u := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_u_ne_y : u ≠ y :=
    Ne.symm fresh_y_ne_u
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have fresh_z_ne_t : z ≠ t := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_t_ne_z : t ≠ z :=
    Ne.symm fresh_z_ne_t
  have fresh_z_ne_u : z ≠ u := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_u_ne_z : u ≠ z :=
    Ne.symm fresh_z_ne_u
  have fresh_w_ne_t : w ≠ t := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_t_ne_w : t ≠ w :=
    Ne.symm fresh_w_ne_t
  have fresh_w_ne_u : w ≠ u := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_u_ne_w : u ≠ w :=
    Ne.symm fresh_w_ne_u
  have fresh_t_ne_u : t ≠ u := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_u_ne_t : u ≠ t :=
    Ne.symm fresh_t_ne_u
  have p0000 :=
    @g_eleq2 A B (syn_copk (.cv w) (.cv t))
  have p0001 :=
    @g_n_3anbi3d (.classEq A B) (.classMem (syn_copk (.cv w) (.cv t)) A) (.classMem (syn_copk (.cv w) (.cv t)) B) (.classEq (.cv y) (syn_csn (syn_csn (.cv w)))) (.classEq (.cv z) (syn_copk (.cv t) (.cv u))) p0000
  have p0002 :=
    @g_n_3exbidv (.classEq A B) (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w)))) (.classEq (.cv z) (syn_copk (.cv t) (.cv u))) (.classMem (syn_copk (.cv w) (.cv t)) A)) (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w)))) (.classEq (.cv z) (syn_copk (.cv t) (.cv u))) (.classMem (syn_copk (.cv w) (.cv t)) B)) w t u (by exact (show w ∉ ((Wff.classEq A B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show w ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ (A).fv from (by exact fresh_w_not_A)) (show w ∉ (B).fv from (by exact fresh_w_not_B))))))) (by exact (show t ∉ ((Wff.classEq A B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show t ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ (A).fv from (by exact fresh_t_not_A)) (show t ∉ (B).fv from (by exact fresh_t_not_B))))))) (by exact (show u ∉ ((Wff.classEq A B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show u ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show u ∉ (A).fv from (by exact fresh_u_not_A)) (show u ∉ (B).fv from (by exact fresh_u_not_B))))))) p0001
  have p0003 :=
    @g_anbi2d (.classEq A B) (syn_wex w (syn_wex t (syn_wex u (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w)))) (.classEq (.cv z) (syn_copk (.cv t) (.cv u))) (.classMem (syn_copk (.cv w) (.cv t)) A))))) (syn_wex w (syn_wex t (syn_wex u (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w)))) (.classEq (.cv z) (syn_copk (.cv t) (.cv u))) (.classMem (syn_copk (.cv w) (.cv t)) B))))) (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) p0002
  have p0004 :=
    @g_n_2exbidv (.classEq A B) (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (syn_wex w (syn_wex t (syn_wex u (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w)))) (.classEq (.cv z) (syn_copk (.cv t) (.cv u))) (.classMem (syn_copk (.cv w) (.cv t)) A)))))) (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (syn_wex w (syn_wex t (syn_wex u (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w)))) (.classEq (.cv z) (syn_copk (.cv t) (.cv u))) (.classMem (syn_copk (.cv w) (.cv t)) B)))))) y z (by exact (show y ∉ ((Wff.classEq A B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ (B).fv from (by exact fresh_y_not_B))))))) (by exact (show z ∉ ((Wff.classEq A B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show z ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ (A).fv from (by exact fresh_z_not_A)) (show z ∉ (B).fv from (by exact fresh_z_not_B))))))) p0003
  have p0005 :=
    @g_abbidv (.classEq A B) (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (syn_wex w (syn_wex t (syn_wex u (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w)))) (.classEq (.cv z) (syn_copk (.cv t) (.cv u))) (.classMem (syn_copk (.cv w) (.cv t)) A)))))))) (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (syn_wex w (syn_wex t (syn_wex u (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w)))) (.classEq (.cv z) (syn_copk (.cv t) (.cv u))) (.classMem (syn_copk (.cv w) (.cv t)) B)))))))) x (by exact (show x ∉ ((Wff.classEq A B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ (B).fv from (by exact fresh_x_not_B))))))) p0004
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ins3k x y z u t w A (by exact (show w ∉ (A).fv from (by exact fresh_w_not_A))) (by exact (show t ∉ (A).fv from (by exact fresh_t_not_A))) (by exact (show u ∉ (A).fv from (by exact fresh_u_not_A))) (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A))) (show w ≠ t from (by exact fresh_w_ne_t)) (show w ≠ u from (by exact fresh_w_ne_u)) (show w ≠ x from (by exact fresh_w_ne_x)) (show w ≠ y from (by exact fresh_w_ne_y)) (show w ≠ z from (by exact fresh_w_ne_z)) (show t ≠ u from (by exact fresh_t_ne_u)) (show t ≠ x from (by exact fresh_t_ne_x)) (show t ≠ y from (by exact fresh_t_ne_y)) (show t ≠ z from (by exact fresh_t_ne_z)) (show u ≠ x from (by exact fresh_u_ne_x)) (show u ≠ y from (by exact fresh_u_ne_y)) (show u ≠ z from (by exact fresh_u_ne_z)) (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z)) (show y ≠ z from (by exact fresh_y_ne_z))
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ins3k x y z u t w B (by exact (show w ∉ (B).fv from (by exact fresh_w_not_B))) (by exact (show t ∉ (B).fv from (by exact fresh_t_not_B))) (by exact (show u ∉ (B).fv from (by exact fresh_u_not_B))) (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B))) (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B))) (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B))) (show w ≠ t from (by exact fresh_w_ne_t)) (show w ≠ u from (by exact fresh_w_ne_u)) (show w ≠ x from (by exact fresh_w_ne_x)) (show w ≠ y from (by exact fresh_w_ne_y)) (show w ≠ z from (by exact fresh_w_ne_z)) (show t ≠ u from (by exact fresh_t_ne_u)) (show t ≠ x from (by exact fresh_t_ne_x)) (show t ≠ y from (by exact fresh_t_ne_y)) (show t ≠ z from (by exact fresh_t_ne_z)) (show u ≠ x from (by exact fresh_u_ne_x)) (show u ≠ y from (by exact fresh_u_ne_y)) (show u ≠ z from (by exact fresh_u_ne_z)) (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z)) (show y ≠ z from (by exact fresh_y_ne_z))
  have p0008 :=
    @g_n_3eqtr4g (.classEq A B) (.cab x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (syn_wex w (syn_wex t (syn_wex u (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w)))) (.classEq (.cv z) (syn_copk (.cv t) (.cv u))) (.classMem (syn_copk (.cv w) (.cv t)) A))))))))) (.cab x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (syn_wex w (syn_wex t (syn_wex u (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w)))) (.classEq (.cv z) (syn_copk (.cv t) (.cv u))) (.classMem (syn_copk (.cv w) (.cv t)) B))))))))) (syn_cins3k A) (syn_cins3k B) p0005 p0006 p0007
  exact p0008

noncomputable def g_imakeq1
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cimak A C) (syn_cimak B C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
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
  have fresh_y_not_C : y ∉ C.fv := by
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
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have p0000 :=
    @g_eleq2 A B (syn_copk (.cv y) (.cv x))
  have p0001 :=
    @g_rexbidv (.classEq A B) (.classMem (syn_copk (.cv y) (.cv x)) A) (.classMem (syn_copk (.cv y) (.cv x)) B) y C (by exact (show y ∉ ((Wff.classEq A B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ (B).fv from (by exact fresh_y_not_B))))))) p0000
  have p0002 :=
    @g_abbidv (.classEq A B) (syn_wrex y C (.classMem (syn_copk (.cv y) (.cv x)) A)) (syn_wrex y C (.classMem (syn_copk (.cv y) (.cv x)) B)) x (by exact (show x ∉ ((Wff.classEq A B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ (B).fv from (by exact fresh_x_not_B))))))) p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_imak x y A C (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show x ∉ (C).fv from (by exact fresh_x_not_C))) (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C))) (show x ≠ y from (by exact fresh_x_ne_y))
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_imak x y B C (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B))) (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B))) (by exact (show x ∉ (C).fv from (by exact fresh_x_not_C))) (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C))) (show x ≠ y from (by exact fresh_x_ne_y))
  have p0005 :=
    @g_n_3eqtr4g (.classEq A B) (.cab x (syn_wrex y C (.classMem (syn_copk (.cv y) (.cv x)) A))) (.cab x (syn_wrex y C (.classMem (syn_copk (.cv y) (.cv x)) B))) (syn_cimak A C) (syn_cimak B C) p0002 p0003 p0004
  exact p0005

noncomputable def g_imakeq2
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cimak C A) (syn_cimak C B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
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
  have fresh_y_not_C : y ∉ C.fv := by
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
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have p0000 :=
    @g_rexeq (.classMem (syn_copk (.cv y) (.cv x)) C) y A B (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
  have p0001 :=
    @g_abbidv (.classEq A B) (syn_wrex y A (.classMem (syn_copk (.cv y) (.cv x)) C)) (syn_wrex y B (.classMem (syn_copk (.cv y) (.cv x)) C)) x (by exact (show x ∉ ((Wff.classEq A B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ (B).fv from (by exact fresh_x_not_B))))))) p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_imak x y C A (by exact (show x ∉ (C).fv from (by exact fresh_x_not_C))) (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C))) (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (show x ≠ y from (by exact fresh_x_ne_y))
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_imak x y C B (by exact (show x ∉ (C).fv from (by exact fresh_x_not_C))) (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C))) (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B))) (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B))) (show x ≠ y from (by exact fresh_x_ne_y))
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B) (.cab x (syn_wrex y A (.classMem (syn_copk (.cv y) (.cv x)) C))) (.cab x (syn_wrex y B (.classMem (syn_copk (.cv y) (.cv x)) C))) (syn_cimak C A) (syn_cimak C B) p0001 p0002 p0003
  exact p0004

noncomputable def g_imakeq1i
    (A : Class) (B : Class) (C : Class) (hyp_imakeq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_cimak A C) (syn_cimak B C)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_imakeq1 A B C
  have p0001 :=
    Nominal.mp hyp_imakeq1i_1 p0000
  exact p0001

noncomputable def g_imakeq1d
    (ph : Wff) (A : Class) (B : Class) (C : Class) (hyp_imakeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cimak A C) (syn_cimak B C))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_imakeq1 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cimak A C) (syn_cimak B C)) hyp_imakeq1d_1 p0000
  exact p0001

noncomputable def g_imakeq2d
    (ph : Wff) (A : Class) (B : Class) (C : Class) (hyp_imakeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cimak C A) (syn_cimak C B))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_imakeq2 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cimak C A) (syn_cimak C B)) hyp_imakeq1d_1 p0000
  exact p0001

noncomputable def g_p6eq
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cp6 A) (syn_cp6 B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @g_sseq2 A B (syn_cxpk (syn_cvv) (syn_csn (syn_csn (.cv x))))
  have p0001 :=
    @g_abbidv (.classEq A B) (syn_wss (syn_cxpk (syn_cvv) (syn_csn (syn_csn (.cv x)))) A) (syn_wss (syn_cxpk (syn_cvv) (syn_csn (syn_csn (.cv x)))) B) x (by exact (show x ∉ ((Wff.classEq A B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ (B).fv from (by exact fresh_x_not_B))))))) p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_p6 x A (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_p6 x B (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B) (.cab x (syn_wss (syn_cxpk (syn_cvv) (syn_csn (syn_csn (.cv x)))) A)) (.cab x (syn_wss (syn_cxpk (syn_cvv) (syn_csn (syn_csn (.cv x)))) B)) (syn_cp6 A) (syn_cp6 B) p0001 p0002 p0003
  exact p0004

noncomputable def g_sikeq
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_csik A) (syn_csik B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  let t : Var := freshVar proofSupport 4
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
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (h))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (h))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
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
  have fresh_x_ne_t : x ≠ t := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_t_ne_x : t ≠ x :=
    Ne.symm fresh_x_ne_t
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
  have fresh_y_ne_t : y ≠ t := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_t_ne_y : t ≠ y :=
    Ne.symm fresh_y_ne_t
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have fresh_z_ne_t : z ≠ t := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_t_ne_z : t ≠ z :=
    Ne.symm fresh_z_ne_t
  have fresh_w_ne_t : w ≠ t := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_t_ne_w : t ≠ w :=
    Ne.symm fresh_w_ne_t
  have p0000 :=
    @g_eleq2 A B (syn_copk (.cv w) (.cv t))
  have p0001 :=
    @g_n_3anbi3d (.classEq A B) (.classMem (syn_copk (.cv w) (.cv t)) A) (.classMem (syn_copk (.cv w) (.cv t)) B) (.classEq (.cv y) (syn_csn (.cv w))) (.classEq (.cv z) (syn_csn (.cv t))) p0000
  have p0002 :=
    @g_n_2exbidv (.classEq A B) (syn_w3a (.classEq (.cv y) (syn_csn (.cv w))) (.classEq (.cv z) (syn_csn (.cv t))) (.classMem (syn_copk (.cv w) (.cv t)) A)) (syn_w3a (.classEq (.cv y) (syn_csn (.cv w))) (.classEq (.cv z) (syn_csn (.cv t))) (.classMem (syn_copk (.cv w) (.cv t)) B)) w t (by exact (show w ∉ ((Wff.classEq A B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show w ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ (A).fv from (by exact fresh_w_not_A)) (show w ∉ (B).fv from (by exact fresh_w_not_B))))))) (by exact (show t ∉ ((Wff.classEq A B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show t ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ (A).fv from (by exact fresh_t_not_A)) (show t ∉ (B).fv from (by exact fresh_t_not_B))))))) p0001
  have p0003 :=
    @g_anbi2d (.classEq A B) (syn_wex w (syn_wex t (syn_w3a (.classEq (.cv y) (syn_csn (.cv w))) (.classEq (.cv z) (syn_csn (.cv t))) (.classMem (syn_copk (.cv w) (.cv t)) A)))) (syn_wex w (syn_wex t (syn_w3a (.classEq (.cv y) (syn_csn (.cv w))) (.classEq (.cv z) (syn_csn (.cv t))) (.classMem (syn_copk (.cv w) (.cv t)) B)))) (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) p0002
  have p0004 :=
    @g_n_2exbidv (.classEq A B) (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (syn_wex w (syn_wex t (syn_w3a (.classEq (.cv y) (syn_csn (.cv w))) (.classEq (.cv z) (syn_csn (.cv t))) (.classMem (syn_copk (.cv w) (.cv t)) A))))) (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (syn_wex w (syn_wex t (syn_w3a (.classEq (.cv y) (syn_csn (.cv w))) (.classEq (.cv z) (syn_csn (.cv t))) (.classMem (syn_copk (.cv w) (.cv t)) B))))) y z (by exact (show y ∉ ((Wff.classEq A B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (A).fv from (by exact fresh_y_not_A)) (show y ∉ (B).fv from (by exact fresh_y_not_B))))))) (by exact (show z ∉ ((Wff.classEq A B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show z ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ (A).fv from (by exact fresh_z_not_A)) (show z ∉ (B).fv from (by exact fresh_z_not_B))))))) p0003
  have p0005 :=
    @g_abbidv (.classEq A B) (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (syn_wex w (syn_wex t (syn_w3a (.classEq (.cv y) (syn_csn (.cv w))) (.classEq (.cv z) (syn_csn (.cv t))) (.classMem (syn_copk (.cv w) (.cv t)) A))))))) (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (syn_wex w (syn_wex t (syn_w3a (.classEq (.cv y) (syn_csn (.cv w))) (.classEq (.cv z) (syn_csn (.cv t))) (.classMem (syn_copk (.cv w) (.cv t)) B))))))) x (by exact (show x ∉ ((Wff.classEq A B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ (B).fv from (by exact fresh_x_not_B))))))) p0004
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sik x y z t w A (by exact (show w ∉ (A).fv from (by exact fresh_w_not_A))) (by exact (show t ∉ (A).fv from (by exact fresh_t_not_A))) (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A))) (show w ≠ t from (by exact fresh_w_ne_t)) (show w ≠ x from (by exact fresh_w_ne_x)) (show w ≠ y from (by exact fresh_w_ne_y)) (show w ≠ z from (by exact fresh_w_ne_z)) (show t ≠ x from (by exact fresh_t_ne_x)) (show t ≠ y from (by exact fresh_t_ne_y)) (show t ≠ z from (by exact fresh_t_ne_z)) (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z)) (show y ≠ z from (by exact fresh_y_ne_z))
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sik x y z t w B (by exact (show w ∉ (B).fv from (by exact fresh_w_not_B))) (by exact (show t ∉ (B).fv from (by exact fresh_t_not_B))) (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B))) (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B))) (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B))) (show w ≠ t from (by exact fresh_w_ne_t)) (show w ≠ x from (by exact fresh_w_ne_x)) (show w ≠ y from (by exact fresh_w_ne_y)) (show w ≠ z from (by exact fresh_w_ne_z)) (show t ≠ x from (by exact fresh_t_ne_x)) (show t ≠ y from (by exact fresh_t_ne_y)) (show t ≠ z from (by exact fresh_t_ne_z)) (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z)) (show y ≠ z from (by exact fresh_y_ne_z))
  have p0008 :=
    @g_n_3eqtr4g (.classEq A B) (.cab x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (syn_wex w (syn_wex t (syn_w3a (.classEq (.cv y) (syn_csn (.cv w))) (.classEq (.cv z) (syn_csn (.cv t))) (.classMem (syn_copk (.cv w) (.cv t)) A)))))))) (.cab x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (syn_wex w (syn_wex t (syn_w3a (.classEq (.cv y) (syn_csn (.cv w))) (.classEq (.cv z) (syn_csn (.cv t))) (.classMem (syn_copk (.cv w) (.cv t)) B)))))))) (syn_csik A) (syn_csik B) p0005 p0006 p0007
  exact p0008

noncomputable def g_opkelopkabg
    (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) (V : Class) (W : Class) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_C_z : z ∉ C.fv) (dv_ch_z : z ∉ ch.fv) (dv_ph_x : x ∉ ph.fv) (dv_ps_y : y ∉ ps.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) (hyp_opkelopkabg_1 : Nominal.NPrf (.classEq A (.cab x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) ph)))))) (hyp_opkelopkabg_2 : Nominal.NPrf (.imp (.classEq (.cv y) B) (syn_wb ph ps))) (hyp_opkelopkabg_3 : Nominal.NPrf (.imp (.classEq (.cv z) C) (syn_wb ps ch))) :
    Nominal.NPrf (.imp (syn_wa (.classMem B V) (.classMem C W)) (syn_wb (.classMem (syn_copk B C) A) ch)) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ V.fv ∪ W.fv
  have p0000 :=
    @g_opkex B C
  have p0001 :=
    @g_eqeq1 (.cv x) (syn_copk B C) (syn_copk (.cv y) (.cv z))
  have p0002 :=
    @g_eqcom (syn_copk B C) (syn_copk (.cv y) (.cv z))
  have p0003 :=
    @g_syl6bb (.classEq (.cv x) (syn_copk B C)) (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C)) p0001 p0002
  have p0004 :=
    @g_anbi1d (.classEq (.cv x) (syn_copk B C)) (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C)) ph p0003
  have p0005 :=
    @g_n_2exbidv (.classEq (.cv x) (syn_copk B C)) (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) ph) (syn_wa (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C)) ph) y z (by exact (show y ∉ ((Wff.classEq (.cv x) (syn_copk B C))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ (((Class.cv x)).fv) ∪ (((syn_copk B C)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact Ne.symm dv_x_y)))))) (show y ∉ ((syn_copk B C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show y ∉ ((B).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (B).fv from (by exact dv_B_y)) (show y ∉ (C).fv from (by exact dv_C_y))))))))))) (by exact (show z ∉ ((Wff.classEq (.cv x) (syn_copk B C))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show z ∉ (((Class.cv x)).fv) ∪ (((syn_copk B C)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact Ne.symm dv_x_z)))))) (show z ∉ ((syn_copk B C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show z ∉ ((B).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ (B).fv from (by exact dv_B_z)) (show z ∉ (C).fv from (by exact dv_C_z))))))))))) p0004
  have p0006 :=
    @g_elab2 (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) ph))) (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C)) ph))) x (syn_copk B C) A (by exact (show x ∉ ((syn_copk B C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show x ∉ ((B).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (B).fv from (by exact dv_B_x)) (show x ∉ (C).fv from (by exact dv_C_x))))))) (by exact (show x ∉ ((syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C)) ph)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex]; exact (show x ∉ (((syn_wex z (syn_wa (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C)) ph))).fv).erase y from (fun hmem => (show x ∉ ((syn_wex z (syn_wa (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C)) ph))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex]; exact (show x ∉ (((syn_wa (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C)) ph)).fv).erase z from (fun hmem => (show x ∉ ((syn_wa (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C)) ph)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show x ∉ (((Wff.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C))).fv) ∪ ((ph).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Wff.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ (((syn_copk (.cv y) (.cv z))).fv) ∪ (((syn_copk B C)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_copk (.cv y) (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show x ∉ (((Class.cv y)).fv) ∪ (((Class.cv z)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ y from (by exact dv_x_y)))))) (show x ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ z from (by exact dv_x_z)))))))))) (show x ∉ ((syn_copk B C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show x ∉ ((B).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (B).fv from (by exact dv_B_x)) (show x ∉ (C).fv from (by exact dv_C_x)))))))))) (show x ∉ (ph).fv from (by exact dv_ph_x)))))) (Finset.mem_of_mem_erase hmem))))) (Finset.mem_of_mem_erase hmem)))))) p0000 p0005 hyp_opkelopkabg_1
  have p0007 :=
    @g_elex B V
  have p0008 :=
    @g_elex C W
  have p0009 :=
    @g_vex y
  have p0010 :=
    @g_vex z
  have p0011 :=
    @g_opkthg (.cv y) (.cv z) B C (syn_cvv) (syn_cvv) (syn_cvv)
  have p0012 :=
    @g_mp3an12 (.classMem (.cv y) (syn_cvv)) (.classMem (.cv z) (syn_cvv)) (.classMem C (syn_cvv)) (syn_wb (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C)) (syn_wa (.classEq (.cv y) B) (.classEq (.cv z) C))) p0009 p0010 p0011
  have p0013 :=
    @g_adantl (.classMem C (syn_cvv)) (syn_wb (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C)) (syn_wa (.classEq (.cv y) B) (.classEq (.cv z) C))) (.classMem B (syn_cvv)) p0012
  have p0014 :=
    @g_anbi1d (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C)) (syn_wa (.classEq (.cv y) B) (.classEq (.cv z) C)) ph p0013
  have p0015 :=
    @g_anass (.classEq (.cv y) B) (.classEq (.cv z) C) ph
  have p0016 :=
    @g_syl6bb (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C)) ph) (syn_wa (syn_wa (.classEq (.cv y) B) (.classEq (.cv z) C)) ph) (syn_wa (.classEq (.cv y) B) (syn_wa (.classEq (.cv z) C) ph)) p0014 p0015
  have p0017 :=
    @g_exbidv (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C)) ph) (syn_wa (.classEq (.cv y) B) (syn_wa (.classEq (.cv z) C) ph)) z (by exact (show z ∉ ((syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show z ∉ (((Wff.classMem B (syn_cvv))).fv) ∪ (((Wff.classMem C (syn_cvv))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Wff.classMem B (syn_cvv))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show z ∉ ((B).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ (B).fv from (by exact dv_B_z)) (show z ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show z ∉ ((Wff.classMem C (syn_cvv))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show z ∉ ((C).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ (C).fv from (by exact dv_C_z)) (show z ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) p0016
  have p0018 :=
    @g_n_19_42v (.classEq (.cv y) B) (syn_wa (.classEq (.cv z) C) ph) z (by exact (show z ∉ ((Wff.classEq (.cv y) B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show z ∉ (((Class.cv y)).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact Ne.symm dv_y_z)))))) (show z ∉ (B).fv from (by exact dv_B_z)))))))
  have p0019 :=
    @g_syl6bb (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (syn_wex z (syn_wa (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C)) ph)) (syn_wex z (syn_wa (.classEq (.cv y) B) (syn_wa (.classEq (.cv z) C) ph))) (syn_wa (.classEq (.cv y) B) (syn_wex z (syn_wa (.classEq (.cv z) C) ph))) p0017 p0018
  have p0020 :=
    @g_exbidv (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (syn_wex z (syn_wa (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C)) ph)) (syn_wa (.classEq (.cv y) B) (syn_wex z (syn_wa (.classEq (.cv z) C) ph))) y (by exact (show y ∉ ((syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show y ∉ (((Wff.classMem B (syn_cvv))).fv) ∪ (((Wff.classMem C (syn_cvv))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Wff.classMem B (syn_cvv))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ ((B).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (B).fv from (by exact dv_B_y)) (show y ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show y ∉ ((Wff.classMem C (syn_cvv))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ ((C).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ (C).fv from (by exact dv_C_y)) (show y ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) p0019
  have p0021 :=
    @g_anbi2d (.classEq (.cv y) B) ph ps (.classEq (.cv z) C) hyp_opkelopkabg_2
  have p0022 :=
    @g_exbidv (.classEq (.cv y) B) (syn_wa (.classEq (.cv z) C) ph) (syn_wa (.classEq (.cv z) C) ps) z (by exact (show z ∉ ((Wff.classEq (.cv y) B)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show z ∉ (((Class.cv y)).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact Ne.symm dv_y_z)))))) (show z ∉ (B).fv from (by exact dv_B_z))))))) p0021
  have p0023 :=
    @g_ceqsexgv (syn_wex z (syn_wa (.classEq (.cv z) C) ph)) (syn_wex z (syn_wa (.classEq (.cv z) C) ps)) y B (syn_cvv) (by exact (show y ∉ (B).fv from (by exact dv_B_y))) (by exact (show y ∉ ((syn_wex z (syn_wa (.classEq (.cv z) C) ps))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex]; exact (show y ∉ (((syn_wa (.classEq (.cv z) C) ps)).fv).erase z from (fun hmem => (show y ∉ ((syn_wa (.classEq (.cv z) C) ps)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show y ∉ (((Wff.classEq (.cv z) C)).fv) ∪ ((ps).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Wff.classEq (.cv z) C)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ (((Class.cv z)).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ z from (by exact dv_y_z)))))) (show y ∉ (C).fv from (by exact dv_C_y)))))) (show y ∉ (ps).fv from (by exact dv_ps_y)))))) (Finset.mem_of_mem_erase hmem)))))) p0022
  have p0024 :=
    @g_adantr (.classMem B (syn_cvv)) (syn_wb (syn_wex y (syn_wa (.classEq (.cv y) B) (syn_wex z (syn_wa (.classEq (.cv z) C) ph)))) (syn_wex z (syn_wa (.classEq (.cv z) C) ps))) (.classMem C (syn_cvv)) p0023
  have p0025 :=
    @g_ceqsexgv ps ch z C (syn_cvv) (by exact (show z ∉ (C).fv from (by exact dv_C_z))) (by exact (show z ∉ (ch).fv from (by exact dv_ch_z))) hyp_opkelopkabg_3
  have p0026 :=
    @g_adantl (.classMem C (syn_cvv)) (syn_wb (syn_wex z (syn_wa (.classEq (.cv z) C) ps)) ch) (.classMem B (syn_cvv)) p0025
  have p0027 :=
    @g_n_3bitrd (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C)) ph))) (syn_wex y (syn_wa (.classEq (.cv y) B) (syn_wex z (syn_wa (.classEq (.cv z) C) ph)))) (syn_wex z (syn_wa (.classEq (.cv z) C) ps)) ch p0020 p0024 p0026
  have p0028 :=
    @g_syl2an (.classMem B V) (.classMem B (syn_cvv)) (.classMem C (syn_cvv)) (syn_wb (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C)) ph))) ch) (.classMem C W) p0007 p0008 p0027
  have p0029 :=
    @g_syl5bb (.classMem (syn_copk B C) A) (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C)) ph))) (syn_wa (.classMem B V) (.classMem C W)) ch p0006 p0028
  exact p0029



#print axioms g_opkelopkabg

end NFChoice.DirectNominalPrf.WPPReplay
