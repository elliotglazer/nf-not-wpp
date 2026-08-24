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
import NominalWPPReplayChunk009StructuralPart033


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

noncomputable def g_nnsucelr
    (A : Class) (M : Class) (X : Class) (hyp_nnsucelr_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_nnsucelr_2 : Nominal.NPrf (.classMem X (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wa (.classMem M (syn_cnnc)) (syn_wa (.neg (.classMem X A)) (.classMem (syn_cun A (syn_csn X)) (syn_cplc M (syn_c1c))))) (.classMem A M)) := by
  let proofSupport : Finset Var := A.fv ∪ M.fv ∪ X.fv
  let x : Var := freshVar proofSupport 0
  let a : Var := freshVar proofSupport 1
  let m : Var := freshVar proofSupport 2
  let y : Var := freshVar proofSupport 3
  let z : Var := freshVar proofSupport 4
  let c : Var := freshVar proofSupport 5
  let n : Var := freshVar proofSupport 6
  let b : Var := freshVar proofSupport 7
  let w : Var := freshVar proofSupport 8
  let d : Var := freshVar proofSupport 9
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_M : x ∉ M.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_X : x ∉ X.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_a_not_M : a ∉ M.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_X : a ∉ X.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_m : m ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_m_not_A : m ∉ A.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_m_not_M : m ∉ M.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_m_not_X : m ∉ X.fv := by
    intro h
    exact fresh_m (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_M : y ∉ M.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_X : y ∉ X.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_M : z ∉ M.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_X : z ∉ X.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_c : c ∉ proofSupport := by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_c_not_A : c ∉ A.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_c_not_M : c ∉ M.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_c_not_X : c ∉ X.fv := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (h))
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_n_not_A : n ∉ A.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_n_not_M : n ∉ M.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_not_X : n ∉ X.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 7 ∉ proofSupport
    exact freshVar_not_mem proofSupport 7
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_b_not_M : b ∉ M.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_not_X : b ∉ X.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 8 ∉ proofSupport
    exact freshVar_not_mem proofSupport 8
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_w_not_M : w ∉ M.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_X : w ∉ X.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_d : d ∉ proofSupport := by
    change freshVar proofSupport 9 ∉ proofSupport
    exact freshVar_not_mem proofSupport 9
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_d_not_M : d ∉ M.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_not_X : d ∉ X.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_x_ne_a : x ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_x : a ≠ x :=
    Ne.symm fresh_x_ne_a
  have fresh_x_ne_m : x ≠ m := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_m_ne_x : m ≠ x :=
    Ne.symm fresh_x_ne_m
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_x_ne_c : x ≠ c := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_c_ne_x : c ≠ x :=
    Ne.symm fresh_x_ne_c
  have fresh_x_ne_n : x ≠ n := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_n_ne_x : n ≠ x :=
    Ne.symm fresh_x_ne_n
  have fresh_x_ne_b : x ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 0) (j := 7) (by decide)
  have fresh_b_ne_x : b ≠ x :=
    Ne.symm fresh_x_ne_b
  have fresh_x_ne_w : x ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 0) (j := 8) (by decide)
  have fresh_w_ne_x : w ≠ x :=
    Ne.symm fresh_x_ne_w
  have fresh_x_ne_d : x ≠ d := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 0) (j := 9) (by decide)
  have fresh_d_ne_x : d ≠ x :=
    Ne.symm fresh_x_ne_d
  have fresh_a_ne_m : a ≠ m := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_m_ne_a : m ≠ a :=
    Ne.symm fresh_a_ne_m
  have fresh_a_ne_y : a ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_y_ne_a : y ≠ a :=
    Ne.symm fresh_a_ne_y
  have fresh_a_ne_z : a ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_z_ne_a : z ≠ a :=
    Ne.symm fresh_a_ne_z
  have fresh_a_ne_c : a ≠ c := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_c_ne_a : c ≠ a :=
    Ne.symm fresh_a_ne_c
  have fresh_a_ne_n : a ≠ n := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_n_ne_a : n ≠ a :=
    Ne.symm fresh_a_ne_n
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 1) (j := 7) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have fresh_a_ne_w : a ≠ w := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 1) (j := 8) (by decide)
  have fresh_w_ne_a : w ≠ a :=
    Ne.symm fresh_a_ne_w
  have fresh_a_ne_d : a ≠ d := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 1) (j := 9) (by decide)
  have fresh_d_ne_a : d ≠ a :=
    Ne.symm fresh_a_ne_d
  have fresh_m_ne_y : m ≠ y := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_y_ne_m : y ≠ m :=
    Ne.symm fresh_m_ne_y
  have fresh_m_ne_z : m ≠ z := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_z_ne_m : z ≠ m :=
    Ne.symm fresh_m_ne_z
  have fresh_m_ne_c : m ≠ c := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_c_ne_m : c ≠ m :=
    Ne.symm fresh_m_ne_c
  have fresh_m_ne_n : m ≠ n := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_n_ne_m : n ≠ m :=
    Ne.symm fresh_m_ne_n
  have fresh_m_ne_b : m ≠ b := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 2) (j := 7) (by decide)
  have fresh_b_ne_m : b ≠ m :=
    Ne.symm fresh_m_ne_b
  have fresh_m_ne_w : m ≠ w := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 2) (j := 8) (by decide)
  have fresh_w_ne_m : w ≠ m :=
    Ne.symm fresh_m_ne_w
  have fresh_m_ne_d : m ≠ d := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 2) (j := 9) (by decide)
  have fresh_d_ne_m : d ≠ m :=
    Ne.symm fresh_m_ne_d
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_y_ne_c : y ≠ c := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_c_ne_y : c ≠ y :=
    Ne.symm fresh_y_ne_c
  have fresh_y_ne_n : y ≠ n := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_n_ne_y : n ≠ y :=
    Ne.symm fresh_y_ne_n
  have fresh_y_ne_b : y ≠ b := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 3) (j := 7) (by decide)
  have fresh_b_ne_y : b ≠ y :=
    Ne.symm fresh_y_ne_b
  have fresh_y_ne_w : y ≠ w := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 3) (j := 8) (by decide)
  have fresh_w_ne_y : w ≠ y :=
    Ne.symm fresh_y_ne_w
  have fresh_y_ne_d : y ≠ d := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 3) (j := 9) (by decide)
  have fresh_d_ne_y : d ≠ y :=
    Ne.symm fresh_y_ne_d
  have fresh_z_ne_c : z ≠ c := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_c_ne_z : c ≠ z :=
    Ne.symm fresh_z_ne_c
  have fresh_z_ne_n : z ≠ n := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_n_ne_z : n ≠ z :=
    Ne.symm fresh_z_ne_n
  have fresh_z_ne_b : z ≠ b := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 4) (j := 7) (by decide)
  have fresh_b_ne_z : b ≠ z :=
    Ne.symm fresh_z_ne_b
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 4) (j := 8) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have fresh_z_ne_d : z ≠ d := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 4) (j := 9) (by decide)
  have fresh_d_ne_z : d ≠ z :=
    Ne.symm fresh_z_ne_d
  have fresh_c_ne_n : c ≠ n := by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_n_ne_c : n ≠ c :=
    Ne.symm fresh_c_ne_n
  have fresh_c_ne_b : c ≠ b := by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 5) (j := 7) (by decide)
  have fresh_b_ne_c : b ≠ c :=
    Ne.symm fresh_c_ne_b
  have fresh_c_ne_w : c ≠ w := by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 5) (j := 8) (by decide)
  have fresh_w_ne_c : w ≠ c :=
    Ne.symm fresh_c_ne_w
  have fresh_c_ne_d : c ≠ d := by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 5) (j := 9) (by decide)
  have fresh_d_ne_c : d ≠ c :=
    Ne.symm fresh_c_ne_d
  have fresh_n_ne_b : n ≠ b := by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 6) (j := 7) (by decide)
  have fresh_b_ne_n : b ≠ n :=
    Ne.symm fresh_n_ne_b
  have fresh_n_ne_w : n ≠ w := by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 6) (j := 8) (by decide)
  have fresh_w_ne_n : w ≠ n :=
    Ne.symm fresh_n_ne_w
  have fresh_n_ne_d : n ≠ d := by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 6) (j := 9) (by decide)
  have fresh_d_ne_n : d ≠ n :=
    Ne.symm fresh_n_ne_d
  have fresh_b_ne_w : b ≠ w := by
    change freshVar proofSupport 7 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 7) (j := 8) (by decide)
  have fresh_w_ne_b : w ≠ b :=
    Ne.symm fresh_b_ne_w
  have fresh_b_ne_d : b ≠ d := by
    change freshVar proofSupport 7 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 7) (j := 9) (by decide)
  have fresh_d_ne_b : d ≠ b :=
    Ne.symm fresh_b_ne_d
  have fresh_w_ne_d : w ≠ d := by
    change freshVar proofSupport 8 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 8) (j := 9) (by decide)
  have fresh_d_ne_w : d ≠ w :=
    Ne.symm fresh_w_ne_d
  have p0000 :=
    @g_nnsucelrlem1 x m a (show a ≠ m from (by exact fresh_a_ne_m)) (show a ≠ x from (by exact fresh_a_ne_x)) (show m ≠ x from (by exact fresh_m_ne_x))
  have p0001 :=
    @g_addceq1 (.cv m) (syn_c0c) (syn_c1c)
  have p0002 :=
    @g_addcid2 (syn_c1c)
  have p0003 :=
    @g_syl6eq (.classEq (.cv m) (syn_c0c)) (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_c0c) (syn_c1c)) (syn_c1c) p0001 p0002
  have p0004 :=
    @g_eleq2d (.classEq (.cv m) (syn_c0c)) (syn_cplc (.cv m) (syn_c1c)) (syn_c1c) (syn_cun (.cv a) (syn_csn (.cv x))) p0003
  have p0005 :=
    @g_el1c y (syn_cun (.cv a) (syn_csn (.cv x))) (by exact (show y ∉ ((syn_cun (.cv a) (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show y ∉ (((Class.cv a)).fv) ∪ (((syn_csn (.cv x))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ a from (by exact fresh_y_ne_a)))))) (show y ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x)))))))))))))
  have p0006 :=
    @g_syl6bb (.classEq (.cv m) (syn_c0c)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c))) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_c1c)) (syn_wex y (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv y)))) p0004 p0005
  have p0007 :=
    @g_anbi2d (.classEq (.cv m) (syn_c0c)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c))) (syn_wex y (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv y)))) (.neg (.objMem x a)) p0006
  have p0008 :=
    @g_eleq2 (.cv m) (syn_c0c) (.cv a)
  have p0009 :=
    (by simpa [syn_c0c] using (Nominal.classEqRefl (syn_c0c)))
  have p0010 :=
    @g_eleq2i (syn_c0c) (syn_csn (syn_c0)) (.cv a) p0009
  have p0011 :=
    @g_vex a
  have p0012 :=
    @g_elsnc (.cv a) (syn_c0) p0011
  have p0013 :=
    @g_bitri (.classMem (.cv a) (syn_c0c)) (.classMem (.cv a) (syn_csn (syn_c0))) (.classEq (.cv a) (syn_c0)) p0010 p0012
  have p0014_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv m) (syn_c0c)) (syn_wb (.objMem a m) (.classMem (.cv a) (syn_c0c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_c0c syn_csn syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cvv syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
      p0008
  have p0014 :=
    @g_syl6bb (.classEq (.cv m) (syn_c0c)) (.objMem a m) (.classMem (.cv a) (syn_c0c)) (.classEq (.cv a) (syn_c0)) p0014_e00_recanon p0013
  have p0015 :=
    @g_imbi12d (.classEq (.cv m) (syn_c0c)) (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c)))) (syn_wa (.neg (.objMem x a)) (syn_wex y (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv y))))) (.objMem a m) (.classEq (.cv a) (syn_c0)) p0007 p0014
  have p0016 :=
    @g_n_2albidv (.classEq (.cv m) (syn_c0c)) (.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c)))) (.objMem a m)) (.imp (syn_wa (.neg (.objMem x a)) (syn_wex y (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv y))))) (.classEq (.cv a) (syn_c0))) a x (by exact (show a ∉ ((Wff.classEq (.cv m) (syn_c0c))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show a ∉ (((Class.cv m)).fv) ∪ (((syn_c0c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ m from (by exact fresh_a_ne_m)))))) (show a ∉ ((syn_c0c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) (by exact (show x ∉ ((Wff.classEq (.cv m) (syn_c0c))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ (((Class.cv m)).fv) ∪ (((syn_c0c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ m from (by exact fresh_x_ne_m)))))) (show x ∉ ((syn_c0c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0015
  have p0017 :=
    @g_addceq1 (.cv m) (.cv n) (syn_c1c)
  have p0018_e00_recanon : Nominal.NPrf (.imp (.objEq m n) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cplc syn_wrex syn_wex syn_wa syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0017
  have p0018 :=
    @g_eleq2d (.objEq m n) (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c)) (syn_cun (.cv a) (syn_csn (.cv x))) p0018_e00_recanon
  have p0019 :=
    @g_anbi2d (.objEq m n) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c))) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem x a)) p0018
  have p0020 :=
    @g_eleq2 (.cv m) (.cv n) (.cv a)
  have p0021_e01_recanon : Nominal.NPrf (.imp (.objEq m n) (syn_wb (.objMem a m) (.objMem a n))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
      )
      p0020
  have p0021 :=
    @g_imbi12d (.objEq m n) (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c)))) (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem a m) (.objMem a n) p0019 p0021_e01_recanon
  have p0022 :=
    @g_n_2albidv (.objEq m n) (.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c)))) (.objMem a m)) (.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem a n)) a x (by exact (show a ∉ ((Wff.objEq m n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]; exact (show a ∉ ({m, n} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show a ≠ m from (by exact fresh_a_ne_m)), (show a ≠ n from (by exact fresh_a_ne_n))⟩))))) (by exact (show x ∉ ((Wff.objEq m n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]; exact (show x ∉ ({m, n} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show x ≠ m from (by exact fresh_x_ne_m)), (show x ≠ n from (by exact fresh_x_ne_n))⟩))))) p0021
  have p0023 :=
    @g_eleq12 (.cv x) (.cv z) (.cv a) (.cv c)
  have p0024_e00_recanon : Nominal.NPrf (.imp (syn_wa (.objEq x z) (.objEq a c)) (syn_wb (.objMem x a) (.objMem z c))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
      )
      p0023
  have p0024 :=
    @g_ancoms (.objEq x z) (.objEq a c) (syn_wb (.objMem x a) (.objMem z c)) p0024_e00_recanon
  have p0025 :=
    @g_notbid (syn_wa (.objEq a c) (.objEq x z)) (.objMem x a) (.objMem z c) p0024
  have p0026 :=
    @g_sneq (.cv x) (.cv z)
  have p0027 :=
    @g_uneq12 (.cv a) (.cv c) (syn_csn (.cv x)) (syn_csn (.cv z))
  have p0028_e00_recanon : Nominal.NPrf (.imp (.objEq x z) (.classEq (syn_csn (.cv x)) (syn_csn (.cv z)))) :=
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
      p0026
  have p0028_e01_recanon : Nominal.NPrf (.imp (syn_wa (.objEq a c) (.classEq (syn_csn (.cv x)) (syn_csn (.cv z)))) (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv c) (syn_csn (.cv z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_csn syn_cun syn_cnin syn_wnan syn_ccompl
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
      p0027
  have p0028 :=
    @g_sylan2 (.objEq x z) (.objEq a c) (.classEq (syn_csn (.cv x)) (syn_csn (.cv z))) (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv c) (syn_csn (.cv z)))) p0028_e00_recanon p0028_e01_recanon
  have p0029 :=
    @g_eleq1d (syn_wa (.objEq a c) (.objEq x z)) (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)) p0028
  have p0030 :=
    @g_anbi12d (syn_wa (.objEq a c) (.objEq x z)) (.neg (.objMem x a)) (.neg (.objMem z c)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c))) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))) p0025 p0029
  have p0031 :=
    @g_eleq1 (.cv a) (.cv c) (.cv n)
  have p0032_e00_recanon : Nominal.NPrf (.imp (.objEq a c) (syn_wb (.objMem a n) (.objMem c n))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
      )
      p0031
  have p0032 :=
    @g_adantr (.objEq a c) (syn_wb (.objMem a n) (.objMem c n)) (.objEq x z) p0032_e00_recanon
  have p0033 :=
    @g_imbi12d (syn_wa (.objEq a c) (.objEq x z)) (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c)))) (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem a n) (.objMem c n) p0030 p0032
  have p0034 :=
    @g_cbval2v (.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem a n)) (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)) a x c z (by exact (show z ∉ ((Wff.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem a n))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show z ∉ (((syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c))))).fv) ∪ (((Wff.objMem a n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show z ∉ (((Wff.neg (.objMem x a))).fv) ∪ (((Wff.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Wff.neg (.objMem x a))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_neg]; exact (show z ∉ ((Wff.objMem x a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show z ∉ ({x, a} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show z ≠ x from (by exact fresh_z_ne_x)), (show z ≠ a from (by exact fresh_z_ne_a))⟩)))))) (show z ∉ ((Wff.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show z ∉ (((syn_cun (.cv a) (syn_csn (.cv x)))).fv) ∪ (((syn_cplc (.cv n) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_cun (.cv a) (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show z ∉ (((Class.cv a)).fv) ∪ (((syn_csn (.cv x))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ a from (by exact fresh_z_ne_a)))))) (show z ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))))))))) (show z ∉ ((syn_cplc (.cv n) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show z ∉ (((Class.cv n)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ n from (by exact fresh_z_ne_n)))))) (show z ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))))) (show z ∉ ((Wff.objMem a n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show z ∉ ({a, n} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show z ≠ a from (by exact fresh_z_ne_a)), (show z ≠ n from (by exact fresh_z_ne_n))⟩))))))))) (by exact (show c ∉ ((Wff.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem a n))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show c ∉ (((syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c))))).fv) ∪ (((Wff.objMem a n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show c ∉ (((Wff.neg (.objMem x a))).fv) ∪ (((Wff.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((Wff.neg (.objMem x a))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_neg]; exact (show c ∉ ((Wff.objMem x a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show c ∉ ({x, a} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show c ≠ x from (by exact fresh_c_ne_x)), (show c ≠ a from (by exact fresh_c_ne_a))⟩)))))) (show c ∉ ((Wff.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show c ∉ (((syn_cun (.cv a) (syn_csn (.cv x)))).fv) ∪ (((syn_cplc (.cv n) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((syn_cun (.cv a) (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show c ∉ (((Class.cv a)).fv) ∪ (((syn_csn (.cv x))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ a from (by exact fresh_c_ne_a)))))) (show c ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show c ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ x from (by exact fresh_c_ne_x)))))))))))) (show c ∉ ((syn_cplc (.cv n) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show c ∉ (((Class.cv n)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ n from (by exact fresh_c_ne_n)))))) (show c ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show c ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))))) (show c ∉ ((Wff.objMem a n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show c ∉ ({a, n} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show c ≠ a from (by exact fresh_c_ne_a)), (show c ≠ n from (by exact fresh_c_ne_n))⟩))))))))) (by exact (show a ∉ ((Wff.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show a ∉ (((syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))).fv) ∪ (((Wff.objMem c n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show a ∉ (((Wff.neg (.objMem z c))).fv) ∪ (((Wff.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Wff.neg (.objMem z c))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_neg]; exact (show a ∉ ((Wff.objMem z c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show a ∉ ({z, c} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show a ≠ z from (by exact fresh_a_ne_z)), (show a ≠ c from (by exact fresh_a_ne_c))⟩)))))) (show a ∉ ((Wff.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show a ∉ (((syn_cun (.cv c) (syn_csn (.cv z)))).fv) ∪ (((syn_cplc (.cv n) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((syn_cun (.cv c) (syn_csn (.cv z)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show a ∉ (((Class.cv c)).fv) ∪ (((syn_csn (.cv z))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ c from (by exact fresh_a_ne_c)))))) (show a ∉ ((syn_csn (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show a ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ z from (by exact fresh_a_ne_z)))))))))))) (show a ∉ ((syn_cplc (.cv n) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show a ∉ (((Class.cv n)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ n from (by exact fresh_a_ne_n)))))) (show a ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))))) (show a ∉ ((Wff.objMem c n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show a ∉ ({c, n} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show a ≠ c from (by exact fresh_a_ne_c)), (show a ≠ n from (by exact fresh_a_ne_n))⟩))))))))) (by exact (show x ∉ ((Wff.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show x ∉ (((syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))).fv) ∪ (((Wff.objMem c n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show x ∉ (((Wff.neg (.objMem z c))).fv) ∪ (((Wff.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Wff.neg (.objMem z c))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_neg]; exact (show x ∉ ((Wff.objMem z c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show x ∉ ({z, c} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show x ≠ z from (by exact fresh_x_ne_z)), (show x ≠ c from (by exact fresh_x_ne_c))⟩)))))) (show x ∉ ((Wff.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((syn_cun (.cv c) (syn_csn (.cv z)))).fv) ∪ (((syn_cplc (.cv n) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cun (.cv c) (syn_csn (.cv z)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show x ∉ (((Class.cv c)).fv) ∪ (((syn_csn (.cv z))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ c from (by exact fresh_x_ne_c)))))) (show x ∉ ((syn_csn (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ z from (by exact fresh_x_ne_z)))))))))))) (show x ∉ ((syn_cplc (.cv n) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ (((Class.cv n)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ n from (by exact fresh_x_ne_n)))))) (show x ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))))) (show x ∉ ((Wff.objMem c n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show x ∉ ({c, n} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show x ≠ c from (by exact fresh_x_ne_c)), (show x ≠ n from (by exact fresh_x_ne_n))⟩))))))))) (show z ≠ a from (by exact fresh_z_ne_a)) (show z ≠ c from (by exact fresh_z_ne_c)) (show a ≠ x from (by exact fresh_a_ne_x)) (show x ≠ c from (by exact fresh_x_ne_c)) p0033
  have p0035 :=
    @g_syl6bb (.objEq m n) (.all a (.all x (.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c)))) (.objMem a m)))) (.all a (.all x (.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem a n)))) (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) p0022 p0034
  have p0036 :=
    @g_addceq1 (.cv m) (syn_cplc (.cv n) (syn_c1c)) (syn_c1c)
  have p0037 :=
    @g_eleq2d (.classEq (.cv m) (syn_cplc (.cv n) (syn_c1c))) (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_c1c)) (syn_cun (.cv a) (syn_csn (.cv x))) p0036
  have p0038 :=
    @g_anbi2d (.classEq (.cv m) (syn_cplc (.cv n) (syn_c1c))) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c))) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_c1c))) (.neg (.objMem x a)) p0037
  have p0039 :=
    @g_eleq2 (.cv m) (syn_cplc (.cv n) (syn_c1c)) (.cv a)
  have p0040_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv m) (syn_cplc (.cv n) (syn_c1c))) (syn_wb (.objMem a m) (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cplc syn_wrex syn_wex syn_wa syn_c1c syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
      p0039
  have p0040 :=
    @g_imbi12d (.classEq (.cv m) (syn_cplc (.cv n) (syn_c1c))) (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c)))) (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_c1c)))) (.objMem a m) (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c))) p0038 p0040_e01_recanon
  have p0041 :=
    @g_n_2albidv (.classEq (.cv m) (syn_cplc (.cv n) (syn_c1c))) (.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c)))) (.objMem a m)) (.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_c1c)))) (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c)))) a x (by exact (show a ∉ ((Wff.classEq (.cv m) (syn_cplc (.cv n) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show a ∉ (((Class.cv m)).fv) ∪ (((syn_cplc (.cv n) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ m from (by exact fresh_a_ne_m)))))) (show a ∉ ((syn_cplc (.cv n) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show a ∉ (((Class.cv n)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ n from (by exact fresh_a_ne_n)))))) (show a ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (by exact (show x ∉ ((Wff.classEq (.cv m) (syn_cplc (.cv n) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ (((Class.cv m)).fv) ∪ (((syn_cplc (.cv n) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ m from (by exact fresh_x_ne_m)))))) (show x ∉ ((syn_cplc (.cv n) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ (((Class.cv n)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ n from (by exact fresh_x_ne_n)))))) (show x ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) p0040
  have p0042 :=
    @g_addceq1 (.cv m) M (syn_c1c)
  have p0043 :=
    @g_eleq2d (.classEq (.cv m) M) (syn_cplc (.cv m) (syn_c1c)) (syn_cplc M (syn_c1c)) (syn_cun (.cv a) (syn_csn (.cv x))) p0042
  have p0044 :=
    @g_anbi2d (.classEq (.cv m) M) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c))) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc M (syn_c1c))) (.neg (.objMem x a)) p0043
  have p0045 :=
    @g_eleq2 (.cv m) M (.cv a)
  have p0046_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv m) M) (syn_wb (.objMem a m) (.classMem (.cv a) M))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
      p0045
  have p0046 :=
    @g_imbi12d (.classEq (.cv m) M) (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c)))) (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc M (syn_c1c)))) (.objMem a m) (.classMem (.cv a) M) p0044 p0046_e01_recanon
  have p0047 :=
    @g_n_2albidv (.classEq (.cv m) M) (.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c)))) (.objMem a m)) (.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc M (syn_c1c)))) (.classMem (.cv a) M)) a x (by exact (show a ∉ ((Wff.classEq (.cv m) M)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show a ∉ (((Class.cv m)).fv) ∪ ((M).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ m from (by exact fresh_a_ne_m)))))) (show a ∉ (M).fv from (by exact fresh_a_not_M))))))) (by exact (show x ∉ ((Wff.classEq (.cv m) M)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show x ∉ (((Class.cv m)).fv) ∪ ((M).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ m from (by exact fresh_x_ne_m)))))) (show x ∉ (M).fv from (by exact fresh_x_not_M))))))) p0046
  have p0048 :=
    @g_vex x
  have p0049 :=
    @g_unsneqsn (.cv a) (.cv x) (.cv y) p0048
  have p0050 :=
    @g_ord (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv y))) (.classEq (.cv a) (syn_c0)) (.classEq (.cv a) (syn_csn (.cv x))) p0049
  have p0051 :=
    @g_snid (.cv x) p0048
  have p0052 :=
    @g_eleq2 (.cv a) (syn_csn (.cv x)) (.cv x)
  have p0053_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv a) (syn_csn (.cv x))) (syn_wb (.objMem x a) (.classMem (.cv x) (syn_csn (.cv x))))) :=
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
      p0052
  have p0053 :=
    @g_mpbiri (.classEq (.cv a) (syn_csn (.cv x))) (.objMem x a) (.classMem (.cv x) (syn_csn (.cv x))) p0051 p0053_e01_recanon
  have p0054 :=
    @g_syl6 (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv y))) (.neg (.classEq (.cv a) (syn_c0))) (.classEq (.cv a) (syn_csn (.cv x))) (.objMem x a) p0050 p0053
  have p0055 :=
    @g_con1d (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv y))) (.classEq (.cv a) (syn_c0)) (.objMem x a) p0054
  have p0056 :=
    @g_exlimiv (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv y))) (.imp (.neg (.objMem x a)) (.classEq (.cv a) (syn_c0))) y (by exact (show y ∉ ((Wff.imp (.neg (.objMem x a)) (.classEq (.cv a) (syn_c0)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show y ∉ (((Wff.neg (.objMem x a))).fv) ∪ (((Wff.classEq (.cv a) (syn_c0))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Wff.neg (.objMem x a))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_neg]; exact (show y ∉ ((Wff.objMem x a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show y ∉ ({x, a} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show y ≠ x from (by exact fresh_y_ne_x)), (show y ≠ a from (by exact fresh_y_ne_a))⟩)))))) (show y ∉ ((Wff.classEq (.cv a) (syn_c0))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show y ∉ (((Class.cv a)).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ a from (by exact fresh_y_ne_a)))))) (show y ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) p0055
  have p0057 :=
    @g_impcom (syn_wex y (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv y)))) (.neg (.objMem x a)) (.classEq (.cv a) (syn_c0)) p0056
  have p0058 :=
    @g_gen2 (.imp (syn_wa (.neg (.objMem x a)) (syn_wex y (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv y))))) (.classEq (.cv a) (syn_c0))) a x p0057
  have p0059 :=
    @g_elsuc y (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c)) b (by exact (show b ∉ ((syn_cun (.cv a) (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show b ∉ (((Class.cv a)).fv) ∪ (((syn_csn (.cv x))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ a from (by exact fresh_b_ne_a)))))) (show b ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show b ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ x from (by exact fresh_b_ne_x))))))))))))) (by exact (show y ∉ ((syn_cun (.cv a) (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show y ∉ (((Class.cv a)).fv) ∪ (((syn_csn (.cv x))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ a from (by exact fresh_y_ne_a)))))) (show y ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ x from (by exact fresh_y_ne_x))))))))))))) (by exact (show b ∉ ((syn_cplc (.cv n) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show b ∉ (((Class.cv n)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ n from (by exact fresh_b_ne_n)))))) (show b ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) (show b ≠ y from (by exact fresh_b_ne_y))
  have p0060 :=
    @g_vex y
  have p0061 :=
    @g_elcompl (.cv y) (.cv b) p0060
  have p0062_e00_recanon : Nominal.NPrf (syn_wb (.classMem (.cv y) (syn_ccompl (.cv b))) (.neg (.objMem y b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
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
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0061
  have p0062 :=
    @g_anbi2i (.classMem (.cv y) (syn_ccompl (.cv b))) (.neg (.objMem y b)) (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) p0062_e00_recanon
  have p0063 :=
    @g_simprrl (.objEq x y) (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a))
  have p0064 :=
    @g_sneq (.cv x) (.cv y)
  have p0065_e00_recanon : Nominal.NPrf (.imp (.objEq x y) (.classEq (syn_csn (.cv x)) (syn_csn (.cv y)))) :=
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
      p0064
  have p0065 :=
    @g_adantr (.objEq x y) (.classEq (syn_csn (.cv x)) (syn_csn (.cv y))) (syn_wa (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a)))) p0065_e00_recanon
  have p0066 :=
    @g_difeq12d (syn_wa (.objEq x y) (syn_wa (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a))))) (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))) (syn_csn (.cv x)) (syn_csn (.cv y)) p0063 p0065
  have p0067 :=
    @g_simprrr (.objEq x y) (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a))
  have p0068 :=
    @g_nnsucelrlem2 (.cv a) (.cv x)
  have p0069_e01_recanon : Nominal.NPrf (.imp (.neg (.objMem x a)) (.classEq (syn_cdif (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv x))) (.cv a))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cun syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0068
  have p0069 :=
    @g_syl (syn_wa (.objEq x y) (syn_wa (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a))))) (.neg (.objMem x a)) (.classEq (syn_cdif (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv x))) (.cv a)) p0067 p0069_e01_recanon
  have p0070 :=
    @g_simprlr (.objEq x y) (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b)) (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a)))
  have p0071 :=
    @g_nnsucelrlem2 (.cv b) (.cv y)
  have p0072_e01_recanon : Nominal.NPrf (.imp (.neg (.objMem y b)) (.classEq (syn_cdif (syn_cun (.cv b) (syn_csn (.cv y))) (syn_csn (.cv y))) (.cv b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cun syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0071
  have p0072 :=
    @g_syl (syn_wa (.objEq x y) (syn_wa (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a))))) (.neg (.objMem y b)) (.classEq (syn_cdif (syn_cun (.cv b) (syn_csn (.cv y))) (syn_csn (.cv y))) (.cv b)) p0070 p0072_e01_recanon
  have p0073 :=
    @g_n_3eqtr3d (syn_wa (.objEq x y) (syn_wa (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a))))) (syn_cdif (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv x))) (syn_cdif (syn_cun (.cv b) (syn_csn (.cv y))) (syn_csn (.cv y))) (.cv a) (.cv b) p0066 p0069 p0072
  have p0074 :=
    @g_simprll (.objEq x y) (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b)) (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a)))
  have p0075 :=
    @g_eqeltrd (syn_wa (.objEq x y) (syn_wa (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a))))) (.cv a) (.cv b) (syn_cplc (.cv n) (syn_c1c)) p0073 p0074
  have p0076 :=
    @g_n_3adantr1 (.objEq x y) (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a))) (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c))) (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) p0075
  have p0077 :=
    @g_ex (.objEq x y) (syn_w3a (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a)))) (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c))) p0076
  have p0078 :=
    @g_simpl (syn_wne (.cv x) (.cv y)) (syn_w3a (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a))))
  have p0079 :=
    @g_simpr3l (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a)) (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wne (.cv x) (.cv y))
  have p0080 :=
    @g_simpr2r (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b)) (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a))) (syn_wne (.cv x) (.cv y))
  have p0081 :=
    @g_nnsucelrlem3 (.cv a) (.cv b) (.cv x) (.cv y) p0048
  have p0082_e03_recanon : Nominal.NPrf (.imp (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem y b))) (.classEq (.cv b) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_wne syn_cun syn_cnin syn_wnan syn_ccompl syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0081
  have p0082 :=
    @g_syl3anc (syn_wa (syn_wne (.cv x) (.cv y)) (syn_w3a (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a))))) (syn_wne (.cv x) (.cv y)) (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem y b)) (.classEq (.cv b) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x)))) p0078 p0079 p0080 p0082_e03_recanon
  have p0083 :=
    @g_simp22r (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b)) (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a))) (syn_wne (.cv x) (.cv y)) (.classEq (.cv b) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))))
  have p0084 :=
    @g_difsn (.cv y) (.cv a)
  have p0085_e00_recanon : Nominal.NPrf (.imp (.neg (.objMem y a)) (.classEq (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv a))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0084
  have p0085 :=
    @g_uneq1d (.neg (.objMem y a)) (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv a) (syn_csn (.cv x)) p0085_e00_recanon
  have p0086 :=
    @g_eqeq2d (.neg (.objMem y a)) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))) (syn_cun (.cv a) (syn_csn (.cv x))) (.cv b) p0085
  have p0087 :=
    @g_biimpcd (.neg (.objMem y a)) (.classEq (.cv b) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x)))) (.classEq (.cv b) (syn_cun (.cv a) (syn_csn (.cv x)))) p0086
  have p0088 :=
    @g_n_3ad2ant3 (.classEq (.cv b) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x)))) (syn_wne (.cv x) (.cv y)) (.imp (.neg (.objMem y a)) (.classEq (.cv b) (syn_cun (.cv a) (syn_csn (.cv x))))) (syn_w3a (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a)))) p0087
  have p0089 :=
    @g_simp23l (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a)) (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wne (.cv x) (.cv y)) (.classEq (.cv b) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))))
  have p0090 :=
    @g_eqeq2d (syn_w3a (syn_wne (.cv x) (.cv y)) (syn_w3a (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a)))) (.classEq (.cv b) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))))) (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))) (.cv b) p0089
  have p0091 :=
    @g_snss (.cv y) (.cv b) p0060
  have p0092 :=
    @g_ssequn2 (syn_csn (.cv y)) (.cv b)
  have p0093_e00_recanon : Nominal.NPrf (syn_wb (.objMem y b) (syn_wss (syn_csn (.cv y)) (.cv b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
      p0091
  have p0093 :=
    @g_bitr2i (.objMem y b) (syn_wss (syn_csn (.cv y)) (.cv b)) (.classEq (syn_cun (.cv b) (syn_csn (.cv y))) (.cv b)) p0093_e00_recanon p0092
  have p0094 :=
    @g_biimpi (.classEq (syn_cun (.cv b) (syn_csn (.cv y))) (.cv b)) (.objMem y b) p0093
  have p0095 :=
    @g_eqcoms (.objMem y b) (syn_cun (.cv b) (syn_csn (.cv y))) (.cv b) p0094
  have p0096 :=
    @g_syl6bi (syn_w3a (syn_wne (.cv x) (.cv y)) (syn_w3a (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a)))) (.classEq (.cv b) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))))) (.classEq (.cv b) (syn_cun (.cv a) (syn_csn (.cv x)))) (.classEq (.cv b) (syn_cun (.cv b) (syn_csn (.cv y)))) (.objMem y b) p0090 p0095
  have p0097 :=
    @g_syld (syn_w3a (syn_wne (.cv x) (.cv y)) (syn_w3a (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a)))) (.classEq (.cv b) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))))) (.neg (.objMem y a)) (.classEq (.cv b) (syn_cun (.cv a) (syn_csn (.cv x)))) (.objMem y b) p0088 p0096
  have p0098 :=
    @g_mt3d (syn_w3a (syn_wne (.cv x) (.cv y)) (syn_w3a (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a)))) (.classEq (.cv b) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))))) (.objMem y a) (.objMem y b) p0083 p0097
  have p0099 :=
    @g_nnsucelrlem4 (.cv y) (.cv a)
  have p0100_e01_recanon : Nominal.NPrf (.imp (.objMem y a) (.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))) (.cv a))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_cdif syn_cin syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0099
  have p0100 :=
    @g_syl (syn_w3a (syn_wne (.cv x) (.cv y)) (syn_w3a (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a)))) (.classEq (.cv b) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))))) (.objMem y a) (.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))) (.cv a)) p0098 p0100_e01_recanon
  have p0101 :=
    @g_simpl3r (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a)) (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (.classEq (.cv b) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))))
  have p0102 :=
    @g_difss (.cv a) (syn_csn (.cv y))
  have p0103 :=
    @g_sseli (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv a) (.cv x) p0102
  have p0104_e01_recanon : Nominal.NPrf (.imp (.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y)))) (.objMem x a)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
      )
      p0103
  have p0104 :=
    @g_nsyl (syn_wa (syn_w3a (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a)))) (.classEq (.cv b) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))))) (.objMem x a) (.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y)))) p0101 p0104_e01_recanon
  have p0105 :=
    @g_simp2l (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b)) (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a)))
  have p0106 :=
    @g_eleq1 (.cv b) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c))
  have p0107 :=
    @g_biimpd (.classEq (.cv b) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x)))) (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.classMem (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c))) p0106
  have p0108 :=
    @g_mpan9 (syn_w3a (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a)))) (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.classEq (.cv b) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x)))) (.classMem (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c))) p0105 p0107
  have p0109 :=
    @g_simpl1 (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a))) (.classEq (.cv b) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))))
  have p0110 :=
    @g_snex (.cv y)
  have p0111 :=
    @g_difex (.cv a) (syn_csn (.cv y)) p0011 p0110
  have p0112 :=
    @g_eleq12 (.cv z) (.cv x) (.cv c) (syn_cdif (.cv a) (syn_csn (.cv y)))
  have p0113_e00_recanon : Nominal.NPrf (.imp (syn_wa (.objEq z x) (.classEq (.cv c) (syn_cdif (.cv a) (syn_csn (.cv y))))) (syn_wb (.objMem z c) (.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_csn syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
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
      p0112
  have p0113 :=
    @g_ancoms (.objEq z x) (.classEq (.cv c) (syn_cdif (.cv a) (syn_csn (.cv y)))) (syn_wb (.objMem z c) (.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y))))) p0113_e00_recanon
  have p0114 :=
    @g_notbid (syn_wa (.classEq (.cv c) (syn_cdif (.cv a) (syn_csn (.cv y)))) (.objEq z x)) (.objMem z c) (.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y)))) p0113
  have p0115 :=
    @g_sneq (.cv z) (.cv x)
  have p0116 :=
    @g_uneq12 (.cv c) (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv z)) (syn_csn (.cv x))
  have p0117_e00_recanon : Nominal.NPrf (.imp (.objEq z x) (.classEq (syn_csn (.cv z)) (syn_csn (.cv x)))) :=
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
      p0115
  have p0117 :=
    @g_sylan2 (.objEq z x) (.classEq (.cv c) (syn_cdif (.cv a) (syn_csn (.cv y)))) (.classEq (syn_csn (.cv z)) (syn_csn (.cv x))) (.classEq (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x)))) p0117_e00_recanon p0116
  have p0118 :=
    @g_eleq1d (syn_wa (.classEq (.cv c) (syn_cdif (.cv a) (syn_csn (.cv y)))) (.objEq z x)) (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c)) p0117
  have p0119 :=
    @g_anbi12d (syn_wa (.classEq (.cv c) (syn_cdif (.cv a) (syn_csn (.cv y)))) (.objEq z x)) (.neg (.objMem z c)) (.neg (.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y))))) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))) (.classMem (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c))) p0114 p0118
  have p0120 :=
    @g_eleq1 (.cv c) (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv n)
  have p0121_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv c) (syn_cdif (.cv a) (syn_csn (.cv y)))) (syn_wb (.objMem c n) (.classMem (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_csn syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
      p0120
  have p0121 :=
    @g_adantr (.classEq (.cv c) (syn_cdif (.cv a) (syn_csn (.cv y)))) (syn_wb (.objMem c n) (.classMem (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv n))) (.objEq z x) p0121_e00_recanon
  have p0122 :=
    @g_imbi12d (syn_wa (.classEq (.cv c) (syn_cdif (.cv a) (syn_csn (.cv y)))) (.objEq z x)) (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (syn_wa (.neg (.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y))))) (.classMem (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n) (.classMem (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv n)) p0119 p0121
  have p0123_e00_recanon : Nominal.NPrf (.imp (syn_wa (.classEq (.cv c) (syn_cdif (.cv a) (syn_csn (.cv y)))) (.classEq (.cv z) (.cv x))) (syn_wb (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)) (.imp (syn_wa (.neg (.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y))))) (.classMem (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c)))) (.classMem (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv n))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_csn syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0122
  have p0123 :=
    @g_spc2gv (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)) (.imp (syn_wa (.neg (.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y))))) (.classMem (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c)))) (.classMem (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv n))) c z (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv x) (syn_cvv) (syn_cvv) (by exact (show c ∉ ((syn_cdif (.cv a) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif]; exact (show c ∉ (((Class.cv a)).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ a from (by exact fresh_c_ne_a)))))) (show c ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show c ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ y from (by exact fresh_c_ne_y))))))))))))) (by exact (show z ∉ ((syn_cdif (.cv a) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif]; exact (show z ∉ (((Class.cv a)).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ a from (by exact fresh_z_ne_a)))))) (show z ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y))))))))))))) (by exact (show c ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ x from (by exact fresh_c_ne_x))))))) (by exact (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x))))))) (by exact (show c ∉ ((Wff.imp (syn_wa (.neg (.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y))))) (.classMem (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c)))) (.classMem (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv n)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show c ∉ (((syn_wa (.neg (.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y))))) (.classMem (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c))))).fv) ∪ (((Wff.classMem (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv n))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((syn_wa (.neg (.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y))))) (.classMem (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show c ∉ (((Wff.neg (.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y)))))).fv) ∪ (((Wff.classMem (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((Wff.neg (.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y)))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_neg]; exact (show c ∉ ((Wff.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show c ∉ (((Class.cv x)).fv) ∪ (((syn_cdif (.cv a) (syn_csn (.cv y)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ x from (by exact fresh_c_ne_x)))))) (show c ∉ ((syn_cdif (.cv a) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif]; exact (show c ∉ (((Class.cv a)).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ a from (by exact fresh_c_ne_a)))))) (show c ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show c ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ y from (by exact fresh_c_ne_y)))))))))))))))))) (show c ∉ ((Wff.classMem (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show c ∉ (((syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x)))).fv) ∪ (((syn_cplc (.cv n) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show c ∉ (((syn_cdif (.cv a) (syn_csn (.cv y)))).fv) ∪ (((syn_csn (.cv x))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((syn_cdif (.cv a) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif]; exact (show c ∉ (((Class.cv a)).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ a from (by exact fresh_c_ne_a)))))) (show c ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show c ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ y from (by exact fresh_c_ne_y)))))))))))) (show c ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show c ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ x from (by exact fresh_c_ne_x)))))))))))) (show c ∉ ((syn_cplc (.cv n) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show c ∉ (((Class.cv n)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ n from (by exact fresh_c_ne_n)))))) (show c ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show c ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))))) (show c ∉ ((Wff.classMem (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv n))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show c ∉ (((syn_cdif (.cv a) (syn_csn (.cv y)))).fv) ∪ (((Class.cv n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((syn_cdif (.cv a) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif]; exact (show c ∉ (((Class.cv a)).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ a from (by exact fresh_c_ne_a)))))) (show c ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show c ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ y from (by exact fresh_c_ne_y)))))))))))) (show c ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ n from (by exact fresh_c_ne_n))))))))))))))) (by exact (show z ∉ ((Wff.imp (syn_wa (.neg (.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y))))) (.classMem (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c)))) (.classMem (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv n)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show z ∉ (((syn_wa (.neg (.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y))))) (.classMem (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c))))).fv) ∪ (((Wff.classMem (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv n))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_wa (.neg (.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y))))) (.classMem (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show z ∉ (((Wff.neg (.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y)))))).fv) ∪ (((Wff.classMem (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Wff.neg (.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y)))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_neg]; exact (show z ∉ ((Wff.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show z ∉ (((Class.cv x)).fv) ∪ (((syn_cdif (.cv a) (syn_csn (.cv y)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))) (show z ∉ ((syn_cdif (.cv a) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif]; exact (show z ∉ (((Class.cv a)).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ a from (by exact fresh_z_ne_a)))))) (show z ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y)))))))))))))))))) (show z ∉ ((Wff.classMem (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show z ∉ (((syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x)))).fv) ∪ (((syn_cplc (.cv n) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show z ∉ (((syn_cdif (.cv a) (syn_csn (.cv y)))).fv) ∪ (((syn_csn (.cv x))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_cdif (.cv a) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif]; exact (show z ∉ (((Class.cv a)).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ a from (by exact fresh_z_ne_a)))))) (show z ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y)))))))))))) (show z ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show z ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ x from (by exact fresh_z_ne_x)))))))))))) (show z ∉ ((syn_cplc (.cv n) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show z ∉ (((Class.cv n)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ n from (by exact fresh_z_ne_n)))))) (show z ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))))) (show z ∉ ((Wff.classMem (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv n))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show z ∉ (((syn_cdif (.cv a) (syn_csn (.cv y)))).fv) ∪ (((Class.cv n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((syn_cdif (.cv a) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif]; exact (show z ∉ (((Class.cv a)).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show z ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ a from (by exact fresh_z_ne_a)))))) (show z ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show z ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ y from (by exact fresh_z_ne_y)))))))))))) (show z ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show z ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show z ≠ n from (by exact fresh_z_ne_n))))))))))))))) (show c ≠ z from (by exact fresh_c_ne_z)) p0123_e00_recanon
  have p0124 :=
    @g_mp2an (.classMem (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_cvv)) (.classMem (.cv x) (syn_cvv)) (.imp (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (.imp (syn_wa (.neg (.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y))))) (.classMem (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c)))) (.classMem (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv n)))) p0111 p0048 p0123
  have p0125 :=
    @g_syl (syn_wa (syn_w3a (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a)))) (.classEq (.cv b) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))))) (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (.imp (syn_wa (.neg (.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y))))) (.classMem (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c)))) (.classMem (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv n))) p0109 p0124
  have p0126 :=
    @g_mp2and (syn_wa (syn_w3a (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a)))) (.classEq (.cv b) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))))) (.neg (.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y))))) (.classMem (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c))) (.classMem (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv n)) p0104 p0108 p0125
  have p0127 :=
    @g_n_3adant1 (syn_w3a (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a)))) (.classEq (.cv b) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x)))) (.classMem (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv n)) (syn_wne (.cv x) (.cv y)) p0126
  have p0128 :=
    @g_snid (.cv y) p0060
  have p0129 :=
    @g_eldif (.cv y) (.cv a) (syn_csn (.cv y))
  have p0130_e00_recanon : Nominal.NPrf (syn_wb (.classMem (.cv y) (syn_cdif (.cv a) (syn_csn (.cv y)))) (syn_wa (.objMem y a) (.neg (.classMem (.cv y) (syn_csn (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
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
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0129
  have p0130 :=
    @g_simprbi (.classMem (.cv y) (syn_cdif (.cv a) (syn_csn (.cv y)))) (.objMem y a) (.neg (.classMem (.cv y) (syn_csn (.cv y)))) p0130_e00_recanon
  have p0131 :=
    @g_mt2 (.classMem (.cv y) (syn_cdif (.cv a) (syn_csn (.cv y)))) (.classMem (.cv y) (syn_csn (.cv y))) p0128 p0130
  have p0132 :=
    @g_elcompl (.cv y) (syn_cdif (.cv a) (syn_csn (.cv y))) p0060
  have p0133 :=
    @g_mpbir (.classMem (.cv y) (syn_ccompl (syn_cdif (.cv a) (syn_csn (.cv y))))) (.neg (.classMem (.cv y) (syn_cdif (.cv a) (syn_csn (.cv y))))) p0131 p0132
  have p0134 :=
    @g_eqid (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y)))
  have p0135 :=
    @g_sneq (.cv w) (.cv y)
  have p0136_e00_recanon : Nominal.NPrf (.imp (.objEq w y) (.classEq (syn_csn (.cv w)) (syn_csn (.cv y)))) :=
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
      p0135
  have p0136 :=
    @g_uneq2d (.objEq w y) (syn_csn (.cv w)) (syn_csn (.cv y)) (syn_cdif (.cv a) (syn_csn (.cv y))) p0136_e00_recanon
  have p0137 :=
    @g_eqeq2d (.objEq w y) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv w))) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))) p0136
  have p0138_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv w) (.cv y)) (syn_wb (.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv w)))) (.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_cdif syn_cin syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0137
  have p0138 :=
    @g_rspcev (.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv w)))) (.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y)))) w (.cv y) (syn_ccompl (syn_cdif (.cv a) (syn_csn (.cv y)))) (by exact (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y))))))) (by exact (show w ∉ ((syn_ccompl (syn_cdif (.cv a) (syn_csn (.cv y))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl]; exact (show w ∉ ((syn_cdif (.cv a) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif]; exact (show w ∉ (((Class.cv a)).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ a from (by exact fresh_w_ne_a)))))) (show w ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y))))))))))))))) (by exact (show w ∉ ((Wff.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show w ∉ (((syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y)))).fv) ∪ (((syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show w ∉ (((syn_cdif (.cv a) (syn_csn (.cv y)))).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((syn_cdif (.cv a) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif]; exact (show w ∉ (((Class.cv a)).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ a from (by exact fresh_w_ne_a)))))) (show w ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y)))))))))))) (show w ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y)))))))))))) (show w ∉ ((syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show w ∉ (((syn_cdif (.cv a) (syn_csn (.cv y)))).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((syn_cdif (.cv a) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif]; exact (show w ∉ (((Class.cv a)).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ a from (by exact fresh_w_ne_a)))))) (show w ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y)))))))))))) (show w ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y))))))))))))))))) p0138_e00_recanon
  have p0139 :=
    @g_mp2an (.classMem (.cv y) (syn_ccompl (syn_cdif (.cv a) (syn_csn (.cv y))))) (.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y)))) (syn_wrex w (syn_ccompl (syn_cdif (.cv a) (syn_csn (.cv y)))) (.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv w))))) p0133 p0134 p0138
  have p0140 :=
    @g_compleq (.cv d) (syn_cdif (.cv a) (syn_csn (.cv y)))
  have p0141 :=
    @g_uneq1 (.cv d) (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv w))
  have p0142 :=
    @g_eqeq2d (.classEq (.cv d) (syn_cdif (.cv a) (syn_csn (.cv y)))) (syn_cun (.cv d) (syn_csn (.cv w))) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv w))) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))) p0141
  have p0143 :=
    @g_rexeqbidv (.classEq (.cv d) (syn_cdif (.cv a) (syn_csn (.cv y)))) (.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))) (syn_cun (.cv d) (syn_csn (.cv w)))) (.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv w)))) w (syn_ccompl (.cv d)) (syn_ccompl (syn_cdif (.cv a) (syn_csn (.cv y)))) (by exact (show w ∉ ((syn_ccompl (.cv d))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl]; exact (show w ∉ ((Class.cv d)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({d} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ d from (by exact fresh_w_ne_d))))))))) (by exact (show w ∉ ((syn_ccompl (syn_cdif (.cv a) (syn_csn (.cv y))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl]; exact (show w ∉ ((syn_cdif (.cv a) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif]; exact (show w ∉ (((Class.cv a)).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ a from (by exact fresh_w_ne_a)))))) (show w ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y))))))))))))))) (by exact (show w ∉ ((Wff.classEq (.cv d) (syn_cdif (.cv a) (syn_csn (.cv y))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show w ∉ (((Class.cv d)).fv) ∪ (((syn_cdif (.cv a) (syn_csn (.cv y)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Class.cv d)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({d} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ d from (by exact fresh_w_ne_d)))))) (show w ∉ ((syn_cdif (.cv a) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif]; exact (show w ∉ (((Class.cv a)).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ a from (by exact fresh_w_ne_a)))))) (show w ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y))))))))))))))))) p0140 p0142
  have p0144 :=
    @g_rspcev (syn_wrex w (syn_ccompl (.cv d)) (.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))) (syn_cun (.cv d) (syn_csn (.cv w))))) (syn_wrex w (syn_ccompl (syn_cdif (.cv a) (syn_csn (.cv y)))) (.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv w))))) d (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv n) (by exact (show d ∉ ((syn_cdif (.cv a) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif]; exact (show d ∉ (((Class.cv a)).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show d ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ a from (by exact fresh_d_ne_a)))))) (show d ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show d ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ y from (by exact fresh_d_ne_y))))))))))))) (by exact (show d ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ n from (by exact fresh_d_ne_n))))))) (by exact (show d ∉ ((syn_wrex w (syn_ccompl (syn_cdif (.cv a) (syn_csn (.cv y)))) (.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv w)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex]; exact (show d ∉ ((((syn_ccompl (syn_cdif (.cv a) (syn_csn (.cv y))))).fv).erase w) ∪ ((((Wff.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv w))))).fv).erase w) from (fun hmem => (Finset.mem_union.mp hmem).elim (show d ∉ (((syn_ccompl (syn_cdif (.cv a) (syn_csn (.cv y))))).fv).erase w from (fun hmem => (show d ∉ ((syn_ccompl (syn_cdif (.cv a) (syn_csn (.cv y))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl]; exact (show d ∉ ((syn_cdif (.cv a) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif]; exact (show d ∉ (((Class.cv a)).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show d ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ a from (by exact fresh_d_ne_a)))))) (show d ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show d ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ y from (by exact fresh_d_ne_y)))))))))))))) (Finset.mem_of_mem_erase hmem))) (show d ∉ (((Wff.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv w))))).fv).erase w from (fun hmem => (show d ∉ ((Wff.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv w))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show d ∉ (((syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y)))).fv) ∪ (((syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv w)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show d ∉ ((syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show d ∉ (((syn_cdif (.cv a) (syn_csn (.cv y)))).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show d ∉ ((syn_cdif (.cv a) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif]; exact (show d ∉ (((Class.cv a)).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show d ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ a from (by exact fresh_d_ne_a)))))) (show d ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show d ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ y from (by exact fresh_d_ne_y)))))))))))) (show d ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show d ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ y from (by exact fresh_d_ne_y)))))))))))) (show d ∉ ((syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv w)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show d ∉ (((syn_cdif (.cv a) (syn_csn (.cv y)))).fv) ∪ (((syn_csn (.cv w))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show d ∉ ((syn_cdif (.cv a) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif]; exact (show d ∉ (((Class.cv a)).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show d ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ a from (by exact fresh_d_ne_a)))))) (show d ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show d ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ y from (by exact fresh_d_ne_y)))))))))))) (show d ∉ ((syn_csn (.cv w))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show d ∉ ((Class.cv w)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({w} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ w from (by exact fresh_d_ne_w)))))))))))))))) (Finset.mem_of_mem_erase hmem)))))))) p0143
  have p0145 :=
    @g_elsuc w (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))) (.cv n) d (by exact (show d ∉ ((syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show d ∉ (((syn_cdif (.cv a) (syn_csn (.cv y)))).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show d ∉ ((syn_cdif (.cv a) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif]; exact (show d ∉ (((Class.cv a)).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show d ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ a from (by exact fresh_d_ne_a)))))) (show d ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show d ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ y from (by exact fresh_d_ne_y)))))))))))) (show d ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show d ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ y from (by exact fresh_d_ne_y))))))))))))) (by exact (show w ∉ ((syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show w ∉ (((syn_cdif (.cv a) (syn_csn (.cv y)))).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((syn_cdif (.cv a) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif]; exact (show w ∉ (((Class.cv a)).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show w ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ a from (by exact fresh_w_ne_a)))))) (show w ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y)))))))))))) (show w ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show w ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show w ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show w ≠ y from (by exact fresh_w_ne_y))))))))))))) (by exact (show d ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ n from (by exact fresh_d_ne_n))))))) (show d ≠ w from (by exact fresh_d_ne_w))
  have p0146 :=
    @g_sylibr (syn_wa (.classMem (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv n)) (syn_wrex w (syn_ccompl (syn_cdif (.cv a) (syn_csn (.cv y)))) (.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv w)))))) (syn_wrex d (.cv n) (syn_wrex w (syn_ccompl (.cv d)) (.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))) (syn_cun (.cv d) (syn_csn (.cv w)))))) (.classMem (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))) (syn_cplc (.cv n) (syn_c1c))) p0144 p0145
  have p0147 :=
    @g_sylancl (syn_w3a (syn_wne (.cv x) (.cv y)) (syn_w3a (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a)))) (.classEq (.cv b) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))))) (.classMem (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv n)) (syn_wrex w (syn_ccompl (syn_cdif (.cv a) (syn_csn (.cv y)))) (.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv w))))) (.classMem (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))) (syn_cplc (.cv n) (syn_c1c))) p0127 p0139 p0146
  have p0148 :=
    @g_eqeltrrd (syn_w3a (syn_wne (.cv x) (.cv y)) (syn_w3a (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a)))) (.classEq (.cv b) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))))) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))) (.cv a) (syn_cplc (.cv n) (syn_c1c)) p0100 p0147
  have p0149 :=
    @g_mpd3an3 (syn_wne (.cv x) (.cv y)) (syn_w3a (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a)))) (.classEq (.cv b) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x)))) (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c))) p0082 p0148
  have p0150 :=
    @g_ex (syn_wne (.cv x) (.cv y)) (syn_w3a (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a)))) (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c))) p0149
  have p0151_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv x) (.cv y)) (.imp (syn_w3a (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a)))) (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_cplc syn_wrex syn_wex syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0077
  have p0151 :=
    @g_pm2_61ine (.imp (syn_w3a (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a)))) (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c)))) (.cv x) (.cv y) p0151_e00_recanon p0150
  have p0152 :=
    @g_n_3expa (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a))) (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c))) p0151
  have p0153 :=
    @g_exp32 (syn_wa (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b)))) (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a)) (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c))) p0152
  have p0154 :=
    @g_sylan2b (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.classMem (.cv y) (syn_ccompl (.cv b)))) (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (.imp (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.imp (.neg (.objMem x a)) (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c))))) p0062 p0153
  have p0155 :=
    @g_rexlimdvva (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))) (.imp (.neg (.objMem x a)) (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c)))) b y (syn_cplc (.cv n) (syn_c1c)) (syn_ccompl (.cv b)) (by exact (show y ∉ ((syn_cplc (.cv n) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show y ∉ (((Class.cv n)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ n from (by exact fresh_y_ne_n)))))) (show y ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) (by exact (show b ∉ ((Wff.imp (.neg (.objMem x a)) (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show b ∉ (((Wff.neg (.objMem x a))).fv) ∪ (((Wff.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Wff.neg (.objMem x a))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_neg]; exact (show b ∉ ((Wff.objMem x a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show b ∉ ({x, a} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show b ≠ x from (by exact fresh_b_ne_x)), (show b ≠ a from (by exact fresh_b_ne_a))⟩)))))) (show b ∉ ((Wff.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ (((Class.cv a)).fv) ∪ (((syn_cplc (.cv n) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ a from (by exact fresh_b_ne_a)))))) (show b ∉ ((syn_cplc (.cv n) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show b ∉ (((Class.cv n)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ n from (by exact fresh_b_ne_n)))))) (show b ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))))))) (by exact (show y ∉ ((Wff.imp (.neg (.objMem x a)) (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show y ∉ (((Wff.neg (.objMem x a))).fv) ∪ (((Wff.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Wff.neg (.objMem x a))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_neg]; exact (show y ∉ ((Wff.objMem x a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show y ∉ ({x, a} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show y ≠ x from (by exact fresh_y_ne_x)), (show y ≠ a from (by exact fresh_y_ne_a))⟩)))))) (show y ∉ ((Wff.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((Class.cv a)).fv) ∪ (((syn_cplc (.cv n) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ a from (by exact fresh_y_ne_a)))))) (show y ∉ ((syn_cplc (.cv n) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show y ∉ (((Class.cv n)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ n from (by exact fresh_y_ne_n)))))) (show y ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))))))) (by exact (show b ∉ ((Wff.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact (show b ∉ (((Wff.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))).fv).erase c from (fun hmem => (show b ∉ ((Wff.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact (show b ∉ (((Wff.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n))).fv).erase z from (fun hmem => (show b ∉ ((Wff.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show b ∉ (((syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))).fv) ∪ (((Wff.objMem c n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show b ∉ (((Wff.neg (.objMem z c))).fv) ∪ (((Wff.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Wff.neg (.objMem z c))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_neg]; exact (show b ∉ ((Wff.objMem z c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show b ∉ ({z, c} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show b ≠ z from (by exact fresh_b_ne_z)), (show b ≠ c from (by exact fresh_b_ne_c))⟩)))))) (show b ∉ ((Wff.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ (((syn_cun (.cv c) (syn_csn (.cv z)))).fv) ∪ (((syn_cplc (.cv n) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_cun (.cv c) (syn_csn (.cv z)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show b ∉ (((Class.cv c)).fv) ∪ (((syn_csn (.cv z))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ c from (by exact fresh_b_ne_c)))))) (show b ∉ ((syn_csn (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show b ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ z from (by exact fresh_b_ne_z)))))))))))) (show b ∉ ((syn_cplc (.cv n) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show b ∉ (((Class.cv n)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ n from (by exact fresh_b_ne_n)))))) (show b ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))))) (show b ∉ ((Wff.objMem c n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show b ∉ ({c, n} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show b ≠ c from (by exact fresh_b_ne_c)), (show b ≠ n from (by exact fresh_b_ne_n))⟩)))))))) (Finset.mem_of_mem_erase hmem))))) (Finset.mem_of_mem_erase hmem)))))) (by exact (show y ∉ ((Wff.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact (show y ∉ (((Wff.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))).fv).erase c from (fun hmem => (show y ∉ ((Wff.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact (show y ∉ (((Wff.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n))).fv).erase z from (fun hmem => (show y ∉ ((Wff.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show y ∉ (((syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))).fv) ∪ (((Wff.objMem c n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show y ∉ (((Wff.neg (.objMem z c))).fv) ∪ (((Wff.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Wff.neg (.objMem z c))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_neg]; exact (show y ∉ ((Wff.objMem z c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show y ∉ ({z, c} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show y ≠ z from (by exact fresh_y_ne_z)), (show y ≠ c from (by exact fresh_y_ne_c))⟩)))))) (show y ∉ ((Wff.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show y ∉ (((syn_cun (.cv c) (syn_csn (.cv z)))).fv) ∪ (((syn_cplc (.cv n) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((syn_cun (.cv c) (syn_csn (.cv z)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show y ∉ (((Class.cv c)).fv) ∪ (((syn_csn (.cv z))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ c from (by exact fresh_y_ne_c)))))) (show y ∉ ((syn_csn (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show y ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ z from (by exact fresh_y_ne_z)))))))))))) (show y ∉ ((syn_cplc (.cv n) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show y ∉ (((Class.cv n)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show y ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show y ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show y ≠ n from (by exact fresh_y_ne_n)))))) (show y ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))))) (show y ∉ ((Wff.objMem c n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show y ∉ ({c, n} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show y ≠ c from (by exact fresh_y_ne_c)), (show y ≠ n from (by exact fresh_y_ne_n))⟩)))))))) (Finset.mem_of_mem_erase hmem))))) (Finset.mem_of_mem_erase hmem)))))) (show b ≠ y from (by exact fresh_b_ne_y)) p0154
  have p0156 :=
    @g_syl5bi (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_c1c))) (syn_wrex b (syn_cplc (.cv n) (syn_c1c)) (syn_wrex y (syn_ccompl (.cv b)) (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))))) (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (.imp (.neg (.objMem x a)) (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c)))) p0059 p0155
  have p0157 :=
    @g_com23 (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_c1c))) (.neg (.objMem x a)) (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c))) p0156
  have p0158 :=
    @g_imp3a (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_c1c))) (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c))) p0157
  have p0159 :=
    @g_alrimivv (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_c1c)))) (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c)))) a x (by exact (show a ∉ ((Wff.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact (show a ∉ (((Wff.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))).fv).erase c from (fun hmem => (show a ∉ ((Wff.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact (show a ∉ (((Wff.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n))).fv).erase z from (fun hmem => (show a ∉ ((Wff.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show a ∉ (((syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))).fv) ∪ (((Wff.objMem c n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show a ∉ (((Wff.neg (.objMem z c))).fv) ∪ (((Wff.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Wff.neg (.objMem z c))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_neg]; exact (show a ∉ ((Wff.objMem z c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show a ∉ ({z, c} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show a ≠ z from (by exact fresh_a_ne_z)), (show a ≠ c from (by exact fresh_a_ne_c))⟩)))))) (show a ∉ ((Wff.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show a ∉ (((syn_cun (.cv c) (syn_csn (.cv z)))).fv) ∪ (((syn_cplc (.cv n) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((syn_cun (.cv c) (syn_csn (.cv z)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show a ∉ (((Class.cv c)).fv) ∪ (((syn_csn (.cv z))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ c from (by exact fresh_a_ne_c)))))) (show a ∉ ((syn_csn (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show a ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ z from (by exact fresh_a_ne_z)))))))))))) (show a ∉ ((syn_cplc (.cv n) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show a ∉ (((Class.cv n)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ n from (by exact fresh_a_ne_n)))))) (show a ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))))) (show a ∉ ((Wff.objMem c n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show a ∉ ({c, n} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show a ≠ c from (by exact fresh_a_ne_c)), (show a ≠ n from (by exact fresh_a_ne_n))⟩)))))))) (Finset.mem_of_mem_erase hmem))))) (Finset.mem_of_mem_erase hmem)))))) (by exact (show x ∉ ((Wff.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact (show x ∉ (((Wff.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))).fv).erase c from (fun hmem => (show x ∉ ((Wff.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact (show x ∉ (((Wff.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n))).fv).erase z from (fun hmem => (show x ∉ ((Wff.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show x ∉ (((syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))).fv) ∪ (((Wff.objMem c n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show x ∉ (((Wff.neg (.objMem z c))).fv) ∪ (((Wff.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Wff.neg (.objMem z c))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_neg]; exact (show x ∉ ((Wff.objMem z c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show x ∉ ({z, c} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show x ≠ z from (by exact fresh_x_ne_z)), (show x ≠ c from (by exact fresh_x_ne_c))⟩)))))) (show x ∉ ((Wff.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((syn_cun (.cv c) (syn_csn (.cv z)))).fv) ∪ (((syn_cplc (.cv n) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cun (.cv c) (syn_csn (.cv z)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show x ∉ (((Class.cv c)).fv) ∪ (((syn_csn (.cv z))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ c from (by exact fresh_x_ne_c)))))) (show x ∉ ((syn_csn (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ z from (by exact fresh_x_ne_z)))))))))))) (show x ∉ ((syn_cplc (.cv n) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ (((Class.cv n)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ n from (by exact fresh_x_ne_n)))))) (show x ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))))) (show x ∉ ((Wff.objMem c n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show x ∉ ({c, n} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show x ≠ c from (by exact fresh_x_ne_c)), (show x ≠ n from (by exact fresh_x_ne_n))⟩)))))))) (Finset.mem_of_mem_erase hmem))))) (Finset.mem_of_mem_erase hmem)))))) p0158
  have p0160 :=
    @g_a1i (.imp (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (.all a (.all x (.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_c1c)))) (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c))))))) (.classMem (.cv n) (syn_cnnc)) p0159
  have p0161 :=
    @g_finds (.all a (.all x (.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c)))) (.objMem a m)))) (.all a (.all x (.imp (syn_wa (.neg (.objMem x a)) (syn_wex y (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv y))))) (.classEq (.cv a) (syn_c0))))) (.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))) (.all a (.all x (.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_c1c)))) (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c)))))) (.all a (.all x (.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc M (syn_c1c)))) (.classMem (.cv a) M)))) m n M (by exact (show m ∉ (M).fv from (by exact fresh_m_not_M))) (by exact (show m ∉ ((Wff.all c (.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact (show m ∉ (((Wff.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))).fv).erase c from (fun hmem => (show m ∉ ((Wff.all z (.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact (show m ∉ (((Wff.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n))).fv).erase z from (fun hmem => (show m ∉ ((Wff.imp (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show m ∉ (((syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))).fv) ∪ (((Wff.objMem c n)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show m ∉ (((Wff.neg (.objMem z c))).fv) ∪ (((Wff.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Wff.neg (.objMem z c))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_neg]; exact (show m ∉ ((Wff.objMem z c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show m ∉ ({z, c} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show m ≠ z from (by exact fresh_m_ne_z)), (show m ≠ c from (by exact fresh_m_ne_c))⟩)))))) (show m ∉ ((Wff.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show m ∉ (((syn_cun (.cv c) (syn_csn (.cv z)))).fv) ∪ (((syn_cplc (.cv n) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_cun (.cv c) (syn_csn (.cv z)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show m ∉ (((Class.cv c)).fv) ∪ (((syn_csn (.cv z))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ c from (by exact fresh_m_ne_c)))))) (show m ∉ ((syn_csn (.cv z))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show m ∉ ((Class.cv z)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({z} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ z from (by exact fresh_m_ne_z)))))))))))) (show m ∉ ((syn_cplc (.cv n) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show m ∉ (((Class.cv n)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ n from (by exact fresh_m_ne_n)))))) (show m ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))))) (show m ∉ ((Wff.objMem c n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show m ∉ ({c, n} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show m ≠ c from (by exact fresh_m_ne_c)), (show m ≠ n from (by exact fresh_m_ne_n))⟩)))))))) (Finset.mem_of_mem_erase hmem))))) (Finset.mem_of_mem_erase hmem)))))) (by exact (show n ∉ ((Wff.all a (.all x (.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c)))) (.objMem a m))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact (show n ∉ (((Wff.all x (.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c)))) (.objMem a m)))).fv).erase a from (fun hmem => (show n ∉ ((Wff.all x (.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c)))) (.objMem a m)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact (show n ∉ (((Wff.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c)))) (.objMem a m))).fv).erase x from (fun hmem => (show n ∉ ((Wff.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c)))) (.objMem a m))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show n ∉ (((syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c))))).fv) ∪ (((Wff.objMem a m)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show n ∉ (((Wff.neg (.objMem x a))).fv) ∪ (((Wff.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((Wff.neg (.objMem x a))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_neg]; exact (show n ∉ ((Wff.objMem x a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show n ∉ ({x, a} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show n ≠ x from (by exact fresh_n_ne_x)), (show n ≠ a from (by exact fresh_n_ne_a))⟩)))))) (show n ∉ ((Wff.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show n ∉ (((syn_cun (.cv a) (syn_csn (.cv x)))).fv) ∪ (((syn_cplc (.cv m) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((syn_cun (.cv a) (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show n ∉ (((Class.cv a)).fv) ∪ (((syn_csn (.cv x))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show n ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show n ≠ a from (by exact fresh_n_ne_a)))))) (show n ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show n ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show n ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show n ≠ x from (by exact fresh_n_ne_x)))))))))))) (show n ∉ ((syn_cplc (.cv m) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show n ∉ (((Class.cv m)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show n ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show n ≠ m from (by exact fresh_n_ne_m)))))) (show n ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))))) (show n ∉ ((Wff.objMem a m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show n ∉ ({a, m} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show n ≠ a from (by exact fresh_n_ne_a)), (show n ≠ m from (by exact fresh_n_ne_m))⟩)))))))) (Finset.mem_of_mem_erase hmem))))) (Finset.mem_of_mem_erase hmem)))))) (by exact (show m ∉ ((Wff.all a (.all x (.imp (syn_wa (.neg (.objMem x a)) (syn_wex y (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv y))))) (.classEq (.cv a) (syn_c0)))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact (show m ∉ (((Wff.all x (.imp (syn_wa (.neg (.objMem x a)) (syn_wex y (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv y))))) (.classEq (.cv a) (syn_c0))))).fv).erase a from (fun hmem => (show m ∉ ((Wff.all x (.imp (syn_wa (.neg (.objMem x a)) (syn_wex y (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv y))))) (.classEq (.cv a) (syn_c0))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact (show m ∉ (((Wff.imp (syn_wa (.neg (.objMem x a)) (syn_wex y (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv y))))) (.classEq (.cv a) (syn_c0)))).fv).erase x from (fun hmem => (show m ∉ ((Wff.imp (syn_wa (.neg (.objMem x a)) (syn_wex y (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv y))))) (.classEq (.cv a) (syn_c0)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show m ∉ (((syn_wa (.neg (.objMem x a)) (syn_wex y (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv y)))))).fv) ∪ (((Wff.classEq (.cv a) (syn_c0))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_wa (.neg (.objMem x a)) (syn_wex y (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv y)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show m ∉ (((Wff.neg (.objMem x a))).fv) ∪ (((syn_wex y (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv y))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Wff.neg (.objMem x a))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_neg]; exact (show m ∉ ((Wff.objMem x a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show m ∉ ({x, a} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show m ≠ x from (by exact fresh_m_ne_x)), (show m ≠ a from (by exact fresh_m_ne_a))⟩)))))) (show m ∉ ((syn_wex y (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv y))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex]; exact (show m ∉ (((Wff.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv y)))).fv).erase y from (fun hmem => (show m ∉ ((Wff.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv y)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show m ∉ (((syn_cun (.cv a) (syn_csn (.cv x)))).fv) ∪ (((syn_csn (.cv y))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_cun (.cv a) (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show m ∉ (((Class.cv a)).fv) ∪ (((syn_csn (.cv x))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ a from (by exact fresh_m_ne_a)))))) (show m ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show m ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ x from (by exact fresh_m_ne_x)))))))))))) (show m ∉ ((syn_csn (.cv y))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show m ∉ ((Class.cv y)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({y} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ y from (by exact fresh_m_ne_y)))))))))))) (Finset.mem_of_mem_erase hmem))))))))) (show m ∉ ((Wff.classEq (.cv a) (syn_c0))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show m ∉ (((Class.cv a)).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ a from (by exact fresh_m_ne_a)))))) (show m ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (Finset.mem_of_mem_erase hmem))))) (Finset.mem_of_mem_erase hmem)))))) (by exact (show m ∉ ((Wff.all a (.all x (.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc M (syn_c1c)))) (.classMem (.cv a) M))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact (show m ∉ (((Wff.all x (.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc M (syn_c1c)))) (.classMem (.cv a) M)))).fv).erase a from (fun hmem => (show m ∉ ((Wff.all x (.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc M (syn_c1c)))) (.classMem (.cv a) M)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact (show m ∉ (((Wff.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc M (syn_c1c)))) (.classMem (.cv a) M))).fv).erase x from (fun hmem => (show m ∉ ((Wff.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc M (syn_c1c)))) (.classMem (.cv a) M))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show m ∉ (((syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc M (syn_c1c))))).fv) ∪ (((Wff.classMem (.cv a) M)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc M (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show m ∉ (((Wff.neg (.objMem x a))).fv) ∪ (((Wff.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc M (syn_c1c)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Wff.neg (.objMem x a))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_neg]; exact (show m ∉ ((Wff.objMem x a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show m ∉ ({x, a} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show m ≠ x from (by exact fresh_m_ne_x)), (show m ≠ a from (by exact fresh_m_ne_a))⟩)))))) (show m ∉ ((Wff.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc M (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show m ∉ (((syn_cun (.cv a) (syn_csn (.cv x)))).fv) ∪ (((syn_cplc M (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_cun (.cv a) (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show m ∉ (((Class.cv a)).fv) ∪ (((syn_csn (.cv x))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ a from (by exact fresh_m_ne_a)))))) (show m ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show m ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ x from (by exact fresh_m_ne_x)))))))))))) (show m ∉ ((syn_cplc M (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show m ∉ ((M).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ (M).fv from (by exact fresh_m_not_M)) (show m ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))))) (show m ∉ ((Wff.classMem (.cv a) M)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show m ∉ (((Class.cv a)).fv) ∪ ((M).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ a from (by exact fresh_m_ne_a)))))) (show m ∉ (M).fv from (by exact fresh_m_not_M)))))))))) (Finset.mem_of_mem_erase hmem))))) (Finset.mem_of_mem_erase hmem)))))) (by exact (show m ∉ ((Wff.all a (.all x (.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_c1c)))) (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c))))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact (show m ∉ (((Wff.all x (.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_c1c)))) (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c)))))).fv).erase a from (fun hmem => (show m ∉ ((Wff.all x (.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_c1c)))) (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c)))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact (show m ∉ (((Wff.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_c1c)))) (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c))))).fv).erase x from (fun hmem => (show m ∉ ((Wff.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_c1c)))) (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show m ∉ (((syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_c1c))))).fv) ∪ (((Wff.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show m ∉ (((Wff.neg (.objMem x a))).fv) ∪ (((Wff.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_c1c)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Wff.neg (.objMem x a))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_neg]; exact (show m ∉ ((Wff.objMem x a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show m ∉ ({x, a} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show m ≠ x from (by exact fresh_m_ne_x)), (show m ≠ a from (by exact fresh_m_ne_a))⟩)))))) (show m ∉ ((Wff.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show m ∉ (((syn_cun (.cv a) (syn_csn (.cv x)))).fv) ∪ (((syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_cun (.cv a) (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show m ∉ (((Class.cv a)).fv) ∪ (((syn_csn (.cv x))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ a from (by exact fresh_m_ne_a)))))) (show m ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show m ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ x from (by exact fresh_m_ne_x)))))))))))) (show m ∉ ((syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show m ∉ (((syn_cplc (.cv n) (syn_c1c))).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_cplc (.cv n) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show m ∉ (((Class.cv n)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ n from (by exact fresh_m_ne_n)))))) (show m ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show m ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))))) (show m ∉ ((Wff.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show m ∉ (((Class.cv a)).fv) ∪ (((syn_cplc (.cv n) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ a from (by exact fresh_m_ne_a)))))) (show m ∉ ((syn_cplc (.cv n) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show m ∉ (((Class.cv n)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ n from (by exact fresh_m_ne_n)))))) (show m ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))))) (Finset.mem_of_mem_erase hmem))))) (Finset.mem_of_mem_erase hmem)))))) (show m ≠ n from (by exact fresh_m_ne_n)) p0000 p0016 p0035 p0041 p0047 p0058 p0160
  have p0162 :=
    @g_eleq1 (.cv x) X (.cv a)
  have p0163_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv x) X) (syn_wb (.objMem x a) (.classMem X (.cv a)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
      p0162
  have p0163 :=
    @g_notbid (.classEq (.cv x) X) (.objMem x a) (.classMem X (.cv a)) p0163_e00_recanon
  have p0164 :=
    @g_sneq (.cv x) X
  have p0165 :=
    @g_uneq2d (.classEq (.cv x) X) (syn_csn (.cv x)) (syn_csn X) (.cv a) p0164
  have p0166 :=
    @g_eleq1d (.classEq (.cv x) X) (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv a) (syn_csn X)) (syn_cplc M (syn_c1c)) p0165
  have p0167 :=
    @g_anbi12d (.classEq (.cv x) X) (.neg (.objMem x a)) (.neg (.classMem X (.cv a))) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc M (syn_c1c))) (.classMem (syn_cun (.cv a) (syn_csn X)) (syn_cplc M (syn_c1c))) p0163 p0166
  have p0168 :=
    @g_imbi1d (.classEq (.cv x) X) (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc M (syn_c1c)))) (syn_wa (.neg (.classMem X (.cv a))) (.classMem (syn_cun (.cv a) (syn_csn X)) (syn_cplc M (syn_c1c)))) (.classMem (.cv a) M) p0167
  have p0169 :=
    @g_spcv (.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc M (syn_c1c)))) (.classMem (.cv a) M)) (.imp (syn_wa (.neg (.classMem X (.cv a))) (.classMem (syn_cun (.cv a) (syn_csn X)) (syn_cplc M (syn_c1c)))) (.classMem (.cv a) M)) x X (by exact (show x ∉ (X).fv from (by exact fresh_x_not_X))) (by exact (show x ∉ ((Wff.imp (syn_wa (.neg (.classMem X (.cv a))) (.classMem (syn_cun (.cv a) (syn_csn X)) (syn_cplc M (syn_c1c)))) (.classMem (.cv a) M))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show x ∉ (((syn_wa (.neg (.classMem X (.cv a))) (.classMem (syn_cun (.cv a) (syn_csn X)) (syn_cplc M (syn_c1c))))).fv) ∪ (((Wff.classMem (.cv a) M)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_wa (.neg (.classMem X (.cv a))) (.classMem (syn_cun (.cv a) (syn_csn X)) (syn_cplc M (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show x ∉ (((Wff.neg (.classMem X (.cv a)))).fv) ∪ (((Wff.classMem (syn_cun (.cv a) (syn_csn X)) (syn_cplc M (syn_c1c)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Wff.neg (.classMem X (.cv a)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_neg]; exact (show x ∉ ((Wff.classMem X (.cv a))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ ((X).fv) ∪ (((Class.cv a)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (X).fv from (by exact fresh_x_not_X)) (show x ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ a from (by exact fresh_x_ne_a)))))))))))) (show x ∉ ((Wff.classMem (syn_cun (.cv a) (syn_csn X)) (syn_cplc M (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((syn_cun (.cv a) (syn_csn X))).fv) ∪ (((syn_cplc M (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cun (.cv a) (syn_csn X))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show x ∉ (((Class.cv a)).fv) ∪ (((syn_csn X)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ a from (by exact fresh_x_ne_a)))))) (show x ∉ ((syn_csn X)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show x ∉ (X).fv from (by exact fresh_x_not_X)))))))) (show x ∉ ((syn_cplc M (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ ((M).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (M).fv from (by exact fresh_x_not_M)) (show x ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))))) (show x ∉ ((Wff.classMem (.cv a) M)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((Class.cv a)).fv) ∪ ((M).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ a from (by exact fresh_x_ne_a)))))) (show x ∉ (M).fv from (by exact fresh_x_not_M))))))))))) hyp_nnsucelr_2 p0168
  have p0170 :=
    @g_alimi (.all x (.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc M (syn_c1c)))) (.classMem (.cv a) M))) (.imp (syn_wa (.neg (.classMem X (.cv a))) (.classMem (syn_cun (.cv a) (syn_csn X)) (syn_cplc M (syn_c1c)))) (.classMem (.cv a) M)) a p0169
  have p0171 :=
    @g_eleq2 (.cv a) A X
  have p0172 :=
    @g_notbid (.classEq (.cv a) A) (.classMem X (.cv a)) (.classMem X A) p0171
  have p0173 :=
    @g_uneq1 (.cv a) A (syn_csn X)
  have p0174 :=
    @g_eleq1d (.classEq (.cv a) A) (syn_cun (.cv a) (syn_csn X)) (syn_cun A (syn_csn X)) (syn_cplc M (syn_c1c)) p0173
  have p0175 :=
    @g_anbi12d (.classEq (.cv a) A) (.neg (.classMem X (.cv a))) (.neg (.classMem X A)) (.classMem (syn_cun (.cv a) (syn_csn X)) (syn_cplc M (syn_c1c))) (.classMem (syn_cun A (syn_csn X)) (syn_cplc M (syn_c1c))) p0172 p0174
  have p0176 :=
    @g_eleq1 (.cv a) A M
  have p0177 :=
    @g_imbi12d (.classEq (.cv a) A) (syn_wa (.neg (.classMem X (.cv a))) (.classMem (syn_cun (.cv a) (syn_csn X)) (syn_cplc M (syn_c1c)))) (syn_wa (.neg (.classMem X A)) (.classMem (syn_cun A (syn_csn X)) (syn_cplc M (syn_c1c)))) (.classMem (.cv a) M) (.classMem A M) p0175 p0176
  have p0178 :=
    @g_spcv (.imp (syn_wa (.neg (.classMem X (.cv a))) (.classMem (syn_cun (.cv a) (syn_csn X)) (syn_cplc M (syn_c1c)))) (.classMem (.cv a) M)) (.imp (syn_wa (.neg (.classMem X A)) (.classMem (syn_cun A (syn_csn X)) (syn_cplc M (syn_c1c)))) (.classMem A M)) a A (by exact (show a ∉ (A).fv from (by exact fresh_a_not_A))) (by exact (show a ∉ ((Wff.imp (syn_wa (.neg (.classMem X A)) (.classMem (syn_cun A (syn_csn X)) (syn_cplc M (syn_c1c)))) (.classMem A M))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show a ∉ (((syn_wa (.neg (.classMem X A)) (.classMem (syn_cun A (syn_csn X)) (syn_cplc M (syn_c1c))))).fv) ∪ (((Wff.classMem A M)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((syn_wa (.neg (.classMem X A)) (.classMem (syn_cun A (syn_csn X)) (syn_cplc M (syn_c1c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show a ∉ (((Wff.neg (.classMem X A))).fv) ∪ (((Wff.classMem (syn_cun A (syn_csn X)) (syn_cplc M (syn_c1c)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Wff.neg (.classMem X A))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_neg]; exact (show a ∉ ((Wff.classMem X A)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show a ∉ ((X).fv) ∪ ((A).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (X).fv from (by exact fresh_a_not_X)) (show a ∉ (A).fv from (by exact fresh_a_not_A)))))))) (show a ∉ ((Wff.classMem (syn_cun A (syn_csn X)) (syn_cplc M (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show a ∉ (((syn_cun A (syn_csn X))).fv) ∪ (((syn_cplc M (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((syn_cun A (syn_csn X))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show a ∉ ((A).fv) ∪ (((syn_csn X)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (A).fv from (by exact fresh_a_not_A)) (show a ∉ ((syn_csn X)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show a ∉ (X).fv from (by exact fresh_a_not_X)))))))) (show a ∉ ((syn_cplc M (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show a ∉ ((M).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (M).fv from (by exact fresh_a_not_M)) (show a ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))))) (show a ∉ ((Wff.classMem A M)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show a ∉ ((A).fv) ∪ ((M).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (A).fv from (by exact fresh_a_not_A)) (show a ∉ (M).fv from (by exact fresh_a_not_M))))))))))) hyp_nnsucelr_1 p0177
  have p0179 :=
    @g_n_3syl (.classMem M (syn_cnnc)) (.all a (.all x (.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc M (syn_c1c)))) (.classMem (.cv a) M)))) (.all a (.imp (syn_wa (.neg (.classMem X (.cv a))) (.classMem (syn_cun (.cv a) (syn_csn X)) (syn_cplc M (syn_c1c)))) (.classMem (.cv a) M))) (.imp (syn_wa (.neg (.classMem X A)) (.classMem (syn_cun A (syn_csn X)) (syn_cplc M (syn_c1c)))) (.classMem A M)) p0161 p0170 p0178
  have p0180 :=
    @g_imp (.classMem M (syn_cnnc)) (syn_wa (.neg (.classMem X A)) (.classMem (syn_cun A (syn_csn X)) (syn_cplc M (syn_c1c)))) (.classMem A M) p0179
  exact p0180



#print axioms g_nnsucelr

end NFChoice.DirectNominalPrf.WPPReplay
