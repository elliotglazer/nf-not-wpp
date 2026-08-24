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
import NominalAlphaRepairedBase001038Leaf1stReflected001
import NominalAlphaRepairedBase001039SwapReflected001
import NominalAlphaRepairedBase001040SsetReflected001
import NominalAlphaRepairedBase001041CoReflected001
import NominalAlphaRepairedBase001042ImaReflected001
import NominalAlphaRepairedBase001043SiReflected001
import NominalAlphaRepairedBase001044IdReflected001
import NominalAlphaRepairedBase001045XpReflected001
import NominalAlphaRepairedBase001046CnvReflected001
import NominalAlphaRepairedBase001047FvReflected001
import NominalAlphaRepairedBase001048Leaf2ndReflected001
import NominalNFLiteralBaseFour
import NominalNFLiteralXpViaCompletenessDev003
import NominalNFLiteralRemainingViaCompletenessDev001
import NominalDefinitionLeafHandlersCanonical001
import NominalDefinitionLeafHandlersObjExtCompat001
import NominalRecanonTransportCompat001
import NominalWPPReplayChunk010Compact001Part009

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

noncomputable def g_nnpweq
    (A : Class) (B : Class) (n : Var) (M : Class) (dv_A_n : n ∉ A.fv) (dv_B_n : n ∉ B.fv) (dv_M_n : n ∉ M.fv) :
    Nominal.NPrf (.imp (syn_w3a (.classMem M (syn_cnnc)) (.classMem A M) (.classMem B M)) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw A) (.cv n)) (.classMem (syn_cpw B) (.cv n))))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ ({n} : Finset Var) ∪ M.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let m : Var := freshVar proofSupport 2
  let k : Var := freshVar proofSupport 3
  let c : Var := freshVar proofSupport 4
  let j : Var := freshVar proofSupport 5
  let d : Var := freshVar proofSupport 6
  let e : Var := freshVar proofSupport 7
  let x : Var := freshVar proofSupport 8
  let f : Var := freshVar proofSupport 9
  let y : Var := freshVar proofSupport 10
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a_ne_n : a ≠ n := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_a : n ≠ a :=
    Ne.symm fresh_a_ne_n
  have fresh_a_not_M : a ∉ M.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_b_ne_n : b ≠ n := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_b : n ≠ b :=
    Ne.symm fresh_b_ne_n
  have fresh_b_not_M : b ∉ M.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_m : m ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_m_not_A : m ∉ A.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_m_not_B : m ∉ B.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_m_ne_n : m ≠ n := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_m : n ≠ m :=
    Ne.symm fresh_m_ne_n
  have fresh_m_not_M : m ∉ M.fv := by
    intro h
    exact fresh_m (Finset.mem_union_right _ (h))
  have fresh_k : k ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_k_not_A : k ∉ A.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_k_not_B : k ∉ B.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_k_ne_n : k ≠ n := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_k : n ≠ k :=
    Ne.symm fresh_k_ne_n
  have fresh_k_not_M : k ∉ M.fv := by
    intro h
    exact fresh_k (Finset.mem_union_right _ (h))
  have fresh_c : c ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_c_not_A : c ∉ A.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_c_not_B : c ∉ B.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_c_ne_n : c ≠ n := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_c : n ≠ c :=
    Ne.symm fresh_c_ne_n
  have fresh_c_not_M : c ∉ M.fv := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (h))
  have fresh_j : j ∉ proofSupport := by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_j_not_A : j ∉ A.fv := by
    intro h
    exact fresh_j (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_j_not_B : j ∉ B.fv := by
    intro h
    exact fresh_j (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_j_ne_n : j ≠ n := by
    intro h
    exact fresh_j (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_j : n ≠ j :=
    Ne.symm fresh_j_ne_n
  have fresh_j_not_M : j ∉ M.fv := by
    intro h
    exact fresh_j (Finset.mem_union_right _ (h))
  have fresh_d : d ∉ proofSupport := by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_d_ne_n : d ≠ n := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_d : n ≠ d :=
    Ne.symm fresh_d_ne_n
  have fresh_d_not_M : d ∉ M.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_e : e ∉ proofSupport := by
    change freshVar proofSupport 7 ∉ proofSupport
    exact freshVar_not_mem proofSupport 7
  have fresh_e_not_A : e ∉ A.fv := by
    intro h
    exact fresh_e (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_e_not_B : e ∉ B.fv := by
    intro h
    exact fresh_e (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_e_ne_n : e ≠ n := by
    intro h
    exact fresh_e (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_e : n ≠ e :=
    Ne.symm fresh_e_ne_n
  have fresh_e_not_M : e ∉ M.fv := by
    intro h
    exact fresh_e (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 8 ∉ proofSupport
    exact freshVar_not_mem proofSupport 8
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_ne_n : x ≠ n := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_x : n ≠ x :=
    Ne.symm fresh_x_ne_n
  have fresh_x_not_M : x ∉ M.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_f : f ∉ proofSupport := by
    change freshVar proofSupport 9 ∉ proofSupport
    exact freshVar_not_mem proofSupport 9
  have fresh_f_not_A : f ∉ A.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_f_not_B : f ∉ B.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_f_ne_n : f ≠ n := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_f : n ≠ f :=
    Ne.symm fresh_f_ne_n
  have fresh_f_not_M : f ∉ M.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 10 ∉ proofSupport
    exact freshVar_not_mem proofSupport 10
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_ne_n : y ≠ n := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_y : n ≠ y :=
    Ne.symm fresh_y_ne_n
  have fresh_y_not_M : y ∉ M.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have fresh_a_ne_m : a ≠ m := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_m_ne_a : m ≠ a :=
    Ne.symm fresh_a_ne_m
  have fresh_a_ne_k : a ≠ k := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_k_ne_a : k ≠ a :=
    Ne.symm fresh_a_ne_k
  have fresh_a_ne_c : a ≠ c := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_c_ne_a : c ≠ a :=
    Ne.symm fresh_a_ne_c
  have fresh_a_ne_j : a ≠ j := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_j_ne_a : j ≠ a :=
    Ne.symm fresh_a_ne_j
  have fresh_a_ne_d : a ≠ d := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_d_ne_a : d ≠ a :=
    Ne.symm fresh_a_ne_d
  have fresh_a_ne_e : a ≠ e := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 0) (j := 7) (by decide)
  have fresh_e_ne_a : e ≠ a :=
    Ne.symm fresh_a_ne_e
  have fresh_a_ne_x : a ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 0) (j := 8) (by decide)
  have fresh_x_ne_a : x ≠ a :=
    Ne.symm fresh_a_ne_x
  have fresh_a_ne_f : a ≠ f := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 0) (j := 9) (by decide)
  have fresh_f_ne_a : f ≠ a :=
    Ne.symm fresh_a_ne_f
  have fresh_a_ne_y : a ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 0) (j := 10) (by decide)
  have fresh_y_ne_a : y ≠ a :=
    Ne.symm fresh_a_ne_y
  have fresh_b_ne_m : b ≠ m := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_m_ne_b : m ≠ b :=
    Ne.symm fresh_b_ne_m
  have fresh_b_ne_k : b ≠ k := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_k_ne_b : k ≠ b :=
    Ne.symm fresh_b_ne_k
  have fresh_b_ne_c : b ≠ c := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_c_ne_b : c ≠ b :=
    Ne.symm fresh_b_ne_c
  have fresh_b_ne_j : b ≠ j := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_j_ne_b : j ≠ b :=
    Ne.symm fresh_b_ne_j
  have fresh_b_ne_d : b ≠ d := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_d_ne_b : d ≠ b :=
    Ne.symm fresh_b_ne_d
  have fresh_b_ne_e : b ≠ e := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 1) (j := 7) (by decide)
  have fresh_e_ne_b : e ≠ b :=
    Ne.symm fresh_b_ne_e
  have fresh_b_ne_x : b ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 1) (j := 8) (by decide)
  have fresh_x_ne_b : x ≠ b :=
    Ne.symm fresh_b_ne_x
  have fresh_b_ne_f : b ≠ f := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 1) (j := 9) (by decide)
  have fresh_f_ne_b : f ≠ b :=
    Ne.symm fresh_b_ne_f
  have fresh_b_ne_y : b ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 1) (j := 10) (by decide)
  have fresh_y_ne_b : y ≠ b :=
    Ne.symm fresh_b_ne_y
  have fresh_m_ne_k : m ≠ k := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_k_ne_m : k ≠ m :=
    Ne.symm fresh_m_ne_k
  have fresh_m_ne_c : m ≠ c := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_c_ne_m : c ≠ m :=
    Ne.symm fresh_m_ne_c
  have fresh_m_ne_j : m ≠ j := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_j_ne_m : j ≠ m :=
    Ne.symm fresh_m_ne_j
  have fresh_m_ne_d : m ≠ d := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_d_ne_m : d ≠ m :=
    Ne.symm fresh_m_ne_d
  have fresh_m_ne_e : m ≠ e := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 2) (j := 7) (by decide)
  have fresh_e_ne_m : e ≠ m :=
    Ne.symm fresh_m_ne_e
  have fresh_m_ne_x : m ≠ x := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 2) (j := 8) (by decide)
  have fresh_x_ne_m : x ≠ m :=
    Ne.symm fresh_m_ne_x
  have fresh_m_ne_f : m ≠ f := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 2) (j := 9) (by decide)
  have fresh_f_ne_m : f ≠ m :=
    Ne.symm fresh_m_ne_f
  have fresh_m_ne_y : m ≠ y := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 2) (j := 10) (by decide)
  have fresh_y_ne_m : y ≠ m :=
    Ne.symm fresh_m_ne_y
  have fresh_k_ne_c : k ≠ c := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_c_ne_k : c ≠ k :=
    Ne.symm fresh_k_ne_c
  have fresh_k_ne_j : k ≠ j := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_j_ne_k : j ≠ k :=
    Ne.symm fresh_k_ne_j
  have fresh_k_ne_d : k ≠ d := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_d_ne_k : d ≠ k :=
    Ne.symm fresh_k_ne_d
  have fresh_k_ne_e : k ≠ e := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 3) (j := 7) (by decide)
  have fresh_e_ne_k : e ≠ k :=
    Ne.symm fresh_k_ne_e
  have fresh_k_ne_x : k ≠ x := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 3) (j := 8) (by decide)
  have fresh_x_ne_k : x ≠ k :=
    Ne.symm fresh_k_ne_x
  have fresh_k_ne_f : k ≠ f := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 3) (j := 9) (by decide)
  have fresh_f_ne_k : f ≠ k :=
    Ne.symm fresh_k_ne_f
  have fresh_k_ne_y : k ≠ y := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 3) (j := 10) (by decide)
  have fresh_y_ne_k : y ≠ k :=
    Ne.symm fresh_k_ne_y
  have fresh_c_ne_j : c ≠ j := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_j_ne_c : j ≠ c :=
    Ne.symm fresh_c_ne_j
  have fresh_c_ne_d : c ≠ d := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_d_ne_c : d ≠ c :=
    Ne.symm fresh_c_ne_d
  have fresh_c_ne_e : c ≠ e := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 4) (j := 7) (by decide)
  have fresh_e_ne_c : e ≠ c :=
    Ne.symm fresh_c_ne_e
  have fresh_c_ne_x : c ≠ x := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 4) (j := 8) (by decide)
  have fresh_x_ne_c : x ≠ c :=
    Ne.symm fresh_c_ne_x
  have fresh_c_ne_f : c ≠ f := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 4) (j := 9) (by decide)
  have fresh_f_ne_c : f ≠ c :=
    Ne.symm fresh_c_ne_f
  have fresh_c_ne_y : c ≠ y := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 4) (j := 10) (by decide)
  have fresh_y_ne_c : y ≠ c :=
    Ne.symm fresh_c_ne_y
  have fresh_j_ne_d : j ≠ d := by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_d_ne_j : d ≠ j :=
    Ne.symm fresh_j_ne_d
  have fresh_j_ne_e : j ≠ e := by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 5) (j := 7) (by decide)
  have fresh_e_ne_j : e ≠ j :=
    Ne.symm fresh_j_ne_e
  have fresh_j_ne_x : j ≠ x := by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 5) (j := 8) (by decide)
  have fresh_x_ne_j : x ≠ j :=
    Ne.symm fresh_j_ne_x
  have fresh_j_ne_f : j ≠ f := by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 5) (j := 9) (by decide)
  have fresh_f_ne_j : f ≠ j :=
    Ne.symm fresh_j_ne_f
  have fresh_j_ne_y : j ≠ y := by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 5) (j := 10) (by decide)
  have fresh_y_ne_j : y ≠ j :=
    Ne.symm fresh_j_ne_y
  have fresh_d_ne_e : d ≠ e := by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 6) (j := 7) (by decide)
  have fresh_e_ne_d : e ≠ d :=
    Ne.symm fresh_d_ne_e
  have fresh_d_ne_x : d ≠ x := by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 6) (j := 8) (by decide)
  have fresh_x_ne_d : x ≠ d :=
    Ne.symm fresh_d_ne_x
  have fresh_d_ne_f : d ≠ f := by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 6) (j := 9) (by decide)
  have fresh_f_ne_d : f ≠ d :=
    Ne.symm fresh_d_ne_f
  have fresh_d_ne_y : d ≠ y := by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 6) (j := 10) (by decide)
  have fresh_y_ne_d : y ≠ d :=
    Ne.symm fresh_d_ne_y
  have fresh_e_ne_x : e ≠ x := by
    change freshVar proofSupport 7 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 7) (j := 8) (by decide)
  have fresh_x_ne_e : x ≠ e :=
    Ne.symm fresh_e_ne_x
  have fresh_e_ne_f : e ≠ f := by
    change freshVar proofSupport 7 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 7) (j := 9) (by decide)
  have fresh_f_ne_e : f ≠ e :=
    Ne.symm fresh_e_ne_f
  have fresh_e_ne_y : e ≠ y := by
    change freshVar proofSupport 7 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 7) (j := 10) (by decide)
  have fresh_y_ne_e : y ≠ e :=
    Ne.symm fresh_e_ne_y
  have fresh_x_ne_f : x ≠ f := by
    change freshVar proofSupport 8 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 8) (j := 9) (by decide)
  have fresh_f_ne_x : f ≠ x :=
    Ne.symm fresh_x_ne_f
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 8 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 8) (j := 10) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_f_ne_y : f ≠ y := by
    change freshVar proofSupport 9 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 9) (j := 10) (by decide)
  have fresh_y_ne_f : y ≠ f :=
    Ne.symm fresh_f_ne_y
  have dv_cache_0001 : a ≠ b := by
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0002 : a ≠ m := by
    clear dv_cache_0001
    exact (show a ≠ m from (by exact fresh_a_ne_m))
  have dv_cache_0003 : a ≠ n := by
    clear dv_cache_0001 dv_cache_0002
    exact (show a ≠ n from (by exact fresh_a_ne_n))
  have dv_cache_0004 : b ≠ m := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show b ≠ m from (by exact fresh_b_ne_m))
  have dv_cache_0005 : b ≠ n := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show b ≠ n from (by exact fresh_b_ne_n))
  have dv_cache_0006 : m ≠ n := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show m ≠ n from (by exact fresh_m_ne_n))
  have dv_cache_0007 : b ∉ ((Class.cv m)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : b ∉ ((syn_c0c)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : a ∉ ((Class.cv m)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : a ∉ ((syn_c0c)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : n ∉ ((Wff.classEq (.cv a) (syn_c0))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : b ∉ ((Wff.classEq (.cv a) (syn_c0))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : a ∉ ((syn_c0)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : a ∉ ((syn_wral b (syn_c0c) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_csn (syn_c0)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_n, fresh_a_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : n ∉ ((Wff.classEq (.cv b) (syn_c0))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : b ∉ ((syn_c0)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : b ∉ ((syn_wrex n (syn_cnnc) (.classMem (syn_csn (syn_c0)) (.cv n)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : b ∉ ((Class.cv k)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : a ∉ ((Class.cv k)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : b ∉ ((syn_cplc (.cv k) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : a ∉ ((syn_cplc (.cv k) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : n ∉ ((Wff.objEq a c)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_a, fresh_n_ne_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : n ∉ ((Wff.objEq b d)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_b, fresh_n_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : c ∉ ((syn_cplc (.cv k) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : d ∉ ((syn_cplc (.cv k) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : d ∉ ((syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv c)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_c, fresh_d_ne_n, fresh_d_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : a ∉ ((syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv c)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_c, fresh_a_ne_n, fresh_a_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0028 : c ∉ ((syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_a, fresh_c_ne_n, fresh_c_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0029 : b ∉ ((syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv c)) (.cv n)) (.classMem (syn_cpw (.cv d)) (.cv n))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_c, fresh_b_ne_n, fresh_b_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0030 : b ≠ c := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (show b ≠ c from (by exact fresh_b_ne_c))
  have dv_cache_0031 : n ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0032 : j ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (by
      have compact_fv_not_mem_empty : j ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0033 : j ∉ ((syn_wa (.classMem (syn_cpw (.cv c)) (.cv n)) (.classMem (syn_cpw (.cv d)) (.cv n)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (by
      have compact_fv_not_mem_empty : j ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_j_ne_c, fresh_j_ne_n, fresh_j_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0034 : n ∉ ((syn_wa (.classMem (syn_cpw (.cv c)) (.cv j)) (.classMem (syn_cpw (.cv d)) (.cv j)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_c, fresh_n_ne_j, fresh_n_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0035 : b ∉ (M).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0036 : a ∉ (M).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0037 : n ∉ ((syn_c1c)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0038 : n ∉ ((Wff.classMem (syn_csn (syn_c0)) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0039 : f ∉ ((Class.cv k)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0040 : e ∉ ((Class.cv k)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_e_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0041 : f ∉ ((syn_wrex x (syn_ccompl (.cv e)) (.classEq (.cv c) (syn_cun (.cv e) (syn_csn (.cv x)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_e, fresh_f_ne_c, fresh_f_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0042 : e ∉ ((syn_wrex y (syn_ccompl (.cv f)) (.classEq (.cv d) (syn_cun (.cv f) (syn_csn (.cv y)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_e_ne_f, fresh_e_ne_d, fresh_e_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0043 : e ≠ f := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042
    exact (show e ≠ f from (by exact fresh_e_ne_f))
  have dv_cache_0044 : y ∉ ((syn_ccompl (.cv e))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_e, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0045 : x ∉ ((syn_ccompl (.cv f))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0046 : y ∉ ((Wff.classEq (.cv c) (syn_cun (.cv e) (syn_csn (.cv x))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_c, fresh_y_ne_e, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0047 : x ∉ ((Wff.classEq (.cv d) (syn_cun (.cv f) (syn_csn (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_d, fresh_x_ne_f, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0048 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0049 : e ∉ ((Class.cv c)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_e_ne_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0050 : x ∉ ((Class.cv c)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0051 : e ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050
    exact (show e ≠ x from (by exact fresh_e_ne_x))
  have dv_cache_0052 : f ∉ ((Class.cv d)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0053 : y ∉ ((Class.cv d)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0054 : f ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
    exact (show f ≠ y from (by exact fresh_f_ne_y))
  have dv_cache_0055 : n ∉ ((Wff.objEq a e)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_a, fresh_n_ne_e, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0056 : n ∉ ((Wff.objEq b f)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_b, fresh_n_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0057 : a ∉ ((Class.cv e)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_e, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0058 : b ∉ ((Class.cv e)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_e, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0059 : b ∉ ((Class.cv f)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0060 : a ∉ ((syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv e)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_e, fresh_a_ne_n, fresh_a_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0061 : b ∉ ((syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv e)) (.cv n)) (.classMem (syn_cpw (.cv f)) (.cv n))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_e, fresh_b_ne_n, fresh_b_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0062 : j ∉ ((syn_cplc (.cv n) (.cv n))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061
    exact (by
      have compact_fv_not_mem_empty : j ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_j_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0063 : j ∉ ((syn_wa (.classMem (syn_cpw (syn_cun (.cv e) (syn_csn (.cv x)))) (syn_cplc (.cv n) (.cv n))) (.classMem (syn_cpw (syn_cun (.cv f) (syn_csn (.cv y)))) (syn_cplc (.cv n) (.cv n))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062
    exact (by
      have compact_fv_not_mem_empty : j ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_j_ne_e, fresh_j_ne_x, fresh_j_ne_n, fresh_j_ne_f, fresh_j_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0064 : j ∉ ((syn_wa (.classEq (.cv c) (syn_cun (.cv e) (syn_csn (.cv x)))) (.classEq (.cv d) (syn_cun (.cv f) (syn_csn (.cv y)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063
    exact (by
      have compact_fv_not_mem_empty : j ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_j_ne_c, fresh_j_ne_e, fresh_j_ne_x, fresh_j_ne_d, fresh_j_ne_f, fresh_j_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0065 : x ∉ ((syn_wrex j (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv c)) (.cv j)) (.classMem (syn_cpw (.cv d)) (.cv j))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_c, fresh_x_ne_j, fresh_x_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0066 : y ∉ ((syn_wrex j (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv c)) (.cv j)) (.classMem (syn_cpw (.cv d)) (.cv j))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_c, fresh_y_ne_j, fresh_y_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0067 : x ∉ ((syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wa (syn_wa (.objMem e k) (.objMem f k)) (syn_wa (.classMem (syn_cpw (.cv e)) (.cv n)) (.classMem (syn_cpw (.cv f)) (.cv n)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_k, fresh_x_ne_n, fresh_x_ne_e, fresh_x_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0068 : y ∉ ((syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wa (syn_wa (.objMem e k) (.objMem f k)) (syn_wa (.classMem (syn_cpw (.cv e)) (.cv n)) (.classMem (syn_cpw (.cv f)) (.cv n)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_k, fresh_y_ne_n, fresh_y_ne_e, fresh_y_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0069 : n ∉ ((Wff.imp (syn_wrex x (syn_ccompl (.cv e)) (syn_wrex y (syn_ccompl (.cv f)) (syn_wa (.classEq (.cv c) (syn_cun (.cv e) (syn_csn (.cv x)))) (.classEq (.cv d) (syn_cun (.cv f) (syn_csn (.cv y))))))) (syn_wrex j (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv c)) (.cv j)) (.classMem (syn_cpw (.cv d)) (.cv j)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_e, fresh_n_ne_f, fresh_n_ne_c, fresh_n_ne_x, fresh_n_ne_d, fresh_n_ne_y, fresh_n_ne_j, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0070 : n ∉ ((syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem e k) (.objMem f k)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_k, fresh_n_ne_e, fresh_n_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0071 : e ∉ ((syn_wrex j (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv c)) (.cv j)) (.classMem (syn_cpw (.cv d)) (.cv j))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_e_ne_c, fresh_e_ne_j, fresh_e_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0072 : f ∉ ((syn_wrex j (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv c)) (.cv j)) (.classMem (syn_cpw (.cv d)) (.cv j))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_c, fresh_f_ne_j, fresh_f_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0073 : e ∉ ((syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wral a (.cv k) (syn_wral b (.cv k) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_e_ne_k, fresh_e_ne_a, fresh_e_ne_n, fresh_e_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0074 : f ∉ ((syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wral a (.cv k) (syn_wral b (.cv k) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_k, fresh_f_ne_a, fresh_f_ne_n, fresh_f_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0075 : c ∉ ((syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wral a (.cv k) (syn_wral b (.cv k) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_k, fresh_c_ne_a, fresh_c_ne_n, fresh_c_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0076 : d ∉ ((syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wral a (.cv k) (syn_wral b (.cv k) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_k, fresh_d_ne_a, fresh_d_ne_n, fresh_d_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0077 : c ≠ d := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076
    exact (show c ≠ d from (by exact fresh_c_ne_d))
  have dv_cache_0078 : m ∉ (M).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0079 : m ∉ ((syn_wral a (.cv k) (syn_wral b (.cv k) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_k, fresh_m_ne_a, fresh_m_ne_n, fresh_m_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0080 : k ∉ ((syn_wral a (.cv m) (syn_wral b (.cv m) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_ne_m, fresh_k_ne_a, fresh_k_ne_n, fresh_k_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0081 : m ∉ ((syn_wrex n (syn_cnnc) (.classMem (syn_csn (syn_c0)) (.cv n)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0082 : m ∉ ((syn_wral a M (syn_wral b M (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_not_M, fresh_m_ne_a, fresh_m_ne_n, fresh_m_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0083 : m ∉ ((syn_wral c (syn_cplc (.cv k) (syn_c1c)) (syn_wral d (syn_cplc (.cv k) (syn_c1c)) (syn_wrex j (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv c)) (.cv j)) (.classMem (syn_cpw (.cv d)) (.cv j))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_k, fresh_m_ne_c, fresh_m_ne_j, fresh_m_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0084 : m ≠ k := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
    exact (show m ≠ k from (by exact fresh_m_ne_k))
  have dv_cache_0085 : n ∉ ((Wff.classEq (.cv a) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_a, dv_A_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0086 : n ∉ ((Wff.classEq (.cv b) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_b, dv_B_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0087 : a ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0088 : b ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0089 : b ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0090 : a ∉ ((syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw A) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, fresh_a_ne_n, fresh_a_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0091 : b ∉ ((syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw A) (.cv n)) (.classMem (syn_cpw B) (.cv n))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_A, fresh_b_ne_n, fresh_b_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_nnpweqlem1 m n a b dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_raleq (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))) b (.cv m) (syn_c0c) dv_cache_0007 dv_cache_0008
  have p0002 :=
    @g_raleqbi1dv (syn_wral b (.cv m) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))))) (syn_wral b (syn_c0c) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))))) a (.cv m) (syn_c0c) dv_cache_0009 dv_cache_0010 p0001
  have p0003 :=
    (by simpa [syn_wb, syn_wral] using (Nominal.biimpRefl (syn_wral a (syn_c0c) (syn_wral b (syn_c0c) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))))))))
  have p0004 :=
    @g_el0c (.cv a)
  have p0005 :=
    @g_imbi1i (.classMem (.cv a) (syn_c0c)) (.classEq (.cv a) (syn_c0)) (syn_wral b (syn_c0c) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))))) p0004
  have p0006 :=
    @g_albii (.imp (.classMem (.cv a) (syn_c0c)) (syn_wral b (syn_c0c) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))))) (.imp (.classEq (.cv a) (syn_c0)) (syn_wral b (syn_c0c) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))))) a p0005
  have p0007 :=
    @g_n_0ex
  have p0008 :=
    @g_pweq (.cv a) (syn_c0)
  have p0009 :=
    @g_pw0
  have p0010 :=
    @g_syl6eq (.classEq (.cv a) (syn_c0)) (syn_cpw (.cv a)) (syn_cpw (syn_c0)) (syn_csn (syn_c0)) p0008 p0009
  have p0011 :=
    @g_eleq1d (.classEq (.cv a) (syn_c0)) (syn_cpw (.cv a)) (syn_csn (syn_c0)) (.cv n) p0010
  have p0012 :=
    @g_anbi1d (.classEq (.cv a) (syn_c0)) (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_csn (syn_c0)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)) p0011
  have p0013 :=
    @g_rexbidv (.classEq (.cv a) (syn_c0)) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))) (syn_wa (.classMem (syn_csn (syn_c0)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))) n (syn_cnnc) dv_cache_0011 p0012
  have p0014 :=
    @g_ralbidv (.classEq (.cv a) (syn_c0)) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_csn (syn_c0)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))) b (syn_c0c) dv_cache_0012 p0013
  have p0015 :=
    @g_ceqsalv (syn_wral b (syn_c0c) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))))) (syn_wral b (syn_c0c) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_csn (syn_c0)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))))) a (syn_c0) dv_cache_0013 dv_cache_0014 p0007 p0014
  have p0016 :=
    (by simpa [syn_wb, syn_wral] using (Nominal.biimpRefl (syn_wral b (syn_c0c) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_csn (syn_c0)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))))))
  have p0017 :=
    @g_el0c (.cv b)
  have p0018 :=
    @g_imbi1i (.classMem (.cv b) (syn_c0c)) (.classEq (.cv b) (syn_c0)) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_csn (syn_c0)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))) p0017
  have p0019 :=
    @g_albii (.imp (.classMem (.cv b) (syn_c0c)) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_csn (syn_c0)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))))) (.imp (.classEq (.cv b) (syn_c0)) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_csn (syn_c0)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))))) b p0018
  have p0020 :=
    @g_bitri (syn_wral b (syn_c0c) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_csn (syn_c0)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))))) (.all b (.imp (.classMem (.cv b) (syn_c0c)) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_csn (syn_c0)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))))) (.all b (.imp (.classEq (.cv b) (syn_c0)) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_csn (syn_c0)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))))) p0016 p0019
  have p0021 :=
    @g_n_0ex
  have p0022 :=
    @g_pweq (.cv b) (syn_c0)
  have p0023 :=
    @g_pw0
  have p0024 :=
    @g_syl6eq (.classEq (.cv b) (syn_c0)) (syn_cpw (.cv b)) (syn_cpw (syn_c0)) (syn_csn (syn_c0)) p0022 p0023
  have p0025 :=
    @g_eleq1d (.classEq (.cv b) (syn_c0)) (syn_cpw (.cv b)) (syn_csn (syn_c0)) (.cv n) p0024
  have p0026 :=
    @g_anbi2d (.classEq (.cv b) (syn_c0)) (.classMem (syn_cpw (.cv b)) (.cv n)) (.classMem (syn_csn (syn_c0)) (.cv n)) (.classMem (syn_csn (syn_c0)) (.cv n)) p0025
  have p0027 :=
    @g_anidm (.classMem (syn_csn (syn_c0)) (.cv n))
  have p0028 :=
    @g_syl6bb (.classEq (.cv b) (syn_c0)) (syn_wa (.classMem (syn_csn (syn_c0)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))) (syn_wa (.classMem (syn_csn (syn_c0)) (.cv n)) (.classMem (syn_csn (syn_c0)) (.cv n))) (.classMem (syn_csn (syn_c0)) (.cv n)) p0026 p0027
  have p0029 :=
    @g_rexbidv (.classEq (.cv b) (syn_c0)) (syn_wa (.classMem (syn_csn (syn_c0)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))) (.classMem (syn_csn (syn_c0)) (.cv n)) n (syn_cnnc) dv_cache_0015 p0028
  have p0030 :=
    @g_ceqsalv (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_csn (syn_c0)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))) (syn_wrex n (syn_cnnc) (.classMem (syn_csn (syn_c0)) (.cv n))) b (syn_c0) dv_cache_0016 dv_cache_0017 p0021 p0029
  have p0031 :=
    @g_n_3bitri (.all a (.imp (.classEq (.cv a) (syn_c0)) (syn_wral b (syn_c0c) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))))))) (syn_wral b (syn_c0c) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_csn (syn_c0)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))))) (.all b (.imp (.classEq (.cv b) (syn_c0)) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_csn (syn_c0)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))))) (syn_wrex n (syn_cnnc) (.classMem (syn_csn (syn_c0)) (.cv n))) p0015 p0020 p0030
  have p0032 :=
    @g_n_3bitri (syn_wral a (syn_c0c) (syn_wral b (syn_c0c) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))))) (.all a (.imp (.classMem (.cv a) (syn_c0c)) (syn_wral b (syn_c0c) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))))))) (.all a (.imp (.classEq (.cv a) (syn_c0)) (syn_wral b (syn_c0c) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))))))) (syn_wrex n (syn_cnnc) (.classMem (syn_csn (syn_c0)) (.cv n))) p0003 p0006 p0031
  have p0033 :=
    @g_syl6bb (.classEq (.cv m) (syn_c0c)) (syn_wral a (.cv m) (syn_wral b (.cv m) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))))) (syn_wral a (syn_c0c) (syn_wral b (syn_c0c) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))))) (syn_wrex n (syn_cnnc) (.classMem (syn_csn (syn_c0)) (.cv n))) p0002 p0032
  have p0034 :=
    @g_raleq (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))) b (.cv m) (.cv k) dv_cache_0007 dv_cache_0018
  have p0035 :=
    @g_raleqbi1dv (syn_wral b (.cv m) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))))) (syn_wral b (.cv k) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))))) a (.cv m) (.cv k) dv_cache_0009 dv_cache_0019 p0034
  have p0036 :=
    @g_raleq (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))) b (.cv m) (syn_cplc (.cv k) (syn_c1c)) dv_cache_0007 dv_cache_0020
  have p0037 :=
    @g_raleqbi1dv (syn_wral b (.cv m) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))))) (syn_wral b (syn_cplc (.cv k) (syn_c1c)) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))))) a (.cv m) (syn_cplc (.cv k) (syn_c1c)) dv_cache_0009 dv_cache_0021 p0036
  have p0038 :=
    @g_pweq (.cv a) (.cv c)
  have p0039_e00_recanon : Nominal.NPrf (.imp (.objEq a c) (.classEq (syn_cpw (.cv a)) (syn_cpw (.cv c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cpw syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0038
  have p0039 :=
    @g_eleq1d (.objEq a c) (syn_cpw (.cv a)) (syn_cpw (.cv c)) (.cv n) p0039_e00_recanon
  have p0040 :=
    @g_anbi1d (.objEq a c) (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv c)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)) p0039
  have p0041 :=
    @g_rexbidv (.objEq a c) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))) (syn_wa (.classMem (syn_cpw (.cv c)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))) n (syn_cnnc) dv_cache_0022 p0040
  have p0042 :=
    @g_pweq (.cv b) (.cv d)
  have p0043_e00_recanon : Nominal.NPrf (.imp (.objEq b d) (.classEq (syn_cpw (.cv b)) (syn_cpw (.cv d)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cpw syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0042
  have p0043 :=
    @g_eleq1d (.objEq b d) (syn_cpw (.cv b)) (syn_cpw (.cv d)) (.cv n) p0043_e00_recanon
  have p0044 :=
    @g_anbi2d (.objEq b d) (.classMem (syn_cpw (.cv b)) (.cv n)) (.classMem (syn_cpw (.cv d)) (.cv n)) (.classMem (syn_cpw (.cv c)) (.cv n)) p0043
  have p0045 :=
    @g_rexbidv (.objEq b d) (syn_wa (.classMem (syn_cpw (.cv c)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))) (syn_wa (.classMem (syn_cpw (.cv c)) (.cv n)) (.classMem (syn_cpw (.cv d)) (.cv n))) n (syn_cnnc) dv_cache_0023 p0044
  have p0046 :=
    @g_cbvral2v (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv c)) (.cv n)) (.classMem (syn_cpw (.cv d)) (.cv n)))) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv c)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))) a b c d (syn_cplc (.cv k) (syn_c1c)) (syn_cplc (.cv k) (syn_c1c)) dv_cache_0021 dv_cache_0024 dv_cache_0025 dv_cache_0021 dv_cache_0020 dv_cache_0024 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0001 dv_cache_0030 p0041 p0045
  have p0047 :=
    @g_eleq2 (.cv n) (.cv j) (syn_cpw (.cv c))
  have p0048 :=
    @g_eleq2 (.cv n) (.cv j) (syn_cpw (.cv d))
  have p0049_e00_recanon : Nominal.NPrf (.imp (.objEq n j) (syn_wb (.classMem (syn_cpw (.cv c)) (.cv n)) (.classMem (syn_cpw (.cv c)) (.cv j)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cpw syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0047
  have p0049_e01_recanon : Nominal.NPrf (.imp (.objEq n j) (syn_wb (.classMem (syn_cpw (.cv d)) (.cv n)) (.classMem (syn_cpw (.cv d)) (.cv j)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cpw syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0048
  have p0049 :=
    @g_anbi12d (.objEq n j) (.classMem (syn_cpw (.cv c)) (.cv n)) (.classMem (syn_cpw (.cv c)) (.cv j)) (.classMem (syn_cpw (.cv d)) (.cv n)) (.classMem (syn_cpw (.cv d)) (.cv j)) p0049_e00_recanon p0049_e01_recanon
  have p0050 :=
    @g_cbvrexv (syn_wa (.classMem (syn_cpw (.cv c)) (.cv n)) (.classMem (syn_cpw (.cv d)) (.cv n))) (syn_wa (.classMem (syn_cpw (.cv c)) (.cv j)) (.classMem (syn_cpw (.cv d)) (.cv j))) n j (syn_cnnc) dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 p0049
  have p0051 :=
    @g_n_2ralbii (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv c)) (.cv n)) (.classMem (syn_cpw (.cv d)) (.cv n)))) (syn_wrex j (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv c)) (.cv j)) (.classMem (syn_cpw (.cv d)) (.cv j)))) c d (syn_cplc (.cv k) (syn_c1c)) (syn_cplc (.cv k) (syn_c1c)) p0050
  have p0052 :=
    @g_bitri (syn_wral a (syn_cplc (.cv k) (syn_c1c)) (syn_wral b (syn_cplc (.cv k) (syn_c1c)) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))))) (syn_wral c (syn_cplc (.cv k) (syn_c1c)) (syn_wral d (syn_cplc (.cv k) (syn_c1c)) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv c)) (.cv n)) (.classMem (syn_cpw (.cv d)) (.cv n)))))) (syn_wral c (syn_cplc (.cv k) (syn_c1c)) (syn_wral d (syn_cplc (.cv k) (syn_c1c)) (syn_wrex j (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv c)) (.cv j)) (.classMem (syn_cpw (.cv d)) (.cv j)))))) p0046 p0051
  have p0053 :=
    @g_syl6bb (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))) (syn_wral a (.cv m) (syn_wral b (.cv m) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))))) (syn_wral a (syn_cplc (.cv k) (syn_c1c)) (syn_wral b (syn_cplc (.cv k) (syn_c1c)) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))))) (syn_wral c (syn_cplc (.cv k) (syn_c1c)) (syn_wral d (syn_cplc (.cv k) (syn_c1c)) (syn_wrex j (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv c)) (.cv j)) (.classMem (syn_cpw (.cv d)) (.cv j)))))) p0037 p0052
  have p0054 :=
    @g_raleq (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))) b (.cv m) M dv_cache_0007 dv_cache_0035
  have p0055 :=
    @g_raleqbi1dv (syn_wral b (.cv m) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))))) (syn_wral b M (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))))) a (.cv m) M dv_cache_0009 dv_cache_0036 p0054
  have p0056 :=
    @g_n_1cnnc
  have p0057 :=
    @g_n_0ex
  have p0058 :=
    @g_snel1c (syn_c0) p0057
  have p0059 :=
    @g_eleq2 (.cv n) (syn_c1c) (syn_csn (syn_c0))
  have p0060 :=
    @g_rspcev (.classMem (syn_csn (syn_c0)) (.cv n)) (.classMem (syn_csn (syn_c0)) (syn_c1c)) n (syn_c1c) (syn_cnnc) dv_cache_0037 dv_cache_0031 dv_cache_0038 p0059
  have p0061 :=
    @g_mp2an (.classMem (syn_c1c) (syn_cnnc)) (.classMem (syn_csn (syn_c0)) (syn_c1c)) (syn_wrex n (syn_cnnc) (.classMem (syn_csn (syn_c0)) (.cv n))) p0056 p0058 p0060
  have p0062 :=
    @g_reeanv (syn_wrex x (syn_ccompl (.cv e)) (.classEq (.cv c) (syn_cun (.cv e) (syn_csn (.cv x))))) (syn_wrex y (syn_ccompl (.cv f)) (.classEq (.cv d) (syn_cun (.cv f) (syn_csn (.cv y))))) e f (.cv k) (.cv k) dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043
  have p0063 :=
    @g_reeanv (.classEq (.cv c) (syn_cun (.cv e) (syn_csn (.cv x)))) (.classEq (.cv d) (syn_cun (.cv f) (syn_csn (.cv y)))) x y (syn_ccompl (.cv e)) (syn_ccompl (.cv f)) dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048
  have p0064 :=
    @g_n_2rexbii (syn_wrex x (syn_ccompl (.cv e)) (syn_wrex y (syn_ccompl (.cv f)) (syn_wa (.classEq (.cv c) (syn_cun (.cv e) (syn_csn (.cv x)))) (.classEq (.cv d) (syn_cun (.cv f) (syn_csn (.cv y))))))) (syn_wa (syn_wrex x (syn_ccompl (.cv e)) (.classEq (.cv c) (syn_cun (.cv e) (syn_csn (.cv x))))) (syn_wrex y (syn_ccompl (.cv f)) (.classEq (.cv d) (syn_cun (.cv f) (syn_csn (.cv y)))))) e f (.cv k) (.cv k) p0063
  have p0065 :=
    @g_elsuc x (.cv c) (.cv k) e dv_cache_0049 dv_cache_0050 dv_cache_0040 dv_cache_0051
  have p0066 :=
    @g_elsuc y (.cv d) (.cv k) f dv_cache_0052 dv_cache_0053 dv_cache_0039 dv_cache_0054
  have p0067 :=
    @g_anbi12i (.classMem (.cv c) (syn_cplc (.cv k) (syn_c1c))) (syn_wrex e (.cv k) (syn_wrex x (syn_ccompl (.cv e)) (.classEq (.cv c) (syn_cun (.cv e) (syn_csn (.cv x)))))) (.classMem (.cv d) (syn_cplc (.cv k) (syn_c1c))) (syn_wrex f (.cv k) (syn_wrex y (syn_ccompl (.cv f)) (.classEq (.cv d) (syn_cun (.cv f) (syn_csn (.cv y)))))) p0065 p0066
  have p0068 :=
    @g_n_3bitr4ri (syn_wrex e (.cv k) (syn_wrex f (.cv k) (syn_wa (syn_wrex x (syn_ccompl (.cv e)) (.classEq (.cv c) (syn_cun (.cv e) (syn_csn (.cv x))))) (syn_wrex y (syn_ccompl (.cv f)) (.classEq (.cv d) (syn_cun (.cv f) (syn_csn (.cv y)))))))) (syn_wa (syn_wrex e (.cv k) (syn_wrex x (syn_ccompl (.cv e)) (.classEq (.cv c) (syn_cun (.cv e) (syn_csn (.cv x)))))) (syn_wrex f (.cv k) (syn_wrex y (syn_ccompl (.cv f)) (.classEq (.cv d) (syn_cun (.cv f) (syn_csn (.cv y))))))) (syn_wrex e (.cv k) (syn_wrex f (.cv k) (syn_wrex x (syn_ccompl (.cv e)) (syn_wrex y (syn_ccompl (.cv f)) (syn_wa (.classEq (.cv c) (syn_cun (.cv e) (syn_csn (.cv x)))) (.classEq (.cv d) (syn_cun (.cv f) (syn_csn (.cv y))))))))) (syn_wa (.classMem (.cv c) (syn_cplc (.cv k) (syn_c1c))) (.classMem (.cv d) (syn_cplc (.cv k) (syn_c1c)))) p0062 p0064 p0067
  have p0069 :=
    @g_pweq (.cv a) (.cv e)
  have p0070_e00_recanon : Nominal.NPrf (.imp (.objEq a e) (.classEq (syn_cpw (.cv a)) (syn_cpw (.cv e)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cpw syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0069
  have p0070 :=
    @g_eleq1d (.objEq a e) (syn_cpw (.cv a)) (syn_cpw (.cv e)) (.cv n) p0070_e00_recanon
  have p0071 :=
    @g_anbi1d (.objEq a e) (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv e)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)) p0070
  have p0072 :=
    @g_rexbidv (.objEq a e) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))) (syn_wa (.classMem (syn_cpw (.cv e)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))) n (syn_cnnc) dv_cache_0055 p0071
  have p0073 :=
    @g_pweq (.cv b) (.cv f)
  have p0074_e00_recanon : Nominal.NPrf (.imp (.objEq b f) (.classEq (syn_cpw (.cv b)) (syn_cpw (.cv f)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cpw syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0073
  have p0074 :=
    @g_eleq1d (.objEq b f) (syn_cpw (.cv b)) (syn_cpw (.cv f)) (.cv n) p0074_e00_recanon
  have p0075 :=
    @g_anbi2d (.objEq b f) (.classMem (syn_cpw (.cv b)) (.cv n)) (.classMem (syn_cpw (.cv f)) (.cv n)) (.classMem (syn_cpw (.cv e)) (.cv n)) p0074
  have p0076 :=
    @g_rexbidv (.objEq b f) (syn_wa (.classMem (syn_cpw (.cv e)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))) (syn_wa (.classMem (syn_cpw (.cv e)) (.cv n)) (.classMem (syn_cpw (.cv f)) (.cv n))) n (syn_cnnc) dv_cache_0056 p0075
  have p0077_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv a) (.cv e)) (syn_wb (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv e)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wrex syn_wex syn_wa syn_cnnc syn_cint
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0072
  have p0077_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv b) (.cv f)) (syn_wb (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv e)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv e)) (.cv n)) (.classMem (syn_cpw (.cv f)) (.cv n)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wrex syn_wex syn_wa syn_cnnc syn_cint
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0076
  have p0077 :=
    @g_rspc2v (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv e)) (.cv n)) (.classMem (syn_cpw (.cv f)) (.cv n)))) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv e)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))) a b (.cv e) (.cv f) (.cv k) (.cv k) dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0019 dv_cache_0019 dv_cache_0018 dv_cache_0060 dv_cache_0061 dv_cache_0001 p0077_e00_recanon p0077_e01_recanon
  have p0078_e00_recanon : Nominal.NPrf (.imp (syn_wa (.objMem e k) (.objMem f k)) (.imp (syn_wral a (.cv k) (syn_wral b (.cv k) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))))) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv e)) (.cv n)) (.classMem (syn_cpw (.cv f)) (.cv n)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wral syn_wrex syn_wex syn_cnnc syn_cint
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0077
  have p0078 :=
    @g_adantl (syn_wa (.objMem e k) (.objMem f k)) (.imp (syn_wral a (.cv k) (syn_wral b (.cv k) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))))) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv e)) (.cv n)) (.classMem (syn_cpw (.cv f)) (.cv n))))) (.classMem (.cv k) (syn_cnnc)) p0078_e00_recanon
  have p0079 :=
    @g_nncaddccl (.cv n) (.cv n)
  have p0080 :=
    @g_anidms (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cnnc)) p0079
  have p0081 :=
    @g_adantl (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)) p0080
  have p0082 :=
    @g_n_3ad2ant1 (syn_wa (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wa (syn_wa (.objMem e k) (.objMem f k)) (syn_wa (.classMem (syn_cpw (.cv e)) (.cv n)) (.classMem (syn_cpw (.cv f)) (.cv n)))) (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cnnc)) (syn_wa (.classMem (.cv x) (syn_ccompl (.cv e))) (.classMem (.cv y) (syn_ccompl (.cv f)))) p0081
  have p0083 :=
    @g_simp1l (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (syn_wa (syn_wa (.objMem e k) (.objMem f k)) (syn_wa (.classMem (syn_cpw (.cv e)) (.cv n)) (.classMem (syn_cpw (.cv f)) (.cv n)))) (syn_wa (.classMem (.cv x) (syn_ccompl (.cv e))) (.classMem (.cv y) (syn_ccompl (.cv f))))
  have p0084 :=
    @g_simp1r (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (syn_wa (syn_wa (.objMem e k) (.objMem f k)) (syn_wa (.classMem (syn_cpw (.cv e)) (.cv n)) (.classMem (syn_cpw (.cv f)) (.cv n)))) (syn_wa (.classMem (.cv x) (syn_ccompl (.cv e))) (.classMem (.cv y) (syn_ccompl (.cv f))))
  have p0085 :=
    @g_simp2ll (.objMem e k) (.objMem f k) (syn_wa (.classMem (syn_cpw (.cv e)) (.cv n)) (.classMem (syn_cpw (.cv f)) (.cv n))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wa (.classMem (.cv x) (syn_ccompl (.cv e))) (.classMem (.cv y) (syn_ccompl (.cv f))))
  have p0086 :=
    @g_simp3l (syn_wa (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wa (syn_wa (.objMem e k) (.objMem f k)) (syn_wa (.classMem (syn_cpw (.cv e)) (.cv n)) (.classMem (syn_cpw (.cv f)) (.cv n)))) (.classMem (.cv x) (syn_ccompl (.cv e))) (.classMem (.cv y) (syn_ccompl (.cv f)))
  have p0087 :=
    @g_simp2rl (.classMem (syn_cpw (.cv e)) (.cv n)) (.classMem (syn_cpw (.cv f)) (.cv n)) (syn_wa (.objMem e k) (.objMem f k)) (syn_wa (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wa (.classMem (.cv x) (syn_ccompl (.cv e))) (.classMem (.cv y) (syn_ccompl (.cv f))))
  have p0088 :=
    @g_nnadjoinpw (.cv e) (.cv k) (.cv n) (.cv x)
  have p0089_e05_recanon : Nominal.NPrf (.imp (syn_w3a (syn_wa (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wa (.objMem e k) (.classMem (.cv x) (syn_ccompl (.cv e)))) (.classMem (syn_cpw (.cv e)) (.cv n))) (.classMem (syn_cpw (syn_cun (.cv e) (syn_csn (.cv x)))) (syn_cplc (.cv n) (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_cpw syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_cplc syn_wrex syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0088
  have p0089 :=
    @g_syl221anc (syn_w3a (syn_wa (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wa (syn_wa (.objMem e k) (.objMem f k)) (syn_wa (.classMem (syn_cpw (.cv e)) (.cv n)) (.classMem (syn_cpw (.cv f)) (.cv n)))) (syn_wa (.classMem (.cv x) (syn_ccompl (.cv e))) (.classMem (.cv y) (syn_ccompl (.cv f))))) (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (.objMem e k) (.classMem (.cv x) (syn_ccompl (.cv e))) (.classMem (syn_cpw (.cv e)) (.cv n)) (.classMem (syn_cpw (syn_cun (.cv e) (syn_csn (.cv x)))) (syn_cplc (.cv n) (.cv n))) p0083 p0084 p0085 p0086 p0087 p0089_e05_recanon
  have p0090 :=
    @g_simp2lr (.objMem e k) (.objMem f k) (syn_wa (.classMem (syn_cpw (.cv e)) (.cv n)) (.classMem (syn_cpw (.cv f)) (.cv n))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wa (.classMem (.cv x) (syn_ccompl (.cv e))) (.classMem (.cv y) (syn_ccompl (.cv f))))
  have p0091 :=
    @g_simp3r (syn_wa (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wa (syn_wa (.objMem e k) (.objMem f k)) (syn_wa (.classMem (syn_cpw (.cv e)) (.cv n)) (.classMem (syn_cpw (.cv f)) (.cv n)))) (.classMem (.cv x) (syn_ccompl (.cv e))) (.classMem (.cv y) (syn_ccompl (.cv f)))
  have p0092 :=
    @g_simp2rr (.classMem (syn_cpw (.cv e)) (.cv n)) (.classMem (syn_cpw (.cv f)) (.cv n)) (syn_wa (.objMem e k) (.objMem f k)) (syn_wa (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wa (.classMem (.cv x) (syn_ccompl (.cv e))) (.classMem (.cv y) (syn_ccompl (.cv f))))
  have p0093 :=
    @g_nnadjoinpw (.cv f) (.cv k) (.cv n) (.cv y)
  have p0094_e05_recanon : Nominal.NPrf (.imp (syn_w3a (syn_wa (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wa (.objMem f k) (.classMem (.cv y) (syn_ccompl (.cv f)))) (.classMem (syn_cpw (.cv f)) (.cv n))) (.classMem (syn_cpw (syn_cun (.cv f) (syn_csn (.cv y)))) (syn_cplc (.cv n) (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_cpw syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_cplc syn_wrex syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0093
  have p0094 :=
    @g_syl221anc (syn_w3a (syn_wa (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wa (syn_wa (.objMem e k) (.objMem f k)) (syn_wa (.classMem (syn_cpw (.cv e)) (.cv n)) (.classMem (syn_cpw (.cv f)) (.cv n)))) (syn_wa (.classMem (.cv x) (syn_ccompl (.cv e))) (.classMem (.cv y) (syn_ccompl (.cv f))))) (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (.objMem f k) (.classMem (.cv y) (syn_ccompl (.cv f))) (.classMem (syn_cpw (.cv f)) (.cv n)) (.classMem (syn_cpw (syn_cun (.cv f) (syn_csn (.cv y)))) (syn_cplc (.cv n) (.cv n))) p0083 p0084 p0090 p0091 p0092 p0094_e05_recanon
  have p0095 :=
    @g_eleq2 (.cv j) (syn_cplc (.cv n) (.cv n)) (syn_cpw (syn_cun (.cv e) (syn_csn (.cv x))))
  have p0096 :=
    @g_eleq2 (.cv j) (syn_cplc (.cv n) (.cv n)) (syn_cpw (syn_cun (.cv f) (syn_csn (.cv y))))
  have p0097 :=
    @g_anbi12d (.classEq (.cv j) (syn_cplc (.cv n) (.cv n))) (.classMem (syn_cpw (syn_cun (.cv e) (syn_csn (.cv x)))) (.cv j)) (.classMem (syn_cpw (syn_cun (.cv e) (syn_csn (.cv x)))) (syn_cplc (.cv n) (.cv n))) (.classMem (syn_cpw (syn_cun (.cv f) (syn_csn (.cv y)))) (.cv j)) (.classMem (syn_cpw (syn_cun (.cv f) (syn_csn (.cv y)))) (syn_cplc (.cv n) (.cv n))) p0095 p0096
  have p0098 :=
    @g_rspcev (syn_wa (.classMem (syn_cpw (syn_cun (.cv e) (syn_csn (.cv x)))) (.cv j)) (.classMem (syn_cpw (syn_cun (.cv f) (syn_csn (.cv y)))) (.cv j))) (syn_wa (.classMem (syn_cpw (syn_cun (.cv e) (syn_csn (.cv x)))) (syn_cplc (.cv n) (.cv n))) (.classMem (syn_cpw (syn_cun (.cv f) (syn_csn (.cv y)))) (syn_cplc (.cv n) (.cv n)))) j (syn_cplc (.cv n) (.cv n)) (syn_cnnc) dv_cache_0062 dv_cache_0032 dv_cache_0063 p0097
  have p0099 :=
    @g_syl12anc (syn_w3a (syn_wa (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wa (syn_wa (.objMem e k) (.objMem f k)) (syn_wa (.classMem (syn_cpw (.cv e)) (.cv n)) (.classMem (syn_cpw (.cv f)) (.cv n)))) (syn_wa (.classMem (.cv x) (syn_ccompl (.cv e))) (.classMem (.cv y) (syn_ccompl (.cv f))))) (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cnnc)) (.classMem (syn_cpw (syn_cun (.cv e) (syn_csn (.cv x)))) (syn_cplc (.cv n) (.cv n))) (.classMem (syn_cpw (syn_cun (.cv f) (syn_csn (.cv y)))) (syn_cplc (.cv n) (.cv n))) (syn_wrex j (syn_cnnc) (syn_wa (.classMem (syn_cpw (syn_cun (.cv e) (syn_csn (.cv x)))) (.cv j)) (.classMem (syn_cpw (syn_cun (.cv f) (syn_csn (.cv y)))) (.cv j)))) p0082 p0089 p0094 p0098
  have p0100 :=
    @g_pweq (.cv c) (syn_cun (.cv e) (syn_csn (.cv x)))
  have p0101 :=
    @g_eleq1d (.classEq (.cv c) (syn_cun (.cv e) (syn_csn (.cv x)))) (syn_cpw (.cv c)) (syn_cpw (syn_cun (.cv e) (syn_csn (.cv x)))) (.cv j) p0100
  have p0102 :=
    @g_pweq (.cv d) (syn_cun (.cv f) (syn_csn (.cv y)))
  have p0103 :=
    @g_eleq1d (.classEq (.cv d) (syn_cun (.cv f) (syn_csn (.cv y)))) (syn_cpw (.cv d)) (syn_cpw (syn_cun (.cv f) (syn_csn (.cv y)))) (.cv j) p0102
  have p0104 :=
    @g_bi2anan9 (.classEq (.cv c) (syn_cun (.cv e) (syn_csn (.cv x)))) (.classMem (syn_cpw (.cv c)) (.cv j)) (.classMem (syn_cpw (syn_cun (.cv e) (syn_csn (.cv x)))) (.cv j)) (.classEq (.cv d) (syn_cun (.cv f) (syn_csn (.cv y)))) (.classMem (syn_cpw (.cv d)) (.cv j)) (.classMem (syn_cpw (syn_cun (.cv f) (syn_csn (.cv y)))) (.cv j)) p0101 p0103
  have p0105 :=
    @g_rexbidv (syn_wa (.classEq (.cv c) (syn_cun (.cv e) (syn_csn (.cv x)))) (.classEq (.cv d) (syn_cun (.cv f) (syn_csn (.cv y))))) (syn_wa (.classMem (syn_cpw (.cv c)) (.cv j)) (.classMem (syn_cpw (.cv d)) (.cv j))) (syn_wa (.classMem (syn_cpw (syn_cun (.cv e) (syn_csn (.cv x)))) (.cv j)) (.classMem (syn_cpw (syn_cun (.cv f) (syn_csn (.cv y)))) (.cv j))) j (syn_cnnc) dv_cache_0064 p0104
  have p0106 :=
    @g_syl5ibrcom (syn_w3a (syn_wa (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wa (syn_wa (.objMem e k) (.objMem f k)) (syn_wa (.classMem (syn_cpw (.cv e)) (.cv n)) (.classMem (syn_cpw (.cv f)) (.cv n)))) (syn_wa (.classMem (.cv x) (syn_ccompl (.cv e))) (.classMem (.cv y) (syn_ccompl (.cv f))))) (syn_wrex j (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv c)) (.cv j)) (.classMem (syn_cpw (.cv d)) (.cv j)))) (syn_wa (.classEq (.cv c) (syn_cun (.cv e) (syn_csn (.cv x)))) (.classEq (.cv d) (syn_cun (.cv f) (syn_csn (.cv y))))) (syn_wrex j (syn_cnnc) (syn_wa (.classMem (syn_cpw (syn_cun (.cv e) (syn_csn (.cv x)))) (.cv j)) (.classMem (syn_cpw (syn_cun (.cv f) (syn_csn (.cv y)))) (.cv j)))) p0099 p0105
  have p0107 :=
    @g_n_3expia (syn_wa (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wa (syn_wa (.objMem e k) (.objMem f k)) (syn_wa (.classMem (syn_cpw (.cv e)) (.cv n)) (.classMem (syn_cpw (.cv f)) (.cv n)))) (syn_wa (.classMem (.cv x) (syn_ccompl (.cv e))) (.classMem (.cv y) (syn_ccompl (.cv f)))) (.imp (syn_wa (.classEq (.cv c) (syn_cun (.cv e) (syn_csn (.cv x)))) (.classEq (.cv d) (syn_cun (.cv f) (syn_csn (.cv y))))) (syn_wrex j (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv c)) (.cv j)) (.classMem (syn_cpw (.cv d)) (.cv j))))) p0106
  have p0108 :=
    @g_rexlimdvv (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wa (syn_wa (.objMem e k) (.objMem f k)) (syn_wa (.classMem (syn_cpw (.cv e)) (.cv n)) (.classMem (syn_cpw (.cv f)) (.cv n))))) (syn_wa (.classEq (.cv c) (syn_cun (.cv e) (syn_csn (.cv x)))) (.classEq (.cv d) (syn_cun (.cv f) (syn_csn (.cv y))))) (syn_wrex j (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv c)) (.cv j)) (.classMem (syn_cpw (.cv d)) (.cv j)))) x y (syn_ccompl (.cv e)) (syn_ccompl (.cv f)) dv_cache_0044 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0048 p0107
  have p0109 :=
    @g_expr (syn_wa (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) (syn_wa (.objMem e k) (.objMem f k)) (syn_wa (.classMem (syn_cpw (.cv e)) (.cv n)) (.classMem (syn_cpw (.cv f)) (.cv n))) (.imp (syn_wrex x (syn_ccompl (.cv e)) (syn_wrex y (syn_ccompl (.cv f)) (syn_wa (.classEq (.cv c) (syn_cun (.cv e) (syn_csn (.cv x)))) (.classEq (.cv d) (syn_cun (.cv f) (syn_csn (.cv y))))))) (syn_wrex j (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv c)) (.cv j)) (.classMem (syn_cpw (.cv d)) (.cv j))))) p0108
  have p0110 :=
    @g_an32s (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (syn_wa (.objMem e k) (.objMem f k)) (.imp (syn_wa (.classMem (syn_cpw (.cv e)) (.cv n)) (.classMem (syn_cpw (.cv f)) (.cv n))) (.imp (syn_wrex x (syn_ccompl (.cv e)) (syn_wrex y (syn_ccompl (.cv f)) (syn_wa (.classEq (.cv c) (syn_cun (.cv e) (syn_csn (.cv x)))) (.classEq (.cv d) (syn_cun (.cv f) (syn_csn (.cv y))))))) (syn_wrex j (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv c)) (.cv j)) (.classMem (syn_cpw (.cv d)) (.cv j)))))) p0109
  have p0111 :=
    @g_rexlimdva (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem e k) (.objMem f k))) (syn_wa (.classMem (syn_cpw (.cv e)) (.cv n)) (.classMem (syn_cpw (.cv f)) (.cv n))) (.imp (syn_wrex x (syn_ccompl (.cv e)) (syn_wrex y (syn_ccompl (.cv f)) (syn_wa (.classEq (.cv c) (syn_cun (.cv e) (syn_csn (.cv x)))) (.classEq (.cv d) (syn_cun (.cv f) (syn_csn (.cv y))))))) (syn_wrex j (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv c)) (.cv j)) (.classMem (syn_cpw (.cv d)) (.cv j))))) n (syn_cnnc) dv_cache_0069 dv_cache_0070 p0110
  have p0112 :=
    @g_syld (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem e k) (.objMem f k))) (syn_wral a (.cv k) (syn_wral b (.cv k) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))))) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv e)) (.cv n)) (.classMem (syn_cpw (.cv f)) (.cv n)))) (.imp (syn_wrex x (syn_ccompl (.cv e)) (syn_wrex y (syn_ccompl (.cv f)) (syn_wa (.classEq (.cv c) (syn_cun (.cv e) (syn_csn (.cv x)))) (.classEq (.cv d) (syn_cun (.cv f) (syn_csn (.cv y))))))) (syn_wrex j (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv c)) (.cv j)) (.classMem (syn_cpw (.cv d)) (.cv j))))) p0078 p0111
  have p0113 :=
    @g_imp (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem e k) (.objMem f k))) (syn_wral a (.cv k) (syn_wral b (.cv k) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))))) (.imp (syn_wrex x (syn_ccompl (.cv e)) (syn_wrex y (syn_ccompl (.cv f)) (syn_wa (.classEq (.cv c) (syn_cun (.cv e) (syn_csn (.cv x)))) (.classEq (.cv d) (syn_cun (.cv f) (syn_csn (.cv y))))))) (syn_wrex j (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv c)) (.cv j)) (.classMem (syn_cpw (.cv d)) (.cv j))))) p0112
  have p0114 :=
    @g_an32s (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem e k) (.objMem f k)) (syn_wral a (.cv k) (syn_wral b (.cv k) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))))) (.imp (syn_wrex x (syn_ccompl (.cv e)) (syn_wrex y (syn_ccompl (.cv f)) (syn_wa (.classEq (.cv c) (syn_cun (.cv e) (syn_csn (.cv x)))) (.classEq (.cv d) (syn_cun (.cv f) (syn_csn (.cv y))))))) (syn_wrex j (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv c)) (.cv j)) (.classMem (syn_cpw (.cv d)) (.cv j))))) p0113
  have p0115_e00_recanon : Nominal.NPrf (.imp (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wral a (.cv k) (syn_wral b (.cv k) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))))))) (syn_wa (.classMem (.cv e) (.cv k)) (.classMem (.cv f) (.cv k)))) (.imp (syn_wrex x (syn_ccompl (.cv e)) (syn_wrex y (syn_ccompl (.cv f)) (syn_wa (.classEq (.cv c) (syn_cun (.cv e) (syn_csn (.cv x)))) (.classEq (.cv d) (syn_cun (.cv f) (syn_csn (.cv y))))))) (syn_wrex j (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv c)) (.cv j)) (.classMem (syn_cpw (.cv d)) (.cv j)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wrex syn_wex syn_ccompl syn_cnin syn_wnan
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0114
  have p0115 :=
    @g_rexlimdvva (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wral a (.cv k) (syn_wral b (.cv k) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))))))) (syn_wrex x (syn_ccompl (.cv e)) (syn_wrex y (syn_ccompl (.cv f)) (syn_wa (.classEq (.cv c) (syn_cun (.cv e) (syn_csn (.cv x)))) (.classEq (.cv d) (syn_cun (.cv f) (syn_csn (.cv y))))))) (syn_wrex j (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv c)) (.cv j)) (.classMem (syn_cpw (.cv d)) (.cv j)))) e f (.cv k) (.cv k) dv_cache_0039 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0043 p0115_e00_recanon
  have p0116 :=
    @g_syl5bi (syn_wa (.classMem (.cv c) (syn_cplc (.cv k) (syn_c1c))) (.classMem (.cv d) (syn_cplc (.cv k) (syn_c1c)))) (syn_wrex e (.cv k) (syn_wrex f (.cv k) (syn_wrex x (syn_ccompl (.cv e)) (syn_wrex y (syn_ccompl (.cv f)) (syn_wa (.classEq (.cv c) (syn_cun (.cv e) (syn_csn (.cv x)))) (.classEq (.cv d) (syn_cun (.cv f) (syn_csn (.cv y))))))))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wral a (.cv k) (syn_wral b (.cv k) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))))))) (syn_wrex j (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv c)) (.cv j)) (.classMem (syn_cpw (.cv d)) (.cv j)))) p0068 p0115
  have p0117 :=
    @g_ralrimivv (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wral a (.cv k) (syn_wral b (.cv k) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))))))) (syn_wrex j (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv c)) (.cv j)) (.classMem (syn_cpw (.cv d)) (.cv j)))) c d (syn_cplc (.cv k) (syn_c1c)) (syn_cplc (.cv k) (syn_c1c)) dv_cache_0025 dv_cache_0075 dv_cache_0076 dv_cache_0077 p0116
  have p0118 :=
    @g_ex (.classMem (.cv k) (syn_cnnc)) (syn_wral a (.cv k) (syn_wral b (.cv k) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))))) (syn_wral c (syn_cplc (.cv k) (syn_c1c)) (syn_wral d (syn_cplc (.cv k) (syn_c1c)) (syn_wrex j (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv c)) (.cv j)) (.classMem (syn_cpw (.cv d)) (.cv j)))))) p0117
  have p0119_e02_recanon : Nominal.NPrf (.imp (.objEq m k) (syn_wb (syn_wral a (.cv m) (syn_wral b (.cv m) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))))) (syn_wral a (.cv k) (syn_wral b (.cv k) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wral
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0035
  have p0119 :=
    @g_finds (syn_wral a (.cv m) (syn_wral b (.cv m) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))))) (syn_wrex n (syn_cnnc) (.classMem (syn_csn (syn_c0)) (.cv n))) (syn_wral a (.cv k) (syn_wral b (.cv k) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))))) (syn_wral c (syn_cplc (.cv k) (syn_c1c)) (syn_wral d (syn_cplc (.cv k) (syn_c1c)) (syn_wrex j (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv c)) (.cv j)) (.classMem (syn_cpw (.cv d)) (.cv j)))))) (syn_wral a M (syn_wral b M (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))))) m k M dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 p0000 p0033 p0119_e02_recanon p0053 p0055 p0061 p0118
  have p0120 :=
    @g_pweq (.cv a) A
  have p0121 :=
    @g_eleq1d (.classEq (.cv a) A) (syn_cpw (.cv a)) (syn_cpw A) (.cv n) p0120
  have p0122 :=
    @g_anbi1d (.classEq (.cv a) A) (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw A) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)) p0121
  have p0123 :=
    @g_rexbidv (.classEq (.cv a) A) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))) (syn_wa (.classMem (syn_cpw A) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))) n (syn_cnnc) dv_cache_0085 p0122
  have p0124 :=
    @g_pweq (.cv b) B
  have p0125 :=
    @g_eleq1d (.classEq (.cv b) B) (syn_cpw (.cv b)) (syn_cpw B) (.cv n) p0124
  have p0126 :=
    @g_anbi2d (.classEq (.cv b) B) (.classMem (syn_cpw (.cv b)) (.cv n)) (.classMem (syn_cpw B) (.cv n)) (.classMem (syn_cpw A) (.cv n)) p0125
  have p0127 :=
    @g_rexbidv (.classEq (.cv b) B) (syn_wa (.classMem (syn_cpw A) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n))) (syn_wa (.classMem (syn_cpw A) (.cv n)) (.classMem (syn_cpw B) (.cv n))) n (syn_cnnc) dv_cache_0086 p0126
  have p0128 :=
    @g_rspc2v (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw A) (.cv n)) (.classMem (syn_cpw B) (.cv n)))) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw A) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))) a b A B M M dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0036 dv_cache_0036 dv_cache_0035 dv_cache_0090 dv_cache_0091 dv_cache_0001 p0123 p0127
  have p0129 :=
    @g_syl5com (.classMem M (syn_cnnc)) (syn_wral a M (syn_wral b M (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))))) (syn_wa (.classMem A M) (.classMem B M)) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw A) (.cv n)) (.classMem (syn_cpw B) (.cv n)))) p0119 p0128
  have p0130 :=
    @g_n_3impib (.classMem M (syn_cnnc)) (.classMem A M) (.classMem B M) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw A) (.cv n)) (.classMem (syn_cpw B) (.cv n)))) p0129
  exact p0130

#print axioms g_nnpweq

end NFChoice.DirectNominalPrf.WPPReplay
