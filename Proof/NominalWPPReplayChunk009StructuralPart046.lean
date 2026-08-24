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
import NominalWPPReplayChunk009StructuralPart045


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

noncomputable def g_ssfin
    (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf (.imp (syn_w3a (.classMem A V) (.classMem B (syn_cfin)) (syn_wss A B)) (.classMem A (syn_cfin))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let n : Var := freshVar proofSupport 2
  let m : Var := freshVar proofSupport 3
  let d : Var := freshVar proofSupport 4
  let k : Var := freshVar proofSupport 5
  let c : Var := freshVar proofSupport 6
  let t : Var := freshVar proofSupport 7
  let x : Var := freshVar proofSupport 8
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_V : a ∉ V.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_not_V : b ∉ V.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_n_not_A : n ∉ A.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_n_not_B : n ∉ B.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_not_V : n ∉ V.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have fresh_m : m ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_m_not_A : m ∉ A.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_m_not_B : m ∉ B.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_m_not_V : m ∉ V.fv := by
    intro h
    exact fresh_m (Finset.mem_union_right _ (h))
  have fresh_d : d ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_not_V : d ∉ V.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_k : k ∉ proofSupport := by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_k_not_A : k ∉ A.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_k_not_B : k ∉ B.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_k_not_V : k ∉ V.fv := by
    intro h
    exact fresh_k (Finset.mem_union_right _ (h))
  have fresh_c : c ∉ proofSupport := by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_c_not_A : c ∉ A.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_c_not_B : c ∉ B.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_c_not_V : c ∉ V.fv := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 7 ∉ proofSupport
    exact freshVar_not_mem proofSupport 7
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_t_not_V : t ∉ V.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 8 ∉ proofSupport
    exact freshVar_not_mem proofSupport 8
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have fresh_a_ne_n : a ≠ n := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_n_ne_a : n ≠ a :=
    Ne.symm fresh_a_ne_n
  have fresh_a_ne_m : a ≠ m := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_m_ne_a : m ≠ a :=
    Ne.symm fresh_a_ne_m
  have fresh_a_ne_d : a ≠ d := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_d_ne_a : d ≠ a :=
    Ne.symm fresh_a_ne_d
  have fresh_a_ne_k : a ≠ k := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_k_ne_a : k ≠ a :=
    Ne.symm fresh_a_ne_k
  have fresh_a_ne_c : a ≠ c := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_c_ne_a : c ≠ a :=
    Ne.symm fresh_a_ne_c
  have fresh_a_ne_t : a ≠ t := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 0) (j := 7) (by decide)
  have fresh_t_ne_a : t ≠ a :=
    Ne.symm fresh_a_ne_t
  have fresh_a_ne_x : a ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 0) (j := 8) (by decide)
  have fresh_x_ne_a : x ≠ a :=
    Ne.symm fresh_a_ne_x
  have fresh_b_ne_n : b ≠ n := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_n_ne_b : n ≠ b :=
    Ne.symm fresh_b_ne_n
  have fresh_b_ne_m : b ≠ m := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_m_ne_b : m ≠ b :=
    Ne.symm fresh_b_ne_m
  have fresh_b_ne_d : b ≠ d := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_d_ne_b : d ≠ b :=
    Ne.symm fresh_b_ne_d
  have fresh_b_ne_k : b ≠ k := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_k_ne_b : k ≠ b :=
    Ne.symm fresh_b_ne_k
  have fresh_b_ne_c : b ≠ c := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_c_ne_b : c ≠ b :=
    Ne.symm fresh_b_ne_c
  have fresh_b_ne_t : b ≠ t := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 1) (j := 7) (by decide)
  have fresh_t_ne_b : t ≠ b :=
    Ne.symm fresh_b_ne_t
  have fresh_b_ne_x : b ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 1) (j := 8) (by decide)
  have fresh_x_ne_b : x ≠ b :=
    Ne.symm fresh_b_ne_x
  have fresh_n_ne_m : n ≠ m := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_m_ne_n : m ≠ n :=
    Ne.symm fresh_n_ne_m
  have fresh_n_ne_d : n ≠ d := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_d_ne_n : d ≠ n :=
    Ne.symm fresh_n_ne_d
  have fresh_n_ne_k : n ≠ k := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_k_ne_n : k ≠ n :=
    Ne.symm fresh_n_ne_k
  have fresh_n_ne_c : n ≠ c := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_c_ne_n : c ≠ n :=
    Ne.symm fresh_n_ne_c
  have fresh_n_ne_t : n ≠ t := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 2) (j := 7) (by decide)
  have fresh_t_ne_n : t ≠ n :=
    Ne.symm fresh_n_ne_t
  have fresh_n_ne_x : n ≠ x := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 2) (j := 8) (by decide)
  have fresh_x_ne_n : x ≠ n :=
    Ne.symm fresh_n_ne_x
  have fresh_m_ne_d : m ≠ d := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_d_ne_m : d ≠ m :=
    Ne.symm fresh_m_ne_d
  have fresh_m_ne_k : m ≠ k := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_k_ne_m : k ≠ m :=
    Ne.symm fresh_m_ne_k
  have fresh_m_ne_c : m ≠ c := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_c_ne_m : c ≠ m :=
    Ne.symm fresh_m_ne_c
  have fresh_m_ne_t : m ≠ t := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 3) (j := 7) (by decide)
  have fresh_t_ne_m : t ≠ m :=
    Ne.symm fresh_m_ne_t
  have fresh_m_ne_x : m ≠ x := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 3) (j := 8) (by decide)
  have fresh_x_ne_m : x ≠ m :=
    Ne.symm fresh_m_ne_x
  have fresh_d_ne_k : d ≠ k := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_k_ne_d : k ≠ d :=
    Ne.symm fresh_d_ne_k
  have fresh_d_ne_c : d ≠ c := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_c_ne_d : c ≠ d :=
    Ne.symm fresh_d_ne_c
  have fresh_d_ne_t : d ≠ t := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 4) (j := 7) (by decide)
  have fresh_t_ne_d : t ≠ d :=
    Ne.symm fresh_d_ne_t
  have fresh_d_ne_x : d ≠ x := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 4) (j := 8) (by decide)
  have fresh_x_ne_d : x ≠ d :=
    Ne.symm fresh_d_ne_x
  have fresh_k_ne_c : k ≠ c := by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_c_ne_k : c ≠ k :=
    Ne.symm fresh_k_ne_c
  have fresh_k_ne_t : k ≠ t := by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 5) (j := 7) (by decide)
  have fresh_t_ne_k : t ≠ k :=
    Ne.symm fresh_k_ne_t
  have fresh_k_ne_x : k ≠ x := by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 5) (j := 8) (by decide)
  have fresh_x_ne_k : x ≠ k :=
    Ne.symm fresh_k_ne_x
  have fresh_c_ne_t : c ≠ t := by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 6) (j := 7) (by decide)
  have fresh_t_ne_c : t ≠ c :=
    Ne.symm fresh_c_ne_t
  have fresh_c_ne_x : c ≠ x := by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 6) (j := 8) (by decide)
  have fresh_x_ne_c : x ≠ c :=
    Ne.symm fresh_c_ne_x
  have fresh_t_ne_x : t ≠ x := by
    change freshVar proofSupport 7 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 7) (j := 8) (by decide)
  have fresh_x_ne_t : x ≠ t :=
    Ne.symm fresh_t_ne_x
  have p0000 :=
    @g_sseq1 (.cv a) A B
  have p0001 :=
    @g_eleq1 (.cv a) A (syn_cfin)
  have p0002 :=
    @g_imbi12d (.classEq (.cv a) A) (syn_wss (.cv a) B) (syn_wss A B) (.classMem (.cv a) (syn_cfin)) (.classMem A (syn_cfin)) p0000 p0001
  have p0003 :=
    @g_imbi2d (.classEq (.cv a) A) (.imp (syn_wss (.cv a) B) (.classMem (.cv a) (syn_cfin))) (.imp (syn_wss A B) (.classMem A (syn_cfin))) (.classMem B (syn_cfin)) p0002
  have p0004 :=
    @g_sseq2 (.cv b) B (.cv a)
  have p0005 :=
    @g_imbi1d (.classEq (.cv b) B) (syn_wss (.cv a) (.cv b)) (syn_wss (.cv a) B) (.classMem (.cv a) (syn_cfin)) p0004
  have p0006 :=
    @g_elfin n (.cv b) (by exact (show n ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show n ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show n ≠ b from (by exact fresh_n_ne_b)))))))
  have p0007 :=
    @g_vex m
  have p0008 :=
    @g_elcompl (.cv m) (syn_cimak (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))) (syn_c1c)) p0007
  have p0009 :=
    @g_alcom (.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))) a b
  have p0010 :=
    @g_impexp (.objMem b m) (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin))
  have p0011 :=
    @g_albii (.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))) (.imp (.objMem b m) (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin)))) a p0010
  have p0012 :=
    @g_n_19_21v (.objMem b m) (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin))) a (by exact (show a ∉ ((Wff.objMem b m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show a ∉ ({b, m} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show a ≠ b from (by exact fresh_a_ne_b)), (show a ≠ m from (by exact fresh_a_ne_m))⟩)))))
  have p0013 :=
    @g_bitri (.all a (.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin)))) (.all a (.imp (.objMem b m) (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin))))) (.imp (.objMem b m) (.all a (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin))))) p0011 p0012
  have p0014 :=
    @g_albii (.all a (.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin)))) (.imp (.objMem b m) (.all a (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin))))) b p0013
  have p0015 :=
    @g_elimak t (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))) (syn_c1c) (.cv m) (by exact (show t ∉ ((syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show t ∉ (((syn_cssetk)).fv) ∪ (((syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show t ∉ ((syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show t ∉ (((syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin))))).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show t ∉ ((syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak]; exact (show t ∉ (((syn_cssetk)).fv) ∪ (((syn_ccompl (syn_cfin))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show t ∉ ((syn_ccompl (syn_cfin))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl]; exact (show t ∉ ((syn_cfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (show t ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (by exact (show t ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show t ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ m from (by exact fresh_t_ne_m))))))) p0007
  have p0016 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex t (syn_c1c) (.classMem (syn_copk (.cv t) (.cv m)) (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))))))
  have p0017 :=
    @g_el1c b (.cv t) (by exact (show b ∉ ((Class.cv t)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({t} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ t from (by exact fresh_b_ne_t)))))))
  have p0018 :=
    @g_anbi1i (.classMem (.cv t) (syn_c1c)) (syn_wex b (.classEq (.cv t) (syn_csn (.cv b)))) (.classMem (syn_copk (.cv t) (.cv m)) (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))) p0017
  have p0019 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (.cv b))) (.classMem (syn_copk (.cv t) (.cv m)) (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))) b (by exact (show b ∉ ((Wff.classMem (syn_copk (.cv t) (.cv m)) (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ (((syn_copk (.cv t) (.cv m))).fv) ∪ (((syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_copk (.cv t) (.cv m))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show b ∉ (((Class.cv t)).fv) ∪ (((Class.cv m)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv t)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({t} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ t from (by exact fresh_b_ne_t)))))) (show b ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ m from (by exact fresh_b_ne_m)))))))))) (show b ∉ ((syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show b ∉ (((syn_cssetk)).fv) ∪ (((syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show b ∉ ((syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show b ∉ (((syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin))))).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show b ∉ ((syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak]; exact (show b ∉ (((syn_cssetk)).fv) ∪ (((syn_ccompl (syn_cfin))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show b ∉ ((syn_ccompl (syn_cfin))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl]; exact (show b ∉ ((syn_cfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (show b ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))))))))
  have p0020 :=
    @g_bitr4i (syn_wa (.classMem (.cv t) (syn_c1c)) (.classMem (syn_copk (.cv t) (.cv m)) (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))))) (syn_wa (syn_wex b (.classEq (.cv t) (syn_csn (.cv b)))) (.classMem (syn_copk (.cv t) (.cv m)) (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))))) (syn_wex b (syn_wa (.classEq (.cv t) (syn_csn (.cv b))) (.classMem (syn_copk (.cv t) (.cv m)) (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))))) p0018 p0019
  have p0021 :=
    @g_exbii (syn_wa (.classMem (.cv t) (syn_c1c)) (.classMem (syn_copk (.cv t) (.cv m)) (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))))) (syn_wex b (syn_wa (.classEq (.cv t) (syn_csn (.cv b))) (.classMem (syn_copk (.cv t) (.cv m)) (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))))) t p0020
  have p0022 :=
    @g_excom (syn_wa (.classEq (.cv t) (syn_csn (.cv b))) (.classMem (syn_copk (.cv t) (.cv m)) (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))))) b t
  have p0023 :=
    @g_bitr4i (syn_wex t (syn_wa (.classMem (.cv t) (syn_c1c)) (.classMem (syn_copk (.cv t) (.cv m)) (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))))) (syn_wex t (syn_wex b (syn_wa (.classEq (.cv t) (syn_csn (.cv b))) (.classMem (syn_copk (.cv t) (.cv m)) (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))))))) (syn_wex b (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv b))) (.classMem (syn_copk (.cv t) (.cv m)) (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))))))) p0021 p0022
  have p0024 :=
    @g_snex (.cv b)
  have p0025 :=
    @g_opkeq1 (.cv t) (syn_csn (.cv b)) (.cv m)
  have p0026 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (.cv b))) (syn_copk (.cv t) (.cv m)) (syn_copk (syn_csn (.cv b)) (.cv m)) (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))) p0025
  have p0027 :=
    @g_ceqsexv (.classMem (syn_copk (.cv t) (.cv m)) (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))) (.classMem (syn_copk (syn_csn (.cv b)) (.cv m)) (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))) t (syn_csn (.cv b)) (by exact (show t ∉ ((syn_csn (.cv b))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ b from (by exact fresh_t_ne_b))))))))) (by exact (show t ∉ ((Wff.classMem (syn_copk (syn_csn (.cv b)) (.cv m)) (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show t ∉ (((syn_copk (syn_csn (.cv b)) (.cv m))).fv) ∪ (((syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_copk (syn_csn (.cv b)) (.cv m))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk]; exact (show t ∉ (((syn_csn (.cv b))).fv) ∪ (((Class.cv m)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_csn (.cv b))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show t ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ b from (by exact fresh_t_ne_b)))))))) (show t ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show t ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show t ≠ m from (by exact fresh_t_ne_m)))))))))) (show t ∉ ((syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show t ∉ (((syn_cssetk)).fv) ∪ (((syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show t ∉ ((syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show t ∉ (((syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin))))).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show t ∉ ((syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak]; exact (show t ∉ (((syn_cssetk)).fv) ∪ (((syn_ccompl (syn_cfin))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show t ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show t ∉ ((syn_ccompl (syn_cfin))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl]; exact (show t ∉ ((syn_cfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (show t ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))))))) p0024 p0026
  have p0028 :=
    @g_elin (syn_copk (syn_csn (.cv b)) (.cv m)) (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))
  have p0029 :=
    @g_vex b
  have p0030 :=
    @g_elssetk (.cv b) (.cv m) p0029 p0007
  have p0031 :=
    @g_opkelxpk (syn_csn (.cv b)) (.cv m) (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv) p0024 p0007
  have p0032 :=
    @g_mpbiran2 (.classMem (syn_copk (syn_csn (.cv b)) (.cv m)) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))) (.classMem (syn_csn (.cv b)) (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin))))) (.classMem (.cv m) (syn_cvv)) p0007 p0031
  have p0033 :=
    @g_snelpw1 (.cv b) (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))
  have p0034 :=
    @g_elimak a (syn_cssetk) (syn_ccompl (syn_cfin)) (.cv b) (by exact (show a ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show a ∉ ((syn_ccompl (syn_cfin))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl]; exact (show a ∉ ((syn_cfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))) (by exact (show a ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ b from (by exact fresh_a_ne_b))))))) p0029
  have p0035 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex a (syn_ccompl (syn_cfin)) (.classMem (syn_copk (.cv a) (.cv b)) (syn_cssetk)))))
  have p0036 :=
    @g_ancom (.classMem (.cv a) (syn_ccompl (syn_cfin))) (.classMem (syn_copk (.cv a) (.cv b)) (syn_cssetk))
  have p0037 :=
    @g_vex a
  have p0038 :=
    @g_opkelssetkg (.cv a) (.cv b) (syn_cvv) (syn_cvv)
  have p0039 :=
    @g_mp2an (.classMem (.cv a) (syn_cvv)) (.classMem (.cv b) (syn_cvv)) (syn_wb (.classMem (syn_copk (.cv a) (.cv b)) (syn_cssetk)) (syn_wss (.cv a) (.cv b))) p0037 p0029 p0038
  have p0040 :=
    @g_elcompl (.cv a) (syn_cfin) p0037
  have p0041 :=
    @g_anbi12i (.classMem (syn_copk (.cv a) (.cv b)) (syn_cssetk)) (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_ccompl (syn_cfin))) (.neg (.classMem (.cv a) (syn_cfin))) p0039 p0040
  have p0042 :=
    @g_bitri (syn_wa (.classMem (.cv a) (syn_ccompl (syn_cfin))) (.classMem (syn_copk (.cv a) (.cv b)) (syn_cssetk))) (syn_wa (.classMem (syn_copk (.cv a) (.cv b)) (syn_cssetk)) (.classMem (.cv a) (syn_ccompl (syn_cfin)))) (syn_wa (syn_wss (.cv a) (.cv b)) (.neg (.classMem (.cv a) (syn_cfin)))) p0036 p0041
  have p0043 :=
    @g_exbii (syn_wa (.classMem (.cv a) (syn_ccompl (syn_cfin))) (.classMem (syn_copk (.cv a) (.cv b)) (syn_cssetk))) (syn_wa (syn_wss (.cv a) (.cv b)) (.neg (.classMem (.cv a) (syn_cfin)))) a p0042
  have p0044 :=
    @g_bitri (syn_wrex a (syn_ccompl (syn_cfin)) (.classMem (syn_copk (.cv a) (.cv b)) (syn_cssetk))) (syn_wex a (syn_wa (.classMem (.cv a) (syn_ccompl (syn_cfin))) (.classMem (syn_copk (.cv a) (.cv b)) (syn_cssetk)))) (syn_wex a (syn_wa (syn_wss (.cv a) (.cv b)) (.neg (.classMem (.cv a) (syn_cfin))))) p0035 p0043
  have p0045 :=
    @g_exanali (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin)) a
  have p0046 :=
    @g_n_3bitri (.classMem (.cv b) (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_wrex a (syn_ccompl (syn_cfin)) (.classMem (syn_copk (.cv a) (.cv b)) (syn_cssetk))) (syn_wex a (syn_wa (syn_wss (.cv a) (.cv b)) (.neg (.classMem (.cv a) (syn_cfin))))) (.neg (.all a (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin))))) p0034 p0044 p0045
  have p0047 :=
    @g_n_3bitri (.classMem (syn_copk (syn_csn (.cv b)) (.cv m)) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))) (.classMem (syn_csn (.cv b)) (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin))))) (.classMem (.cv b) (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (.neg (.all a (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin))))) p0032 p0033 p0046
  have p0048_e00_recanon : Nominal.NPrf (syn_wb (.classMem (syn_copk (syn_csn (.cv b)) (.cv m)) (syn_cssetk)) (.objMem b m)) :=
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
      p0030
  have p0048 :=
    @g_anbi12i (.classMem (syn_copk (syn_csn (.cv b)) (.cv m)) (syn_cssetk)) (.objMem b m) (.classMem (syn_copk (syn_csn (.cv b)) (.cv m)) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))) (.neg (.all a (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin))))) p0048_e00_recanon p0047
  have p0049 :=
    @g_n_3bitri (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv b))) (.classMem (syn_copk (.cv t) (.cv m)) (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))))) (.classMem (syn_copk (syn_csn (.cv b)) (.cv m)) (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))) (syn_wa (.classMem (syn_copk (syn_csn (.cv b)) (.cv m)) (syn_cssetk)) (.classMem (syn_copk (syn_csn (.cv b)) (.cv m)) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))) (syn_wa (.objMem b m) (.neg (.all a (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin)))))) p0027 p0028 p0048
  have p0050 :=
    @g_exbii (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv b))) (.classMem (syn_copk (.cv t) (.cv m)) (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))))) (syn_wa (.objMem b m) (.neg (.all a (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin)))))) b p0049
  have p0051 :=
    @g_n_3bitri (syn_wrex t (syn_c1c) (.classMem (syn_copk (.cv t) (.cv m)) (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))))) (syn_wex t (syn_wa (.classMem (.cv t) (syn_c1c)) (.classMem (syn_copk (.cv t) (.cv m)) (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))))) (syn_wex b (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv b))) (.classMem (syn_copk (.cv t) (.cv m)) (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))))))) (syn_wex b (syn_wa (.objMem b m) (.neg (.all a (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin))))))) p0016 p0023 p0050
  have p0052 :=
    @g_exanali (.objMem b m) (.all a (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin)))) b
  have p0053 :=
    @g_n_3bitri (.classMem (.cv m) (syn_cimak (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))) (syn_c1c))) (syn_wrex t (syn_c1c) (.classMem (syn_copk (.cv t) (.cv m)) (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))))) (syn_wex b (syn_wa (.objMem b m) (.neg (.all a (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin))))))) (.neg (.all b (.imp (.objMem b m) (.all a (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin))))))) p0015 p0051 p0052
  have p0054 :=
    @g_con2bii (.classMem (.cv m) (syn_cimak (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))) (syn_c1c))) (.all b (.imp (.objMem b m) (.all a (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin)))))) p0053
  have p0055 :=
    @g_n_3bitri (.all a (.all b (.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))))) (.all b (.all a (.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))))) (.all b (.imp (.objMem b m) (.all a (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin)))))) (.neg (.classMem (.cv m) (syn_cimak (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))) (syn_c1c)))) p0009 p0014 p0054
  have p0056 :=
    @g_bitr4i (.classMem (.cv m) (syn_ccompl (syn_cimak (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))) (syn_c1c)))) (.neg (.classMem (.cv m) (syn_cimak (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))) (syn_c1c)))) (.all a (.all b (.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))))) p0008 p0055
  have p0057 :=
    @g_eqabi (.all a (.all b (.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))))) m (syn_ccompl (syn_cimak (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))) (syn_c1c))) (by exact (show m ∉ ((syn_ccompl (syn_cimak (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl]; exact (show m ∉ ((syn_cimak (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak]; exact (show m ∉ (((syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show m ∉ (((syn_cssetk)).fv) ∪ (((syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show m ∉ ((syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk]; exact (show m ∉ (((syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin))))).fv) ∪ (((syn_cvv)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show m ∉ ((syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak]; exact (show m ∉ (((syn_cssetk)).fv) ∪ (((syn_ccompl (syn_cfin))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_cssetk)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))) (show m ∉ ((syn_ccompl (syn_cfin))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl]; exact (show m ∉ ((syn_cfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (show m ∉ ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (show m ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))) p0056
  have p0058 :=
    @g_ssetkex
  have p0059 :=
    @g_ssetkex
  have p0060 :=
    @g_finex
  have p0061 :=
    @g_complex (syn_cfin) p0060
  have p0062 :=
    @g_imakex (syn_cssetk) (syn_ccompl (syn_cfin)) p0059 p0061
  have p0063 :=
    @g_pw1ex (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin))) p0062
  have p0064 :=
    @g_vvex
  have p0065 :=
    @g_xpkex (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv) p0063 p0064
  have p0066 :=
    @g_inex (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)) p0058 p0065
  have p0067 :=
    @g_n_1cex
  have p0068 :=
    @g_imakex (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))) (syn_c1c) p0066 p0067
  have p0069 :=
    @g_complex (syn_cimak (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))) (syn_c1c)) p0068
  have p0070 :=
    @g_eqeltrri (syn_ccompl (syn_cimak (syn_cin (syn_cssetk) (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))) (syn_c1c))) (.cab m (.all a (.all b (.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin)))))) (syn_cvv) p0057 p0069
  have p0071 :=
    @g_eleq2 (.cv m) (syn_c0c) (.cv b)
  have p0072 :=
    (by simpa [syn_c0c] using (Nominal.classEqRefl (syn_c0c)))
  have p0073 :=
    @g_eleq2i (syn_c0c) (syn_csn (syn_c0)) (.cv b) p0072
  have p0074 :=
    @g_elsnc (.cv b) (syn_c0) p0029
  have p0075 :=
    @g_bitri (.classMem (.cv b) (syn_c0c)) (.classMem (.cv b) (syn_csn (syn_c0))) (.classEq (.cv b) (syn_c0)) p0073 p0074
  have p0076_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv m) (syn_c0c)) (syn_wb (.objMem b m) (.classMem (.cv b) (syn_c0c)))) :=
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
      p0071
  have p0076 :=
    @g_syl6bb (.classEq (.cv m) (syn_c0c)) (.objMem b m) (.classMem (.cv b) (syn_c0c)) (.classEq (.cv b) (syn_c0)) p0076_e00_recanon p0075
  have p0077 :=
    @g_anbi1d (.classEq (.cv m) (syn_c0c)) (.objMem b m) (.classEq (.cv b) (syn_c0)) (syn_wss (.cv a) (.cv b)) p0076
  have p0078 :=
    @g_imbi1d (.classEq (.cv m) (syn_c0c)) (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b))) (syn_wa (.classEq (.cv b) (syn_c0)) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin)) p0077
  have p0079 :=
    @g_n_2albidv (.classEq (.cv m) (syn_c0c)) (.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))) (.imp (syn_wa (.classEq (.cv b) (syn_c0)) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))) a b (by exact (show a ∉ ((Wff.classEq (.cv m) (syn_c0c))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show a ∉ (((Class.cv m)).fv) ∪ (((syn_c0c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ m from (by exact fresh_a_ne_m)))))) (show a ∉ ((syn_c0c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) (by exact (show b ∉ ((Wff.classEq (.cv m) (syn_c0c))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show b ∉ (((Class.cv m)).fv) ∪ (((syn_c0c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ m from (by exact fresh_b_ne_m)))))) (show b ∉ ((syn_c0c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) p0078
  have p0080 :=
    @g_elequ2 m k b
  have p0081 :=
    @g_anbi1d (.objEq m k) (.objMem b m) (.objMem b k) (syn_wss (.cv a) (.cv b)) p0080
  have p0082 :=
    @g_imbi1d (.objEq m k) (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b))) (syn_wa (.objMem b k) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin)) p0081
  have p0083 :=
    @g_n_2albidv (.objEq m k) (.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))) (.imp (syn_wa (.objMem b k) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))) a b (by exact (show a ∉ ((Wff.objEq m k)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]; exact (show a ∉ ({m, k} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show a ≠ m from (by exact fresh_a_ne_m)), (show a ≠ k from (by exact fresh_a_ne_k))⟩))))) (by exact (show b ∉ ((Wff.objEq m k)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]; exact (show b ∉ ({m, k} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show b ≠ m from (by exact fresh_b_ne_m)), (show b ≠ k from (by exact fresh_b_ne_k))⟩))))) p0082
  have p0084 :=
    @g_eleq1 (.cv b) (.cv d) (.cv k)
  have p0085_e00_recanon : Nominal.NPrf (.imp (.objEq b d) (syn_wb (.objMem b k) (.objMem d k))) :=
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
      p0084
  have p0085 :=
    @g_adantl (.objEq b d) (syn_wb (.objMem b k) (.objMem d k)) (.objEq a c) p0085_e00_recanon
  have p0086 :=
    @g_sseq12 (.cv a) (.cv c) (.cv b) (.cv d)
  have p0087_e01_recanon : Nominal.NPrf (.imp (syn_wa (.objEq a c) (.objEq b d)) (syn_wb (syn_wss (.cv a) (.cv b)) (syn_wss (.cv c) (.cv d)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wb syn_wss syn_cin syn_ccompl syn_cnin syn_wnan
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0086
  have p0087 :=
    @g_anbi12d (syn_wa (.objEq a c) (.objEq b d)) (.objMem b k) (.objMem d k) (syn_wss (.cv a) (.cv b)) (syn_wss (.cv c) (.cv d)) p0085 p0087_e01_recanon
  have p0088 :=
    @g_eleq1 (.cv a) (.cv c) (syn_cfin)
  have p0089_e00_recanon : Nominal.NPrf (.imp (.objEq a c) (syn_wb (.classMem (.cv a) (syn_cfin)) (.classMem (.cv c) (syn_cfin)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cfin syn_cuni syn_wex syn_wa syn_cnnc syn_cint
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0088
  have p0089 :=
    @g_adantr (.objEq a c) (syn_wb (.classMem (.cv a) (syn_cfin)) (.classMem (.cv c) (syn_cfin))) (.objEq b d) p0089_e00_recanon
  have p0090 :=
    @g_imbi12d (syn_wa (.objEq a c) (.objEq b d)) (syn_wa (.objMem b k) (syn_wss (.cv a) (.cv b))) (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv a) (syn_cfin)) (.classMem (.cv c) (syn_cfin)) p0087 p0089
  have p0091 :=
    @g_cbval2v (.imp (syn_wa (.objMem b k) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))) (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin))) a b c d (by exact (show d ∉ ((Wff.imp (syn_wa (.objMem b k) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show d ∉ (((syn_wa (.objMem b k) (syn_wss (.cv a) (.cv b)))).fv) ∪ (((Wff.classMem (.cv a) (syn_cfin))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show d ∉ ((syn_wa (.objMem b k) (syn_wss (.cv a) (.cv b)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show d ∉ (((Wff.objMem b k)).fv) ∪ (((syn_wss (.cv a) (.cv b))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show d ∉ ((Wff.objMem b k)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show d ∉ ({b, k} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show d ≠ b from (by exact fresh_d_ne_b)), (show d ≠ k from (by exact fresh_d_ne_k))⟩)))) (show d ∉ ((syn_wss (.cv a) (.cv b))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss]; exact (show d ∉ (((Class.cv a)).fv) ∪ (((Class.cv b)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show d ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ a from (by exact fresh_d_ne_a)))))) (show d ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ b from (by exact fresh_d_ne_b)))))))))))))) (show d ∉ ((Wff.classMem (.cv a) (syn_cfin))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show d ∉ (((Class.cv a)).fv) ∪ (((syn_cfin)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show d ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ a from (by exact fresh_d_ne_a)))))) (show d ∉ ((syn_cfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin]; exact (show d ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (by exact (show c ∉ ((Wff.imp (syn_wa (.objMem b k) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show c ∉ (((syn_wa (.objMem b k) (syn_wss (.cv a) (.cv b)))).fv) ∪ (((Wff.classMem (.cv a) (syn_cfin))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((syn_wa (.objMem b k) (syn_wss (.cv a) (.cv b)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show c ∉ (((Wff.objMem b k)).fv) ∪ (((syn_wss (.cv a) (.cv b))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((Wff.objMem b k)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show c ∉ ({b, k} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show c ≠ b from (by exact fresh_c_ne_b)), (show c ≠ k from (by exact fresh_c_ne_k))⟩)))) (show c ∉ ((syn_wss (.cv a) (.cv b))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss]; exact (show c ∉ (((Class.cv a)).fv) ∪ (((Class.cv b)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ a from (by exact fresh_c_ne_a)))))) (show c ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ b from (by exact fresh_c_ne_b)))))))))))))) (show c ∉ ((Wff.classMem (.cv a) (syn_cfin))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show c ∉ (((Class.cv a)).fv) ∪ (((syn_cfin)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ a from (by exact fresh_c_ne_a)))))) (show c ∉ ((syn_cfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin]; exact (show c ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (by exact (show a ∉ ((Wff.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show a ∉ (((syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))).fv) ∪ (((Wff.classMem (.cv c) (syn_cfin))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show a ∉ (((Wff.objMem d k)).fv) ∪ (((syn_wss (.cv c) (.cv d))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Wff.objMem d k)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show a ∉ ({d, k} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show a ≠ d from (by exact fresh_a_ne_d)), (show a ≠ k from (by exact fresh_a_ne_k))⟩)))) (show a ∉ ((syn_wss (.cv c) (.cv d))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss]; exact (show a ∉ (((Class.cv c)).fv) ∪ (((Class.cv d)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ c from (by exact fresh_a_ne_c)))))) (show a ∉ ((Class.cv d)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({d} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ d from (by exact fresh_a_ne_d)))))))))))))) (show a ∉ ((Wff.classMem (.cv c) (syn_cfin))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show a ∉ (((Class.cv c)).fv) ∪ (((syn_cfin)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ c from (by exact fresh_a_ne_c)))))) (show a ∉ ((syn_cfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (by exact (show b ∉ ((Wff.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show b ∉ (((syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))).fv) ∪ (((Wff.classMem (.cv c) (syn_cfin))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show b ∉ (((Wff.objMem d k)).fv) ∪ (((syn_wss (.cv c) (.cv d))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Wff.objMem d k)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show b ∉ ({d, k} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show b ≠ d from (by exact fresh_b_ne_d)), (show b ≠ k from (by exact fresh_b_ne_k))⟩)))) (show b ∉ ((syn_wss (.cv c) (.cv d))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss]; exact (show b ∉ (((Class.cv c)).fv) ∪ (((Class.cv d)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ c from (by exact fresh_b_ne_c)))))) (show b ∉ ((Class.cv d)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({d} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ d from (by exact fresh_b_ne_d)))))))))))))) (show b ∉ ((Wff.classMem (.cv c) (syn_cfin))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ (((Class.cv c)).fv) ∪ (((syn_cfin)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ c from (by exact fresh_b_ne_c)))))) (show b ∉ ((syn_cfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (show d ≠ a from (by exact fresh_d_ne_a)) (show d ≠ c from (by exact fresh_d_ne_c)) (show a ≠ b from (by exact fresh_a_ne_b)) (show b ≠ c from (by exact fresh_b_ne_c)) p0090
  have p0092 :=
    @g_syl6bb (.objEq m k) (.all a (.all b (.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))))) (.all a (.all b (.imp (syn_wa (.objMem b k) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))))) (.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin))))) p0083 p0091
  have p0093 :=
    @g_eleq2 (.cv m) (syn_cplc (.cv k) (syn_c1c)) (.cv b)
  have p0094_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))) (syn_wb (.objMem b m) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))))) :=
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
      p0093
  have p0094 :=
    @g_anbi1d (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))) (.objMem b m) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (syn_wss (.cv a) (.cv b)) p0094_e00_recanon
  have p0095 :=
    @g_imbi1d (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))) (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b))) (syn_wa (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin)) p0094
  have p0096 :=
    @g_n_2albidv (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))) (.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))) (.imp (syn_wa (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))) a b (by exact (show a ∉ ((Wff.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show a ∉ (((Class.cv m)).fv) ∪ (((syn_cplc (.cv k) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ m from (by exact fresh_a_ne_m)))))) (show a ∉ ((syn_cplc (.cv k) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show a ∉ (((Class.cv k)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Class.cv k)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({k} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ k from (by exact fresh_a_ne_k)))))) (show a ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (by exact (show b ∉ ((Wff.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show b ∉ (((Class.cv m)).fv) ∪ (((syn_cplc (.cv k) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({m} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ m from (by exact fresh_b_ne_m)))))) (show b ∉ ((syn_cplc (.cv k) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show b ∉ (((Class.cv k)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv k)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({k} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ k from (by exact fresh_b_ne_k)))))) (show b ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) p0095
  have p0097 :=
    @g_elequ2 m n b
  have p0098 :=
    @g_anbi1d (.objEq m n) (.objMem b m) (.objMem b n) (syn_wss (.cv a) (.cv b)) p0097
  have p0099 :=
    @g_imbi1d (.objEq m n) (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b))) (syn_wa (.objMem b n) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin)) p0098
  have p0100 :=
    @g_n_2albidv (.objEq m n) (.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))) (.imp (syn_wa (.objMem b n) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))) a b (by exact (show a ∉ ((Wff.objEq m n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]; exact (show a ∉ ({m, n} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show a ≠ m from (by exact fresh_a_ne_m)), (show a ≠ n from (by exact fresh_a_ne_n))⟩))))) (by exact (show b ∉ ((Wff.objEq m n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]; exact (show b ∉ ({m, n} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show b ≠ m from (by exact fresh_b_ne_m)), (show b ≠ n from (by exact fresh_b_ne_n))⟩))))) p0099
  have p0101 :=
    @g_sseq2 (.cv b) (syn_c0) (.cv a)
  have p0102 :=
    @g_biimpa (.classEq (.cv b) (syn_c0)) (syn_wss (.cv a) (.cv b)) (syn_wss (.cv a) (syn_c0)) p0101
  have p0103 :=
    @g_ss0b (.cv a)
  have p0104 :=
    @g_sylib (syn_wa (.classEq (.cv b) (syn_c0)) (syn_wss (.cv a) (.cv b))) (syn_wss (.cv a) (syn_c0)) (.classEq (.cv a) (syn_c0)) p0102 p0103
  have p0105 :=
    @g_n_0fin
  have p0106 :=
    @g_syl6eqel (syn_wa (.classEq (.cv b) (syn_c0)) (syn_wss (.cv a) (.cv b))) (.cv a) (syn_c0) (syn_cfin) p0104 p0105
  have p0107 :=
    @g_gen2 (.imp (syn_wa (.classEq (.cv b) (syn_c0)) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))) a b p0106
  have p0108 :=
    @g_sspss (.cv a) (.cv b)
  have p0109 :=
    @g_dfpss4 x (.cv a) (.cv b) (by exact (show x ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ a from (by exact fresh_x_ne_a))))))) (by exact (show x ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ b from (by exact fresh_x_ne_b)))))))
  have p0110_e00_recanon : Nominal.NPrf (syn_wb (syn_wpss (.cv a) (.cv b)) (syn_wa (syn_wss (.cv a) (.cv b)) (syn_wrex x (.cv b) (.neg (.objMem x a))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wpss syn_wa syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wne
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wpss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.neg
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
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
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
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
      p0109
  have p0110 :=
    @g_orbi1i (syn_wpss (.cv a) (.cv b)) (syn_wa (syn_wss (.cv a) (.cv b)) (syn_wrex x (.cv b) (.neg (.objMem x a)))) (.objEq a b) p0110_e00_recanon
  have p0111_e00_recanon : Nominal.NPrf (syn_wb (syn_wss (.cv a) (.cv b)) (syn_wo (syn_wpss (.cv a) (.cv b)) (.objEq a b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_wo syn_wpss
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wpss, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
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
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0108
  have p0111 :=
    @g_bitri (syn_wss (.cv a) (.cv b)) (syn_wo (syn_wpss (.cv a) (.cv b)) (.objEq a b)) (syn_wo (syn_wa (syn_wss (.cv a) (.cv b)) (syn_wrex x (.cv b) (.neg (.objMem x a)))) (.objEq a b)) p0111_e00_recanon p0110
  have p0112 :=
    @g_simp1 (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem x b) (.neg (.objMem x a))) (syn_wa (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))))
  have p0113 :=
    @g_vex x
  have p0114 :=
    @g_snid (.cv x) p0113
  have p0115 :=
    @g_eldif (.cv x) (.cv b) (syn_csn (.cv x))
  have p0116_e00_recanon : Nominal.NPrf (syn_wb (.classMem (.cv x) (syn_cdif (.cv b) (syn_csn (.cv x)))) (syn_wa (.objMem x b) (.neg (.classMem (.cv x) (syn_csn (.cv x)))))) :=
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
      p0115
  have p0116 :=
    @g_simprbi (.classMem (.cv x) (syn_cdif (.cv b) (syn_csn (.cv x)))) (.objMem x b) (.neg (.classMem (.cv x) (syn_csn (.cv x)))) p0116_e00_recanon
  have p0117 :=
    @g_mt2 (.classMem (.cv x) (syn_cdif (.cv b) (syn_csn (.cv x)))) (.classMem (.cv x) (syn_csn (.cv x))) p0114 p0116
  have p0118 :=
    @g_a1i (.neg (.classMem (.cv x) (syn_cdif (.cv b) (syn_csn (.cv x))))) (syn_w3a (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem x b) (.neg (.objMem x a))) (syn_wa (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))))) p0117
  have p0119 :=
    @g_undif1 (.cv b) (syn_csn (.cv x))
  have p0120 :=
    @g_snssi (.cv x) (.cv b)
  have p0121 :=
    @g_ssequn2 (syn_csn (.cv x)) (.cv b)
  have p0122_e00_recanon : Nominal.NPrf (.imp (.objMem x b) (syn_wss (syn_csn (.cv x)) (.cv b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0120
  have p0122 :=
    @g_sylib (.objMem x b) (syn_wss (syn_csn (.cv x)) (.cv b)) (.classEq (syn_cun (.cv b) (syn_csn (.cv x))) (.cv b)) p0122_e00_recanon p0121
  have p0123 :=
    @g_adantr (.objMem x b) (.classEq (syn_cun (.cv b) (syn_csn (.cv x))) (.cv b)) (.neg (.objMem x a)) p0122
  have p0124 :=
    @g_n_3ad2ant2 (syn_wa (.objMem x b) (.neg (.objMem x a))) (.classMem (.cv k) (syn_cnnc)) (.classEq (syn_cun (.cv b) (syn_csn (.cv x))) (.cv b)) (syn_wa (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c)))) p0123
  have p0125 :=
    @g_syl5eq (syn_w3a (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem x b) (.neg (.objMem x a))) (syn_wa (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))))) (syn_cun (syn_cdif (.cv b) (syn_csn (.cv x))) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv x))) (.cv b) p0119 p0124
  have p0126 :=
    @g_simp3r (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem x b) (.neg (.objMem x a))) (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c)))
  have p0127 :=
    @g_eqeltrd (syn_w3a (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem x b) (.neg (.objMem x a))) (syn_wa (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))))) (syn_cun (syn_cdif (.cv b) (syn_csn (.cv x))) (syn_csn (.cv x))) (.cv b) (syn_cplc (.cv k) (syn_c1c)) p0125 p0126
  have p0128 :=
    @g_snex (.cv x)
  have p0129 :=
    @g_difex (.cv b) (syn_csn (.cv x)) p0029 p0128
  have p0130 :=
    @g_nnsucelr (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k) (.cv x) p0129 p0113
  have p0131 :=
    @g_syl12anc (syn_w3a (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem x b) (.neg (.objMem x a))) (syn_wa (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))))) (.classMem (.cv k) (syn_cnnc)) (.neg (.classMem (.cv x) (syn_cdif (.cv b) (syn_csn (.cv x))))) (.classMem (syn_cun (syn_cdif (.cv b) (syn_csn (.cv x))) (syn_csn (.cv x))) (syn_cplc (.cv k) (syn_c1c))) (.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k)) p0112 p0118 p0127 p0130
  have p0132 :=
    @g_inass (.cv a) (.cv b) (syn_ccompl (syn_csn (.cv x)))
  have p0133 :=
    (by simpa [syn_cdif] using (Nominal.classEqRefl (syn_cdif (syn_cin (.cv a) (.cv b)) (syn_csn (.cv x)))))
  have p0134 :=
    (by simpa [syn_cdif] using (Nominal.classEqRefl (syn_cdif (.cv b) (syn_csn (.cv x)))))
  have p0135 :=
    @g_ineq2i (syn_cdif (.cv b) (syn_csn (.cv x))) (syn_cin (.cv b) (syn_ccompl (syn_csn (.cv x)))) (.cv a) p0134
  have p0136 :=
    @g_n_3eqtr4ri (syn_cin (syn_cin (.cv a) (.cv b)) (syn_ccompl (syn_csn (.cv x)))) (syn_cin (.cv a) (syn_cin (.cv b) (syn_ccompl (syn_csn (.cv x))))) (syn_cdif (syn_cin (.cv a) (.cv b)) (syn_csn (.cv x))) (syn_cin (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x)))) p0132 p0133 p0135
  have p0137 :=
    (by simpa [syn_wb, syn_wss] using (Nominal.biimpRefl (syn_wss (.cv a) (.cv b))))
  have p0138 :=
    @g_biimpi (syn_wss (.cv a) (.cv b)) (.classEq (syn_cin (.cv a) (.cv b)) (.cv a)) p0137
  have p0139 :=
    @g_adantr (syn_wss (.cv a) (.cv b)) (.classEq (syn_cin (.cv a) (.cv b)) (.cv a)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) p0138
  have p0140 :=
    @g_n_3ad2ant3 (syn_wa (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c)))) (.classMem (.cv k) (syn_cnnc)) (.classEq (syn_cin (.cv a) (.cv b)) (.cv a)) (syn_wa (.objMem x b) (.neg (.objMem x a))) p0139
  have p0141 :=
    @g_difeq1d (syn_w3a (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem x b) (.neg (.objMem x a))) (syn_wa (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))))) (syn_cin (.cv a) (.cv b)) (.cv a) (syn_csn (.cv x)) p0140
  have p0142 :=
    @g_difsn (.cv x) (.cv a)
  have p0143_e00_recanon : Nominal.NPrf (.imp (.neg (.objMem x a)) (.classEq (syn_cdif (.cv a) (syn_csn (.cv x))) (.cv a))) :=
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
      p0142
  have p0143 :=
    @g_adantl (.neg (.objMem x a)) (.classEq (syn_cdif (.cv a) (syn_csn (.cv x))) (.cv a)) (.objMem x b) p0143_e00_recanon
  have p0144 :=
    @g_n_3ad2ant2 (syn_wa (.objMem x b) (.neg (.objMem x a))) (.classMem (.cv k) (syn_cnnc)) (.classEq (syn_cdif (.cv a) (syn_csn (.cv x))) (.cv a)) (syn_wa (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c)))) p0143
  have p0145 :=
    @g_eqtrd (syn_w3a (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem x b) (.neg (.objMem x a))) (syn_wa (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))))) (syn_cdif (syn_cin (.cv a) (.cv b)) (syn_csn (.cv x))) (syn_cdif (.cv a) (syn_csn (.cv x))) (.cv a) p0141 p0144
  have p0146 :=
    @g_syl5eq (syn_w3a (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem x b) (.neg (.objMem x a))) (syn_wa (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))))) (syn_cin (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x)))) (syn_cdif (syn_cin (.cv a) (.cv b)) (syn_csn (.cv x))) (.cv a) p0136 p0145
  have p0147 :=
    (by simpa [syn_wb, syn_wss] using (Nominal.biimpRefl (syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x))))))
  have p0148 :=
    @g_sylibr (syn_w3a (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem x b) (.neg (.objMem x a))) (syn_wa (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))))) (.classEq (syn_cin (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x)))) (.cv a)) (syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x)))) p0146 p0147
  have p0149 :=
    @g_jca (syn_w3a (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem x b) (.neg (.objMem x a))) (syn_wa (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))))) (.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k)) (syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x)))) p0131 p0148
  have p0150 :=
    @g_n_3adant1r (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem x b) (.neg (.objMem x a))) (syn_wa (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c)))) (syn_wa (.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k)) (syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x))))) (.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin))))) p0149
  have p0151 :=
    @g_eleq1 (.cv d) (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k)
  have p0152_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv d) (syn_cdif (.cv b) (syn_csn (.cv x)))) (syn_wb (.objMem d k) (.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k)))) :=
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
      p0151
  have p0152 :=
    @g_adantl (.classEq (.cv d) (syn_cdif (.cv b) (syn_csn (.cv x)))) (syn_wb (.objMem d k) (.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k))) (.objEq c a) p0152_e00_recanon
  have p0153 :=
    @g_sseq12 (.cv c) (.cv a) (.cv d) (syn_cdif (.cv b) (syn_csn (.cv x)))
  have p0154_e01_recanon : Nominal.NPrf (.imp (syn_wa (.objEq c a) (.classEq (.cv d) (syn_cdif (.cv b) (syn_csn (.cv x))))) (syn_wb (syn_wss (.cv c) (.cv d)) (syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_csn syn_wb syn_wss
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
      p0153
  have p0154 :=
    @g_anbi12d (syn_wa (.objEq c a) (.classEq (.cv d) (syn_cdif (.cv b) (syn_csn (.cv x))))) (.objMem d k) (.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k)) (syn_wss (.cv c) (.cv d)) (syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x)))) p0152 p0154_e01_recanon
  have p0155 :=
    @g_eleq1 (.cv c) (.cv a) (syn_cfin)
  have p0156_e00_recanon : Nominal.NPrf (.imp (.objEq c a) (syn_wb (.classMem (.cv c) (syn_cfin)) (.classMem (.cv a) (syn_cfin)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cfin syn_cuni syn_wex syn_wa syn_cnnc syn_cint
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0155
  have p0156 :=
    @g_adantr (.objEq c a) (syn_wb (.classMem (.cv c) (syn_cfin)) (.classMem (.cv a) (syn_cfin))) (.classEq (.cv d) (syn_cdif (.cv b) (syn_csn (.cv x)))) p0156_e00_recanon
  have p0157 :=
    @g_imbi12d (syn_wa (.objEq c a) (.classEq (.cv d) (syn_cdif (.cv b) (syn_csn (.cv x))))) (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (syn_wa (.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k)) (syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x))))) (.classMem (.cv c) (syn_cfin)) (.classMem (.cv a) (syn_cfin)) p0154 p0156
  have p0158_e00_recanon : Nominal.NPrf (.imp (syn_wa (.classEq (.cv c) (.cv a)) (.classEq (.cv d) (syn_cdif (.cv b) (syn_csn (.cv x))))) (syn_wb (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin))) (.imp (syn_wa (.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k)) (syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x))))) (.classMem (.cv a) (syn_cfin))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_csn syn_wb syn_cfin syn_cuni syn_wex syn_cnnc syn_cint
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0157
  have p0158 :=
    @g_spc2gv (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin))) (.imp (syn_wa (.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k)) (syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x))))) (.classMem (.cv a) (syn_cfin))) c d (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x))) (syn_cvv) (syn_cvv) (by exact (show c ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ a from (by exact fresh_c_ne_a))))))) (by exact (show d ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ a from (by exact fresh_d_ne_a))))))) (by exact (show c ∉ ((syn_cdif (.cv b) (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif]; exact (show c ∉ (((Class.cv b)).fv) ∪ (((syn_csn (.cv x))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ b from (by exact fresh_c_ne_b)))))) (show c ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show c ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ x from (by exact fresh_c_ne_x))))))))))))) (by exact (show d ∉ ((syn_cdif (.cv b) (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif]; exact (show d ∉ (((Class.cv b)).fv) ∪ (((syn_csn (.cv x))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show d ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ b from (by exact fresh_d_ne_b)))))) (show d ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show d ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ x from (by exact fresh_d_ne_x))))))))))))) (by exact (show c ∉ ((Wff.imp (syn_wa (.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k)) (syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x))))) (.classMem (.cv a) (syn_cfin)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show c ∉ (((syn_wa (.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k)) (syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x)))))).fv) ∪ (((Wff.classMem (.cv a) (syn_cfin))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((syn_wa (.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k)) (syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show c ∉ (((Wff.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k))).fv) ∪ (((syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((Wff.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show c ∉ (((syn_cdif (.cv b) (syn_csn (.cv x)))).fv) ∪ (((Class.cv k)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((syn_cdif (.cv b) (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif]; exact (show c ∉ (((Class.cv b)).fv) ∪ (((syn_csn (.cv x))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ b from (by exact fresh_c_ne_b)))))) (show c ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show c ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ x from (by exact fresh_c_ne_x)))))))))))) (show c ∉ ((Class.cv k)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({k} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ k from (by exact fresh_c_ne_k)))))))))) (show c ∉ ((syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss]; exact (show c ∉ (((Class.cv a)).fv) ∪ (((syn_cdif (.cv b) (syn_csn (.cv x)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ a from (by exact fresh_c_ne_a)))))) (show c ∉ ((syn_cdif (.cv b) (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif]; exact (show c ∉ (((Class.cv b)).fv) ∪ (((syn_csn (.cv x))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ b from (by exact fresh_c_ne_b)))))) (show c ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show c ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ x from (by exact fresh_c_ne_x)))))))))))))))))))) (show c ∉ ((Wff.classMem (.cv a) (syn_cfin))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show c ∉ (((Class.cv a)).fv) ∪ (((syn_cfin)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ a from (by exact fresh_c_ne_a)))))) (show c ∉ ((syn_cfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin]; exact (show c ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (by exact (show d ∉ ((Wff.imp (syn_wa (.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k)) (syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x))))) (.classMem (.cv a) (syn_cfin)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show d ∉ (((syn_wa (.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k)) (syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x)))))).fv) ∪ (((Wff.classMem (.cv a) (syn_cfin))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show d ∉ ((syn_wa (.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k)) (syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show d ∉ (((Wff.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k))).fv) ∪ (((syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show d ∉ ((Wff.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show d ∉ (((syn_cdif (.cv b) (syn_csn (.cv x)))).fv) ∪ (((Class.cv k)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show d ∉ ((syn_cdif (.cv b) (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif]; exact (show d ∉ (((Class.cv b)).fv) ∪ (((syn_csn (.cv x))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show d ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ b from (by exact fresh_d_ne_b)))))) (show d ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show d ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ x from (by exact fresh_d_ne_x)))))))))))) (show d ∉ ((Class.cv k)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({k} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ k from (by exact fresh_d_ne_k)))))))))) (show d ∉ ((syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss]; exact (show d ∉ (((Class.cv a)).fv) ∪ (((syn_cdif (.cv b) (syn_csn (.cv x)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show d ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ a from (by exact fresh_d_ne_a)))))) (show d ∉ ((syn_cdif (.cv b) (syn_csn (.cv x)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif]; exact (show d ∉ (((Class.cv b)).fv) ∪ (((syn_csn (.cv x))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show d ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ b from (by exact fresh_d_ne_b)))))) (show d ∉ ((syn_csn (.cv x))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show d ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ x from (by exact fresh_d_ne_x)))))))))))))))))))) (show d ∉ ((Wff.classMem (.cv a) (syn_cfin))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show d ∉ (((Class.cv a)).fv) ∪ (((syn_cfin)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show d ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ a from (by exact fresh_d_ne_a)))))) (show d ∉ ((syn_cfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin]; exact (show d ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) (show c ≠ d from (by exact fresh_c_ne_d)) p0158_e00_recanon
  have p0159 :=
    @g_mp2an (.classMem (.cv a) (syn_cvv)) (.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (syn_cvv)) (.imp (.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin))))) (.imp (syn_wa (.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k)) (syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x))))) (.classMem (.cv a) (syn_cfin)))) p0037 p0129 p0158
  have p0160 :=
    @g_adantl (.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin))))) (.imp (syn_wa (.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k)) (syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x))))) (.classMem (.cv a) (syn_cfin))) (.classMem (.cv k) (syn_cnnc)) p0159
  have p0161 :=
    @g_n_3ad2ant1 (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin)))))) (syn_wa (.objMem x b) (.neg (.objMem x a))) (.imp (syn_wa (.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k)) (syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x))))) (.classMem (.cv a) (syn_cfin))) (syn_wa (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c)))) p0160
  have p0162 :=
    @g_mpd (syn_w3a (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin)))))) (syn_wa (.objMem x b) (.neg (.objMem x a))) (syn_wa (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))))) (syn_wa (.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k)) (syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x))))) (.classMem (.cv a) (syn_cfin)) p0150 p0161
  have p0163 :=
    @g_n_3exp (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin)))))) (syn_wa (.objMem x b) (.neg (.objMem x a))) (syn_wa (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c)))) (.classMem (.cv a) (syn_cfin)) p0162
  have p0164 :=
    @g_exp5c (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin)))))) (.objMem x b) (.neg (.objMem x a)) (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (.classMem (.cv a) (syn_cfin)) p0163
  have p0165_e00_recanon : Nominal.NPrf (.imp (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin)))))) (.imp (.classMem (.cv x) (.cv b)) (.imp (.neg (.objMem x a)) (.imp (syn_wss (.cv a) (.cv b)) (.imp (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (.classMem (.cv a) (syn_cfin))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cnnc syn_cint syn_cfin syn_cuni syn_wex syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_cplc syn_wrex syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0164
  have p0165 :=
    @g_rexlimdv (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin)))))) (.neg (.objMem x a)) (.imp (syn_wss (.cv a) (.cv b)) (.imp (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (.classMem (.cv a) (syn_cfin)))) x (.cv b) (by exact (show x ∉ ((Wff.imp (syn_wss (.cv a) (.cv b)) (.imp (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (.classMem (.cv a) (syn_cfin))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show x ∉ (((syn_wss (.cv a) (.cv b))).fv) ∪ (((Wff.imp (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (.classMem (.cv a) (syn_cfin)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_wss (.cv a) (.cv b))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss]; exact (show x ∉ (((Class.cv a)).fv) ∪ (((Class.cv b)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ a from (by exact fresh_x_ne_a)))))) (show x ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ b from (by exact fresh_x_ne_b)))))))))) (show x ∉ ((Wff.imp (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (.classMem (.cv a) (syn_cfin)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show x ∉ (((Wff.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c)))).fv) ∪ (((Wff.classMem (.cv a) (syn_cfin))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Wff.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((Class.cv b)).fv) ∪ (((syn_cplc (.cv k) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ b from (by exact fresh_x_ne_b)))))) (show x ∉ ((syn_cplc (.cv k) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ (((Class.cv k)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv k)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({k} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ k from (by exact fresh_x_ne_k)))))) (show x ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (show x ∉ ((Wff.classMem (.cv a) (syn_cfin))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((Class.cv a)).fv) ∪ (((syn_cfin)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ a from (by exact fresh_x_ne_a)))))) (show x ∉ ((syn_cfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))))))) (by exact (show x ∉ ((syn_wa (.classMem (.cv k) (syn_cnnc)) (.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show x ∉ (((Wff.classMem (.cv k) (syn_cnnc))).fv) ∪ (((Wff.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin)))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Wff.classMem (.cv k) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((Class.cv k)).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv k)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({k} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ k from (by exact fresh_x_ne_k)))))) (show x ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show x ∉ ((Wff.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin)))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact (show x ∉ (((Wff.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin))))).fv).erase c from (fun hmem => (show x ∉ ((Wff.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact (show x ∉ (((Wff.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin)))).fv).erase d from (fun hmem => (show x ∉ ((Wff.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show x ∉ (((syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))).fv) ∪ (((Wff.classMem (.cv c) (syn_cfin))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show x ∉ (((Wff.objMem d k)).fv) ∪ (((syn_wss (.cv c) (.cv d))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Wff.objMem d k)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show x ∉ ({d, k} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show x ≠ d from (by exact fresh_x_ne_d)), (show x ≠ k from (by exact fresh_x_ne_k))⟩)))) (show x ∉ ((syn_wss (.cv c) (.cv d))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss]; exact (show x ∉ (((Class.cv c)).fv) ∪ (((Class.cv d)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ c from (by exact fresh_x_ne_c)))))) (show x ∉ ((Class.cv d)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({d} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ d from (by exact fresh_x_ne_d)))))))))))))) (show x ∉ ((Wff.classMem (.cv c) (syn_cfin))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((Class.cv c)).fv) ∪ (((syn_cfin)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ c from (by exact fresh_x_ne_c)))))) (show x ∉ ((syn_cfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (Finset.mem_of_mem_erase hmem))))) (Finset.mem_of_mem_erase hmem)))))))))) p0165_e00_recanon
  have p0166 :=
    @g_com23 (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin)))))) (syn_wrex x (.cv b) (.neg (.objMem x a))) (syn_wss (.cv a) (.cv b)) (.imp (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (.classMem (.cv a) (syn_cfin))) p0165
  have p0167 :=
    @g_imp3a (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin)))))) (syn_wss (.cv a) (.cv b)) (syn_wrex x (.cv b) (.neg (.objMem x a))) (.imp (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (.classMem (.cv a) (syn_cfin))) p0166
  have p0168 :=
    @g_peano2 (.cv k)
  have p0169 :=
    @g_eleq2 (.cv x) (syn_cplc (.cv k) (syn_c1c)) (.cv b)
  have p0170_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv x) (syn_cplc (.cv k) (syn_c1c))) (syn_wb (.objMem b x) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))))) :=
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
      p0169
  have p0170 :=
    @g_rspcev (.objMem b x) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) x (syn_cplc (.cv k) (syn_c1c)) (syn_cnnc) (by exact (show x ∉ ((syn_cplc (.cv k) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ (((Class.cv k)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv k)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({k} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ k from (by exact fresh_x_ne_k)))))) (show x ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))) (by exact (show x ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show x ∉ ((Wff.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show x ∉ (((Class.cv b)).fv) ∪ (((syn_cplc (.cv k) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ b from (by exact fresh_x_ne_b)))))) (show x ∉ ((syn_cplc (.cv k) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ (((Class.cv k)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((Class.cv k)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({k} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ k from (by exact fresh_x_ne_k)))))) (show x ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) p0170_e00_recanon
  have p0171 :=
    @g_elfin x (.cv b) (by exact (show x ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show x ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show x ≠ b from (by exact fresh_x_ne_b)))))))
  have p0172_e01_recanon : Nominal.NPrf (syn_wb (.classMem (.cv b) (syn_cfin)) (syn_wrex x (syn_cnnc) (.objMem b x))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cfin syn_cuni syn_wex syn_wa syn_cnnc syn_cint syn_wrex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
      p0171
  have p0172 :=
    @g_sylibr (syn_wa (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cnnc)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c)))) (syn_wrex x (syn_cnnc) (.objMem b x)) (.classMem (.cv b) (syn_cfin)) p0170 p0172_e01_recanon
  have p0173 :=
    @g_ex (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cnnc)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (.classMem (.cv b) (syn_cfin)) p0172
  have p0174 :=
    @g_syl (.classMem (.cv k) (syn_cnnc)) (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cnnc)) (.imp (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (.classMem (.cv b) (syn_cfin))) p0168 p0173
  have p0175 :=
    @g_eleq1 (.cv a) (.cv b) (syn_cfin)
  have p0176_e00_recanon : Nominal.NPrf (.imp (.objEq a b) (syn_wb (.classMem (.cv a) (syn_cfin)) (.classMem (.cv b) (syn_cfin)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cfin syn_cuni syn_wex syn_wa syn_cnnc syn_cint
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0175
  have p0176 :=
    @g_biimprd (.objEq a b) (.classMem (.cv a) (syn_cfin)) (.classMem (.cv b) (syn_cfin)) p0176_e00_recanon
  have p0177 :=
    @g_syl9 (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (.classMem (.cv b) (syn_cfin)) (.objEq a b) (.classMem (.cv a) (syn_cfin)) p0174 p0176
  have p0178 :=
    @g_adantr (.classMem (.cv k) (syn_cnnc)) (.imp (.objEq a b) (.imp (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (.classMem (.cv a) (syn_cfin)))) (.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin))))) p0177
  have p0179 :=
    @g_jaod (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin)))))) (syn_wa (syn_wss (.cv a) (.cv b)) (syn_wrex x (.cv b) (.neg (.objMem x a)))) (.imp (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (.classMem (.cv a) (syn_cfin))) (.objEq a b) p0167 p0178
  have p0180 :=
    @g_syl5bi (syn_wss (.cv a) (.cv b)) (syn_wo (syn_wa (syn_wss (.cv a) (.cv b)) (syn_wrex x (.cv b) (.neg (.objMem x a)))) (.objEq a b)) (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin)))))) (.imp (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (.classMem (.cv a) (syn_cfin))) p0111 p0179
  have p0181 :=
    @g_com23 (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin)))))) (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (.classMem (.cv a) (syn_cfin)) p0180
  have p0182 :=
    @g_imp3a (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin)))))) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin)) p0181
  have p0183 :=
    @g_alrimivv (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin)))))) (.imp (syn_wa (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))) a b (by exact (show a ∉ ((syn_wa (.classMem (.cv k) (syn_cnnc)) (.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show a ∉ (((Wff.classMem (.cv k) (syn_cnnc))).fv) ∪ (((Wff.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin)))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Wff.classMem (.cv k) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show a ∉ (((Class.cv k)).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Class.cv k)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({k} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ k from (by exact fresh_a_ne_k)))))) (show a ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show a ∉ ((Wff.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin)))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact (show a ∉ (((Wff.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin))))).fv).erase c from (fun hmem => (show a ∉ ((Wff.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact (show a ∉ (((Wff.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin)))).fv).erase d from (fun hmem => (show a ∉ ((Wff.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show a ∉ (((syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))).fv) ∪ (((Wff.classMem (.cv c) (syn_cfin))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show a ∉ (((Wff.objMem d k)).fv) ∪ (((syn_wss (.cv c) (.cv d))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Wff.objMem d k)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show a ∉ ({d, k} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show a ≠ d from (by exact fresh_a_ne_d)), (show a ≠ k from (by exact fresh_a_ne_k))⟩)))) (show a ∉ ((syn_wss (.cv c) (.cv d))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss]; exact (show a ∉ (((Class.cv c)).fv) ∪ (((Class.cv d)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ c from (by exact fresh_a_ne_c)))))) (show a ∉ ((Class.cv d)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({d} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ d from (by exact fresh_a_ne_d)))))))))))))) (show a ∉ ((Wff.classMem (.cv c) (syn_cfin))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show a ∉ (((Class.cv c)).fv) ∪ (((syn_cfin)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ c from (by exact fresh_a_ne_c)))))) (show a ∉ ((syn_cfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (Finset.mem_of_mem_erase hmem))))) (Finset.mem_of_mem_erase hmem)))))))))) (by exact (show b ∉ ((syn_wa (.classMem (.cv k) (syn_cnnc)) (.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show b ∉ (((Wff.classMem (.cv k) (syn_cnnc))).fv) ∪ (((Wff.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin)))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Wff.classMem (.cv k) (syn_cnnc))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ (((Class.cv k)).fv) ∪ (((syn_cnnc)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv k)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({k} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ k from (by exact fresh_b_ne_k)))))) (show b ∉ ((syn_cnnc)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show b ∉ ((Wff.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin)))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact (show b ∉ (((Wff.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin))))).fv).erase c from (fun hmem => (show b ∉ ((Wff.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact (show b ∉ (((Wff.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin)))).fv).erase d from (fun hmem => (show b ∉ ((Wff.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show b ∉ (((syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))).fv) ∪ (((Wff.classMem (.cv c) (syn_cfin))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show b ∉ (((Wff.objMem d k)).fv) ∪ (((syn_wss (.cv c) (.cv d))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Wff.objMem d k)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show b ∉ ({d, k} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show b ≠ d from (by exact fresh_b_ne_d)), (show b ≠ k from (by exact fresh_b_ne_k))⟩)))) (show b ∉ ((syn_wss (.cv c) (.cv d))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss]; exact (show b ∉ (((Class.cv c)).fv) ∪ (((Class.cv d)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ c from (by exact fresh_b_ne_c)))))) (show b ∉ ((Class.cv d)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({d} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ d from (by exact fresh_b_ne_d)))))))))))))) (show b ∉ ((Wff.classMem (.cv c) (syn_cfin))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ (((Class.cv c)).fv) ∪ (((syn_cfin)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ c from (by exact fresh_b_ne_c)))))) (show b ∉ ((syn_cfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (Finset.mem_of_mem_erase hmem))))) (Finset.mem_of_mem_erase hmem)))))))))) p0182
  have p0184 :=
    @g_ex (.classMem (.cv k) (syn_cnnc)) (.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin))))) (.all a (.all b (.imp (syn_wa (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))))) p0183
  have p0185_e04_recanon : Nominal.NPrf (.imp (.classEq (.cv m) (.cv n)) (syn_wb (.all a (.all b (.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))))) (.all a (.all b (.imp (syn_wa (.objMem b n) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wa syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_cfin syn_cuni syn_wex syn_cnnc syn_cint
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0100
  have p0185 :=
    @g_finds (.all a (.all b (.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))))) (.all a (.all b (.imp (syn_wa (.classEq (.cv b) (syn_c0)) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))))) (.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin))))) (.all a (.all b (.imp (syn_wa (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))))) (.all a (.all b (.imp (syn_wa (.objMem b n) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))))) m k (.cv n) (by exact (show m ∉ ((Class.cv n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({n} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ n from (by exact fresh_m_ne_n))))))) (by exact (show m ∉ ((Wff.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin)))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact (show m ∉ (((Wff.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin))))).fv).erase c from (fun hmem => (show m ∉ ((Wff.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact (show m ∉ (((Wff.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin)))).fv).erase d from (fun hmem => (show m ∉ ((Wff.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show m ∉ (((syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))).fv) ∪ (((Wff.classMem (.cv c) (syn_cfin))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show m ∉ (((Wff.objMem d k)).fv) ∪ (((syn_wss (.cv c) (.cv d))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Wff.objMem d k)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show m ∉ ({d, k} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show m ≠ d from (by exact fresh_m_ne_d)), (show m ≠ k from (by exact fresh_m_ne_k))⟩)))) (show m ∉ ((syn_wss (.cv c) (.cv d))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss]; exact (show m ∉ (((Class.cv c)).fv) ∪ (((Class.cv d)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ c from (by exact fresh_m_ne_c)))))) (show m ∉ ((Class.cv d)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({d} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ d from (by exact fresh_m_ne_d)))))))))))))) (show m ∉ ((Wff.classMem (.cv c) (syn_cfin))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show m ∉ (((Class.cv c)).fv) ∪ (((syn_cfin)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ c from (by exact fresh_m_ne_c)))))) (show m ∉ ((syn_cfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (Finset.mem_of_mem_erase hmem))))) (Finset.mem_of_mem_erase hmem)))))) (by exact (show k ∉ ((Wff.all a (.all b (.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin)))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact (show k ∉ (((Wff.all b (.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))))).fv).erase a from (fun hmem => (show k ∉ ((Wff.all b (.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact (show k ∉ (((Wff.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin)))).fv).erase b from (fun hmem => (show k ∉ ((Wff.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show k ∉ (((syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b)))).fv) ∪ (((Wff.classMem (.cv a) (syn_cfin))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show k ∉ (((Wff.objMem b m)).fv) ∪ (((syn_wss (.cv a) (.cv b))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((Wff.objMem b m)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show k ∉ ({b, m} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show k ≠ b from (by exact fresh_k_ne_b)), (show k ≠ m from (by exact fresh_k_ne_m))⟩)))) (show k ∉ ((syn_wss (.cv a) (.cv b))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss]; exact (show k ∉ (((Class.cv a)).fv) ∪ (((Class.cv b)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show k ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show k ≠ a from (by exact fresh_k_ne_a)))))) (show k ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show k ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show k ≠ b from (by exact fresh_k_ne_b)))))))))))))) (show k ∉ ((Wff.classMem (.cv a) (syn_cfin))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show k ∉ (((Class.cv a)).fv) ∪ (((syn_cfin)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show k ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show k ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show k ≠ a from (by exact fresh_k_ne_a)))))) (show k ∉ ((syn_cfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin]; exact (show k ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (Finset.mem_of_mem_erase hmem))))) (Finset.mem_of_mem_erase hmem)))))) (by exact (show m ∉ ((Wff.all a (.all b (.imp (syn_wa (.classEq (.cv b) (syn_c0)) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin)))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact (show m ∉ (((Wff.all b (.imp (syn_wa (.classEq (.cv b) (syn_c0)) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))))).fv).erase a from (fun hmem => (show m ∉ ((Wff.all b (.imp (syn_wa (.classEq (.cv b) (syn_c0)) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact (show m ∉ (((Wff.imp (syn_wa (.classEq (.cv b) (syn_c0)) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin)))).fv).erase b from (fun hmem => (show m ∉ ((Wff.imp (syn_wa (.classEq (.cv b) (syn_c0)) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show m ∉ (((syn_wa (.classEq (.cv b) (syn_c0)) (syn_wss (.cv a) (.cv b)))).fv) ∪ (((Wff.classMem (.cv a) (syn_cfin))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_wa (.classEq (.cv b) (syn_c0)) (syn_wss (.cv a) (.cv b)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show m ∉ (((Wff.classEq (.cv b) (syn_c0))).fv) ∪ (((syn_wss (.cv a) (.cv b))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Wff.classEq (.cv b) (syn_c0))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show m ∉ (((Class.cv b)).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ b from (by exact fresh_m_ne_b)))))) (show m ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show m ∉ ((syn_wss (.cv a) (.cv b))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss]; exact (show m ∉ (((Class.cv a)).fv) ∪ (((Class.cv b)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ a from (by exact fresh_m_ne_a)))))) (show m ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ b from (by exact fresh_m_ne_b)))))))))))))) (show m ∉ ((Wff.classMem (.cv a) (syn_cfin))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show m ∉ (((Class.cv a)).fv) ∪ (((syn_cfin)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ a from (by exact fresh_m_ne_a)))))) (show m ∉ ((syn_cfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (Finset.mem_of_mem_erase hmem))))) (Finset.mem_of_mem_erase hmem)))))) (by exact (show m ∉ ((Wff.all a (.all b (.imp (syn_wa (.objMem b n) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin)))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact (show m ∉ (((Wff.all b (.imp (syn_wa (.objMem b n) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))))).fv).erase a from (fun hmem => (show m ∉ ((Wff.all b (.imp (syn_wa (.objMem b n) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact (show m ∉ (((Wff.imp (syn_wa (.objMem b n) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin)))).fv).erase b from (fun hmem => (show m ∉ ((Wff.imp (syn_wa (.objMem b n) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show m ∉ (((syn_wa (.objMem b n) (syn_wss (.cv a) (.cv b)))).fv) ∪ (((Wff.classMem (.cv a) (syn_cfin))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_wa (.objMem b n) (syn_wss (.cv a) (.cv b)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show m ∉ (((Wff.objMem b n)).fv) ∪ (((syn_wss (.cv a) (.cv b))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Wff.objMem b n)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]; exact (show m ∉ ({b, n} : Finset Var) from (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨(show m ≠ b from (by exact fresh_m_ne_b)), (show m ≠ n from (by exact fresh_m_ne_n))⟩)))) (show m ∉ ((syn_wss (.cv a) (.cv b))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss]; exact (show m ∉ (((Class.cv a)).fv) ∪ (((Class.cv b)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ a from (by exact fresh_m_ne_a)))))) (show m ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ b from (by exact fresh_m_ne_b)))))))))))))) (show m ∉ ((Wff.classMem (.cv a) (syn_cfin))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show m ∉ (((Class.cv a)).fv) ∪ (((syn_cfin)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ a from (by exact fresh_m_ne_a)))))) (show m ∉ ((syn_cfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (Finset.mem_of_mem_erase hmem))))) (Finset.mem_of_mem_erase hmem)))))) (by exact (show m ∉ ((Wff.all a (.all b (.imp (syn_wa (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin)))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact (show m ∉ (((Wff.all b (.imp (syn_wa (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))))).fv).erase a from (fun hmem => (show m ∉ ((Wff.all b (.imp (syn_wa (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_all]; exact (show m ∉ (((Wff.imp (syn_wa (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin)))).fv).erase b from (fun hmem => (show m ∉ ((Wff.imp (syn_wa (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show m ∉ (((syn_wa (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (syn_wss (.cv a) (.cv b)))).fv) ∪ (((Wff.classMem (.cv a) (syn_cfin))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((syn_wa (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (syn_wss (.cv a) (.cv b)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show m ∉ (((Wff.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c)))).fv) ∪ (((syn_wss (.cv a) (.cv b))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Wff.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show m ∉ (((Class.cv b)).fv) ∪ (((syn_cplc (.cv k) (syn_c1c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ b from (by exact fresh_m_ne_b)))))) (show m ∉ ((syn_cplc (.cv k) (syn_c1c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show m ∉ (((Class.cv k)).fv) ∪ (((syn_c1c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Class.cv k)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({k} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ k from (by exact fresh_m_ne_k)))))) (show m ∉ ((syn_c1c)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (show m ∉ ((syn_wss (.cv a) (.cv b))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss]; exact (show m ∉ (((Class.cv a)).fv) ∪ (((Class.cv b)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ a from (by exact fresh_m_ne_a)))))) (show m ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ b from (by exact fresh_m_ne_b)))))))))))))) (show m ∉ ((Wff.classMem (.cv a) (syn_cfin))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show m ∉ (((Class.cv a)).fv) ∪ (((syn_cfin)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show m ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show m ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show m ≠ a from (by exact fresh_m_ne_a)))))) (show m ∉ ((syn_cfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin]; exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))))))) (Finset.mem_of_mem_erase hmem))))) (Finset.mem_of_mem_erase hmem)))))) (show m ≠ k from (by exact fresh_m_ne_k)) p0070 p0079 p0092 p0096 p0185_e04_recanon p0107 p0184
  have p0186 :=
    @g_n_19_21bbi (.classMem (.cv n) (syn_cnnc)) (.imp (syn_wa (.objMem b n) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))) a b p0185
  have p0187 :=
    @g_exp3a (.classMem (.cv n) (syn_cnnc)) (.objMem b n) (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin)) p0186
  have p0188 :=
    @g_rexlimiv (.objMem b n) (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin))) n (syn_cnnc) (by exact (show n ∉ ((Wff.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show n ∉ (((syn_wss (.cv a) (.cv b))).fv) ∪ (((Wff.classMem (.cv a) (syn_cfin))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((syn_wss (.cv a) (.cv b))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss]; exact (show n ∉ (((Class.cv a)).fv) ∪ (((Class.cv b)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show n ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show n ≠ a from (by exact fresh_n_ne_a)))))) (show n ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show n ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show n ≠ b from (by exact fresh_n_ne_b)))))))))) (show n ∉ ((Wff.classMem (.cv a) (syn_cfin))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show n ∉ (((Class.cv a)).fv) ∪ (((syn_cfin)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show n ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show n ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show n ≠ a from (by exact fresh_n_ne_a)))))) (show n ∉ ((syn_cfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin]; exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) p0187
  have p0189_e00_recanon : Nominal.NPrf (syn_wb (.classMem (.cv b) (syn_cfin)) (syn_wrex n (syn_cnnc) (.objMem b n))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cfin syn_cuni syn_wex syn_wa syn_cnnc syn_cint syn_wrex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
      p0006
  have p0189 :=
    @g_sylbi (.classMem (.cv b) (syn_cfin)) (syn_wrex n (syn_cnnc) (.objMem b n)) (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin))) p0189_e00_recanon p0188
  have p0190 :=
    @g_vtoclga (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin))) (.imp (syn_wss (.cv a) B) (.classMem (.cv a) (syn_cfin))) b B (syn_cfin) (by exact (show b ∉ (B).fv from (by exact fresh_b_not_B))) (by exact (show b ∉ ((syn_cfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))) (by exact (show b ∉ ((Wff.imp (syn_wss (.cv a) B) (.classMem (.cv a) (syn_cfin)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show b ∉ (((syn_wss (.cv a) B)).fv) ∪ (((Wff.classMem (.cv a) (syn_cfin))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_wss (.cv a) B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss]; exact (show b ∉ (((Class.cv a)).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ a from (by exact fresh_b_ne_a)))))) (show b ∉ (B).fv from (by exact fresh_b_not_B)))))) (show b ∉ ((Wff.classMem (.cv a) (syn_cfin))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show b ∉ (((Class.cv a)).fv) ∪ (((syn_cfin)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ a from (by exact fresh_b_ne_a)))))) (show b ∉ ((syn_cfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))) p0005 p0189
  have p0191 :=
    @g_vtoclg (.imp (.classMem B (syn_cfin)) (.imp (syn_wss (.cv a) B) (.classMem (.cv a) (syn_cfin)))) (.imp (.classMem B (syn_cfin)) (.imp (syn_wss A B) (.classMem A (syn_cfin)))) a A V (by exact (show a ∉ (A).fv from (by exact fresh_a_not_A))) (by exact (show a ∉ ((Wff.imp (.classMem B (syn_cfin)) (.imp (syn_wss A B) (.classMem A (syn_cfin))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show a ∉ (((Wff.classMem B (syn_cfin))).fv) ∪ (((Wff.imp (syn_wss A B) (.classMem A (syn_cfin)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Wff.classMem B (syn_cfin))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show a ∉ ((B).fv) ∪ (((syn_cfin)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (B).fv from (by exact fresh_a_not_B)) (show a ∉ ((syn_cfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show a ∉ ((Wff.imp (syn_wss A B) (.classMem A (syn_cfin)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_imp]; exact (show a ∉ (((syn_wss A B)).fv) ∪ (((Wff.classMem A (syn_cfin))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((syn_wss A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss]; exact (show a ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (A).fv from (by exact fresh_a_not_A)) (show a ∉ (B).fv from (by exact fresh_a_not_B)))))) (show a ∉ ((Wff.classMem A (syn_cfin))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact (show a ∉ ((A).fv) ∪ (((syn_cfin)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (A).fv from (by exact fresh_a_not_A)) (show a ∉ ((syn_cfin)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem))))))))))))))))) p0003 p0190
  have p0192 :=
    @g_n_3imp (.classMem A V) (.classMem B (syn_cfin)) (syn_wss A B) (.classMem A (syn_cfin)) p0191
  exact p0192



#print axioms g_ssfin

end NFChoice.DirectNominalPrf.WPPReplay
