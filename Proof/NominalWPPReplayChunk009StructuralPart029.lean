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
import NominalWPPReplayChunk009StructuralPart028


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

noncomputable def g_addcass
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.classEq (syn_cplc (syn_cplc A B) C) (syn_cplc A (syn_cplc B C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  let a : Var := freshVar proofSupport 1
  let b : Var := freshVar proofSupport 2
  let d : Var := freshVar proofSupport 3
  let c : Var := freshVar proofSupport 4
  let e : Var := freshVar proofSupport 5
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
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_C : a ∉ C.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_not_C : b ∉ C.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_d : d ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_not_C : d ∉ C.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_c : c ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_c_not_A : c ∉ A.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_c_not_B : c ∉ B.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_c_not_C : c ∉ C.fv := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (h))
  have fresh_e : e ∉ proofSupport := by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_e_not_A : e ∉ A.fv := by
    intro h
    exact fresh_e (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_e_not_B : e ∉ B.fv := by
    intro h
    exact fresh_e (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_e_not_C : e ∉ C.fv := by
    intro h
    exact fresh_e (Finset.mem_union_right _ (h))
  have fresh_x_ne_a : x ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_x : a ≠ x :=
    Ne.symm fresh_x_ne_a
  have fresh_x_ne_b : x ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_b_ne_x : b ≠ x :=
    Ne.symm fresh_x_ne_b
  have fresh_x_ne_d : x ≠ d := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_d_ne_x : d ≠ x :=
    Ne.symm fresh_x_ne_d
  have fresh_x_ne_c : x ≠ c := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_c_ne_x : c ≠ x :=
    Ne.symm fresh_x_ne_c
  have fresh_x_ne_e : x ≠ e := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_e_ne_x : e ≠ x :=
    Ne.symm fresh_x_ne_e
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have fresh_a_ne_d : a ≠ d := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_d_ne_a : d ≠ a :=
    Ne.symm fresh_a_ne_d
  have fresh_a_ne_c : a ≠ c := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_c_ne_a : c ≠ a :=
    Ne.symm fresh_a_ne_c
  have fresh_a_ne_e : a ≠ e := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_e_ne_a : e ≠ a :=
    Ne.symm fresh_a_ne_e
  have fresh_b_ne_d : b ≠ d := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_d_ne_b : d ≠ b :=
    Ne.symm fresh_b_ne_d
  have fresh_b_ne_c : b ≠ c := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_c_ne_b : c ≠ b :=
    Ne.symm fresh_b_ne_c
  have fresh_b_ne_e : b ≠ e := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_e_ne_b : e ≠ b :=
    Ne.symm fresh_b_ne_e
  have fresh_d_ne_c : d ≠ c := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_c_ne_d : c ≠ d :=
    Ne.symm fresh_d_ne_c
  have fresh_d_ne_e : d ≠ e := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_e_ne_d : e ≠ d :=
    Ne.symm fresh_d_ne_e
  have fresh_c_ne_e : c ≠ e := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_e_ne_c : e ≠ c :=
    Ne.symm fresh_c_ne_e
  have p0000 :=
    @g_ancom (.classEq (syn_cin (.cv a) (.cv c)) (syn_c0)) (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
  have p0001 :=
    @g_anbi2i (syn_wa (.classEq (syn_cin (.cv a) (.cv c)) (syn_c0)) (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))) (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (syn_cin (.cv a) (.cv c)) (syn_c0))) (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) p0000
  have p0002 :=
    @g_an12 (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (syn_cin (.cv a) (.cv c)) (syn_c0))
  have p0003 :=
    @g_bitri (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (syn_wa (.classEq (syn_cin (.cv a) (.cv c)) (syn_c0)) (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)))) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (syn_cin (.cv a) (.cv c)) (syn_c0)))) (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (syn_cin (.cv a) (.cv c)) (syn_c0)))) p0001 p0002
  have p0004 :=
    @g_indir (.cv a) (.cv b) (.cv c)
  have p0005 :=
    @g_eqeq1i (syn_cin (syn_cun (.cv a) (.cv b)) (.cv c)) (syn_cun (syn_cin (.cv a) (.cv c)) (syn_cin (.cv b) (.cv c))) (syn_c0) p0004
  have p0006 :=
    @g_un00 (syn_cin (.cv a) (.cv c)) (syn_cin (.cv b) (.cv c))
  have p0007 :=
    @g_bitr4i (.classEq (syn_cin (syn_cun (.cv a) (.cv b)) (.cv c)) (syn_c0)) (.classEq (syn_cun (syn_cin (.cv a) (.cv c)) (syn_cin (.cv b) (.cv c))) (syn_c0)) (syn_wa (.classEq (syn_cin (.cv a) (.cv c)) (syn_c0)) (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))) p0005 p0006
  have p0008 :=
    @g_anbi2i (.classEq (syn_cin (syn_cun (.cv a) (.cv b)) (.cv c)) (syn_c0)) (syn_wa (.classEq (syn_cin (.cv a) (.cv c)) (syn_c0)) (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))) (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) p0007
  have p0009 :=
    @g_indi (.cv a) (.cv b) (.cv c)
  have p0010 :=
    @g_eqeq1i (syn_cin (.cv a) (syn_cun (.cv b) (.cv c))) (syn_cun (syn_cin (.cv a) (.cv b)) (syn_cin (.cv a) (.cv c))) (syn_c0) p0009
  have p0011 :=
    @g_un00 (syn_cin (.cv a) (.cv b)) (syn_cin (.cv a) (.cv c))
  have p0012 :=
    @g_bitr4i (.classEq (syn_cin (.cv a) (syn_cun (.cv b) (.cv c))) (syn_c0)) (.classEq (syn_cun (syn_cin (.cv a) (.cv b)) (syn_cin (.cv a) (.cv c))) (syn_c0)) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (syn_cin (.cv a) (.cv c)) (syn_c0))) p0010 p0011
  have p0013 :=
    @g_anbi2i (.classEq (syn_cin (.cv a) (syn_cun (.cv b) (.cv c))) (syn_c0)) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (syn_cin (.cv a) (.cv c)) (syn_c0))) (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) p0012
  have p0014 :=
    @g_n_3bitr4i (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (syn_wa (.classEq (syn_cin (.cv a) (.cv c)) (syn_c0)) (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)))) (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (syn_cin (.cv a) (.cv c)) (syn_c0)))) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (syn_cin (syn_cun (.cv a) (.cv b)) (.cv c)) (syn_c0))) (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (syn_cin (.cv a) (syn_cun (.cv b) (.cv c))) (syn_c0))) p0003 p0008 p0013
  have p0015 :=
    @g_unass (.cv a) (.cv b) (.cv c)
  have p0016 :=
    @g_eqeq2i (syn_cun (syn_cun (.cv a) (.cv b)) (.cv c)) (syn_cun (.cv a) (syn_cun (.cv b) (.cv c))) (.cv x) p0015
  have p0017 :=
    @g_anbi12i (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (syn_cin (syn_cun (.cv a) (.cv b)) (.cv c)) (syn_c0))) (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (syn_cin (.cv a) (syn_cun (.cv b) (.cv c))) (syn_c0))) (.classEq (.cv x) (syn_cun (syn_cun (.cv a) (.cv b)) (.cv c))) (.classEq (.cv x) (syn_cun (.cv a) (syn_cun (.cv b) (.cv c)))) p0014 p0016
  have p0018 :=
    @g_anass (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (syn_cin (syn_cun (.cv a) (.cv b)) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (syn_cun (.cv a) (.cv b)) (.cv c)))
  have p0019 :=
    @g_anass (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (syn_cin (.cv a) (syn_cun (.cv b) (.cv c))) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (syn_cun (.cv b) (.cv c))))
  have p0020 :=
    @g_n_3bitr3i (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (syn_cin (syn_cun (.cv a) (.cv b)) (.cv c)) (syn_c0))) (.classEq (.cv x) (syn_cun (syn_cun (.cv a) (.cv b)) (.cv c)))) (syn_wa (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (syn_cin (.cv a) (syn_cun (.cv b) (.cv c))) (syn_c0))) (.classEq (.cv x) (syn_cun (.cv a) (syn_cun (.cv b) (.cv c))))) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (syn_wa (.classEq (syn_cin (syn_cun (.cv a) (.cv b)) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (syn_cun (.cv a) (.cv b)) (.cv c))))) (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (syn_wa (.classEq (syn_cin (.cv a) (syn_cun (.cv b) (.cv c))) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (syn_cun (.cv b) (.cv c)))))) p0017 p0018 p0019
  have p0021 :=
    @g_anass (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b))) (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))
  have p0022 :=
    @g_an12 (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b))) (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))
  have p0023 :=
    @g_bitri (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (syn_wa (.classEq (.cv d) (syn_cun (.cv a) (.cv b))) (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))) (syn_wa (.classEq (.cv d) (syn_cun (.cv a) (.cv b))) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))) p0021 p0022
  have p0024 :=
    @g_exbii (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))) (syn_wa (.classEq (.cv d) (syn_cun (.cv a) (.cv b))) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))) d p0023
  have p0025 :=
    @g_vex a
  have p0026 :=
    @g_vex b
  have p0027 :=
    @g_unex (.cv a) (.cv b) p0025 p0026
  have p0028 :=
    @g_ineq1 (.cv d) (syn_cun (.cv a) (.cv b)) (.cv c)
  have p0029 :=
    @g_eqeq1d (.classEq (.cv d) (syn_cun (.cv a) (.cv b))) (syn_cin (.cv d) (.cv c)) (syn_cin (syn_cun (.cv a) (.cv b)) (.cv c)) (syn_c0) p0028
  have p0030 :=
    @g_uneq1 (.cv d) (syn_cun (.cv a) (.cv b)) (.cv c)
  have p0031 :=
    @g_eqeq2d (.classEq (.cv d) (syn_cun (.cv a) (.cv b))) (syn_cun (.cv d) (.cv c)) (syn_cun (syn_cun (.cv a) (.cv b)) (.cv c)) (.cv x) p0030
  have p0032 :=
    @g_anbi12d (.classEq (.cv d) (syn_cun (.cv a) (.cv b))) (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (syn_cin (syn_cun (.cv a) (.cv b)) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c))) (.classEq (.cv x) (syn_cun (syn_cun (.cv a) (.cv b)) (.cv c))) p0029 p0031
  have p0033 :=
    @g_anbi2d (.classEq (.cv d) (syn_cun (.cv a) (.cv b))) (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))) (syn_wa (.classEq (syn_cin (syn_cun (.cv a) (.cv b)) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (syn_cun (.cv a) (.cv b)) (.cv c)))) (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) p0032
  have p0034 :=
    @g_ceqsexv (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (syn_wa (.classEq (syn_cin (syn_cun (.cv a) (.cv b)) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (syn_cun (.cv a) (.cv b)) (.cv c))))) d (syn_cun (.cv a) (.cv b)) (by exact (show d ∉ ((syn_cun (.cv a) (.cv b))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show d ∉ (((Class.cv a)).fv) ∪ (((Class.cv b)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show d ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ a from (by exact fresh_d_ne_a)))))) (show d ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ b from (by exact fresh_d_ne_b))))))))))) (by exact (show d ∉ ((syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (syn_wa (.classEq (syn_cin (syn_cun (.cv a) (.cv b)) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (syn_cun (.cv a) (.cv b)) (.cv c)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show d ∉ (((Wff.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))).fv) ∪ (((syn_wa (.classEq (syn_cin (syn_cun (.cv a) (.cv b)) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (syn_cun (.cv a) (.cv b)) (.cv c))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show d ∉ ((Wff.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show d ∉ (((syn_cin (.cv a) (.cv b))).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show d ∉ ((syn_cin (.cv a) (.cv b))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show d ∉ (((Class.cv a)).fv) ∪ (((Class.cv b)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show d ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ a from (by exact fresh_d_ne_a)))))) (show d ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ b from (by exact fresh_d_ne_b)))))))))) (show d ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show d ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show d ∉ ((syn_wa (.classEq (syn_cin (syn_cun (.cv a) (.cv b)) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (syn_cun (.cv a) (.cv b)) (.cv c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show d ∉ (((Wff.classEq (syn_cin (syn_cun (.cv a) (.cv b)) (.cv c)) (syn_c0))).fv) ∪ (((Wff.classEq (.cv x) (syn_cun (syn_cun (.cv a) (.cv b)) (.cv c)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show d ∉ ((Wff.classEq (syn_cin (syn_cun (.cv a) (.cv b)) (.cv c)) (syn_c0))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show d ∉ (((syn_cin (syn_cun (.cv a) (.cv b)) (.cv c))).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show d ∉ ((syn_cin (syn_cun (.cv a) (.cv b)) (.cv c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show d ∉ (((syn_cun (.cv a) (.cv b))).fv) ∪ (((Class.cv c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show d ∉ ((syn_cun (.cv a) (.cv b))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show d ∉ (((Class.cv a)).fv) ∪ (((Class.cv b)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show d ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ a from (by exact fresh_d_ne_a)))))) (show d ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ b from (by exact fresh_d_ne_b)))))))))) (show d ∉ ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ c from (by exact fresh_d_ne_c)))))))))) (show d ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show d ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show d ∉ ((Wff.classEq (.cv x) (syn_cun (syn_cun (.cv a) (.cv b)) (.cv c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show d ∉ (((Class.cv x)).fv) ∪ (((syn_cun (syn_cun (.cv a) (.cv b)) (.cv c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show d ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ x from (by exact fresh_d_ne_x)))))) (show d ∉ ((syn_cun (syn_cun (.cv a) (.cv b)) (.cv c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show d ∉ (((syn_cun (.cv a) (.cv b))).fv) ∪ (((Class.cv c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show d ∉ ((syn_cun (.cv a) (.cv b))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show d ∉ (((Class.cv a)).fv) ∪ (((Class.cv b)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show d ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ a from (by exact fresh_d_ne_a)))))) (show d ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ b from (by exact fresh_d_ne_b)))))))))) (show d ∉ ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ c from (by exact fresh_d_ne_c))))))))))))))))))))))) p0027 p0033
  have p0035 :=
    @g_bitri (syn_wex d (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))) (syn_wex d (syn_wa (.classEq (.cv d) (syn_cun (.cv a) (.cv b))) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (syn_wa (.classEq (syn_cin (syn_cun (.cv a) (.cv b)) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (syn_cun (.cv a) (.cv b)) (.cv c))))) p0024 p0034
  have p0036 :=
    @g_anass (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv e) (syn_cun (.cv b) (.cv c))) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))
  have p0037 :=
    @g_an12 (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv e) (syn_cun (.cv b) (.cv c))) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))
  have p0038 :=
    @g_bitri (syn_wa (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv e) (syn_cun (.cv b) (.cv c)))) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))) (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (syn_wa (.classEq (.cv e) (syn_cun (.cv b) (.cv c))) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))))) (syn_wa (.classEq (.cv e) (syn_cun (.cv b) (.cv c))) (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))))) p0036 p0037
  have p0039 :=
    @g_exbii (syn_wa (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv e) (syn_cun (.cv b) (.cv c)))) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))) (syn_wa (.classEq (.cv e) (syn_cun (.cv b) (.cv c))) (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))))) e p0038
  have p0040 :=
    @g_vex c
  have p0041 :=
    @g_unex (.cv b) (.cv c) p0026 p0040
  have p0042 :=
    @g_ineq2 (.cv e) (syn_cun (.cv b) (.cv c)) (.cv a)
  have p0043 :=
    @g_eqeq1d (.classEq (.cv e) (syn_cun (.cv b) (.cv c))) (syn_cin (.cv a) (.cv e)) (syn_cin (.cv a) (syn_cun (.cv b) (.cv c))) (syn_c0) p0042
  have p0044 :=
    @g_uneq2 (.cv e) (syn_cun (.cv b) (.cv c)) (.cv a)
  have p0045 :=
    @g_eqeq2d (.classEq (.cv e) (syn_cun (.cv b) (.cv c))) (syn_cun (.cv a) (.cv e)) (syn_cun (.cv a) (syn_cun (.cv b) (.cv c))) (.cv x) p0044
  have p0046 :=
    @g_anbi12d (.classEq (.cv e) (syn_cun (.cv b) (.cv c))) (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (syn_cin (.cv a) (syn_cun (.cv b) (.cv c))) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e))) (.classEq (.cv x) (syn_cun (.cv a) (syn_cun (.cv b) (.cv c)))) p0043 p0045
  have p0047 :=
    @g_anbi2d (.classEq (.cv e) (syn_cun (.cv b) (.cv c))) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))) (syn_wa (.classEq (syn_cin (.cv a) (syn_cun (.cv b) (.cv c))) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (syn_cun (.cv b) (.cv c))))) (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) p0046
  have p0048 :=
    @g_ceqsexv (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))) (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (syn_wa (.classEq (syn_cin (.cv a) (syn_cun (.cv b) (.cv c))) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (syn_cun (.cv b) (.cv c)))))) e (syn_cun (.cv b) (.cv c)) (by exact (show e ∉ ((syn_cun (.cv b) (.cv c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show e ∉ (((Class.cv b)).fv) ∪ (((Class.cv c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show e ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show e ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show e ≠ b from (by exact fresh_e_ne_b)))))) (show e ∉ ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show e ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show e ≠ c from (by exact fresh_e_ne_c))))))))))) (by exact (show e ∉ ((syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (syn_wa (.classEq (syn_cin (.cv a) (syn_cun (.cv b) (.cv c))) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (syn_cun (.cv b) (.cv c))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show e ∉ (((Wff.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))).fv) ∪ (((syn_wa (.classEq (syn_cin (.cv a) (syn_cun (.cv b) (.cv c))) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (syn_cun (.cv b) (.cv c)))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show e ∉ ((Wff.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show e ∉ (((syn_cin (.cv b) (.cv c))).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show e ∉ ((syn_cin (.cv b) (.cv c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show e ∉ (((Class.cv b)).fv) ∪ (((Class.cv c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show e ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show e ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show e ≠ b from (by exact fresh_e_ne_b)))))) (show e ∉ ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show e ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show e ≠ c from (by exact fresh_e_ne_c)))))))))) (show e ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show e ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show e ∉ ((syn_wa (.classEq (syn_cin (.cv a) (syn_cun (.cv b) (.cv c))) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (syn_cun (.cv b) (.cv c)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show e ∉ (((Wff.classEq (syn_cin (.cv a) (syn_cun (.cv b) (.cv c))) (syn_c0))).fv) ∪ (((Wff.classEq (.cv x) (syn_cun (.cv a) (syn_cun (.cv b) (.cv c))))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show e ∉ ((Wff.classEq (syn_cin (.cv a) (syn_cun (.cv b) (.cv c))) (syn_c0))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show e ∉ (((syn_cin (.cv a) (syn_cun (.cv b) (.cv c)))).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show e ∉ ((syn_cin (.cv a) (syn_cun (.cv b) (.cv c)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show e ∉ (((Class.cv a)).fv) ∪ (((syn_cun (.cv b) (.cv c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show e ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show e ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show e ≠ a from (by exact fresh_e_ne_a)))))) (show e ∉ ((syn_cun (.cv b) (.cv c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show e ∉ (((Class.cv b)).fv) ∪ (((Class.cv c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show e ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show e ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show e ≠ b from (by exact fresh_e_ne_b)))))) (show e ∉ ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show e ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show e ≠ c from (by exact fresh_e_ne_c)))))))))))))) (show e ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show e ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show e ∉ ((Wff.classEq (.cv x) (syn_cun (.cv a) (syn_cun (.cv b) (.cv c))))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show e ∉ (((Class.cv x)).fv) ∪ (((syn_cun (.cv a) (syn_cun (.cv b) (.cv c)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show e ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show e ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show e ≠ x from (by exact fresh_e_ne_x)))))) (show e ∉ ((syn_cun (.cv a) (syn_cun (.cv b) (.cv c)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show e ∉ (((Class.cv a)).fv) ∪ (((syn_cun (.cv b) (.cv c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show e ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show e ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show e ≠ a from (by exact fresh_e_ne_a)))))) (show e ∉ ((syn_cun (.cv b) (.cv c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show e ∉ (((Class.cv b)).fv) ∪ (((Class.cv c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show e ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show e ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show e ≠ b from (by exact fresh_e_ne_b)))))) (show e ∉ ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show e ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show e ≠ c from (by exact fresh_e_ne_c))))))))))))))))))))))))))) p0041 p0047
  have p0049 :=
    @g_bitri (syn_wex e (syn_wa (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv e) (syn_cun (.cv b) (.cv c)))) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))))) (syn_wex e (syn_wa (.classEq (.cv e) (syn_cun (.cv b) (.cv c))) (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))))) (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (syn_wa (.classEq (syn_cin (.cv a) (syn_cun (.cv b) (.cv c))) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (syn_cun (.cv b) (.cv c)))))) p0039 p0048
  have p0050 :=
    @g_n_3bitr4i (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (syn_wa (.classEq (syn_cin (syn_cun (.cv a) (.cv b)) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (syn_cun (.cv a) (.cv b)) (.cv c))))) (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (syn_wa (.classEq (syn_cin (.cv a) (syn_cun (.cv b) (.cv c))) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (syn_cun (.cv b) (.cv c)))))) (syn_wex d (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))) (syn_wex e (syn_wa (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv e) (syn_cun (.cv b) (.cv c)))) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))))) p0020 p0035 p0049
  have p0051 :=
    @g_rexbii (syn_wex d (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))) (syn_wex e (syn_wa (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv e) (syn_cun (.cv b) (.cv c)))) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))))) c C p0050
  have p0052 :=
    @g_n_2rexbii (syn_wrex c C (syn_wex d (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))) (syn_wrex c C (syn_wex e (syn_wa (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv e) (syn_cun (.cv b) (.cv c)))) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))))) a b A B p0051
  have p0053 :=
    @g_eladdc (.cv x) (syn_cplc A B) C d c (by exact (show d ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show d ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show d ≠ x from (by exact fresh_d_ne_x))))))) (by exact (show c ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ x from (by exact fresh_c_ne_x))))))) (by exact (show d ∉ ((syn_cplc A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show d ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show d ∉ (A).fv from (by exact fresh_d_not_A)) (show d ∉ (B).fv from (by exact fresh_d_not_B))))))) (by exact (show c ∉ ((syn_cplc A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show c ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ (A).fv from (by exact fresh_c_not_A)) (show c ∉ (B).fv from (by exact fresh_c_not_B))))))) (by exact (show d ∉ (C).fv from (by exact fresh_d_not_C))) (by exact (show c ∉ (C).fv from (by exact fresh_c_not_C))) (show d ≠ c from (by exact fresh_d_ne_c))
  have p0054 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex d (syn_cplc A B) (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))))
  have p0055 :=
    @g_rexcom4 (syn_wrex b B (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))) a d A (by exact (show d ∉ (A).fv from (by exact fresh_d_not_A))) (show a ≠ d from (by exact fresh_a_ne_d))
  have p0056 :=
    @g_rexcom4 (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))) c d C (by exact (show d ∉ (C).fv from (by exact fresh_d_not_C))) (show c ≠ d from (by exact fresh_c_ne_d))
  have p0057 :=
    @g_r19_42v (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))) c C (by exact (show c ∉ ((syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show c ∉ (((Wff.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))).fv) ∪ (((Wff.classEq (.cv d) (syn_cun (.cv a) (.cv b)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((Wff.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show c ∉ (((syn_cin (.cv a) (.cv b))).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((syn_cin (.cv a) (.cv b))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show c ∉ (((Class.cv a)).fv) ∪ (((Class.cv b)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ a from (by exact fresh_c_ne_a)))))) (show c ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ b from (by exact fresh_c_ne_b)))))))))) (show c ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show c ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show c ∉ ((Wff.classEq (.cv d) (syn_cun (.cv a) (.cv b)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show c ∉ (((Class.cv d)).fv) ∪ (((syn_cun (.cv a) (.cv b))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((Class.cv d)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({d} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ d from (by exact fresh_c_ne_d)))))) (show c ∉ ((syn_cun (.cv a) (.cv b))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show c ∉ (((Class.cv a)).fv) ∪ (((Class.cv b)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ a from (by exact fresh_c_ne_a)))))) (show c ∉ ((Class.cv b)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({b} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ b from (by exact fresh_c_ne_b)))))))))))))))))))
  have p0058 :=
    @g_exbii (syn_wrex c C (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))) (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))) d p0057
  have p0059 :=
    @g_bitri (syn_wrex c C (syn_wex d (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))) (syn_wex d (syn_wrex c C (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))) (syn_wex d (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))) p0056 p0058
  have p0060 :=
    @g_rexbii (syn_wrex c C (syn_wex d (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))) (syn_wex d (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))) b B p0059
  have p0061 :=
    @g_rexcom4 (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))) b d B (by exact (show d ∉ (B).fv from (by exact fresh_d_not_B))) (show b ≠ d from (by exact fresh_b_ne_d))
  have p0062 :=
    @g_bitri (syn_wrex b B (syn_wrex c C (syn_wex d (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))))) (syn_wrex b B (syn_wex d (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))))) (syn_wex d (syn_wrex b B (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))))) p0060 p0061
  have p0063 :=
    @g_rexbii (syn_wrex b B (syn_wrex c C (syn_wex d (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))))) (syn_wex d (syn_wrex b B (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))))) a A p0062
  have p0064 :=
    @g_r19_41v (syn_wrex b B (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b))))) (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))) a A (by exact (show a ∉ ((syn_wrex c C (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex]; exact (show a ∉ (((C).fv).erase c) ∪ ((((syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))).fv).erase c) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((C).fv).erase c from (fun hmem => (show a ∉ (C).fv from (by exact fresh_a_not_C)) (Finset.mem_of_mem_erase hmem))) (show a ∉ (((syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))).fv).erase c from (fun hmem => (show a ∉ ((syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show a ∉ (((Wff.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))).fv) ∪ (((Wff.classEq (.cv x) (syn_cun (.cv d) (.cv c)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Wff.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show a ∉ (((syn_cin (.cv d) (.cv c))).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((syn_cin (.cv d) (.cv c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show a ∉ (((Class.cv d)).fv) ∪ (((Class.cv c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Class.cv d)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({d} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ d from (by exact fresh_a_ne_d)))))) (show a ∉ ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ c from (by exact fresh_a_ne_c)))))))))) (show a ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show a ∉ ((Wff.classEq (.cv x) (syn_cun (.cv d) (.cv c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show a ∉ (((Class.cv x)).fv) ∪ (((syn_cun (.cv d) (.cv c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ x from (by exact fresh_a_ne_x)))))) (show a ∉ ((syn_cun (.cv d) (.cv c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show a ∉ (((Class.cv d)).fv) ∪ (((Class.cv c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ ((Class.cv d)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({d} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ d from (by exact fresh_a_ne_d)))))) (show a ∉ ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ c from (by exact fresh_a_ne_c)))))))))))))))))) (Finset.mem_of_mem_erase hmem))))))))
  have p0065 :=
    @g_r19_41v (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))) b B (by exact (show b ∉ ((syn_wrex c C (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex]; exact (show b ∉ (((C).fv).erase c) ∪ ((((syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))).fv).erase c) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((C).fv).erase c from (fun hmem => (show b ∉ (C).fv from (by exact fresh_b_not_C)) (Finset.mem_of_mem_erase hmem))) (show b ∉ (((syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))).fv).erase c from (fun hmem => (show b ∉ ((syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show b ∉ (((Wff.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))).fv) ∪ (((Wff.classEq (.cv x) (syn_cun (.cv d) (.cv c)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Wff.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show b ∉ (((syn_cin (.cv d) (.cv c))).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_cin (.cv d) (.cv c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show b ∉ (((Class.cv d)).fv) ∪ (((Class.cv c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv d)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({d} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ d from (by exact fresh_b_ne_d)))))) (show b ∉ ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ c from (by exact fresh_b_ne_c)))))))))) (show b ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show b ∉ ((Wff.classEq (.cv x) (syn_cun (.cv d) (.cv c)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show b ∉ (((Class.cv x)).fv) ∪ (((syn_cun (.cv d) (.cv c))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ x from (by exact fresh_b_ne_x)))))) (show b ∉ ((syn_cun (.cv d) (.cv c))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show b ∉ (((Class.cv d)).fv) ∪ (((Class.cv c)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv d)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({d} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ d from (by exact fresh_b_ne_d)))))) (show b ∉ ((Class.cv c)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({c} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ c from (by exact fresh_b_ne_c)))))))))))))))))) (Finset.mem_of_mem_erase hmem))))))))
  have p0066 :=
    @g_rexbii (syn_wrex b B (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))) (syn_wa (syn_wrex b B (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b))))) (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))) a A p0065
  have p0067 :=
    @g_eladdc (.cv d) A B a b (by exact (show a ∉ ((Class.cv d)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({d} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ d from (by exact fresh_a_ne_d))))))) (by exact (show b ∉ ((Class.cv d)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({d} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ d from (by exact fresh_b_ne_d))))))) (by exact (show a ∉ (A).fv from (by exact fresh_a_not_A))) (by exact (show b ∉ (A).fv from (by exact fresh_b_not_A))) (by exact (show a ∉ (B).fv from (by exact fresh_a_not_B))) (by exact (show b ∉ (B).fv from (by exact fresh_b_not_B))) (show a ≠ b from (by exact fresh_a_ne_b))
  have p0068 :=
    @g_anbi1i (.classMem (.cv d) (syn_cplc A B)) (syn_wrex a A (syn_wrex b B (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))))) (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))) p0067
  have p0069 :=
    @g_n_3bitr4ri (syn_wrex a A (syn_wa (syn_wrex b B (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b))))) (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))) (syn_wa (syn_wrex a A (syn_wrex b B (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))))) (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))) (syn_wrex a A (syn_wrex b B (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))))) (syn_wa (.classMem (.cv d) (syn_cplc A B)) (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))) p0064 p0066 p0068
  have p0070 :=
    @g_exbii (syn_wa (.classMem (.cv d) (syn_cplc A B)) (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))) (syn_wrex a A (syn_wrex b B (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))))) d p0069
  have p0071 :=
    @g_n_3bitr4ri (syn_wrex a A (syn_wex d (syn_wrex b B (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))))) (syn_wex d (syn_wrex a A (syn_wrex b B (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))))) (syn_wrex a A (syn_wrex b B (syn_wrex c C (syn_wex d (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))))) (syn_wex d (syn_wa (.classMem (.cv d) (syn_cplc A B)) (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))) p0055 p0063 p0070
  have p0072 :=
    @g_bitri (syn_wrex d (syn_cplc A B) (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))) (syn_wex d (syn_wa (.classMem (.cv d) (syn_cplc A B)) (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))) (syn_wrex a A (syn_wrex b B (syn_wrex c C (syn_wex d (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))))) p0054 p0071
  have p0073 :=
    @g_bitri (.classMem (.cv x) (syn_cplc (syn_cplc A B) C)) (syn_wrex d (syn_cplc A B) (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))) (syn_wrex a A (syn_wrex b B (syn_wrex c C (syn_wex d (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))))) p0053 p0072
  have p0074 :=
    @g_eladdc (.cv x) A (syn_cplc B C) a e (by exact (show a ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show a ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show a ≠ x from (by exact fresh_a_ne_x))))))) (by exact (show e ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show e ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show e ≠ x from (by exact fresh_e_ne_x))))))) (by exact (show a ∉ (A).fv from (by exact fresh_a_not_A))) (by exact (show e ∉ (A).fv from (by exact fresh_e_not_A))) (by exact (show a ∉ ((syn_cplc B C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show a ∉ ((B).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show a ∉ (B).fv from (by exact fresh_a_not_B)) (show a ∉ (C).fv from (by exact fresh_a_not_C))))))) (by exact (show e ∉ ((syn_cplc B C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show e ∉ ((B).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show e ∉ (B).fv from (by exact fresh_e_not_B)) (show e ∉ (C).fv from (by exact fresh_e_not_C))))))) (show a ≠ e from (by exact fresh_a_ne_e))
  have p0075 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex e (syn_cplc B C) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))))))
  have p0076 :=
    @g_rexcom4 (syn_wrex c C (syn_wa (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv e) (syn_cun (.cv b) (.cv c)))) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))))) b e B (by exact (show e ∉ (B).fv from (by exact fresh_e_not_B))) (show b ≠ e from (by exact fresh_b_ne_e))
  have p0077 :=
    @g_rexcom4 (syn_wa (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv e) (syn_cun (.cv b) (.cv c)))) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))) c e C (by exact (show e ∉ (C).fv from (by exact fresh_e_not_C))) (show c ≠ e from (by exact fresh_c_ne_e))
  have p0078 :=
    @g_rexbii (syn_wrex c C (syn_wex e (syn_wa (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv e) (syn_cun (.cv b) (.cv c)))) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))))) (syn_wex e (syn_wrex c C (syn_wa (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv e) (syn_cun (.cv b) (.cv c)))) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))))) b B p0077
  have p0079 :=
    @g_r19_41v (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv e) (syn_cun (.cv b) (.cv c))))) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))) b B (by exact (show b ∉ ((syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show b ∉ (((Wff.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))).fv) ∪ (((Wff.classEq (.cv x) (syn_cun (.cv a) (.cv e)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Wff.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show b ∉ (((syn_cin (.cv a) (.cv e))).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((syn_cin (.cv a) (.cv e))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show b ∉ (((Class.cv a)).fv) ∪ (((Class.cv e)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ a from (by exact fresh_b_ne_a)))))) (show b ∉ ((Class.cv e)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({e} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ e from (by exact fresh_b_ne_e)))))))))) (show b ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show b ∉ ((Wff.classEq (.cv x) (syn_cun (.cv a) (.cv e)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show b ∉ (((Class.cv x)).fv) ∪ (((syn_cun (.cv a) (.cv e))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ x from (by exact fresh_b_ne_x)))))) (show b ∉ ((syn_cun (.cv a) (.cv e))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show b ∉ (((Class.cv a)).fv) ∪ (((Class.cv e)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show b ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ a from (by exact fresh_b_ne_a)))))) (show b ∉ ((Class.cv e)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({e} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ e from (by exact fresh_b_ne_e)))))))))))))))))))
  have p0080 :=
    @g_r19_41v (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv e) (syn_cun (.cv b) (.cv c)))) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))) c C (by exact (show c ∉ ((syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]; exact (show c ∉ (((Wff.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))).fv) ∪ (((Wff.classEq (.cv x) (syn_cun (.cv a) (.cv e)))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((Wff.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show c ∉ (((syn_cin (.cv a) (.cv e))).fv) ∪ (((syn_c0)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((syn_cin (.cv a) (.cv e))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show c ∉ (((Class.cv a)).fv) ∪ (((Class.cv e)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ a from (by exact fresh_c_ne_a)))))) (show c ∉ ((Class.cv e)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({e} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ e from (by exact fresh_c_ne_e)))))))))) (show c ∉ ((syn_c0)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show c ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))))) (show c ∉ ((Wff.classEq (.cv x) (syn_cun (.cv a) (.cv e)))).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact (show c ∉ (((Class.cv x)).fv) ∪ (((syn_cun (.cv a) (.cv e))).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((Class.cv x)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({x} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ x from (by exact fresh_c_ne_x)))))) (show c ∉ ((syn_cun (.cv a) (.cv e))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun]; exact (show c ∉ (((Class.cv a)).fv) ∪ (((Class.cv e)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show c ∉ ((Class.cv a)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({a} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ a from (by exact fresh_c_ne_a)))))) (show c ∉ ((Class.cv e)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({e} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ e from (by exact fresh_c_ne_e)))))))))))))))))))
  have p0081 :=
    @g_rexbii (syn_wrex c C (syn_wa (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv e) (syn_cun (.cv b) (.cv c)))) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))))) (syn_wa (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv e) (syn_cun (.cv b) (.cv c))))) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))) b B p0080
  have p0082 :=
    @g_eladdc (.cv e) B C b c (by exact (show b ∉ ((Class.cv e)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show b ∉ ({e} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show b ≠ e from (by exact fresh_b_ne_e))))))) (by exact (show c ∉ ((Class.cv e)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show c ∉ ({e} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show c ≠ e from (by exact fresh_c_ne_e))))))) (by exact (show b ∉ (B).fv from (by exact fresh_b_not_B))) (by exact (show c ∉ (B).fv from (by exact fresh_c_not_B))) (by exact (show b ∉ (C).fv from (by exact fresh_b_not_C))) (by exact (show c ∉ (C).fv from (by exact fresh_c_not_C))) (show b ≠ c from (by exact fresh_b_ne_c))
  have p0083 :=
    @g_anbi1i (.classMem (.cv e) (syn_cplc B C)) (syn_wrex b B (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv e) (syn_cun (.cv b) (.cv c)))))) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))) p0082
  have p0084 :=
    @g_n_3bitr4ri (syn_wrex b B (syn_wa (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv e) (syn_cun (.cv b) (.cv c))))) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))))) (syn_wa (syn_wrex b B (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv e) (syn_cun (.cv b) (.cv c)))))) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))) (syn_wrex b B (syn_wrex c C (syn_wa (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv e) (syn_cun (.cv b) (.cv c)))) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))))) (syn_wa (.classMem (.cv e) (syn_cplc B C)) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))) p0079 p0081 p0083
  have p0085 :=
    @g_exbii (syn_wa (.classMem (.cv e) (syn_cplc B C)) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))) (syn_wrex b B (syn_wrex c C (syn_wa (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv e) (syn_cun (.cv b) (.cv c)))) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))))) e p0084
  have p0086 :=
    @g_n_3bitr4ri (syn_wrex b B (syn_wex e (syn_wrex c C (syn_wa (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv e) (syn_cun (.cv b) (.cv c)))) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))))))) (syn_wex e (syn_wrex b B (syn_wrex c C (syn_wa (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv e) (syn_cun (.cv b) (.cv c)))) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))))))) (syn_wrex b B (syn_wrex c C (syn_wex e (syn_wa (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv e) (syn_cun (.cv b) (.cv c)))) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))))))) (syn_wex e (syn_wa (.classMem (.cv e) (syn_cplc B C)) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))))) p0076 p0078 p0085
  have p0087 :=
    @g_bitri (syn_wrex e (syn_cplc B C) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))) (syn_wex e (syn_wa (.classMem (.cv e) (syn_cplc B C)) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))))) (syn_wrex b B (syn_wrex c C (syn_wex e (syn_wa (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv e) (syn_cun (.cv b) (.cv c)))) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))))))) p0075 p0086
  have p0088 :=
    @g_rexbii (syn_wrex e (syn_cplc B C) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))) (syn_wrex b B (syn_wrex c C (syn_wex e (syn_wa (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv e) (syn_cun (.cv b) (.cv c)))) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))))))) a A p0087
  have p0089 :=
    @g_bitri (.classMem (.cv x) (syn_cplc A (syn_cplc B C))) (syn_wrex a A (syn_wrex e (syn_cplc B C) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))))) (syn_wrex a A (syn_wrex b B (syn_wrex c C (syn_wex e (syn_wa (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv e) (syn_cun (.cv b) (.cv c)))) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))))))) p0074 p0088
  have p0090 :=
    @g_n_3bitr4i (syn_wrex a A (syn_wrex b B (syn_wrex c C (syn_wex d (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))))) (syn_wrex a A (syn_wrex b B (syn_wrex c C (syn_wex e (syn_wa (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) (.classEq (.cv e) (syn_cun (.cv b) (.cv c)))) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))))))) (.classMem (.cv x) (syn_cplc (syn_cplc A B) C)) (.classMem (.cv x) (syn_cplc A (syn_cplc B C))) p0052 p0073 p0089
  have p0091 :=
    @g_eqriv x (syn_cplc (syn_cplc A B) C) (syn_cplc A (syn_cplc B C)) (by exact (show x ∉ ((syn_cplc (syn_cplc A B) C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ (((syn_cplc A B)).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ ((syn_cplc A B)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ ((A).fv) ∪ ((B).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ (B).fv from (by exact fresh_x_not_B)))))) (show x ∉ (C).fv from (by exact fresh_x_not_C))))))) (by exact (show x ∉ ((syn_cplc A (syn_cplc B C))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ ((A).fv) ∪ (((syn_cplc B C)).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (A).fv from (by exact fresh_x_not_A)) (show x ∉ ((syn_cplc B C)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc]; exact (show x ∉ ((B).fv) ∪ ((C).fv) from (fun hmem => (Finset.mem_union.mp hmem).elim (show x ∉ (B).fv from (by exact fresh_x_not_B)) (show x ∉ (C).fv from (by exact fresh_x_not_C))))))))))) p0090
  exact p0091



#print axioms g_addcass

end NFChoice.DirectNominalPrf.WPPReplay
