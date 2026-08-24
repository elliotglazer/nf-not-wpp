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
import NominalAlphaRepairedBase001049OprabReflected001
import NominalAlphaPrefix050WppNotmem014Data
import NominalAlphaGlobal051ProofData001
import NominalAlphaRelease004Coarse052
import NominalAlphaRelease004Coarse053
import NominalAlphaRelease004Coarse054
import NominalAlphaRelease004Coarse055
import NominalAlphaRelease004Coarse056
import NominalAlphaRelease004Coarse057
import NominalAlphaRelease004Coarse058
import NominalAlphaRelease004Coarse059
import NominalAlphaRelease004Coarse060
import NominalAlphaRelease004Coarse061
import NominalAlphaRelease004Coarse062
import NominalAlphaRelease004Coarse063
import NominalAlphaRelease004Coarse064
import NominalAlphaRelease004Coarse065
import NominalAlphaRelease004Coarse066
import NominalAlphaRelease004Coarse067
import NominalAlphaRelease004Coarse068
import NominalAlphaRelease004Coarse069
import NominalAlphaRelease004Coarse070
import NominalAlphaRelease004Coarse071
import NominalAlphaRelease004Coarse072
import NominalAlphaRelease004Coarse073
import NominalAlphaRelease004Coarse074
import NominalAlphaRelease004Coarse075
import NominalAlphaRelease004Coarse076
import NominalAlphaRelease004Coarse077
import NominalAlphaRelease004Coarse078
import NominalAlphaRelease004Coarse079
import NominalAlphaRelease004Coarse080
import NominalAlphaRelease004Coarse081
import NominalAlphaRelease004Coarse082
import NominalAlphaRelease004Coarse083
import NominalAlphaRelease004Coarse084
import NominalAlphaRelease004Coarse085
import NominalAlphaRelease004Coarse086
import NominalAlphaRelease004Coarse087
import NominalAlphaHygieneV5Probe088
import NominalAlphaRelease004Coarse089
import NominalAlphaRelease004Coarse090
import NominalAlphaHygieneV5Coalesced091B
import NominalAlphaHygieneV5Coalesced092
import NominalAlphaHygieneV5Coalesced093
import NominalAlphaHygieneV5Coalesced094
import NominalAlphaHygieneV5Coalesced095
import NominalAlphaHygieneV5Coalesced096
import NominalAlphaHygieneV5Coalesced097
import NominalNFLiteralBaseFour
import NominalNFLiteralXpViaCompletenessDev003
import NominalNFLiteralRemainingViaCompletenessDev001
import NominalDefinitionLeafHandlersCanonical001
import NominalDefinitionLeafHandlersObjExtCompat001
import NominalRecanonTransportCompat001
import NominalWPPReplayChunk017Compact001Part011

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

noncomputable def g_wppfdpivrangencdlitraw
    (A : Class) (B : Class) (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_B_R : Disjoint B.fv R.fv) (hyp_wppfdpivrangencdlitraw_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_wppfdpivrangencdlitraw_2 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_wppfdpivrangencdlitraw_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wwpp) (syn_wbr (syn_cnc (syn_cfdpivrange2 R A B)) (syn_clec) (syn_cnc (syn_cxp (syn_cxpk B B) (syn_cnnc))))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  let v : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  let k : Var := freshVar proofSupport 2
  let y : Var := freshVar proofSupport 3
  let h : Var := freshVar proofSupport 4
  let t : Var := freshVar proofSupport 5
  let f : Var := freshVar proofSupport 6
  let g : Var := freshVar proofSupport 7
  let z : Var := freshVar proofSupport 8
  have fresh_v : v ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_v_not_B : v ∉ B.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_not_R : v ∉ R.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_k : k ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_k_not_A : k ∉ A.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_k_not_B : k ∉ B.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_k_not_R : k ∉ R.fv := by
    intro h
    exact fresh_k (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_h : h ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_h_not_A : h ∉ A.fv := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_h_not_B : h ∉ B.fv := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_h_not_R : h ∉ R.fv := by
    intro h
    exact fresh_h (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_t_not_R : t ∉ R.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_f : f ∉ proofSupport := by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_f_not_A : f ∉ A.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_f_not_B : f ∉ B.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_f_not_R : f ∉ R.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have fresh_g : g ∉ proofSupport := by
    change freshVar proofSupport 7 ∉ proofSupport
    exact freshVar_not_mem proofSupport 7
  have fresh_g_not_A : g ∉ A.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_g_not_B : g ∉ B.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_g_not_R : g ∉ R.fv := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 8 ∉ proofSupport
    exact freshVar_not_mem proofSupport 8
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_v_ne_u : v ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_v : u ≠ v :=
    Ne.symm fresh_v_ne_u
  have fresh_v_ne_k : v ≠ k := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_k_ne_v : k ≠ v :=
    Ne.symm fresh_v_ne_k
  have fresh_v_ne_y : v ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_y_ne_v : y ≠ v :=
    Ne.symm fresh_v_ne_y
  have fresh_v_ne_h : v ≠ h := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_h_ne_v : h ≠ v :=
    Ne.symm fresh_v_ne_h
  have fresh_v_ne_t : v ≠ t := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_t_ne_v : t ≠ v :=
    Ne.symm fresh_v_ne_t
  have fresh_v_ne_f : v ≠ f := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_f_ne_v : f ≠ v :=
    Ne.symm fresh_v_ne_f
  have fresh_v_ne_g : v ≠ g := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 0) (j := 7) (by decide)
  have fresh_g_ne_v : g ≠ v :=
    Ne.symm fresh_v_ne_g
  have fresh_v_ne_z : v ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 0) (j := 8) (by decide)
  have fresh_z_ne_v : z ≠ v :=
    Ne.symm fresh_v_ne_z
  have fresh_u_ne_k : u ≠ k := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_k_ne_u : k ≠ u :=
    Ne.symm fresh_u_ne_k
  have fresh_u_ne_y : u ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_y_ne_u : y ≠ u :=
    Ne.symm fresh_u_ne_y
  have fresh_u_ne_h : u ≠ h := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_h_ne_u : h ≠ u :=
    Ne.symm fresh_u_ne_h
  have fresh_u_ne_t : u ≠ t := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_t_ne_u : t ≠ u :=
    Ne.symm fresh_u_ne_t
  have fresh_u_ne_f : u ≠ f := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_f_ne_u : f ≠ u :=
    Ne.symm fresh_u_ne_f
  have fresh_u_ne_g : u ≠ g := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 1) (j := 7) (by decide)
  have fresh_g_ne_u : g ≠ u :=
    Ne.symm fresh_u_ne_g
  have fresh_u_ne_z : u ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 1) (j := 8) (by decide)
  have fresh_z_ne_u : z ≠ u :=
    Ne.symm fresh_u_ne_z
  have fresh_k_ne_y : k ≠ y := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_y_ne_k : y ≠ k :=
    Ne.symm fresh_k_ne_y
  have fresh_k_ne_h : k ≠ h := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_h_ne_k : h ≠ k :=
    Ne.symm fresh_k_ne_h
  have fresh_k_ne_t : k ≠ t := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_t_ne_k : t ≠ k :=
    Ne.symm fresh_k_ne_t
  have fresh_k_ne_f : k ≠ f := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_f_ne_k : f ≠ k :=
    Ne.symm fresh_k_ne_f
  have fresh_k_ne_g : k ≠ g := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 2) (j := 7) (by decide)
  have fresh_g_ne_k : g ≠ k :=
    Ne.symm fresh_k_ne_g
  have fresh_k_ne_z : k ≠ z := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 2) (j := 8) (by decide)
  have fresh_z_ne_k : z ≠ k :=
    Ne.symm fresh_k_ne_z
  have fresh_y_ne_h : y ≠ h := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_h_ne_y : h ≠ y :=
    Ne.symm fresh_y_ne_h
  have fresh_y_ne_t : y ≠ t := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_t_ne_y : t ≠ y :=
    Ne.symm fresh_y_ne_t
  have fresh_y_ne_f : y ≠ f := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_f_ne_y : f ≠ y :=
    Ne.symm fresh_y_ne_f
  have fresh_y_ne_g : y ≠ g := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 3) (j := 7) (by decide)
  have fresh_g_ne_y : g ≠ y :=
    Ne.symm fresh_y_ne_g
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 3) (j := 8) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_h_ne_t : h ≠ t := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_t_ne_h : t ≠ h :=
    Ne.symm fresh_h_ne_t
  have fresh_h_ne_f : h ≠ f := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_f_ne_h : f ≠ h :=
    Ne.symm fresh_h_ne_f
  have fresh_h_ne_g : h ≠ g := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 4) (j := 7) (by decide)
  have fresh_g_ne_h : g ≠ h :=
    Ne.symm fresh_h_ne_g
  have fresh_h_ne_z : h ≠ z := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 4) (j := 8) (by decide)
  have fresh_z_ne_h : z ≠ h :=
    Ne.symm fresh_h_ne_z
  have fresh_t_ne_f : t ≠ f := by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_f_ne_t : f ≠ t :=
    Ne.symm fresh_t_ne_f
  have fresh_t_ne_g : t ≠ g := by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 5) (j := 7) (by decide)
  have fresh_g_ne_t : g ≠ t :=
    Ne.symm fresh_t_ne_g
  have fresh_t_ne_z : t ≠ z := by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 5) (j := 8) (by decide)
  have fresh_z_ne_t : z ≠ t :=
    Ne.symm fresh_t_ne_z
  have fresh_f_ne_g : f ≠ g := by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 6) (j := 7) (by decide)
  have fresh_g_ne_f : g ≠ f :=
    Ne.symm fresh_f_ne_g
  have fresh_f_ne_z : f ≠ z := by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 6) (j := 8) (by decide)
  have fresh_z_ne_f : z ≠ f :=
    Ne.symm fresh_f_ne_z
  have fresh_g_ne_z : g ≠ z := by
    change freshVar proofSupport 7 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 7) (j := 8) (by decide)
  have fresh_z_ne_g : z ≠ g :=
    Ne.symm fresh_g_ne_z
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0003 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0004 : Disjoint ((syn_cfdpivmap2 R A B)).fv ((Class.cv v)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show Disjoint ((syn_cfdpivmap2 R A B)).fv ((Class.cv v)).fv from (by rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivmap2, NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (((A).fv) ∪ ((B).fv) ∪ ((R).fv)) (({v} : Finset Var)) from (Finset.disjoint_union_left.mpr ⟨(Finset.disjoint_union_left.mpr ⟨(show Disjoint ((A).fv) (({v} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show v ∉ (A).fv from (by exact fresh_v_not_A)))), (show Disjoint ((B).fv) (({v} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show v ∉ (B).fv from (by exact fresh_v_not_B))))⟩), (show Disjoint ((R).fv) (({v} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show v ∉ (R).fv from (by exact fresh_v_not_R))))⟩))))
  have dv_cache_0005 : Disjoint ((syn_cfdpivmap2 R A B)).fv ((Class.cv u)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show Disjoint ((syn_cfdpivmap2 R A B)).fv ((Class.cv u)).fv from (by rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivmap2, NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (((A).fv) ∪ ((B).fv) ∪ ((R).fv)) (({u} : Finset Var)) from (Finset.disjoint_union_left.mpr ⟨(Finset.disjoint_union_left.mpr ⟨(show Disjoint ((A).fv) (({u} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show u ∉ (A).fv from (by exact fresh_u_not_A)))), (show Disjoint ((B).fv) (({u} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show u ∉ (B).fv from (by exact fresh_u_not_B))))⟩), (show Disjoint ((R).fv) (({u} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show u ∉ (R).fv from (by exact fresh_u_not_R))))⟩))))
  have dv_cache_0006 : y ∉ ((syn_cfdpivmap2 R A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivmap2, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : Disjoint ((Class.cv v)).fv ((Class.cv u)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show Disjoint ((Class.cv v)).fv ((Class.cv u)).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv (v), NFChoice.Compiler.CoreFVSimp.fv_class_cv (u)]; exact (show Disjoint (({v} : Finset Var)) (({u} : Finset Var)) from (Finset.disjoint_singleton_left.mpr (show v ∉ ({u} : Finset Var) from (by simpa only [Finset.mem_singleton] using (show v ≠ u from (by exact fresh_v_ne_u))))))))
  have dv_cache_0008 : y ∉ ((Class.cv v)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((Class.cv u)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : f ∉ ((syn_cfdpivmap2 R A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivmap2, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_A, fresh_f_not_B, fresh_f_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : v ∉ ((syn_cfdpivmap2 R A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivmap2, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, fresh_v_not_B, fresh_v_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : u ∉ ((syn_cfdpivmap2 R A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivmap2, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, fresh_u_not_B, fresh_u_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : f ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show f ≠ v from (by exact fresh_f_ne_v))
  have dv_cache_0014 : f ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show f ≠ u from (by exact fresh_f_ne_u))
  have dv_cache_0015 : f ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show f ≠ y from (by exact fresh_f_ne_y))
  have dv_cache_0016 : v ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show v ≠ u from (by exact fresh_v_ne_u))
  have dv_cache_0017 : v ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show v ≠ y from (by exact fresh_v_ne_y))
  have dv_cache_0018 : u ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show u ≠ y from (by exact fresh_u_ne_y))
  have dv_cache_0019 : z ∉ ((Class.cv v)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : z ∉ ((Class.cv u)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0022 : g ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show g ≠ v from (by exact fresh_g_ne_v))
  have dv_cache_0023 : g ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show g ≠ u from (by exact fresh_g_ne_u))
  have dv_cache_0024 : g ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show g ≠ y from (by exact fresh_g_ne_y))
  have dv_cache_0025 : g ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (show g ≠ z from (by exact fresh_g_ne_z))
  have dv_cache_0026 : v ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (show v ≠ z from (by exact fresh_v_ne_z))
  have dv_cache_0027 : u ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (show u ≠ z from (by exact fresh_u_ne_z))
  have dv_cache_0028 : Disjoint ((syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))).fv ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (show Disjoint ((syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))).fv ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show Disjoint ((((syn_cxp (.cv v) (syn_csn (syn_c0c)))).fv) ∪ (((syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))).fv)) ((∅ : Finset Var)) from (Finset.disjoint_union_left.mpr ⟨(show Disjoint (((syn_cxp (.cv v) (syn_csn (syn_c0c)))).fv) ((∅ : Finset Var)) from (by simp)), (show Disjoint (((syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))).fv) ((∅ : Finset Var)) from (by simp))⟩))))
  have dv_cache_0029 : f ∉ ((syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_v, fresh_f_ne_u, fresh_f_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0030 : g ∉ ((syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_v, fresh_g_ne_u, fresh_g_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0031 : h ∉ ((syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_ne_v, fresh_h_ne_u, fresh_h_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0032 : Disjoint ((syn_cxp (.cv u) (syn_cnnc))).fv ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (show Disjoint ((syn_cxp (.cv u) (syn_cnnc))).fv ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show Disjoint ((((Class.cv u)).fv) ∪ (((syn_cnnc)).fv)) ((∅ : Finset Var)) from (Finset.disjoint_union_left.mpr ⟨(show Disjoint (((Class.cv u)).fv) ((∅ : Finset Var)) from (by simp)), (show Disjoint (((syn_cnnc)).fv) ((∅ : Finset Var)) from (by simp))⟩))))
  have dv_cache_0033 : f ∉ ((syn_cxp (.cv u) (syn_cnnc))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0034 : g ∉ ((syn_cxp (.cv u) (syn_cnnc))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0035 : h ∉ ((syn_cxp (.cv u) (syn_cnnc))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0036 : Disjoint ((syn_cvv)).fv ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact (show Disjoint ((syn_cvv)).fv ((syn_cvv)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv]; exact (show Disjoint ((∅ : Finset Var)) ((∅ : Finset Var)) from (by simp))))
  have dv_cache_0037 : f ≠ g := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036
    exact (show f ≠ g from (by exact fresh_f_ne_g))
  have dv_cache_0038 : f ≠ h := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037
    exact (show f ≠ h from (by exact fresh_f_ne_h))
  have dv_cache_0039 : g ≠ h := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038
    exact (show g ≠ h from (by exact fresh_g_ne_h))
  have dv_cache_0040 : t ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
    exact (show t ≠ v from (by exact fresh_t_ne_v))
  have dv_cache_0041 : t ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040
    exact (show t ≠ u from (by exact fresh_t_ne_u))
  have dv_cache_0042 : t ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
    exact (show t ≠ y from (by exact fresh_t_ne_y))
  have dv_cache_0043 : h ∉ ((Class.cv v)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042
    exact (by
      have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_h_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0044 : k ∉ ((Class.cv v)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0045 : t ∉ ((Class.cv v)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0046 : k ∉ ((syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_ne_v, fresh_k_ne_u, fresh_k_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0047 : t ∉ ((syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_v, fresh_t_ne_u, fresh_t_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0048 : k ∉ ((syn_cxp (.cv u) (syn_cnnc))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0049 : t ∉ ((syn_cxp (.cv u) (syn_cnnc))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0050 : h ≠ k := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049
    exact (show h ≠ k from (by exact fresh_h_ne_k))
  have dv_cache_0051 : h ≠ t := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050
    exact (show h ≠ t from (by exact fresh_h_ne_t))
  have dv_cache_0052 : k ≠ t := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051
    exact (show k ≠ t from (by exact fresh_k_ne_t))
  have dv_cache_0053 : u ∉ ((syn_cxpk B B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0054 : u ∉ ((Wff.imp (syn_wa (.classEq (syn_cxpk B B) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B))) (.imp (syn_wwpp) (syn_wbr (syn_cnc (.cv v)) (syn_clec) (syn_cnc (syn_cxp (syn_cxpk B B) (syn_cnnc))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivrange2, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wwpp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_B, fresh_u_ne_v, fresh_u_not_A, fresh_u_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0055 : v ∉ ((syn_cfdpivrange2 R A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivrange2, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, fresh_v_not_B, fresh_v_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0056 : v ∉ ((Wff.imp (syn_wa (.classEq (syn_cxpk B B) (syn_cxpk B B)) (.classEq (syn_cfdpivrange2 R A B) (syn_cfdpivrange2 R A B))) (.imp (syn_wwpp) (syn_wbr (syn_cnc (syn_cfdpivrange2 R A B)) (syn_clec) (syn_cnc (syn_cxp (syn_cxpk B B) (syn_cnnc))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpivrange2, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wwpp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_B, fresh_v_not_A, fresh_v_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eqid (syn_cxpk B B)
  have p0001 :=
    @g_eqid (syn_cfdpivrange2 R A B)
  have p0002 :=
    @g_pm3_2i (.classEq (syn_cxpk B B) (syn_cxpk B B)) (.classEq (syn_cfdpivrange2 R A B) (syn_cfdpivrange2 R A B)) p0000 p0001
  have p0003 :=
    @g_fdpivrange2ex A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_wppfdpivrangencdlitraw_1 hyp_wppfdpivrangencdlitraw_2 hyp_wppfdpivrangencdlitraw_3
  have p0004 :=
    @g_biidd (.classEq (.cv v) (syn_cfdpivrange2 R A B)) (.classEq (syn_cxpk B B) (syn_cxpk B B))
  have p0005 :=
    @g_id (.classEq (.cv v) (syn_cfdpivrange2 R A B))
  have p0006 :=
    @g_eqeq1d (.classEq (.cv v) (syn_cfdpivrange2 R A B)) (.cv v) (syn_cfdpivrange2 R A B) (syn_cfdpivrange2 R A B) p0005
  have p0007 :=
    @g_anbi12d (.classEq (.cv v) (syn_cfdpivrange2 R A B)) (.classEq (syn_cxpk B B) (syn_cxpk B B)) (.classEq (syn_cxpk B B) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B)) (.classEq (syn_cfdpivrange2 R A B) (syn_cfdpivrange2 R A B)) p0004 p0006
  have p0008 :=
    @g_biidd (.classEq (.cv v) (syn_cfdpivrange2 R A B)) (syn_wwpp)
  have p0009 :=
    @g_id (.classEq (.cv v) (syn_cfdpivrange2 R A B))
  have p0010 :=
    @g_nceqd (.classEq (.cv v) (syn_cfdpivrange2 R A B)) (.cv v) (syn_cfdpivrange2 R A B) p0009
  have p0011 :=
    @g_breq1d (.classEq (.cv v) (syn_cfdpivrange2 R A B)) (syn_cnc (.cv v)) (syn_cnc (syn_cfdpivrange2 R A B)) (syn_cnc (syn_cxp (syn_cxpk B B) (syn_cnnc))) (syn_clec) p0010
  have p0012 :=
    @g_imbi12d (.classEq (.cv v) (syn_cfdpivrange2 R A B)) (syn_wwpp) (syn_wwpp) (syn_wbr (syn_cnc (.cv v)) (syn_clec) (syn_cnc (syn_cxp (syn_cxpk B B) (syn_cnnc)))) (syn_wbr (syn_cnc (syn_cfdpivrange2 R A B)) (syn_clec) (syn_cnc (syn_cxp (syn_cxpk B B) (syn_cnnc)))) p0008 p0011
  have p0013 :=
    @g_imbi12d (.classEq (.cv v) (syn_cfdpivrange2 R A B)) (syn_wa (.classEq (syn_cxpk B B) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B))) (syn_wa (.classEq (syn_cxpk B B) (syn_cxpk B B)) (.classEq (syn_cfdpivrange2 R A B) (syn_cfdpivrange2 R A B))) (.imp (syn_wwpp) (syn_wbr (syn_cnc (.cv v)) (syn_clec) (syn_cnc (syn_cxp (syn_cxpk B B) (syn_cnnc))))) (.imp (syn_wwpp) (syn_wbr (syn_cnc (syn_cfdpivrange2 R A B)) (syn_clec) (syn_cnc (syn_cxp (syn_cxpk B B) (syn_cnnc))))) p0007 p0012
  have p0014 :=
    @g_xpkex B B hyp_wppfdpivrangencdlitraw_3 hyp_wppfdpivrangencdlitraw_3
  have p0015 :=
    @g_id (.classEq (.cv u) (syn_cxpk B B))
  have p0016 :=
    @g_eqeq1d (.classEq (.cv u) (syn_cxpk B B)) (.cv u) (syn_cxpk B B) (syn_cxpk B B) p0015
  have p0017 :=
    @g_biidd (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B))
  have p0018 :=
    @g_anbi12d (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv u) (syn_cxpk B B)) (.classEq (syn_cxpk B B) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B)) p0016 p0017
  have p0019 :=
    @g_biidd (.classEq (.cv u) (syn_cxpk B B)) (syn_wwpp)
  have p0020 :=
    @g_id (.classEq (.cv u) (syn_cxpk B B))
  have p0021 :=
    @g_xpeq1d (.classEq (.cv u) (syn_cxpk B B)) (.cv u) (syn_cxpk B B) (syn_cnnc) p0020
  have p0022 :=
    @g_nceqd (.classEq (.cv u) (syn_cxpk B B)) (syn_cxp (.cv u) (syn_cnnc)) (syn_cxp (syn_cxpk B B) (syn_cnnc)) p0021
  have p0023 :=
    @g_breq2d (.classEq (.cv u) (syn_cxpk B B)) (syn_cnc (syn_cxp (.cv u) (syn_cnnc))) (syn_cnc (syn_cxp (syn_cxpk B B) (syn_cnnc))) (syn_cnc (.cv v)) (syn_clec) p0022
  have p0024 :=
    @g_imbi12d (.classEq (.cv u) (syn_cxpk B B)) (syn_wwpp) (syn_wwpp) (syn_wbr (syn_cnc (.cv v)) (syn_clec) (syn_cnc (syn_cxp (.cv u) (syn_cnnc)))) (syn_wbr (syn_cnc (.cv v)) (syn_clec) (syn_cnc (syn_cxp (syn_cxpk B B) (syn_cnnc)))) p0019 p0023
  have p0025 :=
    @g_imbi12d (.classEq (.cv u) (syn_cxpk B B)) (syn_wa (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B))) (syn_wa (.classEq (syn_cxpk B B) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B))) (.imp (syn_wwpp) (syn_wbr (syn_cnc (.cv v)) (syn_clec) (syn_cnc (syn_cxp (.cv u) (syn_cnnc))))) (.imp (syn_wwpp) (syn_wbr (syn_cnc (.cv v)) (syn_clec) (syn_cnc (syn_cxp (syn_cxpk B B) (syn_cnnc))))) p0018 p0024
  have p0026 :=
    @g_fdpivmap2onto A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_wppfdpivrangencdlitraw_1 hyp_wppfdpivrangencdlitraw_2 hyp_wppfdpivrangencdlitraw_3
  have p0027 :=
    @g_a1i (syn_wfo (syn_cfdpivmap2 R A B) (syn_cxpk B B) (syn_cfdpivrange2 R A B)) (syn_wa (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B))) p0026
  have p0028 :=
    @g_simpl (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B))
  have p0029 :=
    @g_foeq2 (.cv u) (syn_cxpk B B) (syn_cfdpivrange2 R A B) (syn_cfdpivmap2 R A B)
  have p0030 :=
    @g_syl (syn_wa (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B))) (.classEq (.cv u) (syn_cxpk B B)) (syn_wb (syn_wfo (syn_cfdpivmap2 R A B) (.cv u) (syn_cfdpivrange2 R A B)) (syn_wfo (syn_cfdpivmap2 R A B) (syn_cxpk B B) (syn_cfdpivrange2 R A B))) p0028 p0029
  have p0031 :=
    @g_mpbird (syn_wa (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B))) (syn_wfo (syn_cfdpivmap2 R A B) (.cv u) (syn_cfdpivrange2 R A B)) (syn_wfo (syn_cfdpivmap2 R A B) (syn_cxpk B B) (syn_cfdpivrange2 R A B)) p0027 p0030
  have p0032 :=
    @g_simpr (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B))
  have p0033 :=
    @g_foeq3 (.cv v) (syn_cfdpivrange2 R A B) (.cv u) (syn_cfdpivmap2 R A B)
  have p0034 :=
    @g_syl (syn_wa (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B))) (.classEq (.cv v) (syn_cfdpivrange2 R A B)) (syn_wb (syn_wfo (syn_cfdpivmap2 R A B) (.cv u) (.cv v)) (syn_wfo (syn_cfdpivmap2 R A B) (.cv u) (syn_cfdpivrange2 R A B))) p0032 p0033
  have p0035 :=
    @g_mpbird (syn_wa (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B))) (syn_wfo (syn_cfdpivmap2 R A B) (.cv u) (.cv v)) (syn_wfo (syn_cfdpivmap2 R A B) (.cv u) (syn_cfdpivrange2 R A B)) p0031 p0034
  have p0036 :=
    @g_wpppadonto y (syn_cfdpivmap2 R A B) (.cv v) (.cv u) dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0037 :=
    @g_syl (syn_wa (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B))) (syn_wfo (syn_cfdpivmap2 R A B) (.cv u) (.cv v)) (syn_wfo (syn_cun (syn_cpprod (syn_cfdpivmap2 R A B) (syn_cres (syn_cid) (syn_csn (syn_c0c)))) (syn_cres (syn_cid) (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) (syn_cxp (.cv u) (syn_cnnc)) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) p0035 p0036
  have p0038 :=
    @g_fdpivmap2ex A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_wppfdpivrangencdlitraw_1 hyp_wppfdpivrangencdlitraw_2 hyp_wppfdpivrangencdlitraw_3
  have p0039 :=
    @g_padontoex u y v f (syn_cfdpivmap2 R A B) dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0006 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 p0038
  have p0040 :=
    @g_syl (syn_wa (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B))) (syn_wfo (syn_cun (syn_cpprod (syn_cfdpivmap2 R A B) (syn_cres (syn_cid) (syn_csn (syn_c0c)))) (syn_cres (syn_cid) (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) (syn_cxp (.cv u) (syn_cnnc)) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))) (syn_wex f (syn_wfo (.cv f) (syn_cxp (.cv u) (syn_cnnc)) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))) p0037 p0039
  have p0041 :=
    @g_sucxpinj y z (.cv v) (.cv u) dv_cache_0007 dv_cache_0008 dv_cache_0019 dv_cache_0009 dv_cache_0020 dv_cache_0021
  have p0042 :=
    @g_sucxpinjex u y z v g dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0016 dv_cache_0017 dv_cache_0026 dv_cache_0018 dv_cache_0027 dv_cache_0021
  have p0043 :=
    Nominal.mp p0041 p0042
  have p0044 :=
    @g_a1i (syn_wex g (syn_wf1 (.cv g) (syn_cxp (.cv u) (syn_cnnc)) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))) (syn_wa (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B))) p0043
  have p0045 :=
    @g_jca (syn_wa (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B))) (syn_wex f (syn_wfo (.cv f) (syn_cxp (.cv u) (syn_cnnc)) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))) (syn_wex g (syn_wf1 (.cv g) (syn_cxp (.cv u) (syn_cnnc)) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))) p0040 p0044
  have p0046 :=
    @g_padsetex u y v dv_cache_0016 dv_cache_0017 dv_cache_0018
  have p0047 :=
    @g_xnnex u
  have p0048 :=
    @g_pm3_2i (.classMem (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) (syn_cvv)) (.classMem (syn_cxp (.cv u) (syn_cnnc)) (syn_cvv)) p0046 p0047
  have p0049 :=
    @g_wppcg (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) (syn_cxp (.cv u) (syn_cnnc)) f g h (syn_cvv) (syn_cvv) dv_cache_0028 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
  have p0050 :=
    Nominal.mp p0048 p0049
  have p0051 :=
    @g_syl5com (syn_wa (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B))) (syn_wa (syn_wex f (syn_wfo (.cv f) (syn_cxp (.cv u) (syn_cnnc)) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))) (syn_wex g (syn_wf1 (.cv g) (syn_cxp (.cv u) (syn_cnnc)) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))))) (syn_wwpp) (syn_wex h (syn_wf1 (.cv h) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) (syn_cxp (.cv u) (syn_cnnc)))) p0045 p0050
  have p0052 :=
    @g_taginjex u y v t dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0016 dv_cache_0017 dv_cache_0018
  have p0053 :=
    @g_a1i (syn_wex t (syn_wf1 (.cv t) (.cv v) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))) (syn_wwpp) p0052
  have p0054 :=
    @g_a1i (.imp (syn_wwpp) (syn_wex t (syn_wf1 (.cv t) (.cv v) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))))) (syn_wa (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B))) p0053
  have p0055 :=
    @g_jcad (syn_wa (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B))) (syn_wwpp) (syn_wex h (syn_wf1 (.cv h) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) (syn_cxp (.cv u) (syn_cnnc)))) (syn_wex t (syn_wf1 (.cv t) (.cv v) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))))) p0051 p0054
  have p0056 :=
    @g_f1exco t (.cv v) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) (syn_cxp (.cv u) (syn_cnnc)) h k dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0031 dv_cache_0046 dv_cache_0047 dv_cache_0035 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052
  have p0057 :=
    @g_a1i (.imp (syn_wa (syn_wex h (syn_wf1 (.cv h) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) (syn_cxp (.cv u) (syn_cnnc)))) (syn_wex t (syn_wf1 (.cv t) (.cv v) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))))) (syn_wex k (syn_wf1 (.cv k) (.cv v) (syn_cxp (.cv u) (syn_cnnc))))) (syn_wwpp) p0056
  have p0058 :=
    @g_a1i (.imp (syn_wwpp) (.imp (syn_wa (syn_wex h (syn_wf1 (.cv h) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) (syn_cxp (.cv u) (syn_cnnc)))) (syn_wex t (syn_wf1 (.cv t) (.cv v) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))))) (syn_wex k (syn_wf1 (.cv k) (.cv v) (syn_cxp (.cv u) (syn_cnnc)))))) (syn_wa (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B))) p0057
  have p0059 :=
    @g_mpdd (syn_wa (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B))) (syn_wwpp) (syn_wa (syn_wex h (syn_wf1 (.cv h) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c)))))) (syn_cxp (.cv u) (syn_cnnc)))) (syn_wex t (syn_wf1 (.cv t) (.cv v) (syn_cun (syn_cxp (.cv v) (syn_csn (syn_c0c))) (syn_cxp (.cv u) (syn_crab y (syn_cnnc) (.neg (.classEq (.cv y) (syn_c0c))))))))) (syn_wex k (syn_wf1 (.cv k) (.cv v) (syn_cxp (.cv u) (syn_cnnc)))) p0055 p0058
  have p0060 :=
    @g_vex v
  have p0061 :=
    @g_xnnex u
  have p0062 :=
    @g_nclenc (.cv v) (syn_cxp (.cv u) (syn_cnnc)) k dv_cache_0044 dv_cache_0048 p0060 p0061
  have p0063 :=
    @g_a1i (syn_wb (syn_wbr (syn_cnc (.cv v)) (syn_clec) (syn_cnc (syn_cxp (.cv u) (syn_cnnc)))) (syn_wex k (syn_wf1 (.cv k) (.cv v) (syn_cxp (.cv u) (syn_cnnc))))) (syn_wa (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B))) p0062
  have p0064 :=
    @g_sylibrd (syn_wa (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B))) (syn_wwpp) (syn_wex k (syn_wf1 (.cv k) (.cv v) (syn_cxp (.cv u) (syn_cnnc)))) (syn_wbr (syn_cnc (.cv v)) (syn_clec) (syn_cnc (syn_cxp (.cv u) (syn_cnnc)))) p0059 p0063
  have p0065 :=
    @g_vtoclg (.imp (syn_wa (.classEq (.cv u) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B))) (.imp (syn_wwpp) (syn_wbr (syn_cnc (.cv v)) (syn_clec) (syn_cnc (syn_cxp (.cv u) (syn_cnnc)))))) (.imp (syn_wa (.classEq (syn_cxpk B B) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B))) (.imp (syn_wwpp) (syn_wbr (syn_cnc (.cv v)) (syn_clec) (syn_cnc (syn_cxp (syn_cxpk B B) (syn_cnnc)))))) u (syn_cxpk B B) (syn_cvv) dv_cache_0053 dv_cache_0054 p0025 p0064
  have p0066 :=
    Nominal.mp p0014 p0065
  have p0067 :=
    @g_vtoclg (.imp (syn_wa (.classEq (syn_cxpk B B) (syn_cxpk B B)) (.classEq (.cv v) (syn_cfdpivrange2 R A B))) (.imp (syn_wwpp) (syn_wbr (syn_cnc (.cv v)) (syn_clec) (syn_cnc (syn_cxp (syn_cxpk B B) (syn_cnnc)))))) (.imp (syn_wa (.classEq (syn_cxpk B B) (syn_cxpk B B)) (.classEq (syn_cfdpivrange2 R A B) (syn_cfdpivrange2 R A B))) (.imp (syn_wwpp) (syn_wbr (syn_cnc (syn_cfdpivrange2 R A B)) (syn_clec) (syn_cnc (syn_cxp (syn_cxpk B B) (syn_cnnc)))))) v (syn_cfdpivrange2 R A B) (syn_cvv) dv_cache_0055 dv_cache_0056 p0013 p0066
  have p0068 :=
    Nominal.mp p0003 p0067
  have p0069 :=
    Nominal.mp p0002 p0068
  exact p0069

#print axioms g_wppfdpivrangencdlitraw

end NFChoice.DirectNominalPrf.WPPReplay
