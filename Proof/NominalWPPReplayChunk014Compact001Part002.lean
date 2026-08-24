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
import NominalWPPReplayChunk014Compact001Part001

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

noncomputable def g_frecxp
    (F : Class) (G : Class) (I : Class) (hyp_frecxp_1 : Nominal.NPrf (.classEq F (syn_cfrec G I))) (hyp_frecxp_2 : Nominal.NPrf (.classMem G (syn_cvv))) :
    Nominal.NPrf (syn_wss F (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I)))) := by
  let proofSupport : Finset Var := F.fv ∪ G.fv ∪ I.fv
  let i : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let x : Var := freshVar proofSupport 3
  let a : Var := freshVar proofSupport 4
  let b : Var := freshVar proofSupport 5
  let c : Var := freshVar proofSupport 6
  let d : Var := freshVar proofSupport 7
  have fresh_i : i ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_i_not_F : i ∉ F.fv := by
    intro h
    exact fresh_i (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_i_not_G : i ∉ G.fv := by
    intro h
    exact fresh_i (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_i_not_I : i ∉ I.fv := by
    intro h
    exact fresh_i (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_G : y ∉ G.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_I : y ∉ I.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_G : z ∉ G.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_I : z ∉ I.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_G : x ∉ G.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_I : x ∉ I.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_a_not_F : a ∉ F.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_a_not_G : a ∉ G.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_I : a ∉ I.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_b_not_F : b ∉ F.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_b_not_G : b ∉ G.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_not_I : b ∉ I.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_c : c ∉ proofSupport := by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_c_not_F : c ∉ F.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_c_not_G : c ∉ G.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_c_not_I : c ∉ I.fv := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (h))
  have fresh_d : d ∉ proofSupport := by
    change freshVar proofSupport 7 ∉ proofSupport
    exact freshVar_not_mem proofSupport 7
  have fresh_d_not_F : d ∉ F.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_d_not_G : d ∉ G.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_not_I : d ∉ I.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_i_ne_y : i ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_i : y ≠ i :=
    Ne.symm fresh_i_ne_y
  have fresh_i_ne_z : i ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_i : z ≠ i :=
    Ne.symm fresh_i_ne_z
  have fresh_i_ne_x : i ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_x_ne_i : x ≠ i :=
    Ne.symm fresh_i_ne_x
  have fresh_i_ne_a : i ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_a_ne_i : a ≠ i :=
    Ne.symm fresh_i_ne_a
  have fresh_i_ne_b : i ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_b_ne_i : b ≠ i :=
    Ne.symm fresh_i_ne_b
  have fresh_i_ne_c : i ≠ c := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_c_ne_i : c ≠ i :=
    Ne.symm fresh_i_ne_c
  have fresh_i_ne_d : i ≠ d := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 0) (j := 7) (by decide)
  have fresh_d_ne_i : d ≠ i :=
    Ne.symm fresh_i_ne_d
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_ne_a : y ≠ a := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_a_ne_y : a ≠ y :=
    Ne.symm fresh_y_ne_a
  have fresh_y_ne_b : y ≠ b := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_b_ne_y : b ≠ y :=
    Ne.symm fresh_y_ne_b
  have fresh_y_ne_c : y ≠ c := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_c_ne_y : c ≠ y :=
    Ne.symm fresh_y_ne_c
  have fresh_y_ne_d : y ≠ d := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 1) (j := 7) (by decide)
  have fresh_d_ne_y : d ≠ y :=
    Ne.symm fresh_y_ne_d
  have fresh_z_ne_x : z ≠ x := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_a : z ≠ a := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_a_ne_z : a ≠ z :=
    Ne.symm fresh_z_ne_a
  have fresh_z_ne_b : z ≠ b := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_b_ne_z : b ≠ z :=
    Ne.symm fresh_z_ne_b
  have fresh_z_ne_c : z ≠ c := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_c_ne_z : c ≠ z :=
    Ne.symm fresh_z_ne_c
  have fresh_z_ne_d : z ≠ d := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 2) (j := 7) (by decide)
  have fresh_d_ne_z : d ≠ z :=
    Ne.symm fresh_z_ne_d
  have fresh_x_ne_a : x ≠ a := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_a_ne_x : a ≠ x :=
    Ne.symm fresh_x_ne_a
  have fresh_x_ne_b : x ≠ b := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_b_ne_x : b ≠ x :=
    Ne.symm fresh_x_ne_b
  have fresh_x_ne_c : x ≠ c := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_c_ne_x : c ≠ x :=
    Ne.symm fresh_x_ne_c
  have fresh_x_ne_d : x ≠ d := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 3) (j := 7) (by decide)
  have fresh_d_ne_x : d ≠ x :=
    Ne.symm fresh_x_ne_d
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have fresh_a_ne_c : a ≠ c := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_c_ne_a : c ≠ a :=
    Ne.symm fresh_a_ne_c
  have fresh_a_ne_d : a ≠ d := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 4) (j := 7) (by decide)
  have fresh_d_ne_a : d ≠ a :=
    Ne.symm fresh_a_ne_d
  have fresh_b_ne_c : b ≠ c := by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_c_ne_b : c ≠ b :=
    Ne.symm fresh_b_ne_c
  have fresh_b_ne_d : b ≠ d := by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 5) (j := 7) (by decide)
  have fresh_d_ne_b : d ≠ b :=
    Ne.symm fresh_b_ne_d
  have fresh_c_ne_d : c ≠ d := by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 6) (j := 7) (by decide)
  have fresh_d_ne_c : d ≠ c :=
    Ne.symm fresh_c_ne_d
  have dv_cache_0001 : d ∉ ((Class.cv y)).fv := by
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : a ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : b ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : c ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : d ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : a ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : b ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : c ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : d ∉ ((syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : a ∉ ((syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : b ∉ ((syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : c ∉ ((syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : d ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : a ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : b ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : c ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : d ≠ a := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show d ≠ a from (by exact fresh_d_ne_a))
  have dv_cache_0018 : d ≠ b := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show d ≠ b from (by exact fresh_d_ne_b))
  have dv_cache_0019 : d ≠ c := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (show d ≠ c from (by exact fresh_d_ne_c))
  have dv_cache_0020 : a ≠ b := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0021 : a ≠ c := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show a ≠ c from (by exact fresh_a_ne_c))
  have dv_cache_0022 : b ≠ c := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show b ≠ c from (by exact fresh_b_ne_c))
  have dv_cache_0023 : x ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : x ∉ ((Class.cv c)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : c ∉ ((Wff.imp (.classMem (.cv y) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))) (.classMem (.cv z) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_y, fresh_c_not_G, fresh_c_ne_i, fresh_c_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : d ∉ ((Wff.imp (.classMem (.cv y) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))) (.classMem (.cv z) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_y, fresh_d_not_G, fresh_d_ne_i, fresh_d_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : a ∉ ((Wff.imp (.classMem (.cv y) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))) (.classMem (.cv z) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_y, fresh_a_not_G, fresh_a_ne_i, fresh_a_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0028 : b ∉ ((Wff.imp (.classMem (.cv y) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))) (.classMem (.cv z) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_y, fresh_b_not_G, fresh_b_ne_i, fresh_b_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0029 : x ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0030 : x ∉ ((Class.cv i)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_i, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0031 : y ∉ ((syn_cfrec G (.cv i))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_G, fresh_y_ne_i, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0032 : z ∉ ((syn_cfrec G (.cv i))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_G, fresh_z_ne_i, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0033 : y ∉ ((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0034 : z ∉ ((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0035 : y ∉ ((syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_G, fresh_y_ne_i, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0036 : z ∉ ((syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_G, fresh_z_ne_i, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0037 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0038 : i ∉ (I).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037
    exact (by
      have compact_fv_not_mem_empty : i ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_i_not_I, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0039 : i ∉ ((syn_wss (syn_cfrec G I) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038
    exact (by
      have compact_fv_not_mem_empty : i ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_i_not_G, fresh_i_not_I, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0040 : x ∉ (I).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_I, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eqid G
  have p0001 :=
    @g_freceq12 G G (.cv i) I
  have p0002 :=
    @g_mpan (.classEq G G) (.classEq (.cv i) I) (.classEq (syn_cfrec G (.cv i)) (syn_cfrec G I)) p0000 p0001
  have p0003 :=
    @g_sneq (.cv i) I
  have p0004 :=
    @g_uneq2d (.classEq (.cv i) I) (syn_csn (.cv i)) (syn_csn I) (syn_crn G) p0003
  have p0005 :=
    @g_xpeq2d (.classEq (.cv i) I) (syn_cun (syn_crn G) (syn_csn (.cv i))) (syn_cun (syn_crn G) (syn_csn I)) (syn_cnnc) p0004
  have p0006 :=
    @g_sseq12d (.classEq (.cv i) I) (syn_cfrec G (.cv i)) (syn_cfrec G I) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I))) p0002 p0005
  have p0007 :=
    @g_nncex
  have p0008 :=
    @g_rnex G hyp_frecxp_2
  have p0009 :=
    @g_snex (.cv i)
  have p0010 :=
    @g_unex (syn_crn G) (syn_csn (.cv i)) p0008 p0009
  have p0011 :=
    @g_xpex (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))) p0007 p0010
  have p0012 :=
    @g_peano1
  have p0013 :=
    @g_vex i
  have p0014 :=
    @g_snid (.cv i) p0013
  have p0015 :=
    @g_elun2 (.cv i) (syn_csn (.cv i)) (syn_crn G)
  have p0016 :=
    Nominal.mp p0014 p0015
  have p0017 :=
    @g_n_0cex
  have p0018 :=
    @g_opex (syn_c0c) (.cv i) p0017 p0013
  have p0019 :=
    @g_snss (syn_cop (syn_c0c) (.cv i)) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))) p0018
  have p0020 :=
    @g_opelxp (syn_c0c) (.cv i) (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))
  have p0021 :=
    @g_bitr3i (syn_wss (syn_csn (syn_cop (syn_c0c) (.cv i))) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))) (.classMem (syn_cop (syn_c0c) (.cv i)) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))) (syn_wa (.classMem (syn_c0c) (syn_cnnc)) (.classMem (.cv i) (syn_cun (syn_crn G) (syn_csn (.cv i))))) p0019 p0020
  have p0022 :=
    @g_mpbir2an (syn_wss (syn_csn (syn_cop (syn_c0c) (.cv i))) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))) (.classMem (syn_c0c) (syn_cnnc)) (.classMem (.cv i) (syn_cun (syn_crn G) (syn_csn (.cv i)))) p0012 p0016 p0021
  have p0023 :=
    @g_brpprod a b c d (.cv y) (.cv z) (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
  have p0024 :=
    @g_vex a
  have p0025 :=
    @g_vex c
  have p0026 :=
    @g_brcsuc x (.cv a) (.cv c) dv_cache_0023 dv_cache_0024 p0024 p0025
  have p0027 :=
    @g_brelrn (.cv b) (.cv d) G
  have p0028 :=
    @g_elun1 (.cv d) (syn_crn G) (syn_csn (.cv i))
  have p0029 :=
    @g_syl (syn_wbr (.cv b) G (.cv d)) (.classMem (.cv d) (syn_crn G)) (.classMem (.cv d) (syn_cun (syn_crn G) (syn_csn (.cv i)))) p0027 p0028
  have p0030 :=
    @g_peano2 (.cv a)
  have p0031 :=
    @g_anim12ci (syn_wbr (.cv b) G (.cv d)) (.classMem (.cv d) (syn_cun (syn_crn G) (syn_csn (.cv i)))) (.classMem (.cv a) (syn_cnnc)) (.classMem (syn_cplc (.cv a) (syn_c1c)) (syn_cnnc)) p0029 p0030
  have p0032 :=
    @g_adantrr (syn_wbr (.cv b) G (.cv d)) (.classMem (.cv a) (syn_cnnc)) (syn_wa (.classMem (syn_cplc (.cv a) (syn_c1c)) (syn_cnnc)) (.classMem (.cv d) (syn_cun (syn_crn G) (syn_csn (.cv i))))) (.classMem (.cv b) (syn_cun (syn_crn G) (syn_csn (.cv i)))) p0031
  have p0033 :=
    @g_eleq1 (.cv c) (syn_cplc (.cv a) (syn_c1c)) (syn_cnnc)
  have p0034 :=
    @g_anbi1d (.classEq (.cv c) (syn_cplc (.cv a) (syn_c1c))) (.classMem (.cv c) (syn_cnnc)) (.classMem (syn_cplc (.cv a) (syn_c1c)) (syn_cnnc)) (.classMem (.cv d) (syn_cun (syn_crn G) (syn_csn (.cv i)))) p0033
  have p0035 :=
    @g_syl5ibr (syn_wa (syn_wbr (.cv b) G (.cv d)) (syn_wa (.classMem (.cv a) (syn_cnnc)) (.classMem (.cv b) (syn_cun (syn_crn G) (syn_csn (.cv i)))))) (syn_wa (.classMem (.cv c) (syn_cnnc)) (.classMem (.cv d) (syn_cun (syn_crn G) (syn_csn (.cv i))))) (.classEq (.cv c) (syn_cplc (.cv a) (syn_c1c))) (syn_wa (.classMem (syn_cplc (.cv a) (syn_c1c)) (syn_cnnc)) (.classMem (.cv d) (syn_cun (syn_crn G) (syn_csn (.cv i))))) p0032 p0034
  have p0036 :=
    @g_exp3a (.classEq (.cv c) (syn_cplc (.cv a) (syn_c1c))) (syn_wbr (.cv b) G (.cv d)) (syn_wa (.classMem (.cv a) (syn_cnnc)) (.classMem (.cv b) (syn_cun (syn_crn G) (syn_csn (.cv i))))) (syn_wa (.classMem (.cv c) (syn_cnnc)) (.classMem (.cv d) (syn_cun (syn_crn G) (syn_csn (.cv i))))) p0035
  have p0037 :=
    @g_sylbi (syn_wbr (.cv a) (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) (.cv c)) (.classEq (.cv c) (syn_cplc (.cv a) (syn_c1c))) (.imp (syn_wbr (.cv b) G (.cv d)) (.imp (syn_wa (.classMem (.cv a) (syn_cnnc)) (.classMem (.cv b) (syn_cun (syn_crn G) (syn_csn (.cv i))))) (syn_wa (.classMem (.cv c) (syn_cnnc)) (.classMem (.cv d) (syn_cun (syn_crn G) (syn_csn (.cv i))))))) p0026 p0036
  have p0038 :=
    @g_imp (syn_wbr (.cv a) (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) (.cv c)) (syn_wbr (.cv b) G (.cv d)) (.imp (syn_wa (.classMem (.cv a) (syn_cnnc)) (.classMem (.cv b) (syn_cun (syn_crn G) (syn_csn (.cv i))))) (syn_wa (.classMem (.cv c) (syn_cnnc)) (.classMem (.cv d) (syn_cun (syn_crn G) (syn_csn (.cv i)))))) p0037
  have p0039 :=
    @g_eleq1 (.cv y) (syn_cop (.cv a) (.cv b)) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))
  have p0040 :=
    @g_opelxp (.cv a) (.cv b) (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))
  have p0041 :=
    @g_syl6bb (.classEq (.cv y) (syn_cop (.cv a) (.cv b))) (.classMem (.cv y) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))) (.classMem (syn_cop (.cv a) (.cv b)) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))) (syn_wa (.classMem (.cv a) (syn_cnnc)) (.classMem (.cv b) (syn_cun (syn_crn G) (syn_csn (.cv i))))) p0039 p0040
  have p0042 :=
    @g_adantr (.classEq (.cv y) (syn_cop (.cv a) (.cv b))) (syn_wb (.classMem (.cv y) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))) (syn_wa (.classMem (.cv a) (syn_cnnc)) (.classMem (.cv b) (syn_cun (syn_crn G) (syn_csn (.cv i)))))) (.classEq (.cv z) (syn_cop (.cv c) (.cv d))) p0041
  have p0043 :=
    @g_eleq1 (.cv z) (syn_cop (.cv c) (.cv d)) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))
  have p0044 :=
    @g_opelxp (.cv c) (.cv d) (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))
  have p0045 :=
    @g_syl6bb (.classEq (.cv z) (syn_cop (.cv c) (.cv d))) (.classMem (.cv z) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))) (.classMem (syn_cop (.cv c) (.cv d)) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))) (syn_wa (.classMem (.cv c) (syn_cnnc)) (.classMem (.cv d) (syn_cun (syn_crn G) (syn_csn (.cv i))))) p0043 p0044
  have p0046 :=
    @g_adantl (.classEq (.cv z) (syn_cop (.cv c) (.cv d))) (syn_wb (.classMem (.cv z) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))) (syn_wa (.classMem (.cv c) (syn_cnnc)) (.classMem (.cv d) (syn_cun (syn_crn G) (syn_csn (.cv i)))))) (.classEq (.cv y) (syn_cop (.cv a) (.cv b))) p0045
  have p0047 :=
    @g_imbi12d (syn_wa (.classEq (.cv y) (syn_cop (.cv a) (.cv b))) (.classEq (.cv z) (syn_cop (.cv c) (.cv d)))) (.classMem (.cv y) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))) (syn_wa (.classMem (.cv a) (syn_cnnc)) (.classMem (.cv b) (syn_cun (syn_crn G) (syn_csn (.cv i))))) (.classMem (.cv z) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))) (syn_wa (.classMem (.cv c) (syn_cnnc)) (.classMem (.cv d) (syn_cun (syn_crn G) (syn_csn (.cv i))))) p0042 p0046
  have p0048 :=
    @g_syl5ibr (syn_wa (syn_wbr (.cv a) (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) (.cv c)) (syn_wbr (.cv b) G (.cv d))) (.imp (.classMem (.cv y) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))) (.classMem (.cv z) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))))) (syn_wa (.classEq (.cv y) (syn_cop (.cv a) (.cv b))) (.classEq (.cv z) (syn_cop (.cv c) (.cv d)))) (.imp (syn_wa (.classMem (.cv a) (syn_cnnc)) (.classMem (.cv b) (syn_cun (syn_crn G) (syn_csn (.cv i))))) (syn_wa (.classMem (.cv c) (syn_cnnc)) (.classMem (.cv d) (syn_cun (syn_crn G) (syn_csn (.cv i)))))) p0038 p0047
  have p0049 :=
    @g_n_3impia (.classEq (.cv y) (syn_cop (.cv a) (.cv b))) (.classEq (.cv z) (syn_cop (.cv c) (.cv d))) (syn_wa (syn_wbr (.cv a) (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) (.cv c)) (syn_wbr (.cv b) G (.cv d))) (.imp (.classMem (.cv y) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))) (.classMem (.cv z) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))))) p0048
  have p0050 :=
    @g_exlimivv (syn_w3a (.classEq (.cv y) (syn_cop (.cv a) (.cv b))) (.classEq (.cv z) (syn_cop (.cv c) (.cv d))) (syn_wa (syn_wbr (.cv a) (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) (.cv c)) (syn_wbr (.cv b) G (.cv d)))) (.imp (.classMem (.cv y) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))) (.classMem (.cv z) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))))) c d dv_cache_0025 dv_cache_0026 p0049
  have p0051 :=
    @g_exlimivv (syn_wex c (syn_wex d (syn_w3a (.classEq (.cv y) (syn_cop (.cv a) (.cv b))) (.classEq (.cv z) (syn_cop (.cv c) (.cv d))) (syn_wa (syn_wbr (.cv a) (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) (.cv c)) (syn_wbr (.cv b) G (.cv d)))))) (.imp (.classMem (.cv y) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))) (.classMem (.cv z) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))))) a b dv_cache_0027 dv_cache_0028 p0050
  have p0052 :=
    @g_sylbi (syn_wbr (.cv y) (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G) (.cv z)) (syn_wex a (syn_wex b (syn_wex c (syn_wex d (syn_w3a (.classEq (.cv y) (syn_cop (.cv a) (.cv b))) (.classEq (.cv z) (syn_cop (.cv c) (.cv d))) (syn_wa (syn_wbr (.cv a) (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) (.cv c)) (syn_wbr (.cv b) G (.cv d)))))))) (.imp (.classMem (.cv y) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))) (.classMem (.cv z) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))))) p0023 p0051
  have p0053 :=
    @g_impcom (syn_wbr (.cv y) (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G) (.cv z)) (.classMem (.cv y) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))) (.classMem (.cv z) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))) p0052
  have p0054 :=
    Nominal.gen p0053 z
  have p0055 :=
    @g_rgenw (.all z (.imp (syn_wa (.classMem (.cv y) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))) (syn_wbr (.cv y) (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G) (.cv z))) (.classMem (.cv z) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))))) y (syn_cfrec G (.cv i)) p0054
  have p0056 :=
    @g_snex (syn_cop (syn_c0c) (.cv i))
  have p0057 :=
    @g_csucex x
  have p0058 :=
    @g_pprodex (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G p0057 hyp_frecxp_2
  have p0059 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_frec x G (.cv i) dv_cache_0029 dv_cache_0030
  have p0060 :=
    @g_clos1induct y z (syn_cfrec G (.cv i)) (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G) (syn_csn (syn_cop (syn_c0c) (.cv i))) (syn_cvv) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))) dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 p0056 p0058 p0059
  have p0061 :=
    @g_mp3an (.classMem (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))) (syn_cvv)) (syn_wss (syn_csn (syn_cop (syn_c0c) (.cv i))) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))) (syn_wral y (syn_cfrec G (.cv i)) (.all z (.imp (syn_wa (.classMem (.cv y) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))) (syn_wbr (.cv y) (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G) (.cv z))) (.classMem (.cv z) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i)))))))) (syn_wss (syn_cfrec G (.cv i)) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))) p0011 p0022 p0055 p0060
  have p0062 :=
    @g_vtoclg (syn_wss (syn_cfrec G (.cv i)) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn (.cv i))))) (syn_wss (syn_cfrec G I) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I)))) i I (syn_cvv) dv_cache_0038 dv_cache_0039 p0006 p0061
  have p0063 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_frec x G I dv_cache_0029 dv_cache_0040
  have p0064 :=
    @g_opexb (syn_c0c) I
  have p0065 :=
    @g_simprbi (.classMem (syn_cop (syn_c0c) I) (syn_cvv)) (.classMem (syn_c0c) (syn_cvv)) (.classMem I (syn_cvv)) p0064
  have p0066 :=
    @g_con3i (.classMem (syn_cop (syn_c0c) I) (syn_cvv)) (.classMem I (syn_cvv)) p0065
  have p0067 :=
    @g_snprc (syn_cop (syn_c0c) I)
  have p0068 :=
    @g_sylib (.neg (.classMem I (syn_cvv))) (.neg (.classMem (syn_cop (syn_c0c) I) (syn_cvv))) (.classEq (syn_csn (syn_cop (syn_c0c) I)) (syn_c0)) p0066 p0067
  have p0069 :=
    @g_clos1eq1 (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G) (syn_csn (syn_cop (syn_c0c) I)) (syn_c0)
  have p0070 :=
    @g_syl (.neg (.classMem I (syn_cvv))) (.classEq (syn_csn (syn_cop (syn_c0c) I)) (syn_c0)) (.classEq (syn_cclos1 (syn_csn (syn_cop (syn_c0c) I)) (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G)) (syn_cclos1 (syn_c0) (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G))) p0068 p0069
  have p0071 :=
    @g_eqid (syn_cclos1 (syn_c0) (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G))
  have p0072 :=
    @g_clos10 (syn_cclos1 (syn_c0) (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G)) (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G) p0058 p0071
  have p0073 :=
    @g_syl6eq (.neg (.classMem I (syn_cvv))) (syn_cclos1 (syn_csn (syn_cop (syn_c0c) I)) (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G)) (syn_cclos1 (syn_c0) (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G)) (syn_c0) p0070 p0072
  have p0074 :=
    @g_n_0ss (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I)))
  have p0075 :=
    @g_syl6eqss (.neg (.classMem I (syn_cvv))) (syn_cclos1 (syn_csn (syn_cop (syn_c0c) I)) (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G)) (syn_c0) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I))) p0073 p0074
  have p0076 :=
    @g_syl5eqss (.neg (.classMem I (syn_cvv))) (syn_cfrec G I) (syn_cclos1 (syn_csn (syn_cop (syn_c0c) I)) (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G)) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I))) p0063 p0075
  have p0077 :=
    @g_pm2_61i (.classMem I (syn_cvv)) (syn_wss (syn_cfrec G I) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I)))) p0062 p0076
  have p0078 :=
    @g_eqsstri F (syn_cfrec G I) (syn_cxp (syn_cnnc) (syn_cun (syn_crn G) (syn_csn I))) hyp_frecxp_1 p0077
  exact p0078

#print axioms g_frecxp

end NFChoice.DirectNominalPrf.WPPReplay
