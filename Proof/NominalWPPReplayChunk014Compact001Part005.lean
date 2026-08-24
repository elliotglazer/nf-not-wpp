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
import NominalWPPReplayChunk014Compact001Part004

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

noncomputable def g_fnfrec
    (ph : Wff) (F : Class) (G : Class) (I : Class) (hyp_fnfrec_1 : Nominal.NPrf (.classEq F (syn_cfrec G I))) (hyp_fnfrec_2 : Nominal.NPrf (.imp ph (.classMem G (syn_cfuns)))) (hyp_fnfrec_3 : Nominal.NPrf (.imp ph (.classMem I (syn_cdm G)))) (hyp_fnfrec_4 : Nominal.NPrf (.imp ph (syn_wss (syn_crn G) (syn_cdm G)))) :
    Nominal.NPrf (.imp ph (syn_wfn F (syn_cnnc))) := by
  let proofSupport : Finset Var := ph.fv ∪ F.fv ∪ G.fv ∪ I.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  let t : Var := freshVar proofSupport 4
  let a : Var := freshVar proofSupport 5
  let b : Var := freshVar proofSupport 6
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_ph : x ∉ ph.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_G : x ∉ G.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_I : x ∉ I.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_G : y ∉ G.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_I : y ∉ I.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_G : z ∉ G.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_I : z ∉ I.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_w_not_F : w ∉ F.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_G : w ∉ G.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_I : w ∉ I.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_t_not_ph : t ∉ ph.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_t_not_F : t ∉ F.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_t_not_G : t ∉ G.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_t_not_I : t ∉ I.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_a_not_ph : a ∉ ph.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_a_not_F : a ∉ F.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a_not_G : a ∉ G.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_I : a ∉ I.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_b_not_ph : b ∉ ph.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_b_not_F : b ∉ F.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_b_not_G : b ∉ G.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_not_I : b ∉ I.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
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
  have fresh_x_ne_a : x ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_a_ne_x : a ≠ x :=
    Ne.symm fresh_x_ne_a
  have fresh_x_ne_b : x ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_b_ne_x : b ≠ x :=
    Ne.symm fresh_x_ne_b
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
  have fresh_y_ne_a : y ≠ a := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_a_ne_y : a ≠ y :=
    Ne.symm fresh_y_ne_a
  have fresh_y_ne_b : y ≠ b := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_b_ne_y : b ≠ y :=
    Ne.symm fresh_y_ne_b
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
  have fresh_z_ne_a : z ≠ a := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_a_ne_z : a ≠ z :=
    Ne.symm fresh_z_ne_a
  have fresh_z_ne_b : z ≠ b := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_b_ne_z : b ≠ z :=
    Ne.symm fresh_z_ne_b
  have fresh_w_ne_t : w ≠ t := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_t_ne_w : t ≠ w :=
    Ne.symm fresh_w_ne_t
  have fresh_w_ne_a : w ≠ a := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_a_ne_w : a ≠ w :=
    Ne.symm fresh_w_ne_a
  have fresh_w_ne_b : w ≠ b := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_b_ne_w : b ≠ w :=
    Ne.symm fresh_w_ne_b
  have fresh_t_ne_a : t ≠ a := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_a_ne_t : a ≠ t :=
    Ne.symm fresh_t_ne_a
  have fresh_t_ne_b : t ≠ b := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_b_ne_t : b ≠ t :=
    Ne.symm fresh_t_ne_b
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have dv_cache_0001 : w ∉ (F).fv := by
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (F).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : w ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show w ≠ y from (by exact fresh_w_ne_y))
  have dv_cache_0005 : w ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show w ≠ z from (by exact fresh_w_ne_z))
  have dv_cache_0006 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0007 : y ∉ ((Wff.classEq (.cv w) (syn_c0c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : z ∉ ((Wff.classEq (.cv w) (syn_c0c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((Wff.objEq w t)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_w, fresh_y_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : z ∉ ((Wff.objEq w t)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_w, fresh_z_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((Wff.classEq (.cv w) (syn_cplc (.cv t) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_w, fresh_y_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : z ∉ ((Wff.classEq (.cv w) (syn_cplc (.cv t) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_w, fresh_z_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : b ∉ ((Wff.imp (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv y)) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv z))) (.objEq y z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_t, fresh_b_ne_y, fresh_b_not_F, fresh_b_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : a ∉ ((Wff.imp (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv y)) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv z))) (.objEq y z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_t, fresh_a_ne_y, fresh_a_not_F, fresh_a_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : y ∉ ((Wff.imp (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a)) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b))) (.objEq a b))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_t, fresh_y_ne_a, fresh_y_not_F, fresh_y_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : z ∉ ((Wff.imp (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a)) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b))) (.objEq a b))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_t, fresh_z_ne_a, fresh_z_not_F, fresh_z_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : b ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show b ≠ y from (by exact fresh_b_ne_y))
  have dv_cache_0018 : b ≠ a := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show b ≠ a from (by exact fresh_b_ne_a))
  have dv_cache_0019 : z ≠ a := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (show z ≠ a from (by exact fresh_z_ne_a))
  have dv_cache_0020 : y ∉ ((Wff.objEq w x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_w, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : z ∉ ((Wff.objEq w x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_w, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : y ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : z ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : y ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : y ∉ (I).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_I, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : y ∉ ((Class.cv t)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : y ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0028 : y ∉ ((syn_wa (syn_wa ph (.classMem (.cv t) (syn_cnnc))) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_ph, fresh_y_ne_t, fresh_y_ne_a, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0029 : z ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0030 : z ∉ (I).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_I, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0031 : z ∉ ((Class.cv t)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0032 : z ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0033 : z ∉ ((syn_wa (syn_wa ph (.classMem (.cv t) (syn_cnnc))) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_ph, fresh_z_ne_t, fresh_z_ne_b, fresh_z_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0034 : z ∉ ((syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_t, fresh_z_ne_y, fresh_z_not_F, fresh_z_ne_a, fresh_z_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0035 : y ∉ ((syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_t, fresh_y_ne_z, fresh_y_not_F, fresh_y_ne_b, fresh_y_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0036 : y ∉ ((Wff.objEq a b)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_a, fresh_y_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0037 : z ∉ ((Wff.objEq a b)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_a, fresh_z_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0038 : a ∉ ((syn_wa ph (syn_wa (.classMem (.cv t) (syn_cnnc)) (.all y (.all z (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_ph, fresh_a_ne_t, fresh_a_ne_y, fresh_a_not_F, fresh_a_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0039 : b ∉ ((syn_wa ph (syn_wa (.classMem (.cv t) (syn_cnnc)) (.all y (.all z (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_ph, fresh_b_ne_t, fresh_b_ne_y, fresh_b_not_F, fresh_b_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0040 : w ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0041 : w ∉ ((Wff.all y (.all z (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_t, fresh_w_ne_y, fresh_w_not_F, fresh_w_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0042 : t ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0043 : t ∉ ((Wff.all y (.all z (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) (.objEq y z))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_w, fresh_t_ne_y, fresh_t_not_F, fresh_t_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0044 : w ∉ ((Wff.all y (.all z (.imp (syn_wa (syn_wbr (syn_c0c) F (.cv y)) (syn_wbr (syn_c0c) F (.cv z))) (.objEq y z))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_y, fresh_w_not_F, fresh_w_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0045 : w ∉ ((Wff.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) F (.cv y)) (syn_wbr (.cv x) F (.cv z))) (.objEq y z))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, fresh_w_not_F, fresh_w_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0046 : w ∉ ((Wff.all a (.all b (.imp (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a)) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b))) (.objEq a b))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_t, fresh_w_ne_a, fresh_w_not_F, fresh_w_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0047 : w ≠ t := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046
    exact (show w ≠ t from (by exact fresh_w_ne_t))
  have dv_cache_0048 : x ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0049 : x ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0050 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0051 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have p0000 :=
    @g_breldm (.cv x) (.cv y) F
  have p0001 :=
    @g_adantl (syn_wbr (.cv x) F (.cv y)) (.classMem (.cv x) (syn_cdm F)) ph p0000
  have p0002 :=
    @g_dmfrec ph F G I (syn_cfuns) hyp_fnfrec_1 hyp_fnfrec_2 hyp_fnfrec_3 hyp_fnfrec_4
  have p0003 :=
    @g_adantr ph (.classEq (syn_cdm F) (syn_cnnc)) (syn_wbr (.cv x) F (.cv y)) p0002
  have p0004 :=
    @g_eleqtrd (syn_wa ph (syn_wbr (.cv x) F (.cv y))) (.cv x) (syn_cdm F) (syn_cnnc) p0001 p0003
  have p0005 :=
    @g_adantrr ph (syn_wbr (.cv x) F (.cv y)) (.classMem (.cv x) (syn_cnnc)) (syn_wbr (.cv x) F (.cv z)) p0004
  have p0006 :=
    @g_frecexg F G I (syn_cfuns) hyp_fnfrec_1
  have p0007 :=
    @g_fnfreclem1 y z w F (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0008 :=
    @g_n_3syl ph (.classMem G (syn_cfuns)) (.classMem F (syn_cvv)) (.classMem (.cab w (.all y (.all z (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) (.objEq y z))))) (syn_cvv)) hyp_fnfrec_2 p0006 p0007
  have p0009 :=
    @g_breq1 (.cv w) (syn_c0c) (.cv y) F
  have p0010 :=
    @g_breq1 (.cv w) (syn_c0c) (.cv z) F
  have p0011 :=
    @g_anbi12d (.classEq (.cv w) (syn_c0c)) (syn_wbr (.cv w) F (.cv y)) (syn_wbr (syn_c0c) F (.cv y)) (syn_wbr (.cv w) F (.cv z)) (syn_wbr (syn_c0c) F (.cv z)) p0009 p0010
  have p0012 :=
    @g_imbi1d (.classEq (.cv w) (syn_c0c)) (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) (syn_wa (syn_wbr (syn_c0c) F (.cv y)) (syn_wbr (syn_c0c) F (.cv z))) (.objEq y z) p0011
  have p0013 :=
    @g_n_2albidv (.classEq (.cv w) (syn_c0c)) (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) (.objEq y z)) (.imp (syn_wa (syn_wbr (syn_c0c) F (.cv y)) (syn_wbr (syn_c0c) F (.cv z))) (.objEq y z)) y z dv_cache_0007 dv_cache_0008 p0012
  have p0014 :=
    @g_breq1 (.cv w) (.cv t) (.cv y) F
  have p0015 :=
    @g_breq1 (.cv w) (.cv t) (.cv z) F
  have p0016_e00_recanon : Nominal.NPrf (.imp (.objEq w t) (syn_wb (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv t) F (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0014
  have p0016_e01_recanon : Nominal.NPrf (.imp (.objEq w t) (syn_wb (syn_wbr (.cv w) F (.cv z)) (syn_wbr (.cv t) F (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0015
  have p0016 :=
    @g_anbi12d (.objEq w t) (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv w) F (.cv z)) (syn_wbr (.cv t) F (.cv z)) p0016_e00_recanon p0016_e01_recanon
  have p0017 :=
    @g_imbi1d (.objEq w t) (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z) p0016
  have p0018 :=
    @g_n_2albidv (.objEq w t) (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) (.objEq y z)) (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z)) y z dv_cache_0009 dv_cache_0010 p0017
  have p0019 :=
    @g_breq1 (.cv w) (syn_cplc (.cv t) (syn_c1c)) (.cv y) F
  have p0020 :=
    @g_breq1 (.cv w) (syn_cplc (.cv t) (syn_c1c)) (.cv z) F
  have p0021 :=
    @g_anbi12d (.classEq (.cv w) (syn_cplc (.cv t) (syn_c1c))) (syn_wbr (.cv w) F (.cv y)) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv y)) (syn_wbr (.cv w) F (.cv z)) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv z)) p0019 p0020
  have p0022 :=
    @g_imbi1d (.classEq (.cv w) (syn_cplc (.cv t) (syn_c1c))) (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv y)) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv z))) (.objEq y z) p0021
  have p0023 :=
    @g_n_2albidv (.classEq (.cv w) (syn_cplc (.cv t) (syn_c1c))) (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) (.objEq y z)) (.imp (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv y)) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv z))) (.objEq y z)) y z dv_cache_0011 dv_cache_0012 p0022
  have p0024 :=
    @g_breq2 (.cv y) (.cv a) (syn_cplc (.cv t) (syn_c1c)) F
  have p0025 :=
    @g_breq2 (.cv z) (.cv b) (syn_cplc (.cv t) (syn_c1c)) F
  have p0026_e00_recanon : Nominal.NPrf (.imp (.objEq y a) (syn_wb (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv y)) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_cplc syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0024
  have p0026_e01_recanon : Nominal.NPrf (.imp (.objEq z b) (syn_wb (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv z)) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_cplc syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0025
  have p0026 :=
    @g_bi2anan9 (.objEq y a) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv y)) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a)) (.objEq z b) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv z)) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b)) p0026_e00_recanon p0026_e01_recanon
  have p0027 :=
    @g_eqeq12 (.cv y) (.cv a) (.cv z) (.cv b)
  have p0028_e01_recanon : Nominal.NPrf (.imp (syn_wa (.objEq y a) (.objEq z b)) (syn_wb (.objEq y z) (.objEq a b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0027
  have p0028 :=
    @g_imbi12d (syn_wa (.objEq y a) (.objEq z b)) (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv y)) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv z))) (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a)) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b))) (.objEq y z) (.objEq a b) p0026 p0028_e01_recanon
  have p0029 :=
    @g_cbval2v (.imp (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv y)) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv z))) (.objEq y z)) (.imp (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a)) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b))) (.objEq a b)) y z a b dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0006 dv_cache_0019 p0028
  have p0030 :=
    @g_syl6bb (.classEq (.cv w) (syn_cplc (.cv t) (syn_c1c))) (.all y (.all z (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) (.objEq y z)))) (.all y (.all z (.imp (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv y)) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv z))) (.objEq y z)))) (.all a (.all b (.imp (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a)) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b))) (.objEq a b)))) p0023 p0029
  have p0031 :=
    @g_breq1 (.cv w) (.cv x) (.cv y) F
  have p0032 :=
    @g_breq1 (.cv w) (.cv x) (.cv z) F
  have p0033_e00_recanon : Nominal.NPrf (.imp (.objEq w x) (syn_wb (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv x) F (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0031
  have p0033_e01_recanon : Nominal.NPrf (.imp (.objEq w x) (syn_wb (syn_wbr (.cv w) F (.cv z)) (syn_wbr (.cv x) F (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0032
  have p0033 :=
    @g_anbi12d (.objEq w x) (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv x) F (.cv y)) (syn_wbr (.cv w) F (.cv z)) (syn_wbr (.cv x) F (.cv z)) p0033_e00_recanon p0033_e01_recanon
  have p0034 :=
    @g_imbi1d (.objEq w x) (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) (syn_wa (syn_wbr (.cv x) F (.cv y)) (syn_wbr (.cv x) F (.cv z))) (.objEq y z) p0033
  have p0035 :=
    @g_n_2albidv (.objEq w x) (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) (.objEq y z)) (.imp (syn_wa (syn_wbr (.cv x) F (.cv y)) (syn_wbr (.cv x) F (.cv z))) (.objEq y z)) y z dv_cache_0020 dv_cache_0021 p0034
  have p0036 :=
    @g_fnfreclem2 ph F G I (syn_cfuns) (.cv y) hyp_fnfrec_1 hyp_fnfrec_2 hyp_fnfrec_3 hyp_fnfrec_4
  have p0037 :=
    @g_imp ph (syn_wbr (syn_c0c) F (.cv y)) (.classEq (.cv y) I) p0036
  have p0038 :=
    @g_adantrr ph (syn_wbr (syn_c0c) F (.cv y)) (.classEq (.cv y) I) (syn_wbr (syn_c0c) F (.cv z)) p0037
  have p0039 :=
    @g_fnfreclem2 ph F G I (syn_cfuns) (.cv z) hyp_fnfrec_1 hyp_fnfrec_2 hyp_fnfrec_3 hyp_fnfrec_4
  have p0040 :=
    @g_imp ph (syn_wbr (syn_c0c) F (.cv z)) (.classEq (.cv z) I) p0039
  have p0041 :=
    @g_adantrl ph (syn_wbr (syn_c0c) F (.cv z)) (.classEq (.cv z) I) (syn_wbr (syn_c0c) F (.cv y)) p0040
  have p0042 :=
    @g_eqtr4d (syn_wa ph (syn_wa (syn_wbr (syn_c0c) F (.cv y)) (syn_wbr (syn_c0c) F (.cv z)))) (.cv y) I (.cv z) p0038 p0041
  have p0043_e00_recanon : Nominal.NPrf (.imp (syn_wa ph (syn_wa (syn_wbr (syn_c0c) F (.cv y)) (syn_wbr (syn_c0c) F (.cv z)))) (.objEq y z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0042
  have p0043 :=
    @g_ex ph (syn_wa (syn_wbr (syn_c0c) F (.cv y)) (syn_wbr (syn_c0c) F (.cv z))) (.objEq y z) p0043_e00_recanon
  have p0044 :=
    @g_alrimivv ph (.imp (syn_wa (syn_wbr (syn_c0c) F (.cv y)) (syn_wbr (syn_c0c) F (.cv z))) (.objEq y z)) y z dv_cache_0022 dv_cache_0023 p0043
  have p0045 :=
    @g_ad2antrr ph (.classMem G (syn_cfuns)) (.classMem (.cv t) (syn_cnnc)) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a)) hyp_fnfrec_2
  have p0046 :=
    @g_ad2antrr ph (.classMem I (syn_cdm G)) (.classMem (.cv t) (syn_cnnc)) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a)) hyp_fnfrec_3
  have p0047 :=
    @g_ad2antrr ph (syn_wss (syn_crn G) (syn_cdm G)) (.classMem (.cv t) (syn_cnnc)) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a)) hyp_fnfrec_4
  have p0048 :=
    @g_simplr ph (.classMem (.cv t) (syn_cnnc)) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a))
  have p0049 :=
    @g_simpr (syn_wa ph (.classMem (.cv t) (syn_cnnc))) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a))
  have p0050 :=
    @g_fnfreclem3 (syn_wa (syn_wa ph (.classMem (.cv t) (syn_cnnc))) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a))) y F G I (syn_cfuns) (.cv t) (.cv a) dv_cache_0002 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 hyp_fnfrec_1 p0045 p0046 p0047 p0048 p0049
  have p0051 :=
    @g_adantlrr ph (.classMem (.cv t) (syn_cnnc)) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a)) (syn_wex y (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a)))) (.all y (.all z (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z)))) p0050
  have p0052 :=
    @g_ex (syn_wa ph (syn_wa (.classMem (.cv t) (syn_cnnc)) (.all y (.all z (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z)))))) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a)) (syn_wex y (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a)))) p0051
  have p0053 :=
    @g_ad2antrr ph (.classMem G (syn_cfuns)) (.classMem (.cv t) (syn_cnnc)) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b)) hyp_fnfrec_2
  have p0054 :=
    @g_ad2antrr ph (.classMem I (syn_cdm G)) (.classMem (.cv t) (syn_cnnc)) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b)) hyp_fnfrec_3
  have p0055 :=
    @g_ad2antrr ph (syn_wss (syn_crn G) (syn_cdm G)) (.classMem (.cv t) (syn_cnnc)) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b)) hyp_fnfrec_4
  have p0056 :=
    @g_simplr ph (.classMem (.cv t) (syn_cnnc)) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b))
  have p0057 :=
    @g_simpr (syn_wa ph (.classMem (.cv t) (syn_cnnc))) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b))
  have p0058 :=
    @g_fnfreclem3 (syn_wa (syn_wa ph (.classMem (.cv t) (syn_cnnc))) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b))) z F G I (syn_cfuns) (.cv t) (.cv b) dv_cache_0003 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 hyp_fnfrec_1 p0053 p0054 p0055 p0056 p0057
  have p0059 :=
    @g_adantlrr ph (.classMem (.cv t) (syn_cnnc)) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b)) (syn_wex z (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b)))) (.all y (.all z (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z)))) p0058
  have p0060 :=
    @g_ex (syn_wa ph (syn_wa (.classMem (.cv t) (syn_cnnc)) (.all y (.all z (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z)))))) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b)) (syn_wex z (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b)))) p0059
  have p0061 :=
    @g_anim12d (syn_wa ph (syn_wa (.classMem (.cv t) (syn_cnnc)) (.all y (.all z (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z)))))) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a)) (syn_wex y (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a)))) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b)) (syn_wex z (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b)))) p0052 p0060
  have p0062 :=
    @g_eeanv (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a))) (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b))) y z dv_cache_0034 dv_cache_0035
  have p0063 :=
    @g_syl6ibr (syn_wa ph (syn_wa (.classMem (.cv t) (syn_cnnc)) (.all y (.all z (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z)))))) (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a)) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b))) (syn_wa (syn_wex y (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a)))) (syn_wex z (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b))))) (syn_wex y (syn_wex z (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a))) (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b)))))) p0061 p0062
  have p0064 :=
    @g_n_19_29 (.all z (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z))) (syn_wex z (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a))) (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b))))) y
  have p0065 :=
    @g_n_19_29 (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z)) (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a))) (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b)))) z
  have p0066 :=
    @g_eximi (syn_wa (.all z (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z))) (syn_wex z (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a))) (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b)))))) (syn_wex z (syn_wa (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z)) (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a))) (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b)))))) y p0065
  have p0067 :=
    @g_syl (syn_wa (.all y (.all z (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z)))) (syn_wex y (syn_wex z (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a))) (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b))))))) (syn_wex y (syn_wa (.all z (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z))) (syn_wex z (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a))) (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b))))))) (syn_wex y (syn_wex z (syn_wa (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z)) (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a))) (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b))))))) p0064 p0066
  have p0068 :=
    @g_pm3_35 (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z)
  have p0069 :=
    @g_breq1 (.cv y) (.cv z) (.cv a) G
  have p0070_e00_recanon : Nominal.NPrf (.imp (.objEq y z) (syn_wb (syn_wbr (.cv y) G (.cv a)) (syn_wbr (.cv z) G (.cv a)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0069
  have p0070 :=
    @g_anbi1d (.objEq y z) (syn_wbr (.cv y) G (.cv a)) (syn_wbr (.cv z) G (.cv a)) (syn_wbr (.cv z) G (.cv b)) p0070_e00_recanon
  have p0071 :=
    @g_biimpa (.objEq y z) (syn_wa (syn_wbr (.cv y) G (.cv a)) (syn_wbr (.cv z) G (.cv b))) (syn_wa (syn_wbr (.cv z) G (.cv a)) (syn_wbr (.cv z) G (.cv b))) p0070
  have p0072 :=
    @g_elfunsi G
  have p0073 :=
    @g_funbrfv (.cv z) (.cv a) G
  have p0074 :=
    @g_n_3syl ph (.classMem G (syn_cfuns)) (syn_wfun G) (.imp (syn_wbr (.cv z) G (.cv a)) (.classEq (syn_cfv G (.cv z)) (.cv a))) hyp_fnfrec_2 p0072 p0073
  have p0075 :=
    @g_funbrfv (.cv z) (.cv b) G
  have p0076 :=
    @g_n_3syl ph (.classMem G (syn_cfuns)) (syn_wfun G) (.imp (syn_wbr (.cv z) G (.cv b)) (.classEq (syn_cfv G (.cv z)) (.cv b))) hyp_fnfrec_2 p0072 p0075
  have p0077 :=
    @g_anim12d ph (syn_wbr (.cv z) G (.cv a)) (.classEq (syn_cfv G (.cv z)) (.cv a)) (syn_wbr (.cv z) G (.cv b)) (.classEq (syn_cfv G (.cv z)) (.cv b)) p0074 p0076
  have p0078 :=
    @g_eqtr2 (syn_cfv G (.cv z)) (.cv a) (.cv b)
  have p0079_e02_recanon : Nominal.NPrf (.imp (syn_wa (.classEq (syn_cfv G (.cv z)) (.cv a)) (.classEq (syn_cfv G (.cv z)) (.cv b))) (.objEq a b)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cfv syn_cio syn_cuni syn_wex syn_csn syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0078
  have p0079 :=
    @g_syl56 (syn_wa (.objEq y z) (syn_wa (syn_wbr (.cv y) G (.cv a)) (syn_wbr (.cv z) G (.cv b)))) (syn_wa (syn_wbr (.cv z) G (.cv a)) (syn_wbr (.cv z) G (.cv b))) ph (syn_wa (.classEq (syn_cfv G (.cv z)) (.cv a)) (.classEq (syn_cfv G (.cv z)) (.cv b))) (.objEq a b) p0071 p0077 p0079_e02_recanon
  have p0080 :=
    @g_exp3a ph (.objEq y z) (syn_wa (syn_wbr (.cv y) G (.cv a)) (syn_wbr (.cv z) G (.cv b))) (.objEq a b) p0079
  have p0081 :=
    @g_syl5 (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z))) (.objEq y z) ph (.imp (syn_wa (syn_wbr (.cv y) G (.cv a)) (syn_wbr (.cv z) G (.cv b))) (.objEq a b)) p0068 p0080
  have p0082 :=
    @g_exp3a ph (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z)) (.imp (syn_wa (syn_wbr (.cv y) G (.cv a)) (syn_wbr (.cv z) G (.cv b))) (.objEq a b)) p0081
  have p0083 :=
    @g_com34 ph (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z)) (syn_wa (syn_wbr (.cv y) G (.cv a)) (syn_wbr (.cv z) G (.cv b))) (.objEq a b) p0082
  have p0084 :=
    @g_imp3a ph (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (syn_wa (syn_wbr (.cv y) G (.cv a)) (syn_wbr (.cv z) G (.cv b))) (.imp (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z)) (.objEq a b)) p0083
  have p0085 :=
    @g_com12 ph (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (syn_wa (syn_wbr (.cv y) G (.cv a)) (syn_wbr (.cv z) G (.cv b)))) (.imp (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z)) (.objEq a b)) p0084
  have p0086 :=
    @g_an4s (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv y) G (.cv a)) (syn_wbr (.cv z) G (.cv b)) (.imp ph (.imp (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z)) (.objEq a b))) p0085
  have p0087 :=
    @g_com3l (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a))) (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b)))) ph (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z)) (.objEq a b) p0086
  have p0088 :=
    @g_imp3a ph (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z)) (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a))) (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b)))) (.objEq a b) p0087
  have p0089 :=
    @g_exlimdvv ph (syn_wa (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z)) (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a))) (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b))))) (.objEq a b) y z dv_cache_0036 dv_cache_0037 dv_cache_0022 dv_cache_0023 p0088
  have p0090 :=
    @g_adantr ph (.imp (syn_wex y (syn_wex z (syn_wa (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z)) (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a))) (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b))))))) (.objEq a b)) (.classMem (.cv t) (syn_cnnc)) p0089
  have p0091 :=
    @g_syl5 (syn_wa (.all y (.all z (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z)))) (syn_wex y (syn_wex z (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a))) (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b))))))) (syn_wex y (syn_wex z (syn_wa (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z)) (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a))) (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b))))))) (syn_wa ph (.classMem (.cv t) (syn_cnnc))) (.objEq a b) p0067 p0090
  have p0092 :=
    @g_exp3a (syn_wa ph (.classMem (.cv t) (syn_cnnc))) (.all y (.all z (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z)))) (syn_wex y (syn_wex z (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a))) (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b)))))) (.objEq a b) p0091
  have p0093 :=
    @g_impr ph (.classMem (.cv t) (syn_cnnc)) (.all y (.all z (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z)))) (.imp (syn_wex y (syn_wex z (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a))) (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b)))))) (.objEq a b)) p0092
  have p0094 :=
    @g_syld (syn_wa ph (syn_wa (.classMem (.cv t) (syn_cnnc)) (.all y (.all z (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z)))))) (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a)) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b))) (syn_wex y (syn_wex z (syn_wa (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv y) G (.cv a))) (syn_wa (syn_wbr (.cv t) F (.cv z)) (syn_wbr (.cv z) G (.cv b)))))) (.objEq a b) p0063 p0093
  have p0095 :=
    @g_alrimivv (syn_wa ph (syn_wa (.classMem (.cv t) (syn_cnnc)) (.all y (.all z (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z)))))) (.imp (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a)) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b))) (.objEq a b)) a b dv_cache_0038 dv_cache_0039 p0094
  have p0096 :=
    @g_expr ph (.classMem (.cv t) (syn_cnnc)) (.all y (.all z (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z)))) (.all a (.all b (.imp (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a)) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b))) (.objEq a b)))) p0095
  have p0097 :=
    @g_ancoms ph (.classMem (.cv t) (syn_cnnc)) (.imp (.all y (.all z (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z)))) (.all a (.all b (.imp (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a)) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b))) (.objEq a b))))) p0096
  have p0098_e04_recanon : Nominal.NPrf (.imp (.classEq (.cv w) (.cv x)) (syn_wb (.all y (.all z (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) (.objEq y z)))) (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) F (.cv y)) (syn_wbr (.cv x) F (.cv z))) (.objEq y z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0035
  have p0098 :=
    @g_findsd (.all y (.all z (.imp (syn_wa (syn_wbr (.cv w) F (.cv y)) (syn_wbr (.cv w) F (.cv z))) (.objEq y z)))) (.all y (.all z (.imp (syn_wa (syn_wbr (syn_c0c) F (.cv y)) (syn_wbr (syn_c0c) F (.cv z))) (.objEq y z)))) (.all y (.all z (.imp (syn_wa (syn_wbr (.cv t) F (.cv y)) (syn_wbr (.cv t) F (.cv z))) (.objEq y z)))) (.all a (.all b (.imp (syn_wa (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv a)) (syn_wbr (syn_cplc (.cv t) (syn_c1c)) F (.cv b))) (.objEq a b)))) (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) F (.cv y)) (syn_wbr (.cv x) F (.cv z))) (.objEq y z)))) ph w t (.cv x) (syn_cvv) dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 p0008 p0013 p0018 p0030 p0098_e04_recanon p0044 p0097
  have p0099 :=
    @g_n_19_21bbi (syn_wa (.classMem (.cv x) (syn_cnnc)) ph) (.imp (syn_wa (syn_wbr (.cv x) F (.cv y)) (syn_wbr (.cv x) F (.cv z))) (.objEq y z)) y z p0098
  have p0100 :=
    @g_ex (.classMem (.cv x) (syn_cnnc)) ph (.imp (syn_wa (syn_wbr (.cv x) F (.cv y)) (syn_wbr (.cv x) F (.cv z))) (.objEq y z)) p0099
  have p0101 :=
    @g_imp3a (.classMem (.cv x) (syn_cnnc)) ph (syn_wa (syn_wbr (.cv x) F (.cv y)) (syn_wbr (.cv x) F (.cv z))) (.objEq y z) p0100
  have p0102 :=
    @g_mpcom (.classMem (.cv x) (syn_cnnc)) (syn_wa ph (syn_wa (syn_wbr (.cv x) F (.cv y)) (syn_wbr (.cv x) F (.cv z)))) (.objEq y z) p0005 p0101
  have p0103 :=
    @g_ex ph (syn_wa (syn_wbr (.cv x) F (.cv y)) (syn_wbr (.cv x) F (.cv z))) (.objEq y z) p0102
  have p0104 :=
    @g_alrimivv ph (.imp (syn_wa (syn_wbr (.cv x) F (.cv y)) (syn_wbr (.cv x) F (.cv z))) (.objEq y z)) y z dv_cache_0022 dv_cache_0023 p0103
  have p0105 :=
    @g_alrimiv ph (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) F (.cv y)) (syn_wbr (.cv x) F (.cv z))) (.objEq y z)))) x dv_cache_0048 p0104
  have p0106 :=
    @g_dffun2 x y z F dv_cache_0049 dv_cache_0002 dv_cache_0003 dv_cache_0050 dv_cache_0051 dv_cache_0006
  have p0107 :=
    @g_sylibr ph (.all x (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) F (.cv y)) (syn_wbr (.cv x) F (.cv z))) (.objEq y z))))) (syn_wfun F) p0105 p0106
  have p0108 :=
    (by simpa [syn_wb, syn_wfn] using (Nominal.biimpRefl (syn_wfn F (syn_cnnc))))
  have p0109 :=
    @g_sylanbrc ph (syn_wfun F) (.classEq (syn_cdm F) (syn_cnnc)) (syn_wfn F (syn_cnnc)) p0107 p0002 p0108
  exact p0109

#print axioms g_fnfrec

end NFChoice.DirectNominalPrf.WPPReplay
