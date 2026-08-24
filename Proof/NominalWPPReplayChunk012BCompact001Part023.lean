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
import NominalWPPReplayChunk012BCompact001Part022

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

noncomputable def g_oqelins4
    (A : Class) (B : Class) (C : Class) (D : Class) (R : Class) (hyp_oqelins4_4 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem (syn_cop A (syn_cop B (syn_cop C D))) (syn_cins4 R)) (.classMem (syn_cop A (syn_cop B C)) R)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let p : Var := freshVar proofSupport 3
  let b : Var := freshVar proofSupport 4
  let a : Var := freshVar proofSupport 5
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_p_not_B : p ∉ B.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_p_not_C : p ∉ C.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_p_not_D : p ∉ D.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_not_R : p ∉ R.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_b_not_C : b ∉ C.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_b_not_D : b ∉ D.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_not_R : b ∉ R.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_a_not_C : a ∉ C.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a_not_D : a ∉ D.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
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
  have fresh_x_ne_p : x ≠ p := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_p_ne_x : p ≠ x :=
    Ne.symm fresh_x_ne_p
  have fresh_x_ne_b : x ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_b_ne_x : b ≠ x :=
    Ne.symm fresh_x_ne_b
  have fresh_x_ne_a : x ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_a_ne_x : a ≠ x :=
    Ne.symm fresh_x_ne_a
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_y_ne_p : y ≠ p := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_p_ne_y : p ≠ y :=
    Ne.symm fresh_y_ne_p
  have fresh_y_ne_b : y ≠ b := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_b_ne_y : b ≠ y :=
    Ne.symm fresh_y_ne_b
  have fresh_y_ne_a : y ≠ a := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_a_ne_y : a ≠ y :=
    Ne.symm fresh_y_ne_a
  have fresh_z_ne_p : z ≠ p := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_p_ne_z : p ≠ z :=
    Ne.symm fresh_z_ne_p
  have fresh_z_ne_b : z ≠ b := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_b_ne_z : b ≠ z :=
    Ne.symm fresh_z_ne_b
  have fresh_z_ne_a : z ≠ a := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_a_ne_z : a ≠ z :=
    Ne.symm fresh_z_ne_a
  have fresh_p_ne_b : p ≠ b := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_b_ne_p : b ≠ p :=
    Ne.symm fresh_p_ne_b
  have fresh_p_ne_a : p ≠ a := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_a_ne_p : a ≠ p :=
    Ne.symm fresh_p_ne_a
  have fresh_b_ne_a : b ≠ a := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_a_ne_b : a ≠ b :=
    Ne.symm fresh_b_ne_a
  have dv_cache_0001 : a ∉ ((syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))).fv := by
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_x, fresh_a_ne_y, fresh_a_ne_z, fresh_a_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : b ∉ ((syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_x, fresh_b_ne_y, fresh_b_ne_z, fresh_b_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : a ∉ ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : b ∉ ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : a ∉ ((syn_c1st)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : b ∉ ((syn_c1st)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : a ∉ ((syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : b ∉ ((syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : a ≠ b := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0010 : b ∉ ((Wff.objEq a x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_a, fresh_b_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : a ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : a ∉ ((syn_wex b (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv b))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_p, fresh_a_ne_x, fresh_a_ne_b, fresh_a_ne_y, fresh_a_ne_z, fresh_a_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : p ∉ ((syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_x, fresh_p_ne_y, fresh_p_ne_z, fresh_p_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : p ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : a ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : p ∉ ((syn_ccom (syn_c1st) (syn_c2nd))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : a ∉ ((syn_ccom (syn_c1st) (syn_c2nd))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : p ∉ ((syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : a ∉ ((syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : p ≠ a := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (show p ≠ a from (by exact fresh_p_ne_a))
  have dv_cache_0021 : p ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : a ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : p ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : a ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : a ∉ ((Wff.classEq (.cv b) (syn_cop (.cv y) (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_b, fresh_a_ne_y, fresh_a_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : p ∉ ((Wff.classEq (.cv b) (syn_cop (.cv y) (.cv a)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_b, fresh_p_ne_y, fresh_p_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : b ∉ ((syn_cop (.cv y) (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_y, fresh_b_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0028 : b ∉ ((Wff.classEq (.cv p) (syn_cop (.cv x) (syn_cop (.cv y) (.cv z))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_p, fresh_b_ne_x, fresh_b_ne_y, fresh_b_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0029 : p ∉ ((syn_ccnv (syn_ctxp (syn_c1st) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0030 : p ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0031 : p ∉ ((syn_cop (.cv x) (syn_cop (.cv y) (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_x, fresh_p_ne_y, fresh_p_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0032 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0033 : z ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0034 : z ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0035 : z ∉ ((syn_wb (.classMem (syn_cop (.cv x) (syn_cop B (syn_cop C D))) (syn_cins4 R)) (.classMem (syn_cop (.cv x) (syn_cop B C)) R))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_B, fresh_z_not_C, fresh_z_not_D, fresh_z_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0036 : y ∉ ((syn_wb (.classMem (syn_cop (.cv x) (syn_cop B (syn_cop (.cv z) D))) (syn_cins4 R)) (.classMem (syn_cop (.cv x) (syn_cop B (.cv z))) R))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_B, fresh_y_ne_z, fresh_y_not_D, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0037 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0038 : x ∉ ((Wff.imp (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (syn_wb (.classMem (syn_cop A (syn_cop B (syn_cop C D))) (syn_cins4 R)) (.classMem (syn_cop A (syn_cop B C)) R)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, fresh_x_not_C, fresh_x_not_A, fresh_x_not_D, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elex (syn_cop A (syn_cop B (syn_cop C D))) (syn_cins4 R)
  have p0001 :=
    @g_opexb A (syn_cop B (syn_cop C D))
  have p0002 :=
    @g_opexb B (syn_cop C D)
  have p0003 :=
    @g_anbi2i (.classMem (syn_cop B (syn_cop C D)) (syn_cvv)) (syn_wa (.classMem B (syn_cvv)) (.classMem (syn_cop C D) (syn_cvv))) (.classMem A (syn_cvv)) p0002
  have p0004 :=
    @g_bitri (.classMem (syn_cop A (syn_cop B (syn_cop C D))) (syn_cvv)) (syn_wa (.classMem A (syn_cvv)) (.classMem (syn_cop B (syn_cop C D)) (syn_cvv))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem B (syn_cvv)) (.classMem (syn_cop C D) (syn_cvv)))) p0001 p0003
  have p0005 :=
    @g_opexb C D
  have p0006 :=
    @g_simplbi (.classMem (syn_cop C D) (syn_cvv)) (.classMem C (syn_cvv)) (.classMem D (syn_cvv)) p0005
  have p0007 :=
    @g_anim2i (.classMem (syn_cop C D) (syn_cvv)) (.classMem C (syn_cvv)) (.classMem B (syn_cvv)) p0006
  have p0008 :=
    @g_anim2i (syn_wa (.classMem B (syn_cvv)) (.classMem (syn_cop C D) (syn_cvv))) (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (.classMem A (syn_cvv)) p0007
  have p0009 :=
    @g_sylbi (.classMem (syn_cop A (syn_cop B (syn_cop C D))) (syn_cvv)) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem B (syn_cvv)) (.classMem (syn_cop C D) (syn_cvv)))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))) p0004 p0008
  have p0010 :=
    @g_syl (.classMem (syn_cop A (syn_cop B (syn_cop C D))) (syn_cins4 R)) (.classMem (syn_cop A (syn_cop B (syn_cop C D))) (syn_cvv)) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))) p0000 p0009
  have p0011 :=
    @g_elex (syn_cop A (syn_cop B C)) R
  have p0012 :=
    @g_opexb A (syn_cop B C)
  have p0013 :=
    @g_opexb B C
  have p0014 :=
    @g_anbi2i (.classMem (syn_cop B C) (syn_cvv)) (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (.classMem A (syn_cvv)) p0013
  have p0015 :=
    @g_bitri (.classMem (syn_cop A (syn_cop B C)) (syn_cvv)) (syn_wa (.classMem A (syn_cvv)) (.classMem (syn_cop B C) (syn_cvv))) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))) p0012 p0014
  have p0016 :=
    @g_sylib (.classMem (syn_cop A (syn_cop B C)) R) (.classMem (syn_cop A (syn_cop B C)) (syn_cvv)) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))) p0011 p0015
  have p0017 :=
    @g_opeq1 (.cv x) A (syn_cop B (syn_cop C D))
  have p0018 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_cop (.cv x) (syn_cop B (syn_cop C D))) (syn_cop A (syn_cop B (syn_cop C D))) (syn_cins4 R) p0017
  have p0019 :=
    @g_opeq1 (.cv x) A (syn_cop B C)
  have p0020 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_cop (.cv x) (syn_cop B C)) (syn_cop A (syn_cop B C)) R p0019
  have p0021 :=
    @g_bibi12d (.classEq (.cv x) A) (.classMem (syn_cop (.cv x) (syn_cop B (syn_cop C D))) (syn_cins4 R)) (.classMem (syn_cop A (syn_cop B (syn_cop C D))) (syn_cins4 R)) (.classMem (syn_cop (.cv x) (syn_cop B C)) R) (.classMem (syn_cop A (syn_cop B C)) R) p0018 p0020
  have p0022 :=
    @g_imbi2d (.classEq (.cv x) A) (syn_wb (.classMem (syn_cop (.cv x) (syn_cop B (syn_cop C D))) (syn_cins4 R)) (.classMem (syn_cop (.cv x) (syn_cop B C)) R)) (syn_wb (.classMem (syn_cop A (syn_cop B (syn_cop C D))) (syn_cins4 R)) (.classMem (syn_cop A (syn_cop B C)) R)) (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) p0021
  have p0023 :=
    @g_opeq1 (.cv y) B (syn_cop (.cv z) D)
  have p0024 :=
    @g_opeq2d (.classEq (.cv y) B) (syn_cop (.cv y) (syn_cop (.cv z) D)) (syn_cop B (syn_cop (.cv z) D)) (.cv x) p0023
  have p0025 :=
    @g_eleq1d (.classEq (.cv y) B) (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_cop (.cv x) (syn_cop B (syn_cop (.cv z) D))) (syn_cins4 R) p0024
  have p0026 :=
    @g_opeq1 (.cv y) B (.cv z)
  have p0027 :=
    @g_opeq2d (.classEq (.cv y) B) (syn_cop (.cv y) (.cv z)) (syn_cop B (.cv z)) (.cv x) p0026
  have p0028 :=
    @g_eleq1d (.classEq (.cv y) B) (syn_cop (.cv x) (syn_cop (.cv y) (.cv z))) (syn_cop (.cv x) (syn_cop B (.cv z))) R p0027
  have p0029 :=
    @g_bibi12d (.classEq (.cv y) B) (.classMem (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_cins4 R)) (.classMem (syn_cop (.cv x) (syn_cop B (syn_cop (.cv z) D))) (syn_cins4 R)) (.classMem (syn_cop (.cv x) (syn_cop (.cv y) (.cv z))) R) (.classMem (syn_cop (.cv x) (syn_cop B (.cv z))) R) p0025 p0028
  have p0030 :=
    @g_opeq1 (.cv z) C D
  have p0031 :=
    @g_opeq2d (.classEq (.cv z) C) (syn_cop (.cv z) D) (syn_cop C D) B p0030
  have p0032 :=
    @g_opeq2d (.classEq (.cv z) C) (syn_cop B (syn_cop (.cv z) D)) (syn_cop B (syn_cop C D)) (.cv x) p0031
  have p0033 :=
    @g_eleq1d (.classEq (.cv z) C) (syn_cop (.cv x) (syn_cop B (syn_cop (.cv z) D))) (syn_cop (.cv x) (syn_cop B (syn_cop C D))) (syn_cins4 R) p0032
  have p0034 :=
    @g_opeq2 (.cv z) C B
  have p0035 :=
    @g_opeq2d (.classEq (.cv z) C) (syn_cop B (.cv z)) (syn_cop B C) (.cv x) p0034
  have p0036 :=
    @g_eleq1d (.classEq (.cv z) C) (syn_cop (.cv x) (syn_cop B (.cv z))) (syn_cop (.cv x) (syn_cop B C)) R p0035
  have p0037 :=
    @g_bibi12d (.classEq (.cv z) C) (.classMem (syn_cop (.cv x) (syn_cop B (syn_cop (.cv z) D))) (syn_cins4 R)) (.classMem (syn_cop (.cv x) (syn_cop B (syn_cop C D))) (syn_cins4 R)) (.classMem (syn_cop (.cv x) (syn_cop B (.cv z))) R) (.classMem (syn_cop (.cv x) (syn_cop B C)) R) p0033 p0036
  have p0038 :=
    (by simpa [syn_cins4] using (Nominal.classEqRefl (syn_cins4 R)))
  have p0039 :=
    @g_eleq2i (syn_cins4 R) (syn_cima (syn_ccnv (syn_ctxp (syn_c1st) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))))) R) (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) p0038
  have p0040 :=
    @g_brcnv (.cv p) (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_c1st) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))))
  have p0041 :=
    @g_brtxp a b (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (.cv p) (syn_c1st) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0042 :=
    @g_n_3ancoma (.classEq (.cv p) (syn_cop (.cv a) (.cv b))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_c1st) (.cv a)) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))
  have p0043 :=
    @g_n_3anass (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_c1st) (.cv a)) (.classEq (.cv p) (syn_cop (.cv a) (.cv b))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))
  have p0044 :=
    @g_vex x
  have p0045 :=
    @g_vex y
  have p0046 :=
    @g_vex z
  have p0047 :=
    @g_opex (.cv z) D p0046 hyp_oqelins4_4
  have p0048 :=
    @g_opex (.cv y) (syn_cop (.cv z) D) p0045 p0047
  have p0049 :=
    @g_opbr1st (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)) (.cv a) p0044 p0048
  have p0050 :=
    @g_equcom x a
  have p0051_e00_recanon : Nominal.NPrf (syn_wb (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_c1st) (.cv a)) (.objEq x a)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_c1st syn_copab
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
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
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0049
  have p0051 :=
    @g_bitri (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_c1st) (.cv a)) (.objEq x a) (.objEq a x) p0051_e00_recanon p0050
  have p0052 :=
    @g_anbi1i (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_c1st) (.cv a)) (.objEq a x) (syn_wa (.classEq (.cv p) (syn_cop (.cv a) (.cv b))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))) p0051
  have p0053 :=
    @g_n_3bitri (syn_w3a (.classEq (.cv p) (syn_cop (.cv a) (.cv b))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_c1st) (.cv a)) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))) (syn_w3a (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_c1st) (.cv a)) (.classEq (.cv p) (syn_cop (.cv a) (.cv b))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))) (syn_wa (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_c1st) (.cv a)) (syn_wa (.classEq (.cv p) (syn_cop (.cv a) (.cv b))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b)))) (syn_wa (.objEq a x) (syn_wa (.classEq (.cv p) (syn_cop (.cv a) (.cv b))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b)))) p0042 p0043 p0052
  have p0054 :=
    @g_exbii (syn_w3a (.classEq (.cv p) (syn_cop (.cv a) (.cv b))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_c1st) (.cv a)) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))) (syn_wa (.objEq a x) (syn_wa (.classEq (.cv p) (syn_cop (.cv a) (.cv b))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b)))) b p0053
  have p0055 :=
    @g_n_19_42v (.objEq a x) (syn_wa (.classEq (.cv p) (syn_cop (.cv a) (.cv b))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))) b dv_cache_0010
  have p0056 :=
    @g_bitri (syn_wex b (syn_w3a (.classEq (.cv p) (syn_cop (.cv a) (.cv b))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_c1st) (.cv a)) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b)))) (syn_wex b (syn_wa (.objEq a x) (syn_wa (.classEq (.cv p) (syn_cop (.cv a) (.cv b))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))))) (syn_wa (.objEq a x) (syn_wex b (syn_wa (.classEq (.cv p) (syn_cop (.cv a) (.cv b))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))))) p0054 p0055
  have p0057 :=
    @g_exbii (syn_wex b (syn_w3a (.classEq (.cv p) (syn_cop (.cv a) (.cv b))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_c1st) (.cv a)) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b)))) (syn_wa (.objEq a x) (syn_wex b (syn_wa (.classEq (.cv p) (syn_cop (.cv a) (.cv b))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))))) a p0056
  have p0058 :=
    @g_opeq1 (.cv a) (.cv x) (.cv b)
  have p0059_e00_recanon : Nominal.NPrf (.imp (.objEq a x) (.classEq (syn_cop (.cv a) (.cv b)) (syn_cop (.cv x) (.cv b)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0058
  have p0059 :=
    @g_eqeq2d (.objEq a x) (syn_cop (.cv a) (.cv b)) (syn_cop (.cv x) (.cv b)) (.cv p) p0059_e00_recanon
  have p0060 :=
    @g_anbi1d (.objEq a x) (.classEq (.cv p) (syn_cop (.cv a) (.cv b))) (.classEq (.cv p) (syn_cop (.cv x) (.cv b))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b)) p0059
  have p0061 :=
    @g_exbidv (.objEq a x) (syn_wa (.classEq (.cv p) (syn_cop (.cv a) (.cv b))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))) (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv b))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))) b dv_cache_0010 p0060
  have p0062_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv a) (.cv x)) (syn_wb (syn_wex b (syn_wa (.classEq (.cv p) (syn_cop (.cv a) (.cv b))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b)))) (syn_wex b (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv b))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_wa syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex syn_cphi syn_wbr syn_ctxp syn_cin syn_ccom syn_copab syn_ccnv syn_c1st
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0061
  have p0062 :=
    @g_ceqsexv (syn_wex b (syn_wa (.classEq (.cv p) (syn_cop (.cv a) (.cv b))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b)))) (syn_wex b (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv b))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b)))) a (.cv x) dv_cache_0011 dv_cache_0012 p0044 p0062_e01_recanon
  have p0063_e02_recanon : Nominal.NPrf (syn_wb (syn_wex a (syn_wa (.objEq a x) (syn_wex b (syn_wa (.classEq (.cv p) (syn_cop (.cv a) (.cv b))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b)))))) (syn_wex b (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv b))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
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
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0062
  have p0063 :=
    @g_n_3bitri (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_c1st) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd)))) (.cv p)) (syn_wex a (syn_wex b (syn_w3a (.classEq (.cv p) (syn_cop (.cv a) (.cv b))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_c1st) (.cv a)) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))))) (syn_wex a (syn_wa (.objEq a x) (syn_wex b (syn_wa (.classEq (.cv p) (syn_cop (.cv a) (.cv b))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b)))))) (syn_wex b (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv b))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b)))) p0041 p0057 p0063_e02_recanon
  have p0064 :=
    @g_ancom (.classEq (.cv p) (syn_cop (.cv x) (.cv b))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))
  have p0065 :=
    @g_brtxp p a (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (.cv b) (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd)) dv_cache_0013 dv_cache_0001 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
  have p0066 :=
    @g_n_3anrot (.classEq (.cv b) (syn_cop (.cv p) (.cv a))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ccom (syn_c1st) (syn_c2nd)) (.cv p)) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd)) (.cv a))
  have p0067 :=
    @g_brco2nd (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)) (.cv p) (syn_c1st) p0044 p0048
  have p0068 :=
    @g_opbr1st (.cv y) (syn_cop (.cv z) D) (.cv p) p0045 p0047
  have p0069 :=
    @g_equcom y p
  have p0070_e01_recanon : Nominal.NPrf (syn_wb (syn_wbr (syn_cop (.cv y) (syn_cop (.cv z) D)) (syn_c1st) (.cv p)) (.objEq y p)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_c1st syn_copab
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
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
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0068
  have p0070 :=
    @g_n_3bitri (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ccom (syn_c1st) (syn_c2nd)) (.cv p)) (syn_wbr (syn_cop (.cv y) (syn_cop (.cv z) D)) (syn_c1st) (.cv p)) (.objEq y p) (.objEq p y) p0067 p0070_e01_recanon p0069
  have p0071 :=
    @g_brco2nd (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)) (.cv a) (syn_ccom (syn_c1st) (syn_c2nd)) p0044 p0048
  have p0072 :=
    @g_brco2nd (.cv y) (syn_cop (.cv z) D) (.cv a) (syn_c1st) p0045 p0047
  have p0073 :=
    @g_opbr1st (.cv z) D (.cv a) p0046 hyp_oqelins4_4
  have p0074_e01_recanon : Nominal.NPrf (syn_wb (syn_wbr (syn_cop (.cv z) D) (syn_c1st) (.cv a)) (.objEq z a)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_c1st syn_copab
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
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
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0073
  have p0074 :=
    @g_bitri (syn_wbr (syn_cop (.cv y) (syn_cop (.cv z) D)) (syn_ccom (syn_c1st) (syn_c2nd)) (.cv a)) (syn_wbr (syn_cop (.cv z) D) (syn_c1st) (.cv a)) (.objEq z a) p0072 p0074_e01_recanon
  have p0075 :=
    @g_equcom z a
  have p0076 :=
    @g_n_3bitri (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd)) (.cv a)) (syn_wbr (syn_cop (.cv y) (syn_cop (.cv z) D)) (syn_ccom (syn_c1st) (syn_c2nd)) (.cv a)) (.objEq z a) (.objEq a z) p0071 p0074 p0075
  have p0077 :=
    @g_biid (.classEq (.cv b) (syn_cop (.cv p) (.cv a)))
  have p0078 :=
    @g_n_3anbi123i (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ccom (syn_c1st) (syn_c2nd)) (.cv p)) (.objEq p y) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd)) (.cv a)) (.objEq a z) (.classEq (.cv b) (syn_cop (.cv p) (.cv a))) (.classEq (.cv b) (syn_cop (.cv p) (.cv a))) p0070 p0076 p0077
  have p0079 :=
    @g_bitri (syn_w3a (.classEq (.cv b) (syn_cop (.cv p) (.cv a))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ccom (syn_c1st) (syn_c2nd)) (.cv p)) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd)) (.cv a))) (syn_w3a (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ccom (syn_c1st) (syn_c2nd)) (.cv p)) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd)) (.cv a)) (.classEq (.cv b) (syn_cop (.cv p) (.cv a)))) (syn_w3a (.objEq p y) (.objEq a z) (.classEq (.cv b) (syn_cop (.cv p) (.cv a)))) p0066 p0078
  have p0080 :=
    @g_n_2exbii (syn_w3a (.classEq (.cv b) (syn_cop (.cv p) (.cv a))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ccom (syn_c1st) (syn_c2nd)) (.cv p)) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd)) (.cv a))) (syn_w3a (.objEq p y) (.objEq a z) (.classEq (.cv b) (syn_cop (.cv p) (.cv a)))) p a p0079
  have p0081 :=
    @g_opeq1 (.cv p) (.cv y) (.cv a)
  have p0082_e00_recanon : Nominal.NPrf (.imp (.objEq p y) (.classEq (syn_cop (.cv p) (.cv a)) (syn_cop (.cv y) (.cv a)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0081
  have p0082 :=
    @g_eqeq2d (.objEq p y) (syn_cop (.cv p) (.cv a)) (syn_cop (.cv y) (.cv a)) (.cv b) p0082_e00_recanon
  have p0083 :=
    @g_opeq2 (.cv a) (.cv z) (.cv y)
  have p0084_e00_recanon : Nominal.NPrf (.imp (.objEq a z) (.classEq (syn_cop (.cv y) (.cv a)) (syn_cop (.cv y) (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0083
  have p0084 :=
    @g_eqeq2d (.objEq a z) (syn_cop (.cv y) (.cv a)) (syn_cop (.cv y) (.cv z)) (.cv b) p0084_e00_recanon
  have p0085_e02_recanon : Nominal.NPrf (.imp (.classEq (.cv p) (.cv y)) (syn_wb (.classEq (.cv b) (syn_cop (.cv p) (.cv a))) (.classEq (.cv b) (syn_cop (.cv y) (.cv a))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0082
  have p0085_e03_recanon : Nominal.NPrf (.imp (.classEq (.cv a) (.cv z)) (syn_wb (.classEq (.cv b) (syn_cop (.cv y) (.cv a))) (.classEq (.cv b) (syn_cop (.cv y) (.cv z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0084
  have p0085 :=
    @g_ceqsex2v (.classEq (.cv b) (syn_cop (.cv p) (.cv a))) (.classEq (.cv b) (syn_cop (.cv y) (.cv a))) (.classEq (.cv b) (syn_cop (.cv y) (.cv z))) p a (.cv y) (.cv z) dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0020 p0045 p0046 p0085_e02_recanon p0085_e03_recanon
  have p0086_e02_recanon : Nominal.NPrf (syn_wb (syn_wex p (syn_wex a (syn_w3a (.objEq p y) (.objEq a z) (.classEq (.cv b) (syn_cop (.cv p) (.cv a)))))) (.classEq (.cv b) (syn_cop (.cv y) (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
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
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
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
      p0085
  have p0086 :=
    @g_n_3bitri (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b)) (syn_wex p (syn_wex a (syn_w3a (.classEq (.cv b) (syn_cop (.cv p) (.cv a))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ccom (syn_c1st) (syn_c2nd)) (.cv p)) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd)) (.cv a))))) (syn_wex p (syn_wex a (syn_w3a (.objEq p y) (.objEq a z) (.classEq (.cv b) (syn_cop (.cv p) (.cv a)))))) (.classEq (.cv b) (syn_cop (.cv y) (.cv z))) p0065 p0080 p0086_e02_recanon
  have p0087 :=
    @g_anbi1i (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b)) (.classEq (.cv b) (syn_cop (.cv y) (.cv z))) (.classEq (.cv p) (syn_cop (.cv x) (.cv b))) p0086
  have p0088 :=
    @g_bitri (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv b))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))) (syn_wa (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b)) (.classEq (.cv p) (syn_cop (.cv x) (.cv b)))) (syn_wa (.classEq (.cv b) (syn_cop (.cv y) (.cv z))) (.classEq (.cv p) (syn_cop (.cv x) (.cv b)))) p0064 p0087
  have p0089 :=
    @g_exbii (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv b))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b))) (syn_wa (.classEq (.cv b) (syn_cop (.cv y) (.cv z))) (.classEq (.cv p) (syn_cop (.cv x) (.cv b)))) b p0088
  have p0090 :=
    @g_opex (.cv y) (.cv z) p0045 p0046
  have p0091 :=
    @g_opeq2 (.cv b) (syn_cop (.cv y) (.cv z)) (.cv x)
  have p0092 :=
    @g_eqeq2d (.classEq (.cv b) (syn_cop (.cv y) (.cv z))) (syn_cop (.cv x) (.cv b)) (syn_cop (.cv x) (syn_cop (.cv y) (.cv z))) (.cv p) p0091
  have p0093 :=
    @g_ceqsexv (.classEq (.cv p) (syn_cop (.cv x) (.cv b))) (.classEq (.cv p) (syn_cop (.cv x) (syn_cop (.cv y) (.cv z)))) b (syn_cop (.cv y) (.cv z)) dv_cache_0027 dv_cache_0028 p0090 p0092
  have p0094 :=
    @g_bitri (syn_wex b (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv b))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b)))) (syn_wex b (syn_wa (.classEq (.cv b) (syn_cop (.cv y) (.cv z))) (.classEq (.cv p) (syn_cop (.cv x) (.cv b))))) (.classEq (.cv p) (syn_cop (.cv x) (syn_cop (.cv y) (.cv z)))) p0089 p0093
  have p0095 :=
    @g_n_3bitri (syn_wbr (.cv p) (syn_ccnv (syn_ctxp (syn_c1st) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))))) (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_c1st) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd)))) (.cv p)) (syn_wex b (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv b))) (syn_wbr (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))) (.cv b)))) (.classEq (.cv p) (syn_cop (.cv x) (syn_cop (.cv y) (.cv z)))) p0040 p0063 p0094
  have p0096 :=
    @g_rexbii (syn_wbr (.cv p) (syn_ccnv (syn_ctxp (syn_c1st) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))))) (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D)))) (.classEq (.cv p) (syn_cop (.cv x) (syn_cop (.cv y) (.cv z)))) p R p0095
  have p0097 :=
    @g_elima p (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_ccnv (syn_ctxp (syn_c1st) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))))) R dv_cache_0013 dv_cache_0029 dv_cache_0030
  have p0098 :=
    @g_risset p (syn_cop (.cv x) (syn_cop (.cv y) (.cv z))) R dv_cache_0031 dv_cache_0030
  have p0099 :=
    @g_n_3bitr4i (syn_wrex p R (syn_wbr (.cv p) (syn_ccnv (syn_ctxp (syn_c1st) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))))) (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))))) (syn_wrex p R (.classEq (.cv p) (syn_cop (.cv x) (syn_cop (.cv y) (.cv z))))) (.classMem (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_cima (syn_ccnv (syn_ctxp (syn_c1st) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))))) R)) (.classMem (syn_cop (.cv x) (syn_cop (.cv y) (.cv z))) R) p0096 p0097 p0098
  have p0100 :=
    @g_bitri (.classMem (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_cins4 R)) (.classMem (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_cima (syn_ccnv (syn_ctxp (syn_c1st) (syn_ctxp (syn_ccom (syn_c1st) (syn_c2nd)) (syn_ccom (syn_ccom (syn_c1st) (syn_c2nd)) (syn_c2nd))))) R)) (.classMem (syn_cop (.cv x) (syn_cop (.cv y) (.cv z))) R) p0039 p0099
  have p0101 :=
    @g_vtocl2g (syn_wb (.classMem (syn_cop (.cv x) (syn_cop (.cv y) (syn_cop (.cv z) D))) (syn_cins4 R)) (.classMem (syn_cop (.cv x) (syn_cop (.cv y) (.cv z))) R)) (syn_wb (.classMem (syn_cop (.cv x) (syn_cop B (syn_cop (.cv z) D))) (syn_cins4 R)) (.classMem (syn_cop (.cv x) (syn_cop B (.cv z))) R)) (syn_wb (.classMem (syn_cop (.cv x) (syn_cop B (syn_cop C D))) (syn_cins4 R)) (.classMem (syn_cop (.cv x) (syn_cop B C)) R)) y z B C (syn_cvv) (syn_cvv) dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 p0029 p0037 p0100
  have p0102 :=
    @g_vtoclg (.imp (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (syn_wb (.classMem (syn_cop (.cv x) (syn_cop B (syn_cop C D))) (syn_cins4 R)) (.classMem (syn_cop (.cv x) (syn_cop B C)) R))) (.imp (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (syn_wb (.classMem (syn_cop A (syn_cop B (syn_cop C D))) (syn_cins4 R)) (.classMem (syn_cop A (syn_cop B C)) R))) x A (syn_cvv) dv_cache_0037 dv_cache_0038 p0022 p0101
  have p0103 :=
    @g_imp (.classMem A (syn_cvv)) (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (syn_wb (.classMem (syn_cop A (syn_cop B (syn_cop C D))) (syn_cins4 R)) (.classMem (syn_cop A (syn_cop B C)) R)) p0102
  have p0104 :=
    @g_pm5_21nii (.classMem (syn_cop A (syn_cop B (syn_cop C D))) (syn_cins4 R)) (syn_wa (.classMem A (syn_cvv)) (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))) (.classMem (syn_cop A (syn_cop B C)) R) p0010 p0016 p0103
  exact p0104

#print axioms g_oqelins4

end NFChoice.DirectNominalPrf.WPPReplay
