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
import NominalWPPReplayChunk013Compact001Part054

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

noncomputable def g_taddc
    (A : Class) (B : Class) (X : Class) (c : Var) (dv_X_c : c ∉ X.fv) :
    Nominal.NPrf (.imp (syn_wa (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem X (syn_cncs))) (.classEq (syn_ctc A) (syn_cplc (syn_ctc B) X))) (syn_wrex c (syn_cncs) (.classEq X (syn_ctc (.cv c))))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ X.fv ∪ ({c} : Finset Var)
  let w : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  let z : Var := freshVar proofSupport 3
  let a : Var := freshVar proofSupport 4
  let b : Var := freshVar proofSupport 5
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_X : w ∉ X.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_ne_c : w ≠ c := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_c_ne_w : c ≠ w :=
    Ne.symm fresh_w_ne_c
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_X : x ∉ X.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_ne_c : x ≠ c := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_c_ne_x : c ≠ x :=
    Ne.symm fresh_x_ne_c
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_X : y ∉ X.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_c : y ≠ c := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_c_ne_y : c ≠ y :=
    Ne.symm fresh_y_ne_c
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_X : z ∉ X.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_ne_c : z ≠ c := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_c_ne_z : c ≠ z :=
    Ne.symm fresh_z_ne_c
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a_not_X : a ∉ X.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_ne_c : a ≠ c := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_c_ne_a : c ≠ a :=
    Ne.symm fresh_a_ne_c
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_b_not_X : b ∉ X.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_ne_c : b ≠ c := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_c_ne_b : c ≠ b :=
    Ne.symm fresh_b_ne_c
  have fresh_w_ne_x : w ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_w : y ≠ w :=
    Ne.symm fresh_w_ne_y
  have fresh_w_ne_z : w ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_z_ne_w : z ≠ w :=
    Ne.symm fresh_w_ne_z
  have fresh_w_ne_a : w ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_a_ne_w : a ≠ w :=
    Ne.symm fresh_w_ne_a
  have fresh_w_ne_b : w ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_b_ne_w : b ≠ w :=
    Ne.symm fresh_w_ne_b
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_x_ne_a : x ≠ a := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_a_ne_x : a ≠ x :=
    Ne.symm fresh_x_ne_a
  have fresh_x_ne_b : x ≠ b := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_b_ne_x : b ≠ x :=
    Ne.symm fresh_x_ne_b
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_y_ne_a : y ≠ a := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_a_ne_y : a ≠ y :=
    Ne.symm fresh_y_ne_a
  have fresh_y_ne_b : y ≠ b := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_b_ne_y : b ≠ y :=
    Ne.symm fresh_y_ne_b
  have fresh_z_ne_a : z ≠ a := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_a_ne_z : a ≠ z :=
    Ne.symm fresh_z_ne_a
  have fresh_z_ne_b : z ≠ b := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_b_ne_z : b ≠ z :=
    Ne.symm fresh_z_ne_b
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ (X).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classEq X (syn_cnc (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_X, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((Wff.classEq X (syn_cnc (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_X, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((Wff.classEq A (syn_cnc (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((Wff.classEq A (syn_cnc (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((Wff.classEq B (syn_cnc (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((Wff.classEq B (syn_cnc (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_B, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0011 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0012 : a ∉ ((syn_cpw1 (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : b ∉ ((syn_cpw1 (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : a ∉ ((syn_cnc (syn_cpw1 (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : b ∉ ((syn_cnc (syn_cpw1 (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : a ∉ ((syn_cnc (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : b ∉ ((syn_cnc (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : a ≠ b := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0019 : c ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : w ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : c ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : w ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : c ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : w ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : c ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (show c ≠ w from (by exact fresh_c_ne_w))
  have dv_cache_0026 : w ∉ ((Wff.classMem (.cv b) (syn_cnc (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_b, fresh_w_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : c ∉ ((syn_wex w (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_z, fresh_c_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0028 : c ∉ ((Wff.classMem (.cv b) (syn_cnc (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_b, fresh_c_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0029 : b ∉ ((syn_wex w (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_z, fresh_b_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0030 : a ∉ ((syn_wex w (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_z, fresh_a_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0031 : w ∉ ((Wff.classEq X (syn_cnc (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_X, fresh_w_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0032 : z ∉ ((Wff.imp (.classEq (syn_ctc A) (syn_cplc (syn_ctc B) X)) (syn_wex w (.classEq X (syn_cnc (syn_cpw1 (.cv w))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_not_B, fresh_z_not_X, fresh_z_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0033 : x ∉ ((Wff.imp (.classEq (syn_ctc A) (syn_cplc (syn_ctc B) X)) (syn_wex w (.classEq X (syn_cnc (syn_cpw1 (.cv w))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, fresh_x_not_X, fresh_x_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0034 : y ∉ ((Wff.imp (.classEq (syn_ctc A) (syn_cplc (syn_ctc B) X)) (syn_wex w (.classEq X (syn_cnc (syn_cpw1 (.cv w))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, fresh_y_not_X, fresh_y_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0035 : w ∉ ((Class.cv c)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0036 : w ∉ ((Wff.classEq X (syn_ctc (.cv c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_X, fresh_w_ne_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0037 : c ∉ ((syn_cnc (.cv w))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0038 : c ∉ ((Wff.classEq X (syn_cnc (syn_cpw1 (.cv w))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_X_c, fresh_c_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elncs x A dv_cache_0001
  have p0001 :=
    @g_elncs y B dv_cache_0002
  have p0002 :=
    @g_elncs z X dv_cache_0003
  have p0003 :=
    @g_n_3anbi123i (.classMem A (syn_cncs)) (syn_wex x (.classEq A (syn_cnc (.cv x)))) (.classMem B (syn_cncs)) (syn_wex y (.classEq B (syn_cnc (.cv y)))) (.classMem X (syn_cncs)) (syn_wex z (.classEq X (syn_cnc (.cv z)))) p0000 p0001 p0002
  have p0004 :=
    @g_eeeanv (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y))) (.classEq X (syn_cnc (.cv z))) x y z dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0005 :=
    @g_bitr4i (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem X (syn_cncs))) (syn_w3a (syn_wex x (.classEq A (syn_cnc (.cv x)))) (syn_wex y (.classEq B (syn_cnc (.cv y)))) (syn_wex z (.classEq X (syn_cnc (.cv z))))) (syn_wex x (syn_wex y (syn_wex z (syn_w3a (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y))) (.classEq X (syn_cnc (.cv z))))))) p0003 p0004
  have p0006 :=
    @g_vex x
  have p0007 :=
    @g_tcnc (.cv x) p0006
  have p0008 :=
    @g_vex y
  have p0009 :=
    @g_tcnc (.cv y) p0008
  have p0010 :=
    @g_addceq1i (syn_ctc (syn_cnc (.cv y))) (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (.cv z)) p0009
  have p0011 :=
    @g_eqeq12i (syn_ctc (syn_cnc (.cv x))) (syn_cnc (syn_cpw1 (.cv x))) (syn_cplc (syn_ctc (syn_cnc (.cv y))) (syn_cnc (.cv z))) (syn_cplc (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (.cv z))) p0007 p0010
  have p0012 :=
    @g_eqcom (syn_cnc (syn_cpw1 (.cv x))) (syn_cplc (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (.cv z)))
  have p0013 :=
    @g_pw1ex (.cv y) p0008
  have p0014 :=
    @g_ncelncsi (syn_cpw1 (.cv y)) p0013
  have p0015 :=
    @g_vex z
  have p0016 :=
    @g_ncelncsi (.cv z) p0015
  have p0017 :=
    @g_ncaddccl (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (.cv z))
  have p0018 :=
    @g_mp2an (.classMem (syn_cnc (syn_cpw1 (.cv y))) (syn_cncs)) (.classMem (syn_cnc (.cv z)) (syn_cncs)) (.classMem (syn_cplc (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (.cv z))) (syn_cncs)) p0014 p0016 p0017
  have p0019 :=
    @g_ncseqnc (syn_cplc (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (.cv z))) (syn_cpw1 (.cv x))
  have p0020 :=
    Nominal.mp p0018 p0019
  have p0021 :=
    @g_n_3bitri (.classEq (syn_ctc (syn_cnc (.cv x))) (syn_cplc (syn_ctc (syn_cnc (.cv y))) (syn_cnc (.cv z)))) (.classEq (syn_cnc (syn_cpw1 (.cv x))) (syn_cplc (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (.cv z)))) (.classEq (syn_cplc (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (.cv z))) (syn_cnc (syn_cpw1 (.cv x)))) (.classMem (syn_cpw1 (.cv x)) (syn_cplc (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (.cv z)))) p0011 p0012 p0020
  have p0022 :=
    @g_eladdc (syn_cpw1 (.cv x)) (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (.cv z)) a b dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
  have p0023 :=
    @g_vex a
  have p0024 :=
    @g_vex b
  have p0025 :=
    @g_pw1equn c w (.cv a) (.cv b) (.cv x) dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 p0023 p0024
  have p0026 :=
    @g_simp3 (.classEq (.cv x) (syn_cun (.cv c) (.cv w))) (.classEq (.cv a) (syn_cpw1 (.cv c))) (.classEq (.cv b) (syn_cpw1 (.cv w)))
  have p0027 :=
    @g_elnc (.cv b) (.cv z)
  have p0028 :=
    @g_ensym (.cv b) (.cv z)
  have p0029 :=
    @g_breq2 (.cv b) (syn_cpw1 (.cv w)) (.cv z) (syn_cen)
  have p0030 :=
    @g_biimpcd (.classEq (.cv b) (syn_cpw1 (.cv w))) (syn_wbr (.cv z) (syn_cen) (.cv b)) (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w))) p0029
  have p0031 :=
    @g_sylbi (syn_wbr (.cv b) (syn_cen) (.cv z)) (syn_wbr (.cv z) (syn_cen) (.cv b)) (.imp (.classEq (.cv b) (syn_cpw1 (.cv w))) (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w)))) p0028 p0030
  have p0032 :=
    @g_sylbi (.classMem (.cv b) (syn_cnc (.cv z))) (syn_wbr (.cv b) (syn_cen) (.cv z)) (.imp (.classEq (.cv b) (syn_cpw1 (.cv w))) (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w)))) p0027 p0031
  have p0033 :=
    @g_syl5 (syn_w3a (.classEq (.cv x) (syn_cun (.cv c) (.cv w))) (.classEq (.cv a) (syn_cpw1 (.cv c))) (.classEq (.cv b) (syn_cpw1 (.cv w)))) (.classEq (.cv b) (syn_cpw1 (.cv w))) (.classMem (.cv b) (syn_cnc (.cv z))) (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w))) p0026 p0032
  have p0034 :=
    @g_eximdv (.classMem (.cv b) (syn_cnc (.cv z))) (syn_w3a (.classEq (.cv x) (syn_cun (.cv c) (.cv w))) (.classEq (.cv a) (syn_cpw1 (.cv c))) (.classEq (.cv b) (syn_cpw1 (.cv w)))) (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w))) w dv_cache_0026 p0033
  have p0035 :=
    @g_exlimdv (.classMem (.cv b) (syn_cnc (.cv z))) (syn_wex w (syn_w3a (.classEq (.cv x) (syn_cun (.cv c) (.cv w))) (.classEq (.cv a) (syn_cpw1 (.cv c))) (.classEq (.cv b) (syn_cpw1 (.cv w))))) (syn_wex w (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w)))) c dv_cache_0027 dv_cache_0028 p0034
  have p0036 :=
    @g_syl5bi (.classEq (syn_cpw1 (.cv x)) (syn_cun (.cv a) (.cv b))) (syn_wex c (syn_wex w (syn_w3a (.classEq (.cv x) (syn_cun (.cv c) (.cv w))) (.classEq (.cv a) (syn_cpw1 (.cv c))) (.classEq (.cv b) (syn_cpw1 (.cv w)))))) (.classMem (.cv b) (syn_cnc (.cv z))) (syn_wex w (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w)))) p0025 p0035
  have p0037 :=
    @g_adantld (.classMem (.cv b) (syn_cnc (.cv z))) (.classEq (syn_cpw1 (.cv x)) (syn_cun (.cv a) (.cv b))) (syn_wex w (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w)))) (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) p0036
  have p0038 :=
    @g_rexlimiv (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (syn_cpw1 (.cv x)) (syn_cun (.cv a) (.cv b)))) (syn_wex w (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w)))) b (syn_cnc (.cv z)) dv_cache_0029 p0037
  have p0039 :=
    @g_rexlimivw (syn_wrex b (syn_cnc (.cv z)) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (syn_cpw1 (.cv x)) (syn_cun (.cv a) (.cv b))))) (syn_wex w (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w)))) a (syn_cnc (syn_cpw1 (.cv y))) dv_cache_0030 p0038
  have p0040 :=
    @g_sylbi (.classMem (syn_cpw1 (.cv x)) (syn_cplc (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (.cv z)))) (syn_wrex a (syn_cnc (syn_cpw1 (.cv y))) (syn_wrex b (syn_cnc (.cv z)) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (syn_cpw1 (.cv x)) (syn_cun (.cv a) (.cv b)))))) (syn_wex w (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w)))) p0022 p0039
  have p0041 :=
    @g_sylbi (.classEq (syn_ctc (syn_cnc (.cv x))) (syn_cplc (syn_ctc (syn_cnc (.cv y))) (syn_cnc (.cv z)))) (.classMem (syn_cpw1 (.cv x)) (syn_cplc (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (.cv z)))) (syn_wex w (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w)))) p0021 p0040
  have p0042 :=
    @g_tceq A (syn_cnc (.cv x))
  have p0043 :=
    @g_n_3ad2ant1 (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y))) (.classEq (syn_ctc A) (syn_ctc (syn_cnc (.cv x)))) (.classEq X (syn_cnc (.cv z))) p0042
  have p0044 :=
    @g_tceq B (syn_cnc (.cv y))
  have p0045 :=
    @g_adantr (.classEq B (syn_cnc (.cv y))) (.classEq (syn_ctc B) (syn_ctc (syn_cnc (.cv y)))) (.classEq X (syn_cnc (.cv z))) p0044
  have p0046 :=
    @g_simpr (.classEq B (syn_cnc (.cv y))) (.classEq X (syn_cnc (.cv z)))
  have p0047 :=
    @g_addceq12d (syn_wa (.classEq B (syn_cnc (.cv y))) (.classEq X (syn_cnc (.cv z)))) (syn_ctc B) (syn_ctc (syn_cnc (.cv y))) X (syn_cnc (.cv z)) p0045 p0046
  have p0048 :=
    @g_n_3adant1 (.classEq B (syn_cnc (.cv y))) (.classEq X (syn_cnc (.cv z))) (.classEq (syn_cplc (syn_ctc B) X) (syn_cplc (syn_ctc (syn_cnc (.cv y))) (syn_cnc (.cv z)))) (.classEq A (syn_cnc (.cv x))) p0047
  have p0049 :=
    @g_eqeq12d (syn_w3a (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y))) (.classEq X (syn_cnc (.cv z)))) (syn_ctc A) (syn_ctc (syn_cnc (.cv x))) (syn_cplc (syn_ctc B) X) (syn_cplc (syn_ctc (syn_cnc (.cv y))) (syn_cnc (.cv z))) p0043 p0048
  have p0050 :=
    @g_eqeq1 X (syn_cnc (.cv z)) (syn_cnc (syn_cpw1 (.cv w)))
  have p0051 :=
    @g_eqnc (.cv z) (syn_cpw1 (.cv w)) p0015
  have p0052 :=
    @g_syl6bb (.classEq X (syn_cnc (.cv z))) (.classEq X (syn_cnc (syn_cpw1 (.cv w)))) (.classEq (syn_cnc (.cv z)) (syn_cnc (syn_cpw1 (.cv w)))) (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w))) p0050 p0051
  have p0053 :=
    @g_exbidv (.classEq X (syn_cnc (.cv z))) (.classEq X (syn_cnc (syn_cpw1 (.cv w)))) (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w))) w dv_cache_0031 p0052
  have p0054 :=
    @g_n_3ad2ant3 (.classEq X (syn_cnc (.cv z))) (.classEq A (syn_cnc (.cv x))) (syn_wb (syn_wex w (.classEq X (syn_cnc (syn_cpw1 (.cv w))))) (syn_wex w (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w))))) (.classEq B (syn_cnc (.cv y))) p0053
  have p0055 :=
    @g_imbi12d (syn_w3a (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y))) (.classEq X (syn_cnc (.cv z)))) (.classEq (syn_ctc A) (syn_cplc (syn_ctc B) X)) (.classEq (syn_ctc (syn_cnc (.cv x))) (syn_cplc (syn_ctc (syn_cnc (.cv y))) (syn_cnc (.cv z)))) (syn_wex w (.classEq X (syn_cnc (syn_cpw1 (.cv w))))) (syn_wex w (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w)))) p0049 p0054
  have p0056 :=
    @g_mpbiri (syn_w3a (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y))) (.classEq X (syn_cnc (.cv z)))) (.imp (.classEq (syn_ctc A) (syn_cplc (syn_ctc B) X)) (syn_wex w (.classEq X (syn_cnc (syn_cpw1 (.cv w)))))) (.imp (.classEq (syn_ctc (syn_cnc (.cv x))) (syn_cplc (syn_ctc (syn_cnc (.cv y))) (syn_cnc (.cv z)))) (syn_wex w (syn_wbr (.cv z) (syn_cen) (syn_cpw1 (.cv w))))) p0041 p0055
  have p0057 :=
    @g_exlimiv (syn_w3a (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y))) (.classEq X (syn_cnc (.cv z)))) (.imp (.classEq (syn_ctc A) (syn_cplc (syn_ctc B) X)) (syn_wex w (.classEq X (syn_cnc (syn_cpw1 (.cv w)))))) z dv_cache_0032 p0056
  have p0058 :=
    @g_exlimivv (syn_wex z (syn_w3a (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y))) (.classEq X (syn_cnc (.cv z))))) (.imp (.classEq (syn_ctc A) (syn_cplc (syn_ctc B) X)) (syn_wex w (.classEq X (syn_cnc (syn_cpw1 (.cv w)))))) x y dv_cache_0033 dv_cache_0034 p0057
  have p0059 :=
    @g_sylbi (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem X (syn_cncs))) (syn_wex x (syn_wex y (syn_wex z (syn_w3a (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y))) (.classEq X (syn_cnc (.cv z))))))) (.imp (.classEq (syn_ctc A) (syn_cplc (syn_ctc B) X)) (syn_wex w (.classEq X (syn_cnc (syn_cpw1 (.cv w)))))) p0005 p0058
  have p0060 :=
    @g_imp (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem X (syn_cncs))) (.classEq (syn_ctc A) (syn_cplc (syn_ctc B) X)) (syn_wex w (.classEq X (syn_cnc (syn_cpw1 (.cv w))))) p0059
  have p0061 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex c (syn_cncs) (.classEq X (syn_ctc (.cv c))))))
  have p0062 :=
    @g_elncs w (.cv c) dv_cache_0035
  have p0063 :=
    @g_anbi1i (.classMem (.cv c) (syn_cncs)) (syn_wex w (.classEq (.cv c) (syn_cnc (.cv w)))) (.classEq X (syn_ctc (.cv c))) p0062
  have p0064 :=
    @g_n_19_41v (.classEq (.cv c) (syn_cnc (.cv w))) (.classEq X (syn_ctc (.cv c))) w dv_cache_0036
  have p0065 :=
    @g_bitr4i (syn_wa (.classMem (.cv c) (syn_cncs)) (.classEq X (syn_ctc (.cv c)))) (syn_wa (syn_wex w (.classEq (.cv c) (syn_cnc (.cv w)))) (.classEq X (syn_ctc (.cv c)))) (syn_wex w (syn_wa (.classEq (.cv c) (syn_cnc (.cv w))) (.classEq X (syn_ctc (.cv c))))) p0063 p0064
  have p0066 :=
    @g_exbii (syn_wa (.classMem (.cv c) (syn_cncs)) (.classEq X (syn_ctc (.cv c)))) (syn_wex w (syn_wa (.classEq (.cv c) (syn_cnc (.cv w))) (.classEq X (syn_ctc (.cv c))))) c p0065
  have p0067 :=
    @g_excom (syn_wa (.classEq (.cv c) (syn_cnc (.cv w))) (.classEq X (syn_ctc (.cv c)))) c w
  have p0068 :=
    @g_ncex (.cv w)
  have p0069 :=
    @g_tceq (.cv c) (syn_cnc (.cv w))
  have p0070 :=
    @g_vex w
  have p0071 :=
    @g_tcnc (.cv w) p0070
  have p0072 :=
    @g_syl6eq (.classEq (.cv c) (syn_cnc (.cv w))) (syn_ctc (.cv c)) (syn_ctc (syn_cnc (.cv w))) (syn_cnc (syn_cpw1 (.cv w))) p0069 p0071
  have p0073 :=
    @g_eqeq2d (.classEq (.cv c) (syn_cnc (.cv w))) (syn_ctc (.cv c)) (syn_cnc (syn_cpw1 (.cv w))) X p0072
  have p0074 :=
    @g_ceqsexv (.classEq X (syn_ctc (.cv c))) (.classEq X (syn_cnc (syn_cpw1 (.cv w)))) c (syn_cnc (.cv w)) dv_cache_0037 dv_cache_0038 p0068 p0073
  have p0075 :=
    @g_exbii (syn_wex c (syn_wa (.classEq (.cv c) (syn_cnc (.cv w))) (.classEq X (syn_ctc (.cv c))))) (.classEq X (syn_cnc (syn_cpw1 (.cv w)))) w p0074
  have p0076 :=
    @g_bitri (syn_wex c (syn_wex w (syn_wa (.classEq (.cv c) (syn_cnc (.cv w))) (.classEq X (syn_ctc (.cv c)))))) (syn_wex w (syn_wex c (syn_wa (.classEq (.cv c) (syn_cnc (.cv w))) (.classEq X (syn_ctc (.cv c)))))) (syn_wex w (.classEq X (syn_cnc (syn_cpw1 (.cv w))))) p0067 p0075
  have p0077 :=
    @g_n_3bitri (syn_wrex c (syn_cncs) (.classEq X (syn_ctc (.cv c)))) (syn_wex c (syn_wa (.classMem (.cv c) (syn_cncs)) (.classEq X (syn_ctc (.cv c))))) (syn_wex c (syn_wex w (syn_wa (.classEq (.cv c) (syn_cnc (.cv w))) (.classEq X (syn_ctc (.cv c)))))) (syn_wex w (.classEq X (syn_cnc (syn_cpw1 (.cv w))))) p0061 p0066 p0076
  have p0078 :=
    @g_sylibr (syn_wa (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem X (syn_cncs))) (.classEq (syn_ctc A) (syn_cplc (syn_ctc B) X))) (syn_wex w (.classEq X (syn_cnc (syn_cpw1 (.cv w))))) (syn_wrex c (syn_cncs) (.classEq X (syn_ctc (.cv c)))) p0060 p0077
  exact p0078

#print axioms g_taddc

end NFChoice.DirectNominalPrf.WPPReplay
