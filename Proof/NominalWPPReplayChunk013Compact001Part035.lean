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
import NominalWPPReplayChunk013Compact001Part034

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

noncomputable def g_enpw1
    (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (syn_wbr A (syn_cen) B) (syn_wbr (syn_cpw1 A) (syn_cen) (syn_cpw1 B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let f : Var := freshVar proofSupport 2
  let g : Var := freshVar proofSupport 3
  let x : Var := freshVar proofSupport 4
  let y : Var := freshVar proofSupport 5
  let z : Var := freshVar proofSupport 6
  let w : Var := freshVar proofSupport 7
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (h))
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (h))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_f : f ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_f_not_A : f ∉ A.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (h))
  have fresh_f_not_B : f ∉ B.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have fresh_g : g ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_g_not_A : g ∉ A.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (h))
  have fresh_g_not_B : g ∉ B.fv := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 7 ∉ proofSupport
    exact freshVar_not_mem proofSupport 7
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (h))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have fresh_a_ne_f : a ≠ f := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_f_ne_a : f ≠ a :=
    Ne.symm fresh_a_ne_f
  have fresh_a_ne_g : a ≠ g := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_g_ne_a : g ≠ a :=
    Ne.symm fresh_a_ne_g
  have fresh_a_ne_x : a ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_x_ne_a : x ≠ a :=
    Ne.symm fresh_a_ne_x
  have fresh_a_ne_y : a ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_y_ne_a : y ≠ a :=
    Ne.symm fresh_a_ne_y
  have fresh_a_ne_z : a ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_z_ne_a : z ≠ a :=
    Ne.symm fresh_a_ne_z
  have fresh_a_ne_w : a ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 0) (j := 7) (by decide)
  have fresh_w_ne_a : w ≠ a :=
    Ne.symm fresh_a_ne_w
  have fresh_b_ne_f : b ≠ f := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_f_ne_b : f ≠ b :=
    Ne.symm fresh_b_ne_f
  have fresh_b_ne_g : b ≠ g := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_g_ne_b : g ≠ b :=
    Ne.symm fresh_b_ne_g
  have fresh_b_ne_x : b ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_x_ne_b : x ≠ b :=
    Ne.symm fresh_b_ne_x
  have fresh_b_ne_y : b ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_y_ne_b : y ≠ b :=
    Ne.symm fresh_b_ne_y
  have fresh_b_ne_z : b ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_z_ne_b : z ≠ b :=
    Ne.symm fresh_b_ne_z
  have fresh_b_ne_w : b ≠ w := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 1) (j := 7) (by decide)
  have fresh_w_ne_b : w ≠ b :=
    Ne.symm fresh_b_ne_w
  have fresh_f_ne_g : f ≠ g := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_g_ne_f : g ≠ f :=
    Ne.symm fresh_f_ne_g
  have fresh_f_ne_x : f ≠ x := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_x_ne_f : x ≠ f :=
    Ne.symm fresh_f_ne_x
  have fresh_f_ne_y : f ≠ y := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_y_ne_f : y ≠ f :=
    Ne.symm fresh_f_ne_y
  have fresh_f_ne_z : f ≠ z := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_z_ne_f : z ≠ f :=
    Ne.symm fresh_f_ne_z
  have fresh_f_ne_w : f ≠ w := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 2) (j := 7) (by decide)
  have fresh_w_ne_f : w ≠ f :=
    Ne.symm fresh_f_ne_w
  have fresh_g_ne_x : g ≠ x := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_x_ne_g : x ≠ g :=
    Ne.symm fresh_g_ne_x
  have fresh_g_ne_y : g ≠ y := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_y_ne_g : y ≠ g :=
    Ne.symm fresh_g_ne_y
  have fresh_g_ne_z : g ≠ z := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_z_ne_g : z ≠ g :=
    Ne.symm fresh_g_ne_z
  have fresh_g_ne_w : g ≠ w := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 3) (j := 7) (by decide)
  have fresh_w_ne_g : w ≠ g :=
    Ne.symm fresh_g_ne_w
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_x_ne_w : x ≠ w := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 4) (j := 7) (by decide)
  have fresh_w_ne_x : w ≠ x :=
    Ne.symm fresh_x_ne_w
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_y_ne_w : y ≠ w := by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 5) (j := 7) (by decide)
  have fresh_w_ne_y : w ≠ y :=
    Ne.symm fresh_y_ne_w
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 6) (j := 7) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have dv_cache_0001 : f ∉ ((Class.cv a)).fv := by
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : f ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : f ∉ ((syn_wbr (syn_cpw1 (.cv a)) (syn_cen) (syn_cpw1 (.cv b)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_a, fresh_f_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : g ∉ ((syn_cpw1 (.cv a))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : g ∉ ((syn_cpw1 (.cv b))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_a, fresh_y_ne_b, fresh_y_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_a, fresh_z_ne_b, fresh_z_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : z ∉ ((syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_z, fresh_y_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0011 : x ∉ ((syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_a, fresh_x_ne_b, fresh_x_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0013 : z ∉ ((syn_csn (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : z ∉ ((Class.cv g)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : w ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : w ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : y ∉ ((Class.cv w)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : y ∉ ((syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv w)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_w, fresh_y_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : w ∉ ((Wff.imp (syn_wbr (syn_csn (.cv x)) (.cv g) (.cv z)) (syn_wex y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_z, fresh_w_ne_g, fresh_w_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : z ∉ ((syn_wex y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : y ∉ ((Wff.classMem (syn_csn (.cv x)) (syn_cdm (.cv g)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : x ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : x ∉ ((syn_wbr (syn_csn (.cv z)) (.cv g) (syn_csn (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, fresh_x_ne_y, fresh_x_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0025 : y ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have dv_cache_0026 : z ∉ ((syn_csn (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : w ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0028 : x ∉ ((Class.cv w)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0029 : x ∉ ((syn_wbr (syn_csn (.cv w)) (.cv g) (syn_csn (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_w, fresh_x_ne_y, fresh_x_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0030 : w ∉ ((Wff.imp (syn_wbr (.cv z) (.cv g) (syn_csn (.cv y))) (syn_wex x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_z, fresh_w_ne_y, fresh_w_ne_g, fresh_w_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0031 : z ∉ ((syn_wex x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0032 : x ∉ ((Wff.classMem (syn_csn (.cv y)) (syn_crn (.cv g)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, fresh_x_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0033 : y ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0034 : g ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (show g ≠ x from (by exact fresh_g_ne_x))
  have dv_cache_0035 : g ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact (show g ≠ y from (by exact fresh_g_ne_y))
  have dv_cache_0036 : g ∉ ((syn_wbr (.cv a) (syn_cen) (.cv b))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_a, fresh_g_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0037 : a ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0038 : b ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0039 : b ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0040 : b ∉ ((syn_wb (syn_wbr A (syn_cen) B) (syn_wbr (syn_cpw1 A) (syn_cen) (syn_cpw1 B)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_A, fresh_b_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0041 : a ∉ ((syn_wb (syn_wbr A (syn_cen) (.cv b)) (syn_wbr (syn_cpw1 A) (syn_cen) (syn_cpw1 (.cv b))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, fresh_a_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_brex A B (syn_cen)
  have p0001 :=
    @g_brex (syn_cpw1 A) (syn_cpw1 B) (syn_cen)
  have p0002 :=
    @g_pw1exb A
  have p0003 :=
    @g_pw1exb B
  have p0004 :=
    @g_anbi12i (.classMem (syn_cpw1 A) (syn_cvv)) (.classMem A (syn_cvv)) (.classMem (syn_cpw1 B) (syn_cvv)) (.classMem B (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_sylib (syn_wbr (syn_cpw1 A) (syn_cen) (syn_cpw1 B)) (syn_wa (.classMem (syn_cpw1 A) (syn_cvv)) (.classMem (syn_cpw1 B) (syn_cvv))) (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) p0001 p0004
  have p0006 :=
    @g_breq1 (.cv a) A (.cv b) (syn_cen)
  have p0007 :=
    @g_pw1eq (.cv a) A
  have p0008 :=
    @g_breq1d (.classEq (.cv a) A) (syn_cpw1 (.cv a)) (syn_cpw1 A) (syn_cpw1 (.cv b)) (syn_cen) p0007
  have p0009 :=
    @g_bibi12d (.classEq (.cv a) A) (syn_wbr (.cv a) (syn_cen) (.cv b)) (syn_wbr A (syn_cen) (.cv b)) (syn_wbr (syn_cpw1 (.cv a)) (syn_cen) (syn_cpw1 (.cv b))) (syn_wbr (syn_cpw1 A) (syn_cen) (syn_cpw1 (.cv b))) p0006 p0008
  have p0010 :=
    @g_breq2 (.cv b) B A (syn_cen)
  have p0011 :=
    @g_pw1eq (.cv b) B
  have p0012 :=
    @g_breq2d (.classEq (.cv b) B) (syn_cpw1 (.cv b)) (syn_cpw1 B) (syn_cpw1 A) (syn_cen) p0011
  have p0013 :=
    @g_bibi12d (.classEq (.cv b) B) (syn_wbr A (syn_cen) (.cv b)) (syn_wbr A (syn_cen) B) (syn_wbr (syn_cpw1 A) (syn_cen) (syn_cpw1 (.cv b))) (syn_wbr (syn_cpw1 A) (syn_cen) (syn_cpw1 B)) p0010 p0012
  have p0014 :=
    @g_bren (.cv a) (.cv b) f dv_cache_0001 dv_cache_0002
  have p0015 :=
    @g_f1ofun (.cv a) (.cv b) (.cv f)
  have p0016 :=
    @g_funsi (.cv f)
  have p0017 :=
    @g_syl (syn_wf1o (.cv f) (.cv a) (.cv b)) (syn_wfun (.cv f)) (syn_wfun (syn_csi (.cv f))) p0015 p0016
  have p0018 :=
    @g_f1odm (.cv a) (.cv b) (.cv f)
  have p0019 :=
    @g_dmsi (.cv f)
  have p0020 :=
    @g_pw1eq (syn_cdm (.cv f)) (.cv a)
  have p0021 :=
    @g_syl5eq (.classEq (syn_cdm (.cv f)) (.cv a)) (syn_cdm (syn_csi (.cv f))) (syn_cpw1 (syn_cdm (.cv f))) (syn_cpw1 (.cv a)) p0019 p0020
  have p0022 :=
    @g_syl (syn_wf1o (.cv f) (.cv a) (.cv b)) (.classEq (syn_cdm (.cv f)) (.cv a)) (.classEq (syn_cdm (syn_csi (.cv f))) (syn_cpw1 (.cv a))) p0018 p0021
  have p0023 :=
    (by simpa [syn_wb, syn_wfn] using (Nominal.biimpRefl (syn_wfn (syn_csi (.cv f)) (syn_cpw1 (.cv a)))))
  have p0024 :=
    @g_sylanbrc (syn_wf1o (.cv f) (.cv a) (.cv b)) (syn_wfun (syn_csi (.cv f))) (.classEq (syn_cdm (syn_csi (.cv f))) (syn_cpw1 (.cv a))) (syn_wfn (syn_csi (.cv f)) (syn_cpw1 (.cv a))) p0017 p0022 p0023
  have p0025 :=
    @g_f1of1 (.cv a) (.cv b) (.cv f)
  have p0026 :=
    (by simpa [syn_wb, syn_wf1] using (Nominal.biimpRefl (syn_wf1 (.cv f) (.cv a) (.cv b))))
  have p0027 :=
    @g_simprbi (syn_wf1 (.cv f) (.cv a) (.cv b)) (syn_wf (.cv f) (.cv a) (.cv b)) (syn_wfun (syn_ccnv (.cv f))) p0026
  have p0028 :=
    @g_funsi (syn_ccnv (.cv f))
  have p0029 :=
    @g_n_3syl (syn_wf1o (.cv f) (.cv a) (.cv b)) (syn_wf1 (.cv f) (.cv a) (.cv b)) (syn_wfun (syn_ccnv (.cv f))) (syn_wfun (syn_csi (syn_ccnv (.cv f)))) p0025 p0027 p0028
  have p0030 :=
    @g_cnvsi (.cv f)
  have p0031 :=
    @g_funeqi (syn_ccnv (syn_csi (.cv f))) (syn_csi (syn_ccnv (.cv f))) p0030
  have p0032 :=
    @g_sylibr (syn_wf1o (.cv f) (.cv a) (.cv b)) (syn_wfun (syn_csi (syn_ccnv (.cv f)))) (syn_wfun (syn_ccnv (syn_csi (.cv f)))) p0029 p0031
  have p0033 :=
    @g_f1ofo (.cv a) (.cv b) (.cv f)
  have p0034 :=
    @g_forn (.cv a) (.cv b) (.cv f)
  have p0035 :=
    @g_rnsi (.cv f)
  have p0036 :=
    @g_dfrn4 (syn_csi (.cv f))
  have p0037 :=
    @g_eqtr3i (syn_crn (syn_csi (.cv f))) (syn_cpw1 (syn_crn (.cv f))) (syn_cdm (syn_ccnv (syn_csi (.cv f)))) p0035 p0036
  have p0038 :=
    @g_pw1eq (syn_crn (.cv f)) (.cv b)
  have p0039 :=
    @g_syl5eqr (.classEq (syn_crn (.cv f)) (.cv b)) (syn_cdm (syn_ccnv (syn_csi (.cv f)))) (syn_cpw1 (syn_crn (.cv f))) (syn_cpw1 (.cv b)) p0037 p0038
  have p0040 :=
    @g_n_3syl (syn_wf1o (.cv f) (.cv a) (.cv b)) (syn_wfo (.cv f) (.cv a) (.cv b)) (.classEq (syn_crn (.cv f)) (.cv b)) (.classEq (syn_cdm (syn_ccnv (syn_csi (.cv f)))) (syn_cpw1 (.cv b))) p0033 p0034 p0039
  have p0041 :=
    (by simpa [syn_wb, syn_wfn] using (Nominal.biimpRefl (syn_wfn (syn_ccnv (syn_csi (.cv f))) (syn_cpw1 (.cv b)))))
  have p0042 :=
    @g_sylanbrc (syn_wf1o (.cv f) (.cv a) (.cv b)) (syn_wfun (syn_ccnv (syn_csi (.cv f)))) (.classEq (syn_cdm (syn_ccnv (syn_csi (.cv f)))) (syn_cpw1 (.cv b))) (syn_wfn (syn_ccnv (syn_csi (.cv f))) (syn_cpw1 (.cv b))) p0032 p0040 p0041
  have p0043 :=
    @g_dff1o4 (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)) (syn_csi (.cv f))
  have p0044 :=
    @g_sylanbrc (syn_wf1o (.cv f) (.cv a) (.cv b)) (syn_wfn (syn_csi (.cv f)) (syn_cpw1 (.cv a))) (syn_wfn (syn_ccnv (syn_csi (.cv f))) (syn_cpw1 (.cv b))) (syn_wf1o (syn_csi (.cv f)) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) p0024 p0042 p0043
  have p0045 :=
    @g_vex f
  have p0046 :=
    @g_siex (.cv f) p0045
  have p0047 :=
    @g_f1oen (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)) (syn_csi (.cv f)) p0046
  have p0048 :=
    @g_syl (syn_wf1o (.cv f) (.cv a) (.cv b)) (syn_wf1o (syn_csi (.cv f)) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (syn_wbr (syn_cpw1 (.cv a)) (syn_cen) (syn_cpw1 (.cv b))) p0044 p0047
  have p0049 :=
    @g_exlimiv (syn_wf1o (.cv f) (.cv a) (.cv b)) (syn_wbr (syn_cpw1 (.cv a)) (syn_cen) (syn_cpw1 (.cv b))) f dv_cache_0003 p0048
  have p0050 :=
    @g_sylbi (syn_wbr (.cv a) (syn_cen) (.cv b)) (syn_wex f (syn_wf1o (.cv f) (.cv a) (.cv b))) (syn_wbr (syn_cpw1 (.cv a)) (syn_cen) (syn_cpw1 (.cv b))) p0014 p0049
  have p0051 :=
    @g_bren (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)) g dv_cache_0004 dv_cache_0005
  have p0052 :=
    @g_f1ofun (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)) (.cv g)
  have p0053 :=
    @g_fununiq (syn_csn (.cv x)) (syn_csn (.cv y)) (syn_csn (.cv z)) (.cv g)
  have p0054 :=
    @g_vex y
  have p0055 :=
    @g_sneqb (.cv y) (.cv z) p0054
  have p0056_e01_recanon : Nominal.NPrf (syn_wb (.classEq (syn_csn (.cv y)) (syn_csn (.cv z))) (.objEq y z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
      p0055
  have p0056 :=
    @g_sylib (syn_w3a (syn_wfun (.cv g)) (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))) (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv z)))) (.classEq (syn_csn (.cv y)) (syn_csn (.cv z))) (.objEq y z) p0053 p0056_e01_recanon
  have p0057 :=
    @g_n_3expib (syn_wfun (.cv g)) (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))) (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv z))) (.objEq y z) p0056
  have p0058 :=
    @g_syl (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (syn_wfun (.cv g)) (.imp (syn_wa (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))) (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv z)))) (.objEq y z)) p0052 p0057
  have p0059 :=
    @g_alrimivv (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (.imp (syn_wa (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))) (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv z)))) (.objEq y z)) y z dv_cache_0006 dv_cache_0007 p0058
  have p0060 :=
    @g_sneq (.cv y) (.cv z)
  have p0061_e00_recanon : Nominal.NPrf (.imp (.objEq y z) (.classEq (syn_csn (.cv y)) (syn_csn (.cv z)))) :=
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
      p0060
  have p0061 :=
    @g_breq2d (.objEq y z) (syn_csn (.cv y)) (syn_csn (.cv z)) (syn_csn (.cv x)) (.cv g) p0061_e00_recanon
  have p0062 :=
    @g_mo4 (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))) (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv z))) y z dv_cache_0008 dv_cache_0009 dv_cache_0010 p0061
  have p0063 :=
    @g_sylibr (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (.all y (.all z (.imp (syn_wa (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))) (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv z)))) (.objEq y z)))) (syn_wmo y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) p0059 p0062
  have p0064 :=
    @g_alrimiv (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (syn_wmo y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) x dv_cache_0011 p0063
  have p0065 :=
    @g_funopab (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))) x y dv_cache_0012
  have p0066 :=
    @g_sylibr (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (.all x (syn_wmo y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))) (syn_wfun (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))) p0064 p0065
  have p0067 :=
    @g_dmopab (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))) x y dv_cache_0012
  have p0068 :=
    @g_eldm z (syn_csn (.cv x)) (.cv g) dv_cache_0013 dv_cache_0014
  have p0069 :=
    @g_brelrn (syn_csn (.cv x)) (.cv z) (.cv g)
  have p0070 :=
    @g_f1ofo (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)) (.cv g)
  have p0071 :=
    @g_forn (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)) (.cv g)
  have p0072 :=
    @g_syl (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (syn_wfo (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (.classEq (syn_crn (.cv g)) (syn_cpw1 (.cv b))) p0070 p0071
  have p0073 :=
    @g_eleq2d (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (syn_crn (.cv g)) (syn_cpw1 (.cv b)) (.cv z) p0072
  have p0074 :=
    @g_elpw1 w (.cv z) (.cv b) dv_cache_0015 dv_cache_0016
  have p0075 :=
    @g_breq2 (.cv z) (syn_csn (.cv w)) (syn_csn (.cv x)) (.cv g)
  have p0076 :=
    @g_vex w
  have p0077 :=
    @g_sneq (.cv y) (.cv w)
  have p0078_e00_recanon : Nominal.NPrf (.imp (.objEq y w) (.classEq (syn_csn (.cv y)) (syn_csn (.cv w)))) :=
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
      p0077
  have p0078 :=
    @g_breq2d (.objEq y w) (syn_csn (.cv y)) (syn_csn (.cv w)) (syn_csn (.cv x)) (.cv g) p0078_e00_recanon
  have p0079_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv y) (.cv w)) (syn_wb (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))) (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv w))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0078
  have p0079 :=
    @g_spcev (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))) (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv w))) y (.cv w) dv_cache_0017 dv_cache_0018 p0076 p0079_e01_recanon
  have p0080 :=
    @g_syl6bi (.classEq (.cv z) (syn_csn (.cv w))) (syn_wbr (syn_csn (.cv x)) (.cv g) (.cv z)) (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv w))) (syn_wex y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) p0075 p0079
  have p0081 :=
    @g_rexlimivw (.classEq (.cv z) (syn_csn (.cv w))) (.imp (syn_wbr (syn_csn (.cv x)) (.cv g) (.cv z)) (syn_wex y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))) w (.cv b) dv_cache_0019 p0080
  have p0082 :=
    @g_sylbi (.classMem (.cv z) (syn_cpw1 (.cv b))) (syn_wrex w (.cv b) (.classEq (.cv z) (syn_csn (.cv w)))) (.imp (syn_wbr (syn_csn (.cv x)) (.cv g) (.cv z)) (syn_wex y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))) p0074 p0081
  have p0083 :=
    @g_syl6bi (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (.classMem (.cv z) (syn_crn (.cv g))) (.classMem (.cv z) (syn_cpw1 (.cv b))) (.imp (syn_wbr (syn_csn (.cv x)) (.cv g) (.cv z)) (syn_wex y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))) p0073 p0082
  have p0084 :=
    @g_com23 (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (.classMem (.cv z) (syn_crn (.cv g))) (syn_wbr (syn_csn (.cv x)) (.cv g) (.cv z)) (syn_wex y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) p0083
  have p0085 :=
    @g_mpdi (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (syn_wbr (syn_csn (.cv x)) (.cv g) (.cv z)) (.classMem (.cv z) (syn_crn (.cv g))) (syn_wex y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) p0069 p0084
  have p0086 :=
    @g_exlimdv (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (syn_wbr (syn_csn (.cv x)) (.cv g) (.cv z)) (syn_wex y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) z dv_cache_0020 dv_cache_0007 p0085
  have p0087 :=
    @g_syl5bi (.classMem (syn_csn (.cv x)) (syn_cdm (.cv g))) (syn_wex z (syn_wbr (syn_csn (.cv x)) (.cv g) (.cv z))) (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (syn_wex y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) p0068 p0086
  have p0088 :=
    @g_breldm (syn_csn (.cv x)) (syn_csn (.cv y)) (.cv g)
  have p0089 :=
    @g_exlimiv (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))) (.classMem (syn_csn (.cv x)) (syn_cdm (.cv g))) y dv_cache_0021 p0088
  have p0090 :=
    @g_impbid1 (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (.classMem (syn_csn (.cv x)) (syn_cdm (.cv g))) (syn_wex y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) p0087 p0089
  have p0091 :=
    @g_f1odm (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)) (.cv g)
  have p0092 :=
    @g_eleq2d (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (syn_cdm (.cv g)) (syn_cpw1 (.cv a)) (syn_csn (.cv x)) p0091
  have p0093 :=
    @g_bitr3d (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (.classMem (syn_csn (.cv x)) (syn_cdm (.cv g))) (syn_wex y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (.classMem (syn_csn (.cv x)) (syn_cpw1 (.cv a))) p0090 p0092
  have p0094 :=
    @g_snelpw1 (.cv x) (.cv a)
  have p0095_e01_recanon : Nominal.NPrf (syn_wb (.classMem (syn_csn (.cv x)) (syn_cpw1 (.cv a))) (.objMem x a)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cpw syn_wss syn_c1c syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
      p0094
  have p0095 :=
    @g_syl6bb (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (syn_wex y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (.classMem (syn_csn (.cv x)) (syn_cpw1 (.cv a))) (.objMem x a) p0093 p0095_e01_recanon
  have p0096_e00_recanon : Nominal.NPrf (.imp (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (syn_wb (syn_wex y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (.classMem (.cv x) (.cv a)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wf1o syn_wa syn_wf1 syn_wfo syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_cpw syn_wss syn_c1c syn_wex syn_csn syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0095
  have p0096 :=
    @g_eqabcdv (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (syn_wex y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) x (.cv a) dv_cache_0022 dv_cache_0011 p0096_e00_recanon
  have p0097 :=
    @g_syl5eq (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (syn_cdm (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))) (.cab x (syn_wex y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))) (.cv a) p0067 p0096
  have p0098 :=
    (by simpa [syn_wb, syn_wfn] using (Nominal.biimpRefl (syn_wfn (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (.cv a))))
  have p0099 :=
    @g_sylanbrc (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (syn_wfun (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))) (.classEq (syn_cdm (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))) (.cv a)) (syn_wfn (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (.cv a)) p0066 p0097 p0098
  have p0100 :=
    @g_f1ocnv (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)) (.cv g)
  have p0101 :=
    @g_f1ofun (syn_cpw1 (.cv b)) (syn_cpw1 (.cv a)) (syn_ccnv (.cv g))
  have p0102 :=
    @g_fununiq (syn_csn (.cv y)) (syn_csn (.cv x)) (syn_csn (.cv z)) (syn_ccnv (.cv g))
  have p0103 :=
    @g_n_3expib (syn_wfun (syn_ccnv (.cv g))) (syn_wbr (syn_csn (.cv y)) (syn_ccnv (.cv g)) (syn_csn (.cv x))) (syn_wbr (syn_csn (.cv y)) (syn_ccnv (.cv g)) (syn_csn (.cv z))) (.classEq (syn_csn (.cv x)) (syn_csn (.cv z))) p0102
  have p0104 :=
    @g_brcnv (syn_csn (.cv y)) (syn_csn (.cv x)) (.cv g)
  have p0105 :=
    @g_brcnv (syn_csn (.cv y)) (syn_csn (.cv z)) (.cv g)
  have p0106 :=
    @g_anbi12i (syn_wbr (syn_csn (.cv y)) (syn_ccnv (.cv g)) (syn_csn (.cv x))) (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))) (syn_wbr (syn_csn (.cv y)) (syn_ccnv (.cv g)) (syn_csn (.cv z))) (syn_wbr (syn_csn (.cv z)) (.cv g) (syn_csn (.cv y))) p0104 p0105
  have p0107 :=
    @g_vex x
  have p0108 :=
    @g_sneqb (.cv x) (.cv z) p0107
  have p0109_e02_recanon : Nominal.NPrf (syn_wb (.classEq (syn_csn (.cv x)) (syn_csn (.cv z))) (.objEq x z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
      p0108
  have p0109 :=
    @g_n_3imtr3g (syn_wfun (syn_ccnv (.cv g))) (syn_wa (syn_wbr (syn_csn (.cv y)) (syn_ccnv (.cv g)) (syn_csn (.cv x))) (syn_wbr (syn_csn (.cv y)) (syn_ccnv (.cv g)) (syn_csn (.cv z)))) (.classEq (syn_csn (.cv x)) (syn_csn (.cv z))) (syn_wa (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))) (syn_wbr (syn_csn (.cv z)) (.cv g) (syn_csn (.cv y)))) (.objEq x z) p0103 p0106 p0109_e02_recanon
  have p0110 :=
    @g_n_3syl (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (syn_wf1o (syn_ccnv (.cv g)) (syn_cpw1 (.cv b)) (syn_cpw1 (.cv a))) (syn_wfun (syn_ccnv (.cv g))) (.imp (syn_wa (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))) (syn_wbr (syn_csn (.cv z)) (.cv g) (syn_csn (.cv y)))) (.objEq x z)) p0100 p0101 p0109
  have p0111 :=
    @g_alrimivv (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (.imp (syn_wa (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))) (syn_wbr (syn_csn (.cv z)) (.cv g) (syn_csn (.cv y)))) (.objEq x z)) x z dv_cache_0011 dv_cache_0007 p0110
  have p0112 :=
    @g_sneq (.cv x) (.cv z)
  have p0113_e00_recanon : Nominal.NPrf (.imp (.objEq x z) (.classEq (syn_csn (.cv x)) (syn_csn (.cv z)))) :=
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
      p0112
  have p0113 :=
    @g_breq1d (.objEq x z) (syn_csn (.cv x)) (syn_csn (.cv z)) (syn_csn (.cv y)) (.cv g) p0113_e00_recanon
  have p0114 :=
    @g_mo4 (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))) (syn_wbr (syn_csn (.cv z)) (.cv g) (syn_csn (.cv y))) x z dv_cache_0008 dv_cache_0023 dv_cache_0024 p0113
  have p0115 :=
    @g_sylibr (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (.all x (.all z (.imp (syn_wa (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))) (syn_wbr (syn_csn (.cv z)) (.cv g) (syn_csn (.cv y)))) (.objEq x z)))) (syn_wmo x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) p0111 p0114
  have p0116 :=
    @g_alrimiv (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (syn_wmo x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) y dv_cache_0006 p0115
  have p0117 :=
    @g_funopab (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))) y x dv_cache_0025
  have p0118 :=
    @g_sylibr (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (.all y (syn_wmo x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))) (syn_wfun (syn_copab y x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))) p0116 p0117
  have p0119 :=
    @g_dmopab (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))) y x dv_cache_0025
  have p0120 :=
    @g_elrn z (syn_csn (.cv y)) (.cv g) dv_cache_0026 dv_cache_0014
  have p0121 :=
    @g_breldm (.cv z) (syn_csn (.cv y)) (.cv g)
  have p0122 :=
    @g_eleq2d (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (syn_cdm (.cv g)) (syn_cpw1 (.cv a)) (.cv z) p0091
  have p0123 :=
    @g_elpw1 w (.cv z) (.cv a) dv_cache_0015 dv_cache_0027
  have p0124 :=
    @g_breq1 (.cv z) (syn_csn (.cv w)) (syn_csn (.cv y)) (.cv g)
  have p0125 :=
    @g_sneq (.cv x) (.cv w)
  have p0126_e00_recanon : Nominal.NPrf (.imp (.objEq x w) (.classEq (syn_csn (.cv x)) (syn_csn (.cv w)))) :=
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
      p0125
  have p0126 :=
    @g_breq1d (.objEq x w) (syn_csn (.cv x)) (syn_csn (.cv w)) (syn_csn (.cv y)) (.cv g) p0126_e00_recanon
  have p0127_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv x) (.cv w)) (syn_wb (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))) (syn_wbr (syn_csn (.cv w)) (.cv g) (syn_csn (.cv y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0126
  have p0127 :=
    @g_spcev (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))) (syn_wbr (syn_csn (.cv w)) (.cv g) (syn_csn (.cv y))) x (.cv w) dv_cache_0028 dv_cache_0029 p0076 p0127_e01_recanon
  have p0128 :=
    @g_syl6bi (.classEq (.cv z) (syn_csn (.cv w))) (syn_wbr (.cv z) (.cv g) (syn_csn (.cv y))) (syn_wbr (syn_csn (.cv w)) (.cv g) (syn_csn (.cv y))) (syn_wex x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) p0124 p0127
  have p0129 :=
    @g_rexlimivw (.classEq (.cv z) (syn_csn (.cv w))) (.imp (syn_wbr (.cv z) (.cv g) (syn_csn (.cv y))) (syn_wex x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))) w (.cv a) dv_cache_0030 p0128
  have p0130 :=
    @g_sylbi (.classMem (.cv z) (syn_cpw1 (.cv a))) (syn_wrex w (.cv a) (.classEq (.cv z) (syn_csn (.cv w)))) (.imp (syn_wbr (.cv z) (.cv g) (syn_csn (.cv y))) (syn_wex x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))) p0123 p0129
  have p0131 :=
    @g_syl6bi (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (.classMem (.cv z) (syn_cdm (.cv g))) (.classMem (.cv z) (syn_cpw1 (.cv a))) (.imp (syn_wbr (.cv z) (.cv g) (syn_csn (.cv y))) (syn_wex x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))) p0122 p0130
  have p0132 :=
    @g_com23 (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (.classMem (.cv z) (syn_cdm (.cv g))) (syn_wbr (.cv z) (.cv g) (syn_csn (.cv y))) (syn_wex x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) p0131
  have p0133 :=
    @g_mpdi (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (syn_wbr (.cv z) (.cv g) (syn_csn (.cv y))) (.classMem (.cv z) (syn_cdm (.cv g))) (syn_wex x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) p0121 p0132
  have p0134 :=
    @g_exlimdv (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (syn_wbr (.cv z) (.cv g) (syn_csn (.cv y))) (syn_wex x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) z dv_cache_0031 dv_cache_0007 p0133
  have p0135 :=
    @g_syl5bi (.classMem (syn_csn (.cv y)) (syn_crn (.cv g))) (syn_wex z (syn_wbr (.cv z) (.cv g) (syn_csn (.cv y)))) (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (syn_wex x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) p0120 p0134
  have p0136 :=
    @g_brelrn (syn_csn (.cv x)) (syn_csn (.cv y)) (.cv g)
  have p0137 :=
    @g_exlimiv (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))) (.classMem (syn_csn (.cv y)) (syn_crn (.cv g))) x dv_cache_0032 p0136
  have p0138 :=
    @g_impbid1 (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (.classMem (syn_csn (.cv y)) (syn_crn (.cv g))) (syn_wex x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) p0135 p0137
  have p0139 :=
    @g_eleq2d (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (syn_crn (.cv g)) (syn_cpw1 (.cv b)) (syn_csn (.cv y)) p0072
  have p0140 :=
    @g_bitr3d (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (.classMem (syn_csn (.cv y)) (syn_crn (.cv g))) (syn_wex x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (.classMem (syn_csn (.cv y)) (syn_cpw1 (.cv b))) p0138 p0139
  have p0141 :=
    @g_snelpw1 (.cv y) (.cv b)
  have p0142_e01_recanon : Nominal.NPrf (syn_wb (.classMem (syn_csn (.cv y)) (syn_cpw1 (.cv b))) (.objMem y b)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cpw syn_wss syn_c1c syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
      p0141
  have p0142 :=
    @g_syl6bb (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (syn_wex x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (.classMem (syn_csn (.cv y)) (syn_cpw1 (.cv b))) (.objMem y b) p0140 p0142_e01_recanon
  have p0143_e00_recanon : Nominal.NPrf (.imp (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (syn_wb (syn_wex x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (.classMem (.cv y) (.cv b)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wf1o syn_wa syn_wf1 syn_wfo syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_cpw syn_wss syn_c1c syn_wex syn_csn syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0142
  have p0143 :=
    @g_eqabcdv (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (syn_wex x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) y (.cv b) dv_cache_0033 dv_cache_0006 p0143_e00_recanon
  have p0144 :=
    @g_syl5eq (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (syn_cdm (syn_copab y x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))) (.cab y (syn_wex x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))) (.cv b) p0119 p0143
  have p0145 :=
    (by simpa [syn_wb, syn_wfn] using (Nominal.biimpRefl (syn_wfn (syn_copab y x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (.cv b))))
  have p0146 :=
    @g_sylanbrc (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (syn_wfun (syn_copab y x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))) (.classEq (syn_cdm (syn_copab y x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))) (.cv b)) (syn_wfn (syn_copab y x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (.cv b)) p0118 p0144 p0145
  have p0147 :=
    @g_cnvopab (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))) x y dv_cache_0012
  have p0148 :=
    @g_fneq1i (.cv b) (syn_ccnv (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))) (syn_copab y x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) p0147
  have p0149 :=
    @g_sylibr (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (syn_wfn (syn_copab y x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (.cv b)) (syn_wfn (syn_ccnv (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))) (.cv b)) p0146 p0148
  have p0150 :=
    @g_dff1o4 (.cv a) (.cv b) (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))
  have p0151 :=
    @g_sylanbrc (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (syn_wfn (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (.cv a)) (syn_wfn (syn_ccnv (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))) (.cv b)) (syn_wf1o (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (.cv a) (.cv b)) p0099 p0149 p0150
  have p0152 :=
    @g_enpw1lem1 x y g dv_cache_0034 dv_cache_0035 dv_cache_0012
  have p0153 :=
    @g_f1oen (.cv a) (.cv b) (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) p0152
  have p0154 :=
    @g_syl (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (syn_wf1o (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (.cv a) (.cv b)) (syn_wbr (.cv a) (syn_cen) (.cv b)) p0151 p0153
  have p0155 :=
    @g_exlimiv (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (syn_wbr (.cv a) (syn_cen) (.cv b)) g dv_cache_0036 p0154
  have p0156 :=
    @g_sylbi (syn_wbr (syn_cpw1 (.cv a)) (syn_cen) (syn_cpw1 (.cv b))) (syn_wex g (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))) (syn_wbr (.cv a) (syn_cen) (.cv b)) p0051 p0155
  have p0157 :=
    @g_impbii (syn_wbr (.cv a) (syn_cen) (.cv b)) (syn_wbr (syn_cpw1 (.cv a)) (syn_cen) (syn_cpw1 (.cv b))) p0050 p0156
  have p0158 :=
    @g_vtocl2g (syn_wb (syn_wbr (.cv a) (syn_cen) (.cv b)) (syn_wbr (syn_cpw1 (.cv a)) (syn_cen) (syn_cpw1 (.cv b)))) (syn_wb (syn_wbr A (syn_cen) (.cv b)) (syn_wbr (syn_cpw1 A) (syn_cen) (syn_cpw1 (.cv b)))) (syn_wb (syn_wbr A (syn_cen) B) (syn_wbr (syn_cpw1 A) (syn_cen) (syn_cpw1 B))) a b A B (syn_cvv) (syn_cvv) dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 p0009 p0013 p0157
  have p0159 :=
    @g_pm5_21nii (syn_wbr A (syn_cen) B) (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (syn_wbr (syn_cpw1 A) (syn_cen) (syn_cpw1 B)) p0000 p0005 p0158
  exact p0159

#print axioms g_enpw1

end NFChoice.DirectNominalPrf.WPPReplay
