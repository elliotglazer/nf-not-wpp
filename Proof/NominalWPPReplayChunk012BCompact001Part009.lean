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
import NominalWPPReplayChunk012BCompact001Part008

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

noncomputable def g_dfrn5
    (A : Class) :
    Nominal.NPrf (.classEq (syn_crn A) (syn_cima (syn_c2nd) A)) := by
  let proofSupport : Finset Var := A.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ≠ x := by
    clear dv_cache_0001
    exact (show z ≠ x from (by exact fresh_z_ne_x))
  have dv_cache_0003 : x ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((syn_cop (.cv x) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : z ∉ ((syn_c2nd)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((syn_crn A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((syn_cima (syn_c2nd) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_rexcom4 (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) z x A dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_vex y
  have p0002 :=
    @g_br2nd x (.cv z) (.cv y) dv_cache_0003 dv_cache_0004 p0001
  have p0003 :=
    @g_rexbii (syn_wbr (.cv z) (syn_c2nd) (.cv y)) (syn_wex x (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))) z A p0002
  have p0004 :=
    @g_risset z (syn_cop (.cv x) (.cv y)) A dv_cache_0005 dv_cache_0006
  have p0005 :=
    @g_exbii (.classMem (syn_cop (.cv x) (.cv y)) A) (syn_wrex z A (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))) x p0004
  have p0006 :=
    @g_n_3bitr4ri (syn_wrex z A (syn_wex x (.classEq (.cv z) (syn_cop (.cv x) (.cv y))))) (syn_wex x (syn_wrex z A (.classEq (.cv z) (syn_cop (.cv x) (.cv y))))) (syn_wrex z A (syn_wbr (.cv z) (syn_c2nd) (.cv y))) (syn_wex x (.classMem (syn_cop (.cv x) (.cv y)) A)) p0000 p0003 p0005
  have p0007 :=
    @g_elrn2 x (.cv y) A dv_cache_0004 dv_cache_0001
  have p0008 :=
    @g_elima z (.cv y) (syn_c2nd) A dv_cache_0007 dv_cache_0008 dv_cache_0006
  have p0009 :=
    @g_n_3bitr4i (syn_wex x (.classMem (syn_cop (.cv x) (.cv y)) A)) (syn_wrex z A (syn_wbr (.cv z) (syn_c2nd) (.cv y))) (.classMem (.cv y) (syn_crn A)) (.classMem (.cv y) (syn_cima (syn_c2nd) A)) p0006 p0007 p0008
  have p0010 :=
    @g_eqriv y (syn_crn A) (syn_cima (syn_c2nd) A) dv_cache_0009 dv_cache_0010 p0009
  exact p0010

noncomputable def g_brswap
    (x : Var) (y : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (syn_wb (syn_wbr A (syn_cswap) B) (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq B (syn_cop (.cv y) (.cv x))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_ne_x : a ≠ x := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_a : x ≠ a :=
    Ne.symm fresh_a_ne_x
  have fresh_a_ne_y : a ≠ y := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_a : y ≠ a :=
    Ne.symm fresh_a_ne_y
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_ne_x : b ≠ x := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_b : x ≠ b :=
    Ne.symm fresh_b_ne_x
  have fresh_b_ne_y : b ≠ y := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_b : y ≠ b :=
    Ne.symm fresh_b_ne_y
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have dv_cache_0001 : x ∉ ((syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classEq (.cv a) A)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_a, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Wff.classEq (.cv a) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_a, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classEq (.cv b) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_b, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((Wff.classEq (.cv b) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_b, dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ≠ a := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show y ≠ a from (by exact fresh_y_ne_a))
  have dv_cache_0008 : y ≠ b := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show y ≠ b from (by exact fresh_y_ne_b))
  have dv_cache_0009 : y ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show y ≠ x from (by exact Ne.symm dv_x_y))
  have dv_cache_0010 : a ≠ b := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0011 : a ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0012 : b ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show b ≠ x from (by exact fresh_b_ne_x))
  have dv_cache_0013 : a ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : b ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : a ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : b ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : a ∉ ((syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq B (syn_cop (.cv y) (.cv x))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, fresh_a_ne_x, fresh_a_ne_y, fresh_a_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : b ∉ ((syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq B (syn_cop (.cv y) (.cv x))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_A, fresh_b_ne_x, fresh_b_ne_y, fresh_b_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_brex A B (syn_cswap)
  have p0001 :=
    @g_vex x
  have p0002 :=
    @g_vex y
  have p0003 :=
    @g_opex (.cv x) (.cv y) p0001 p0002
  have p0004 :=
    @g_eleq1 A (syn_cop (.cv x) (.cv y)) (syn_cvv)
  have p0005 :=
    @g_mpbiri (.classEq A (syn_cop (.cv x) (.cv y))) (.classMem A (syn_cvv)) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_opex (.cv y) (.cv x) p0002 p0001
  have p0007 :=
    @g_eleq1 B (syn_cop (.cv y) (.cv x)) (syn_cvv)
  have p0008 :=
    @g_mpbiri (.classEq B (syn_cop (.cv y) (.cv x))) (.classMem B (syn_cvv)) (.classMem (syn_cop (.cv y) (.cv x)) (syn_cvv)) p0006 p0007
  have p0009 :=
    @g_anim12i (.classEq A (syn_cop (.cv x) (.cv y))) (.classMem A (syn_cvv)) (.classEq B (syn_cop (.cv y) (.cv x))) (.classMem B (syn_cvv)) p0005 p0008
  have p0010 :=
    @g_exlimivv (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq B (syn_cop (.cv y) (.cv x)))) (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) x y dv_cache_0001 dv_cache_0002 p0009
  have p0011 :=
    @g_eqeq1 (.cv a) A (syn_cop (.cv x) (.cv y))
  have p0012 :=
    @g_anbi1d (.classEq (.cv a) A) (.classEq (.cv a) (syn_cop (.cv x) (.cv y))) (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq (.cv b) (syn_cop (.cv y) (.cv x))) p0011
  have p0013 :=
    @g_n_2exbidv (.classEq (.cv a) A) (syn_wa (.classEq (.cv a) (syn_cop (.cv x) (.cv y))) (.classEq (.cv b) (syn_cop (.cv y) (.cv x)))) (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq (.cv b) (syn_cop (.cv y) (.cv x)))) x y dv_cache_0003 dv_cache_0004 p0012
  have p0014 :=
    @g_eqeq1 (.cv b) B (syn_cop (.cv y) (.cv x))
  have p0015 :=
    @g_anbi2d (.classEq (.cv b) B) (.classEq (.cv b) (syn_cop (.cv y) (.cv x))) (.classEq B (syn_cop (.cv y) (.cv x))) (.classEq A (syn_cop (.cv x) (.cv y))) p0014
  have p0016 :=
    @g_n_2exbidv (.classEq (.cv b) B) (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq (.cv b) (syn_cop (.cv y) (.cv x)))) (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq B (syn_cop (.cv y) (.cv x)))) x y dv_cache_0005 dv_cache_0006 p0015
  have p0017 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_swap a b x y dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0018 :=
    @g_brabg (syn_wex x (syn_wex y (syn_wa (.classEq (.cv a) (syn_cop (.cv x) (.cv y))) (.classEq (.cv b) (syn_cop (.cv y) (.cv x)))))) (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq (.cv b) (syn_cop (.cv y) (.cv x)))))) (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq B (syn_cop (.cv y) (.cv x)))))) a b A B (syn_cvv) (syn_cvv) (syn_cswap) dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0010 p0013 p0016 p0017
  have p0019 :=
    @g_pm5_21nii (syn_wbr A (syn_cswap) B) (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq B (syn_cop (.cv y) (.cv x)))))) p0000 p0010 p0018
  exact p0019

noncomputable def g_cnvswap
     :
    Nominal.NPrf (.classEq (syn_ccnv (syn_cswap)) (syn_cswap)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  let x : Var := freshVar proofSupport 3
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have fresh_a_ne_y : a ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_a : y ≠ a :=
    Ne.symm fresh_a_ne_y
  have fresh_a_ne_x : a ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_x_ne_a : x ≠ a :=
    Ne.symm fresh_a_ne_x
  have fresh_b_ne_y : b ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_b : y ≠ b :=
    Ne.symm fresh_b_ne_y
  have fresh_b_ne_x : b ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_x_ne_b : x ≠ b :=
    Ne.symm fresh_b_ne_x
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have dv_cache_0001 : y ∉ ((Class.cv b)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have dv_cache_0006 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0007 : a ∉ ((syn_ccnv (syn_cswap))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : b ∉ ((syn_ccnv (syn_cswap))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : a ∉ ((syn_cswap)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : b ∉ ((syn_cswap)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : a ≠ b := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have p0000 :=
    @g_ancom (.classEq (.cv b) (syn_cop (.cv y) (.cv x))) (.classEq (.cv a) (syn_cop (.cv x) (.cv y)))
  have p0001 :=
    @g_n_2exbii (syn_wa (.classEq (.cv b) (syn_cop (.cv y) (.cv x))) (.classEq (.cv a) (syn_cop (.cv x) (.cv y)))) (syn_wa (.classEq (.cv a) (syn_cop (.cv x) (.cv y))) (.classEq (.cv b) (syn_cop (.cv y) (.cv x)))) x y p0000
  have p0002 :=
    @g_brcnv (.cv a) (.cv b) (syn_cswap)
  have p0003 :=
    @g_brswap y x (.cv b) (.cv a) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0004 :=
    @g_excom (syn_wa (.classEq (.cv b) (syn_cop (.cv y) (.cv x))) (.classEq (.cv a) (syn_cop (.cv x) (.cv y)))) y x
  have p0005 :=
    @g_n_3bitri (syn_wbr (.cv a) (syn_ccnv (syn_cswap)) (.cv b)) (syn_wbr (.cv b) (syn_cswap) (.cv a)) (syn_wex y (syn_wex x (syn_wa (.classEq (.cv b) (syn_cop (.cv y) (.cv x))) (.classEq (.cv a) (syn_cop (.cv x) (.cv y)))))) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv b) (syn_cop (.cv y) (.cv x))) (.classEq (.cv a) (syn_cop (.cv x) (.cv y)))))) p0002 p0003 p0004
  have p0006 :=
    @g_brswap x y (.cv a) (.cv b) dv_cache_0004 dv_cache_0003 dv_cache_0002 dv_cache_0001 dv_cache_0006
  have p0007 :=
    @g_n_3bitr4i (syn_wex x (syn_wex y (syn_wa (.classEq (.cv b) (syn_cop (.cv y) (.cv x))) (.classEq (.cv a) (syn_cop (.cv x) (.cv y)))))) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv a) (syn_cop (.cv x) (.cv y))) (.classEq (.cv b) (syn_cop (.cv y) (.cv x)))))) (syn_wbr (.cv a) (syn_ccnv (syn_cswap)) (.cv b)) (syn_wbr (.cv a) (syn_cswap) (.cv b)) p0001 p0005 p0006
  have p0008 :=
    @g_eqbrriv a b (syn_ccnv (syn_cswap)) (syn_cswap) dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 p0007
  exact p0008

noncomputable def g_swapf1o
     :
    Nominal.NPrf (syn_wf1o (syn_cswap) (syn_cvv) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
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
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have dv_cache_0001 : x ∉ ((syn_cswap)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cswap)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_cswap)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0005 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0006 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0007 : x ∉ ((syn_cdm (syn_cswap))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_dffun2 x y z (syn_cswap) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_opeq (.cv y)
  have p0002 :=
    @g_breq2i (.cv y) (syn_cop (syn_cproj1 (.cv y)) (syn_cproj2 (.cv y))) (.cv x) (syn_cswap) p0001
  have p0003 :=
    @g_vex y
  have p0004 :=
    @g_proj1ex (.cv y) p0003
  have p0005 :=
    @g_proj2ex (.cv y) p0003
  have p0006 :=
    @g_brswap2 (.cv x) (syn_cproj1 (.cv y)) (syn_cproj2 (.cv y)) p0004 p0005
  have p0007 :=
    @g_bitri (syn_wbr (.cv x) (syn_cswap) (.cv y)) (syn_wbr (.cv x) (syn_cswap) (syn_cop (syn_cproj1 (.cv y)) (syn_cproj2 (.cv y)))) (.classEq (.cv x) (syn_cop (syn_cproj2 (.cv y)) (syn_cproj1 (.cv y)))) p0002 p0006
  have p0008 :=
    @g_opeq (.cv z)
  have p0009 :=
    @g_breq2i (.cv z) (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))) (.cv x) (syn_cswap) p0008
  have p0010 :=
    @g_vex z
  have p0011 :=
    @g_proj1ex (.cv z) p0010
  have p0012 :=
    @g_proj2ex (.cv z) p0010
  have p0013 :=
    @g_brswap2 (.cv x) (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z)) p0011 p0012
  have p0014 :=
    @g_bitri (syn_wbr (.cv x) (syn_cswap) (.cv z)) (syn_wbr (.cv x) (syn_cswap) (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z)))) (.classEq (.cv x) (syn_cop (syn_cproj2 (.cv z)) (syn_cproj1 (.cv z)))) p0009 p0013
  have p0015 :=
    @g_eqtr2 (.cv x) (syn_cop (syn_cproj2 (.cv y)) (syn_cproj1 (.cv y))) (syn_cop (syn_cproj2 (.cv z)) (syn_cproj1 (.cv z)))
  have p0016 :=
    @g_ancom (.classEq (syn_cproj2 (.cv y)) (syn_cproj2 (.cv z))) (.classEq (syn_cproj1 (.cv y)) (syn_cproj1 (.cv z)))
  have p0017 :=
    @g_opth (syn_cproj2 (.cv y)) (syn_cproj1 (.cv y)) (syn_cproj2 (.cv z)) (syn_cproj1 (.cv z))
  have p0018 :=
    @g_eqeq12i (.cv y) (syn_cop (syn_cproj1 (.cv y)) (syn_cproj2 (.cv y))) (.cv z) (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))) p0001 p0008
  have p0019 :=
    @g_opth (syn_cproj1 (.cv y)) (syn_cproj2 (.cv y)) (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))
  have p0020_e00_recanon : Nominal.NPrf (syn_wb (.objEq y z) (.classEq (syn_cop (syn_cproj1 (.cv y)) (syn_cproj2 (.cv y))) (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_cproj1 syn_cproj2
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj2, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0018
  have p0020 :=
    @g_bitri (.objEq y z) (.classEq (syn_cop (syn_cproj1 (.cv y)) (syn_cproj2 (.cv y))) (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z)))) (syn_wa (.classEq (syn_cproj1 (.cv y)) (syn_cproj1 (.cv z))) (.classEq (syn_cproj2 (.cv y)) (syn_cproj2 (.cv z)))) p0020_e00_recanon p0019
  have p0021 :=
    @g_n_3bitr4i (syn_wa (.classEq (syn_cproj2 (.cv y)) (syn_cproj2 (.cv z))) (.classEq (syn_cproj1 (.cv y)) (syn_cproj1 (.cv z)))) (syn_wa (.classEq (syn_cproj1 (.cv y)) (syn_cproj1 (.cv z))) (.classEq (syn_cproj2 (.cv y)) (syn_cproj2 (.cv z)))) (.classEq (syn_cop (syn_cproj2 (.cv y)) (syn_cproj1 (.cv y))) (syn_cop (syn_cproj2 (.cv z)) (syn_cproj1 (.cv z)))) (.objEq y z) p0016 p0017 p0020
  have p0022 :=
    @g_sylib (syn_wa (.classEq (.cv x) (syn_cop (syn_cproj2 (.cv y)) (syn_cproj1 (.cv y)))) (.classEq (.cv x) (syn_cop (syn_cproj2 (.cv z)) (syn_cproj1 (.cv z))))) (.classEq (syn_cop (syn_cproj2 (.cv y)) (syn_cproj1 (.cv y))) (syn_cop (syn_cproj2 (.cv z)) (syn_cproj1 (.cv z)))) (.objEq y z) p0015 p0021
  have p0023 :=
    @g_syl2anb (syn_wbr (.cv x) (syn_cswap) (.cv y)) (.classEq (.cv x) (syn_cop (syn_cproj2 (.cv y)) (syn_cproj1 (.cv y)))) (.classEq (.cv x) (syn_cop (syn_cproj2 (.cv z)) (syn_cproj1 (.cv z)))) (.objEq y z) (syn_wbr (.cv x) (syn_cswap) (.cv z)) p0007 p0014 p0022
  have p0024 :=
    @g_gen2 (.imp (syn_wa (syn_wbr (.cv x) (syn_cswap) (.cv y)) (syn_wbr (.cv x) (syn_cswap) (.cv z))) (.objEq y z)) y z p0023
  have p0025 :=
    @g_mpgbir (syn_wfun (syn_cswap)) (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) (syn_cswap) (.cv y)) (syn_wbr (.cv x) (syn_cswap) (.cv z))) (.objEq y z)))) x p0000 p0024
  have p0026 :=
    @g_eqv x (syn_cdm (syn_cswap)) dv_cache_0007
  have p0027 :=
    @g_opeq (.cv x)
  have p0028 :=
    @g_eqid (syn_cop (syn_cproj1 (.cv x)) (syn_cproj2 (.cv x)))
  have p0029 :=
    @g_vex x
  have p0030 :=
    @g_proj2ex (.cv x) p0029
  have p0031 :=
    @g_proj1ex (.cv x) p0029
  have p0032 :=
    @g_brswap2 (syn_cop (syn_cproj1 (.cv x)) (syn_cproj2 (.cv x))) (syn_cproj2 (.cv x)) (syn_cproj1 (.cv x)) p0030 p0031
  have p0033 :=
    @g_mpbir (syn_wbr (syn_cop (syn_cproj1 (.cv x)) (syn_cproj2 (.cv x))) (syn_cswap) (syn_cop (syn_cproj2 (.cv x)) (syn_cproj1 (.cv x)))) (.classEq (syn_cop (syn_cproj1 (.cv x)) (syn_cproj2 (.cv x))) (syn_cop (syn_cproj1 (.cv x)) (syn_cproj2 (.cv x)))) p0028 p0032
  have p0034 :=
    @g_breldm (syn_cop (syn_cproj1 (.cv x)) (syn_cproj2 (.cv x))) (syn_cop (syn_cproj2 (.cv x)) (syn_cproj1 (.cv x))) (syn_cswap)
  have p0035 :=
    Nominal.mp p0033 p0034
  have p0036 :=
    @g_eqeltri (.cv x) (syn_cop (syn_cproj1 (.cv x)) (syn_cproj2 (.cv x))) (syn_cdm (syn_cswap)) p0027 p0035
  have p0037 :=
    @g_mpgbir (.classEq (syn_cdm (syn_cswap)) (syn_cvv)) (.classMem (.cv x) (syn_cdm (syn_cswap))) x p0026 p0036
  have p0038 :=
    (by simpa [syn_wb, syn_wfn] using (Nominal.biimpRefl (syn_wfn (syn_cswap) (syn_cvv))))
  have p0039 :=
    @g_mpbir2an (syn_wfn (syn_cswap) (syn_cvv)) (syn_wfun (syn_cswap)) (.classEq (syn_cdm (syn_cswap)) (syn_cvv)) p0025 p0037 p0038
  have p0040 :=
    @g_cnvswap
  have p0041 :=
    @g_fneq1i (syn_cvv) (syn_ccnv (syn_cswap)) (syn_cswap) p0040
  have p0042 :=
    @g_mpbir (syn_wfn (syn_ccnv (syn_cswap)) (syn_cvv)) (syn_wfn (syn_cswap) (syn_cvv)) p0039 p0041
  have p0043 :=
    @g_dff1o4 (syn_cvv) (syn_cvv) (syn_cswap)
  have p0044 :=
    @g_mpbir2an (syn_wf1o (syn_cswap) (syn_cvv) (syn_cvv)) (syn_wfn (syn_cswap) (syn_cvv)) (syn_wfn (syn_ccnv (syn_cswap)) (syn_cvv)) p0039 p0042 p0043
  exact p0044

noncomputable def g_swapres
    (A : Class) :
    Nominal.NPrf (syn_wf1o (syn_cres (syn_cswap) A) A (syn_ccnv A)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_swapf1o
  have p0001 :=
    @g_f1of1 (syn_cvv) (syn_cvv) (syn_cswap)
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_ssv A
  have p0004 :=
    @g_f1ores (syn_cvv) (syn_cvv) A (syn_cswap)
  have p0005 :=
    @g_mp2an (syn_wf1 (syn_cswap) (syn_cvv) (syn_cvv)) (syn_wss A (syn_cvv)) (syn_wf1o (syn_cres (syn_cswap) A) A (syn_cima (syn_cswap) A)) p0002 p0003 p0004
  have p0006 :=
    @g_dfcnv2 A
  have p0007 :=
    @g_f1oeq3 (syn_ccnv A) (syn_cima (syn_cswap) A) A (syn_cres (syn_cswap) A)
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_mpbir (syn_wf1o (syn_cres (syn_cswap) A) A (syn_ccnv A)) (syn_wf1o (syn_cres (syn_cswap) A) A (syn_cima (syn_cswap) A)) p0005 p0008
  exact p0009

noncomputable def g_xpnedisj
    (A : Class) (B : Class) (C : Class) (D : Class) (hyp_xpnedisj_1 : Nominal.NPrf (.classMem C (syn_cvv))) (hyp_xpnedisj_2 : Nominal.NPrf (syn_wne C D)) :
    Nominal.NPrf (.classEq (syn_cin (syn_cxp A (syn_csn C)) (syn_cxp B (syn_csn D))) (syn_c0)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
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
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have dv_cache_0001 : x ∉ ((syn_cxp A (syn_csn C))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cxp B (syn_csn D))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((syn_csn C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : z ∉ ((syn_csn C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0010 : z ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : z ∉ ((Wff.classEq (.cv x) (syn_cop (.cv y) C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ ((Wff.neg (.classMem (.cv x) (syn_cxp B (syn_csn D))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_B, fresh_y_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_disj x (syn_cxp A (syn_csn C)) (syn_cxp B (syn_csn D)) dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_elxp2 y z (.cv x) A (syn_csn C) dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0002 :=
    @g_opeq2 (.cv z) C (.cv y)
  have p0003 :=
    @g_eqeq2d (.classEq (.cv z) C) (syn_cop (.cv y) (.cv z)) (syn_cop (.cv y) C) (.cv x) p0002
  have p0004 :=
    @g_rexsn (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) (.classEq (.cv x) (syn_cop (.cv y) C)) z C dv_cache_0010 dv_cache_0011 hyp_xpnedisj_1 p0003
  have p0005 :=
    @g_rexbii (syn_wrex z (syn_csn C) (.classEq (.cv x) (syn_cop (.cv y) (.cv z)))) (.classEq (.cv x) (syn_cop (.cv y) C)) y A p0004
  have p0006 :=
    @g_bitri (.classMem (.cv x) (syn_cxp A (syn_csn C))) (syn_wrex y A (syn_wrex z (syn_csn C) (.classEq (.cv x) (syn_cop (.cv y) (.cv z))))) (syn_wrex y A (.classEq (.cv x) (syn_cop (.cv y) C))) p0001 p0005
  have p0007 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne C D)))
  have p0008 :=
    @g_mpbi (syn_wne C D) (.neg (.classEq C D)) hyp_xpnedisj_2 p0007
  have p0009 :=
    @g_elsni C D
  have p0010 :=
    @g_mto (.classMem C (syn_csn D)) (.classEq C D) p0008 p0009
  have p0011 :=
    @g_intnan (.classMem C (syn_csn D)) (.classMem (.cv y) B) p0010
  have p0012 :=
    @g_eleq1 (.cv x) (syn_cop (.cv y) C) (syn_cxp B (syn_csn D))
  have p0013 :=
    @g_opelxp (.cv y) C B (syn_csn D)
  have p0014 :=
    @g_syl6bb (.classEq (.cv x) (syn_cop (.cv y) C)) (.classMem (.cv x) (syn_cxp B (syn_csn D))) (.classMem (syn_cop (.cv y) C) (syn_cxp B (syn_csn D))) (syn_wa (.classMem (.cv y) B) (.classMem C (syn_csn D))) p0012 p0013
  have p0015 :=
    @g_mtbiri (.classEq (.cv x) (syn_cop (.cv y) C)) (.classMem (.cv x) (syn_cxp B (syn_csn D))) (syn_wa (.classMem (.cv y) B) (.classMem C (syn_csn D))) p0011 p0014
  have p0016 :=
    @g_rexlimivw (.classEq (.cv x) (syn_cop (.cv y) C)) (.neg (.classMem (.cv x) (syn_cxp B (syn_csn D)))) y A dv_cache_0012 p0015
  have p0017 :=
    @g_sylbi (.classMem (.cv x) (syn_cxp A (syn_csn C))) (syn_wrex y A (.classEq (.cv x) (syn_cop (.cv y) C))) (.neg (.classMem (.cv x) (syn_cxp B (syn_csn D)))) p0006 p0016
  have p0018 :=
    @g_mprgbir (.classEq (syn_cin (syn_cxp A (syn_csn C)) (syn_cxp B (syn_csn D))) (syn_c0)) (.neg (.classMem (.cv x) (syn_cxp B (syn_csn D)))) x (syn_cxp A (syn_csn C)) p0000 p0017
  exact p0018

noncomputable def g_opfv1st
    (A : Class) (B : Class) (hyp_opfv1st_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_opfv1st_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_c1st) (syn_cop A B)) A) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_eqid A
  have p0001 :=
    @g_opbr1st A B A hyp_opfv1st_1 hyp_opfv1st_2
  have p0002 :=
    @g_mpbir (syn_wbr (syn_cop A B) (syn_c1st) A) (.classEq A A) p0000 p0001
  have p0003 :=
    @g_n_1stfo
  have p0004 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_opex A B hyp_opfv1st_1 hyp_opfv1st_2
  have p0007 :=
    @g_fnbrfvb (syn_cvv) (syn_cop A B) A (syn_c1st)
  have p0008 :=
    @g_mp2an (syn_wfn (syn_c1st) (syn_cvv)) (.classMem (syn_cop A B) (syn_cvv)) (syn_wb (.classEq (syn_cfv (syn_c1st) (syn_cop A B)) A) (syn_wbr (syn_cop A B) (syn_c1st) A)) p0005 p0006 p0007
  have p0009 :=
    @g_mpbir (.classEq (syn_cfv (syn_c1st) (syn_cop A B)) A) (syn_wbr (syn_cop A B) (syn_c1st) A) p0002 p0008
  exact p0009

noncomputable def g_opfv2nd
    (A : Class) (B : Class) (hyp_opfv1st_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_opfv1st_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_c2nd) (syn_cop A B)) B) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_eqid B
  have p0001 :=
    @g_opbr2nd A B B hyp_opfv1st_1 hyp_opfv1st_2
  have p0002 :=
    @g_mpbir (syn_wbr (syn_cop A B) (syn_c2nd) B) (.classEq B B) p0000 p0001
  have p0003 :=
    @g_n_2ndfo
  have p0004 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_opex A B hyp_opfv1st_1 hyp_opfv1st_2
  have p0007 :=
    @g_fnbrfvb (syn_cvv) (syn_cop A B) B (syn_c2nd)
  have p0008 :=
    @g_mp2an (syn_wfn (syn_c2nd) (syn_cvv)) (.classMem (syn_cop A B) (syn_cvv)) (syn_wb (.classEq (syn_cfv (syn_c2nd) (syn_cop A B)) B) (syn_wbr (syn_cop A B) (syn_c2nd) B)) p0005 p0006 p0007
  have p0009 :=
    @g_mpbir (.classEq (syn_cfv (syn_c2nd) (syn_cop A B)) B) (syn_wbr (syn_cop A B) (syn_c2nd) B) p0002 p0008
  exact p0009

#print axioms g_opfv2nd

end NFChoice.DirectNominalPrf.WPPReplay
