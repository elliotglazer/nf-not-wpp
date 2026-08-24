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
import NominalWPPReplayChunk013Compact001Part001

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

noncomputable def g_addcfnex
     :
    Nominal.NPrf (.classMem (syn_caddcfn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let a : Var := freshVar proofSupport 3
  let b : Var := freshVar proofSupport 4
  let p : Var := freshVar proofSupport 5
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
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
  have fresh_x_ne_a : x ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_a_ne_x : a ≠ x :=
    Ne.symm fresh_x_ne_a
  have fresh_x_ne_b : x ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_b_ne_x : b ≠ x :=
    Ne.symm fresh_x_ne_b
  have fresh_x_ne_p : x ≠ p := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_p_ne_x : p ≠ x :=
    Ne.symm fresh_x_ne_p
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_y_ne_a : y ≠ a := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_a_ne_y : a ≠ y :=
    Ne.symm fresh_y_ne_a
  have fresh_y_ne_b : y ≠ b := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_b_ne_y : b ≠ y :=
    Ne.symm fresh_y_ne_b
  have fresh_y_ne_p : y ≠ p := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_p_ne_y : p ≠ y :=
    Ne.symm fresh_y_ne_p
  have fresh_z_ne_a : z ≠ a := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_a_ne_z : a ≠ z :=
    Ne.symm fresh_z_ne_a
  have fresh_z_ne_b : z ≠ b := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_b_ne_z : b ≠ z :=
    Ne.symm fresh_z_ne_b
  have fresh_z_ne_p : z ≠ p := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_p_ne_z : p ≠ z :=
    Ne.symm fresh_z_ne_p
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have fresh_a_ne_p : a ≠ p := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_p_ne_a : p ≠ a :=
    Ne.symm fresh_a_ne_p
  have fresh_b_ne_p : b ≠ p := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_p_ne_b : p ≠ b :=
    Ne.symm fresh_b_ne_p
  have dv_cache_0001 : x ≠ y := by
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0002 : x ∉ ((Class.cv p)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_c1st)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((syn_wbr (.cv p) (syn_c1st) (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_p, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_cop (.cv a) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_a, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_p, fresh_x_ne_a, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_p, fresh_y_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : z ∉ ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : z ∉ ((syn_cop (.cv a) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_a, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : z ∉ ((syn_wb (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b)) (.objEq y b))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_p, fresh_z_ne_b, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : y ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : y ∉ ((syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv b)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_p, fresh_y_ne_a, fresh_y_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : p ∉ ((syn_cop (.cv a) (syn_cop (.cv b) (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_a, fresh_p_ne_b, fresh_p_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : p ∉ ((syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : p ∉ ((syn_ccup)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccup, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : p ∉ ((syn_cop (syn_cop (.cv a) (.cv b)) (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_a, fresh_p_ne_b, fresh_p_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : a ∉ ((syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_b, fresh_a_ne_z, fresh_a_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : a ∉ ((syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdisj, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccup, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : b ∉ ((syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_z, fresh_b_ne_x, fresh_b_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : b ∉ ((syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))))) (syn_c1c))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdisj, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccup, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : a ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : b ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : a ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : b ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0028 : a ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0029 : b ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0030 : a ≠ b := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0031 : x ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0032 : y ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0033 : x ∉ ((syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))))) (syn_c1c)))) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdisj, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccup, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0034 : y ∉ ((syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))))) (syn_c1c)))) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdisj, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccup, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0035 : z ∉ ((syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))))) (syn_c1c)))) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdisj, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccup, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0036 : z ∉ ((syn_cplc (.cv x) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0037 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0038 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_addcfn x y dv_cache_0001
  have p0001 :=
    @g_elin (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))) (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))))) (syn_c1c)))
  have p0002 :=
    @g_snex (.cv z)
  have p0003 :=
    @g_otelins2 (syn_csn (.cv b)) (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)) (syn_cins2 (syn_csset)) p0002
  have p0004 :=
    @g_vex x
  have p0005 :=
    @g_otelins2 (syn_csn (.cv b)) (.cv x) (.cv y) (syn_csset) p0004
  have p0006 :=
    @g_vex b
  have p0007 :=
    @g_vex y
  have p0008 :=
    @g_opelssetsn (.cv b) (.cv y) p0006 p0007
  have p0009_e02_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv b)) (.cv y)) (syn_csset)) (.objMem b y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
      p0008
  have p0009 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.classMem (syn_cop (syn_csn (.cv b)) (syn_cop (.cv x) (.cv y))) (syn_cins2 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv b)) (.cv y)) (syn_csset)) (.objMem b y) p0003 p0005 p0009_e02_recanon
  have p0010 :=
    @g_oqelins4 (syn_csn (.cv b)) (syn_csn (.cv z)) (.cv x) (.cv y) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))))) (syn_c1c)) p0007
  have p0011 :=
    @g_elin (syn_cop (syn_csn (.cv a)) (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x)))) (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))))
  have p0012 :=
    @g_snex (.cv b)
  have p0013 :=
    @g_otelins2 (syn_csn (.cv a)) (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x)) (syn_cins2 (syn_csset)) p0012
  have p0014 :=
    @g_otelins2 (syn_csn (.cv a)) (syn_csn (.cv z)) (.cv x) (syn_csset) p0002
  have p0015 :=
    @g_vex a
  have p0016 :=
    @g_opelssetsn (.cv a) (.cv x) p0015 p0004
  have p0017_e02_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv a)) (.cv x)) (syn_csset)) (.objMem a x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
      p0016
  have p0017 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv a)) (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.classMem (syn_cop (syn_csn (.cv a)) (syn_cop (syn_csn (.cv z)) (.cv x))) (syn_cins2 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv a)) (.cv x)) (syn_csset)) (.objMem a x) p0013 p0014 p0017_e02_recanon
  have p0018 :=
    @g_oqelins4 (syn_csn (.cv a)) (syn_csn (.cv b)) (syn_csn (.cv z)) (.cv x) (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))) p0004
  have p0019 :=
    @g_vex z
  have p0020 :=
    @g_otsnelsi3 (.cv a) (.cv b) (.cv z) (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup))) p0015 p0006 p0019
  have p0021 :=
    @g_elin (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))) (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup))
  have p0022 :=
    @g_otelins3 (.cv a) (.cv b) (.cv z) (syn_cdisj) p0019
  have p0023 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv a) (syn_cdisj) (.cv b))))
  have p0024 :=
    @g_brdisj (.cv a) (.cv b) p0015 p0006
  have p0025 :=
    @g_n_3bitr2i (.classMem (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))) (syn_cins3 (syn_cdisj))) (.classMem (syn_cop (.cv a) (.cv b)) (syn_cdisj)) (syn_wbr (.cv a) (syn_cdisj) (.cv b)) (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) p0022 p0023 p0024
  have p0026 :=
    @g_trtxp (.cv p) (.cv b) (.cv z) (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)
  have p0027 :=
    @g_anbi2i (syn_wbr (.cv p) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)) (syn_cop (.cv b) (.cv z))) (syn_wa (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b)) (syn_wbr (.cv p) (syn_c2nd) (.cv z))) (syn_wbr (.cv p) (syn_ccom (syn_c1st) (syn_c1st)) (.cv a)) p0026
  have p0028 :=
    @g_trtxp (.cv p) (.cv a) (syn_cop (.cv b) (.cv z)) (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))
  have p0029 :=
    @g_anass (syn_wbr (.cv p) (syn_ccom (syn_c1st) (syn_c1st)) (.cv a)) (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b)) (syn_wbr (.cv p) (syn_c2nd) (.cv z))
  have p0030 :=
    @g_n_3bitr4i (syn_wa (syn_wbr (.cv p) (syn_ccom (syn_c1st) (syn_c1st)) (.cv a)) (syn_wbr (.cv p) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)) (syn_cop (.cv b) (.cv z)))) (syn_wa (syn_wbr (.cv p) (syn_ccom (syn_c1st) (syn_c1st)) (.cv a)) (syn_wa (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b)) (syn_wbr (.cv p) (syn_c2nd) (.cv z)))) (syn_wbr (.cv p) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_cop (.cv a) (syn_cop (.cv b) (.cv z)))) (syn_wa (syn_wa (syn_wbr (.cv p) (syn_ccom (syn_c1st) (syn_c1st)) (.cv a)) (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b))) (syn_wbr (.cv p) (syn_c2nd) (.cv z))) p0027 p0028 p0029
  have p0031 :=
    @g_brco x (.cv p) (.cv a) (syn_c1st) (syn_c1st) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0004
  have p0032 :=
    @g_br1st y (.cv x) (.cv a) dv_cache_0005 dv_cache_0006 p0015
  have p0033 :=
    @g_anbi2i (syn_wbr (.cv x) (syn_c1st) (.cv a)) (syn_wex y (.classEq (.cv x) (syn_cop (.cv a) (.cv y)))) (syn_wbr (.cv p) (syn_c1st) (.cv x)) p0032
  have p0034 :=
    @g_n_19_42v (syn_wbr (.cv p) (syn_c1st) (.cv x)) (.classEq (.cv x) (syn_cop (.cv a) (.cv y))) y dv_cache_0007
  have p0035 :=
    @g_bitr4i (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv x)) (syn_wbr (.cv x) (syn_c1st) (.cv a))) (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv x)) (syn_wex y (.classEq (.cv x) (syn_cop (.cv a) (.cv y))))) (syn_wex y (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv x)) (.classEq (.cv x) (syn_cop (.cv a) (.cv y))))) p0033 p0034
  have p0036 :=
    @g_exbii (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv x)) (syn_wbr (.cv x) (syn_c1st) (.cv a))) (syn_wex y (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv x)) (.classEq (.cv x) (syn_cop (.cv a) (.cv y))))) x p0035
  have p0037 :=
    @g_excom (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv x)) (.classEq (.cv x) (syn_cop (.cv a) (.cv y)))) x y
  have p0038 :=
    @g_exancom (syn_wbr (.cv p) (syn_c1st) (.cv x)) (.classEq (.cv x) (syn_cop (.cv a) (.cv y))) x
  have p0039 :=
    @g_opex (.cv a) (.cv y) p0015 p0007
  have p0040 :=
    @g_breq2 (.cv x) (syn_cop (.cv a) (.cv y)) (.cv p) (syn_c1st)
  have p0041 :=
    @g_ceqsexv (syn_wbr (.cv p) (syn_c1st) (.cv x)) (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y))) x (syn_cop (.cv a) (.cv y)) dv_cache_0008 dv_cache_0009 p0039 p0040
  have p0042 :=
    @g_bitri (syn_wex x (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv x)) (.classEq (.cv x) (syn_cop (.cv a) (.cv y))))) (syn_wex x (syn_wa (.classEq (.cv x) (syn_cop (.cv a) (.cv y))) (syn_wbr (.cv p) (syn_c1st) (.cv x)))) (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y))) p0038 p0041
  have p0043 :=
    @g_exbii (syn_wex x (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv x)) (.classEq (.cv x) (syn_cop (.cv a) (.cv y))))) (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y))) y p0042
  have p0044 :=
    @g_bitri (syn_wex x (syn_wex y (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv x)) (.classEq (.cv x) (syn_cop (.cv a) (.cv y)))))) (syn_wex y (syn_wex x (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv x)) (.classEq (.cv x) (syn_cop (.cv a) (.cv y)))))) (syn_wex y (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y)))) p0037 p0043
  have p0045 :=
    @g_n_3bitri (syn_wbr (.cv p) (syn_ccom (syn_c1st) (syn_c1st)) (.cv a)) (syn_wex x (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv x)) (syn_wbr (.cv x) (syn_c1st) (.cv a)))) (syn_wex x (syn_wex y (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv x)) (.classEq (.cv x) (syn_cop (.cv a) (.cv y)))))) (syn_wex y (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y)))) p0031 p0036 p0044
  have p0046 :=
    @g_anbi1i (syn_wbr (.cv p) (syn_ccom (syn_c1st) (syn_c1st)) (.cv a)) (syn_wex y (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y)))) (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b)) p0045
  have p0047 :=
    @g_n_19_41v (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y))) (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b)) y dv_cache_0010
  have p0048 :=
    @g_br1st z (.cv p) (syn_cop (.cv a) (.cv y)) dv_cache_0011 dv_cache_0012 p0039
  have p0049 :=
    @g_breq1 (.cv p) (syn_cop (syn_cop (.cv a) (.cv y)) (.cv z)) (.cv b) (syn_ccom (syn_c2nd) (syn_c1st))
  have p0050 :=
    @g_brco1st (syn_cop (.cv a) (.cv y)) (.cv z) (.cv b) (syn_c2nd) p0039 p0019
  have p0051 :=
    @g_opbr2nd (.cv a) (.cv y) (.cv b) p0015 p0007
  have p0052_e01_recanon : Nominal.NPrf (syn_wb (syn_wbr (syn_cop (.cv a) (.cv y)) (syn_c2nd) (.cv b)) (.objEq y b)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_c2nd syn_copab
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
      p0051
  have p0052 :=
    @g_bitri (syn_wbr (syn_cop (syn_cop (.cv a) (.cv y)) (.cv z)) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b)) (syn_wbr (syn_cop (.cv a) (.cv y)) (syn_c2nd) (.cv b)) (.objEq y b) p0050 p0052_e01_recanon
  have p0053 :=
    @g_syl6bb (.classEq (.cv p) (syn_cop (syn_cop (.cv a) (.cv y)) (.cv z))) (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b)) (syn_wbr (syn_cop (syn_cop (.cv a) (.cv y)) (.cv z)) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b)) (.objEq y b) p0049 p0052
  have p0054 :=
    @g_exlimiv (.classEq (.cv p) (syn_cop (syn_cop (.cv a) (.cv y)) (.cv z))) (syn_wb (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b)) (.objEq y b)) z dv_cache_0013 p0053
  have p0055 :=
    @g_sylbi (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y))) (syn_wex z (.classEq (.cv p) (syn_cop (syn_cop (.cv a) (.cv y)) (.cv z)))) (syn_wb (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b)) (.objEq y b)) p0048 p0054
  have p0056 :=
    @g_pm5_32i (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y))) (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b)) (.objEq y b) p0055
  have p0057 :=
    @g_exbii (syn_wa (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y))) (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b))) (syn_wa (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y))) (.objEq y b)) y p0056
  have p0058 :=
    @g_exancom (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y))) (.objEq y b) y
  have p0059 :=
    @g_bitri (syn_wex y (syn_wa (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y))) (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b)))) (syn_wex y (syn_wa (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y))) (.objEq y b))) (syn_wex y (syn_wa (.objEq y b) (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y))))) p0057 p0058
  have p0060 :=
    @g_n_3bitr2i (syn_wa (syn_wbr (.cv p) (syn_ccom (syn_c1st) (syn_c1st)) (.cv a)) (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b))) (syn_wa (syn_wex y (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y)))) (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b))) (syn_wex y (syn_wa (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y))) (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b)))) (syn_wex y (syn_wa (.objEq y b) (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y))))) p0046 p0047 p0059
  have p0061 :=
    @g_opeq2 (.cv y) (.cv b) (.cv a)
  have p0062_e00_recanon : Nominal.NPrf (.imp (.objEq y b) (.classEq (syn_cop (.cv a) (.cv y)) (syn_cop (.cv a) (.cv b)))) :=
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
      p0061
  have p0062 :=
    @g_breq2d (.objEq y b) (syn_cop (.cv a) (.cv y)) (syn_cop (.cv a) (.cv b)) (.cv p) (syn_c1st) p0062_e00_recanon
  have p0063_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv y) (.cv b)) (syn_wb (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y))) (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv b))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_c1st syn_copab
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0062
  have p0063 :=
    @g_ceqsexv (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y))) (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv b))) y (.cv b) dv_cache_0014 dv_cache_0015 p0006 p0063_e01_recanon
  have p0064_e01_recanon : Nominal.NPrf (syn_wb (syn_wex y (syn_wa (.objEq y b) (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y))))) (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv b)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex syn_cphi syn_c1st syn_copab
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
      p0063
  have p0064 :=
    @g_bitri (syn_wa (syn_wbr (.cv p) (syn_ccom (syn_c1st) (syn_c1st)) (.cv a)) (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b))) (syn_wex y (syn_wa (.objEq y b) (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv y))))) (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv b))) p0060 p0064_e01_recanon
  have p0065 :=
    @g_anbi1i (syn_wa (syn_wbr (.cv p) (syn_ccom (syn_c1st) (syn_c1st)) (.cv a)) (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b))) (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv b))) (syn_wbr (.cv p) (syn_c2nd) (.cv z)) p0064
  have p0066 :=
    @g_opex (.cv a) (.cv b) p0015 p0006
  have p0067 :=
    @g_op1st2nd (syn_cop (.cv a) (.cv b)) (.cv z) (.cv p) p0066 p0019
  have p0068 :=
    @g_n_3bitri (syn_wbr (.cv p) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_cop (.cv a) (syn_cop (.cv b) (.cv z)))) (syn_wa (syn_wa (syn_wbr (.cv p) (syn_ccom (syn_c1st) (syn_c1st)) (.cv a)) (syn_wbr (.cv p) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv b))) (syn_wbr (.cv p) (syn_c2nd) (.cv z))) (syn_wa (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv a) (.cv b))) (syn_wbr (.cv p) (syn_c2nd) (.cv z))) (.classEq (.cv p) (syn_cop (syn_cop (.cv a) (.cv b)) (.cv z))) p0030 p0065 p0067
  have p0069 :=
    @g_rexbii (syn_wbr (.cv p) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_cop (.cv a) (syn_cop (.cv b) (.cv z)))) (.classEq (.cv p) (syn_cop (syn_cop (.cv a) (.cv b)) (.cv z))) p (syn_ccup) p0068
  have p0070 :=
    @g_elima p (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup) dv_cache_0016 dv_cache_0017 dv_cache_0018
  have p0071 :=
    @g_risset p (syn_cop (syn_cop (.cv a) (.cv b)) (.cv z)) (syn_ccup) dv_cache_0019 dv_cache_0018
  have p0072 :=
    @g_n_3bitr4i (syn_wrex p (syn_ccup) (syn_wbr (.cv p) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))))) (syn_wrex p (syn_ccup) (.classEq (.cv p) (syn_cop (syn_cop (.cv a) (.cv b)) (.cv z)))) (.classMem (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup))) (.classMem (syn_cop (syn_cop (.cv a) (.cv b)) (.cv z)) (syn_ccup)) p0069 p0070 p0071
  have p0073 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (syn_cop (.cv a) (.cv b)) (syn_ccup) (.cv z))))
  have p0074 :=
    @g_brcup (.cv a) (.cv b) (.cv z) p0015 p0006
  have p0075 :=
    @g_n_3bitr2i (.classMem (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup))) (.classMem (syn_cop (syn_cop (.cv a) (.cv b)) (.cv z)) (syn_ccup)) (syn_wbr (syn_cop (.cv a) (.cv b)) (syn_ccup) (.cv z)) (.classEq (.cv z) (syn_cun (.cv a) (.cv b))) p0072 p0073 p0074
  have p0076 :=
    @g_anbi12i (.classMem (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))) (syn_cins3 (syn_cdisj))) (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classMem (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup))) (.classEq (.cv z) (syn_cun (.cv a) (.cv b))) p0025 p0075
  have p0077 :=
    @g_bitri (.classMem (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))) (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))) (syn_wa (.classMem (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))) (syn_cins3 (syn_cdisj))) (.classMem (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv z) (syn_cun (.cv a) (.cv b)))) p0021 p0076
  have p0078 :=
    @g_n_3bitri (.classMem (syn_cop (syn_csn (.cv a)) (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x)))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))))) (.classMem (syn_cop (syn_csn (.cv a)) (syn_cop (syn_csn (.cv b)) (syn_csn (.cv z)))) (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup))))) (.classMem (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))) (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv z) (syn_cun (.cv a) (.cv b)))) p0018 p0020 p0077
  have p0079 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv a)) (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.objMem a x) (.classMem (syn_cop (syn_csn (.cv a)) (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x)))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))))) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv z) (syn_cun (.cv a) (.cv b)))) p0017 p0078
  have p0080 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv a)) (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x)))) (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup))))))) (syn_wa (.classMem (syn_cop (syn_csn (.cv a)) (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.classMem (syn_cop (syn_csn (.cv a)) (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x)))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup))))))) (syn_wa (.objMem a x) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv z) (syn_cun (.cv a) (.cv b))))) p0011 p0079
  have p0081 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv a)) (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x)))) (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup))))))) (syn_wa (.objMem a x) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv z) (syn_cun (.cv a) (.cv b))))) a p0080
  have p0082 :=
    @g_elima1c a (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x))) (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))))) dv_cache_0020 dv_cache_0021
  have p0083 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex a (.cv x) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv z) (syn_cun (.cv a) (.cv b)))))))
  have p0084_e02_recanon : Nominal.NPrf (syn_wb (syn_wrex a (.cv x) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv z) (syn_cun (.cv a) (.cv b))))) (syn_wex a (syn_wa (.objMem a x) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv z) (syn_cun (.cv a) (.cv b))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wrex syn_wex syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
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
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0083
  have p0084 :=
    @g_n_3bitr4i (syn_wex a (.classMem (syn_cop (syn_csn (.cv a)) (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x)))) (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))))))) (syn_wex a (syn_wa (.objMem a x) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv z) (syn_cun (.cv a) (.cv b)))))) (.classMem (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))))) (syn_c1c))) (syn_wrex a (.cv x) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv z) (syn_cun (.cv a) (.cv b))))) p0081 p0082 p0084_e02_recanon
  have p0085 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))))) (syn_c1c)))) (.classMem (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))))) (syn_c1c))) (syn_wrex a (.cv x) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv z) (syn_cun (.cv a) (.cv b))))) p0010 p0084
  have p0086 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.objMem b y) (.classMem (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))))) (syn_c1c)))) (syn_wrex a (.cv x) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv z) (syn_cun (.cv a) (.cv b))))) p0009 p0085
  have p0087 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))) (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))))) (syn_c1c))))) (syn_wa (.classMem (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))) (syn_cins2 (syn_cins2 (syn_csset)))) (.classMem (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))))) (syn_c1c))))) (syn_wa (.objMem b y) (syn_wrex a (.cv x) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv z) (syn_cun (.cv a) (.cv b)))))) p0001 p0086
  have p0088 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))) (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))))) (syn_c1c))))) (syn_wa (.objMem b y) (syn_wrex a (.cv x) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv z) (syn_cun (.cv a) (.cv b)))))) b p0087
  have p0089 :=
    @g_elima1c b (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))))) (syn_c1c)))) dv_cache_0022 dv_cache_0023
  have p0090 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex b (.cv y) (syn_wrex a (.cv x) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv z) (syn_cun (.cv a) (.cv b))))))))
  have p0091_e02_recanon : Nominal.NPrf (syn_wb (syn_wrex b (.cv y) (syn_wrex a (.cv x) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv z) (syn_cun (.cv a) (.cv b)))))) (syn_wex b (syn_wa (.objMem b y) (syn_wrex a (.cv x) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv z) (syn_cun (.cv a) (.cv b)))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wrex syn_wex syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
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
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0090
  have p0091 :=
    @g_n_3bitr4i (syn_wex b (.classMem (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))) (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))))) (syn_c1c)))))) (syn_wex b (syn_wa (.objMem b y) (syn_wrex a (.cv x) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv z) (syn_cun (.cv a) (.cv b))))))) (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))))) (syn_c1c)))) (syn_c1c))) (syn_wrex b (.cv y) (syn_wrex a (.cv x) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv z) (syn_cun (.cv a) (.cv b)))))) p0088 p0089 p0091_e02_recanon
  have p0092 :=
    @g_eladdc (.cv z) (.cv x) (.cv y) a b dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
  have p0093 :=
    @g_rexcom (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv z) (syn_cun (.cv a) (.cv b)))) a b (.cv x) (.cv y) dv_cache_0027 dv_cache_0028 dv_cache_0030
  have p0094 :=
    @g_bitri (.classMem (.cv z) (syn_cplc (.cv x) (.cv y))) (syn_wrex a (.cv x) (syn_wrex b (.cv y) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv z) (syn_cun (.cv a) (.cv b)))))) (syn_wrex b (.cv y) (syn_wrex a (.cv x) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv z) (syn_cun (.cv a) (.cv b)))))) p0092 p0093
  have p0095 :=
    @g_bitr4i (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))))) (syn_c1c)))) (syn_c1c))) (syn_wrex b (.cv y) (syn_wrex a (.cv x) (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) (.classEq (.cv z) (syn_cun (.cv a) (.cv b)))))) (.classMem (.cv z) (syn_cplc (.cv x) (.cv y))) p0091 p0094
  have p0096 :=
    @g_releqmpt2 x y z (syn_cvv) (syn_cvv) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))))) (syn_c1c)))) (syn_c1c)) (syn_cplc (.cv x) (.cv y)) dv_cache_0031 dv_cache_0032 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0001 dv_cache_0037 dv_cache_0038 p0095
  have p0097 :=
    @g_eqtr4i (syn_caddcfn) (syn_cmpt2 x (syn_cvv) y (syn_cvv) (syn_cplc (.cv x) (.cv y))) (syn_cdif (syn_cxp (syn_cxp (syn_cvv) (syn_cvv)) (syn_cvv)) (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))))) (syn_c1c)))) (syn_c1c)))) (syn_c1c))) p0000 p0096
  have p0098 :=
    @g_vvex
  have p0099 :=
    @g_vvex
  have p0100 :=
    @g_ssetex
  have p0101 :=
    @g_ins2ex (syn_csset) p0100
  have p0102 :=
    @g_ins2ex (syn_cins2 (syn_csset)) p0101
  have p0103 :=
    @g_disjex
  have p0104 :=
    @g_ins3ex (syn_cdisj) p0103
  have p0105 :=
    @g_n_1stex
  have p0106 :=
    @g_n_1stex
  have p0107 :=
    @g_coex (syn_c1st) (syn_c1st) p0105 p0106
  have p0108 :=
    @g_n_2ndex
  have p0109 :=
    @g_n_1stex
  have p0110 :=
    @g_coex (syn_c2nd) (syn_c1st) p0108 p0109
  have p0111 :=
    @g_n_2ndex
  have p0112 :=
    @g_txpex (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd) p0110 p0111
  have p0113 :=
    @g_txpex (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)) p0107 p0112
  have p0114 :=
    @g_cupex
  have p0115 :=
    @g_imaex (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup) p0113 p0114
  have p0116 :=
    @g_inex (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)) p0104 p0115
  have p0117 :=
    @g_si3ex (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup))) p0116
  have p0118 :=
    @g_ins4ex (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))) p0117
  have p0119 :=
    @g_inex (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup))))) p0102 p0118
  have p0120 :=
    @g_n_1cex
  have p0121 :=
    @g_imaex (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))))) (syn_c1c) p0119 p0120
  have p0122 :=
    @g_ins4ex (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))))) (syn_c1c)) p0121
  have p0123 :=
    @g_inex (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))))) (syn_c1c))) p0102 p0122
  have p0124 :=
    @g_n_1cex
  have p0125 :=
    @g_imaex (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))))) (syn_c1c)))) (syn_c1c) p0123 p0124
  have p0126 :=
    @g_mpt2exlem (syn_cvv) (syn_cvv) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))))) (syn_c1c)))) (syn_c1c)) p0098 p0099 p0125
  have p0127 :=
    @g_eqeltri (syn_caddcfn) (syn_cdif (syn_cxp (syn_cxp (syn_cvv) (syn_cvv)) (syn_cvv)) (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3 (syn_cin (syn_cins3 (syn_cdisj)) (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_ccup)))))) (syn_c1c)))) (syn_c1c)))) (syn_c1c))) (syn_cvv) p0097 p0126
  exact p0127

#print axioms g_addcfnex

end NFChoice.DirectNominalPrf.WPPReplay
