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
import NominalWPPReplayChunk013Compact001Part033

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

noncomputable def g_enpw1lem1
    (x : Var) (y : Var) (g : Var) (dv_g_x : g ≠ x) (dv_g_y : g ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classMem (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (syn_cvv)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({g} : Finset Var)
  let p : Var := freshVar proofSupport 0
  let a : Var := freshVar proofSupport 1
  let b : Var := freshVar proofSupport 2
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_ne_x : p ≠ x := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_p : x ≠ p :=
    Ne.symm fresh_p_ne_x
  have fresh_p_ne_y : p ≠ y := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_p : y ≠ p :=
    Ne.symm fresh_p_ne_y
  have fresh_p_ne_g : p ≠ g := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_g_ne_p : g ≠ p :=
    Ne.symm fresh_p_ne_g
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_a_ne_x : a ≠ x := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_a : x ≠ a :=
    Ne.symm fresh_a_ne_x
  have fresh_a_ne_y : a ≠ y := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_a : y ≠ a :=
    Ne.symm fresh_a_ne_y
  have fresh_a_ne_g : a ≠ g := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_g_ne_a : g ≠ a :=
    Ne.symm fresh_a_ne_g
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_b_ne_x : b ≠ x := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_b : x ≠ b :=
    Ne.symm fresh_b_ne_x
  have fresh_b_ne_y : b ≠ y := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_b : y ≠ b :=
    Ne.symm fresh_b_ne_y
  have fresh_b_ne_g : b ≠ g := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_g_ne_b : g ≠ b :=
    Ne.symm fresh_b_ne_g
  have fresh_p_ne_a : p ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_p : a ≠ p :=
    Ne.symm fresh_p_ne_a
  have fresh_p_ne_b : p ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_b_ne_p : b ≠ p :=
    Ne.symm fresh_p_ne_b
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have dv_cache_0001 : p ∉ ((syn_csn (syn_cop (.cv x) (.cv y)))).fv := by
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_x, fresh_p_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((syn_cin (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st)) (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : p ∉ ((Class.cv g)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : a ∉ ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : a ∉ ((syn_csn (syn_cop (.cv x) (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_x, fresh_a_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : a ∉ ((syn_csi (syn_ccnv (syn_c1st)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : a ∉ ((syn_c1st)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : b ∉ ((syn_cop (.cv x) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_x, fresh_b_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : b ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : b ∉ ((syn_ccnv (syn_c1st))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : b ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : b ∉ ((Wff.classEq (.cv a) (syn_csn (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_a, fresh_b_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : a ∉ ((syn_csn (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : a ∉ ((syn_wbr (.cv p) (syn_c1st) (syn_csn (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_p, fresh_a_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : a ∉ ((syn_csi (syn_ccnv (syn_c2nd)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : a ∉ ((syn_c2nd)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : b ∉ ((syn_ccnv (syn_c2nd))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : b ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : b ∉ ((Wff.classEq (.cv a) (syn_csn (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_a, fresh_b_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : a ∉ ((syn_csn (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : a ∉ ((syn_wbr (.cv p) (syn_c2nd) (syn_csn (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_p, fresh_a_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : p ∉ ((syn_cop (syn_csn (.cv x)) (syn_csn (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_x, fresh_p_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : x ∉ ((syn_cuni1 (syn_cima (syn_cin (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st)) (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd))) (.cv g)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_g_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : y ∉ ((syn_cuni1 (syn_cima (syn_cin (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st)) (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd))) (.cv g)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_g_y), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @g_vex x
  have p0001 :=
    @g_vex y
  have p0002 :=
    @g_opex (.cv x) (.cv y) p0000 p0001
  have p0003 :=
    @g_eluni1 (syn_cop (.cv x) (.cv y)) (syn_cima (syn_cin (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st)) (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd))) (.cv g)) p0002
  have p0004 :=
    @g_elima p (syn_csn (syn_cop (.cv x) (.cv y))) (syn_cin (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st)) (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd))) (.cv g) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0005 :=
    @g_brin (.cv p) (syn_csn (syn_cop (.cv x) (.cv y))) (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st)) (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd))
  have p0006 :=
    @g_brco a (.cv p) (syn_csn (syn_cop (.cv x) (.cv y))) (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st) dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0007 :=
    @g_ancom (syn_wbr (.cv p) (syn_c1st) (.cv a)) (syn_wbr (.cv a) (syn_csi (syn_ccnv (syn_c1st))) (syn_csn (syn_cop (.cv x) (.cv y))))
  have p0008 :=
    @g_brsnsi2 b (syn_cop (.cv x) (.cv y)) (.cv a) (syn_ccnv (syn_c1st)) dv_cache_0008 dv_cache_0009 dv_cache_0010 p0002
  have p0009 :=
    @g_ancom (.classEq (.cv a) (syn_csn (.cv b))) (syn_wbr (.cv b) (syn_ccnv (syn_c1st)) (syn_cop (.cv x) (.cv y)))
  have p0010 :=
    @g_brcnv (.cv b) (syn_cop (.cv x) (.cv y)) (syn_c1st)
  have p0011 :=
    @g_opbr1st (.cv x) (.cv y) (.cv b) p0000 p0001
  have p0012 :=
    @g_equcom x b
  have p0013_e01_recanon : Nominal.NPrf (syn_wb (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_c1st) (.cv b)) (.objEq x b)) :=
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
      p0011
  have p0013 :=
    @g_n_3bitri (syn_wbr (.cv b) (syn_ccnv (syn_c1st)) (syn_cop (.cv x) (.cv y))) (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_c1st) (.cv b)) (.objEq x b) (.objEq b x) p0010 p0013_e01_recanon p0012
  have p0014 :=
    @g_anbi1i (syn_wbr (.cv b) (syn_ccnv (syn_c1st)) (syn_cop (.cv x) (.cv y))) (.objEq b x) (.classEq (.cv a) (syn_csn (.cv b))) p0013
  have p0015 :=
    @g_bitri (syn_wa (.classEq (.cv a) (syn_csn (.cv b))) (syn_wbr (.cv b) (syn_ccnv (syn_c1st)) (syn_cop (.cv x) (.cv y)))) (syn_wa (syn_wbr (.cv b) (syn_ccnv (syn_c1st)) (syn_cop (.cv x) (.cv y))) (.classEq (.cv a) (syn_csn (.cv b)))) (syn_wa (.objEq b x) (.classEq (.cv a) (syn_csn (.cv b)))) p0009 p0014
  have p0016 :=
    @g_exbii (syn_wa (.classEq (.cv a) (syn_csn (.cv b))) (syn_wbr (.cv b) (syn_ccnv (syn_c1st)) (syn_cop (.cv x) (.cv y)))) (syn_wa (.objEq b x) (.classEq (.cv a) (syn_csn (.cv b)))) b p0015
  have p0017 :=
    @g_sneq (.cv b) (.cv x)
  have p0018_e00_recanon : Nominal.NPrf (.imp (.objEq b x) (.classEq (syn_csn (.cv b)) (syn_csn (.cv x)))) :=
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
      p0017
  have p0018 :=
    @g_eqeq2d (.objEq b x) (syn_csn (.cv b)) (syn_csn (.cv x)) (.cv a) p0018_e00_recanon
  have p0019_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv b) (.cv x)) (syn_wb (.classEq (.cv a) (syn_csn (.cv b))) (.classEq (.cv a) (syn_csn (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0018
  have p0019 :=
    @g_ceqsexv (.classEq (.cv a) (syn_csn (.cv b))) (.classEq (.cv a) (syn_csn (.cv x))) b (.cv x) dv_cache_0011 dv_cache_0012 p0000 p0019_e01_recanon
  have p0020_e02_recanon : Nominal.NPrf (syn_wb (syn_wex b (syn_wa (.objEq b x) (.classEq (.cv a) (syn_csn (.cv b))))) (.classEq (.cv a) (syn_csn (.cv x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_wa syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
      p0019
  have p0020 :=
    @g_n_3bitri (syn_wbr (.cv a) (syn_csi (syn_ccnv (syn_c1st))) (syn_csn (syn_cop (.cv x) (.cv y)))) (syn_wex b (syn_wa (.classEq (.cv a) (syn_csn (.cv b))) (syn_wbr (.cv b) (syn_ccnv (syn_c1st)) (syn_cop (.cv x) (.cv y))))) (syn_wex b (syn_wa (.objEq b x) (.classEq (.cv a) (syn_csn (.cv b))))) (.classEq (.cv a) (syn_csn (.cv x))) p0008 p0016 p0020_e02_recanon
  have p0021 :=
    @g_anbi1i (syn_wbr (.cv a) (syn_csi (syn_ccnv (syn_c1st))) (syn_csn (syn_cop (.cv x) (.cv y)))) (.classEq (.cv a) (syn_csn (.cv x))) (syn_wbr (.cv p) (syn_c1st) (.cv a)) p0020
  have p0022 :=
    @g_bitri (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv a)) (syn_wbr (.cv a) (syn_csi (syn_ccnv (syn_c1st))) (syn_csn (syn_cop (.cv x) (.cv y))))) (syn_wa (syn_wbr (.cv a) (syn_csi (syn_ccnv (syn_c1st))) (syn_csn (syn_cop (.cv x) (.cv y)))) (syn_wbr (.cv p) (syn_c1st) (.cv a))) (syn_wa (.classEq (.cv a) (syn_csn (.cv x))) (syn_wbr (.cv p) (syn_c1st) (.cv a))) p0007 p0021
  have p0023 :=
    @g_exbii (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv a)) (syn_wbr (.cv a) (syn_csi (syn_ccnv (syn_c1st))) (syn_csn (syn_cop (.cv x) (.cv y))))) (syn_wa (.classEq (.cv a) (syn_csn (.cv x))) (syn_wbr (.cv p) (syn_c1st) (.cv a))) a p0022
  have p0024 :=
    @g_snex (.cv x)
  have p0025 :=
    @g_breq2 (.cv a) (syn_csn (.cv x)) (.cv p) (syn_c1st)
  have p0026 :=
    @g_ceqsexv (syn_wbr (.cv p) (syn_c1st) (.cv a)) (syn_wbr (.cv p) (syn_c1st) (syn_csn (.cv x))) a (syn_csn (.cv x)) dv_cache_0013 dv_cache_0014 p0024 p0025
  have p0027 :=
    @g_n_3bitri (syn_wbr (.cv p) (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st)) (syn_csn (syn_cop (.cv x) (.cv y)))) (syn_wex a (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv a)) (syn_wbr (.cv a) (syn_csi (syn_ccnv (syn_c1st))) (syn_csn (syn_cop (.cv x) (.cv y)))))) (syn_wex a (syn_wa (.classEq (.cv a) (syn_csn (.cv x))) (syn_wbr (.cv p) (syn_c1st) (.cv a)))) (syn_wbr (.cv p) (syn_c1st) (syn_csn (.cv x))) p0006 p0023 p0026
  have p0028 :=
    @g_brco a (.cv p) (syn_csn (syn_cop (.cv x) (.cv y))) (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd) dv_cache_0004 dv_cache_0005 dv_cache_0015 dv_cache_0016
  have p0029 :=
    @g_brsnsi2 b (syn_cop (.cv x) (.cv y)) (.cv a) (syn_ccnv (syn_c2nd)) dv_cache_0008 dv_cache_0009 dv_cache_0017 p0002
  have p0030 :=
    @g_brcnv (.cv b) (syn_cop (.cv x) (.cv y)) (syn_c2nd)
  have p0031 :=
    @g_opbr2nd (.cv x) (.cv y) (.cv b) p0000 p0001
  have p0032 :=
    @g_equcom y b
  have p0033_e01_recanon : Nominal.NPrf (syn_wb (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_c2nd) (.cv b)) (.objEq y b)) :=
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
      p0031
  have p0033 :=
    @g_n_3bitri (syn_wbr (.cv b) (syn_ccnv (syn_c2nd)) (syn_cop (.cv x) (.cv y))) (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_c2nd) (.cv b)) (.objEq y b) (.objEq b y) p0030 p0033_e01_recanon p0032
  have p0034 :=
    @g_anbi2i (syn_wbr (.cv b) (syn_ccnv (syn_c2nd)) (syn_cop (.cv x) (.cv y))) (.objEq b y) (.classEq (.cv a) (syn_csn (.cv b))) p0033
  have p0035 :=
    @g_ancom (.classEq (.cv a) (syn_csn (.cv b))) (.objEq b y)
  have p0036 :=
    @g_bitri (syn_wa (.classEq (.cv a) (syn_csn (.cv b))) (syn_wbr (.cv b) (syn_ccnv (syn_c2nd)) (syn_cop (.cv x) (.cv y)))) (syn_wa (.classEq (.cv a) (syn_csn (.cv b))) (.objEq b y)) (syn_wa (.objEq b y) (.classEq (.cv a) (syn_csn (.cv b)))) p0034 p0035
  have p0037 :=
    @g_exbii (syn_wa (.classEq (.cv a) (syn_csn (.cv b))) (syn_wbr (.cv b) (syn_ccnv (syn_c2nd)) (syn_cop (.cv x) (.cv y)))) (syn_wa (.objEq b y) (.classEq (.cv a) (syn_csn (.cv b)))) b p0036
  have p0038 :=
    @g_sneq (.cv b) (.cv y)
  have p0039_e00_recanon : Nominal.NPrf (.imp (.objEq b y) (.classEq (syn_csn (.cv b)) (syn_csn (.cv y)))) :=
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
      p0038
  have p0039 :=
    @g_eqeq2d (.objEq b y) (syn_csn (.cv b)) (syn_csn (.cv y)) (.cv a) p0039_e00_recanon
  have p0040_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv b) (.cv y)) (syn_wb (.classEq (.cv a) (syn_csn (.cv b))) (.classEq (.cv a) (syn_csn (.cv y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0039
  have p0040 :=
    @g_ceqsexv (.classEq (.cv a) (syn_csn (.cv b))) (.classEq (.cv a) (syn_csn (.cv y))) b (.cv y) dv_cache_0018 dv_cache_0019 p0001 p0040_e01_recanon
  have p0041_e02_recanon : Nominal.NPrf (syn_wb (syn_wex b (syn_wa (.objEq b y) (.classEq (.cv a) (syn_csn (.cv b))))) (.classEq (.cv a) (syn_csn (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_wa syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
      p0040
  have p0041 :=
    @g_n_3bitri (syn_wbr (.cv a) (syn_csi (syn_ccnv (syn_c2nd))) (syn_csn (syn_cop (.cv x) (.cv y)))) (syn_wex b (syn_wa (.classEq (.cv a) (syn_csn (.cv b))) (syn_wbr (.cv b) (syn_ccnv (syn_c2nd)) (syn_cop (.cv x) (.cv y))))) (syn_wex b (syn_wa (.objEq b y) (.classEq (.cv a) (syn_csn (.cv b))))) (.classEq (.cv a) (syn_csn (.cv y))) p0029 p0037 p0041_e02_recanon
  have p0042 :=
    @g_anbi2i (syn_wbr (.cv a) (syn_csi (syn_ccnv (syn_c2nd))) (syn_csn (syn_cop (.cv x) (.cv y)))) (.classEq (.cv a) (syn_csn (.cv y))) (syn_wbr (.cv p) (syn_c2nd) (.cv a)) p0041
  have p0043 :=
    @g_ancom (syn_wbr (.cv p) (syn_c2nd) (.cv a)) (.classEq (.cv a) (syn_csn (.cv y)))
  have p0044 :=
    @g_bitri (syn_wa (syn_wbr (.cv p) (syn_c2nd) (.cv a)) (syn_wbr (.cv a) (syn_csi (syn_ccnv (syn_c2nd))) (syn_csn (syn_cop (.cv x) (.cv y))))) (syn_wa (syn_wbr (.cv p) (syn_c2nd) (.cv a)) (.classEq (.cv a) (syn_csn (.cv y)))) (syn_wa (.classEq (.cv a) (syn_csn (.cv y))) (syn_wbr (.cv p) (syn_c2nd) (.cv a))) p0042 p0043
  have p0045 :=
    @g_exbii (syn_wa (syn_wbr (.cv p) (syn_c2nd) (.cv a)) (syn_wbr (.cv a) (syn_csi (syn_ccnv (syn_c2nd))) (syn_csn (syn_cop (.cv x) (.cv y))))) (syn_wa (.classEq (.cv a) (syn_csn (.cv y))) (syn_wbr (.cv p) (syn_c2nd) (.cv a))) a p0044
  have p0046 :=
    @g_snex (.cv y)
  have p0047 :=
    @g_breq2 (.cv a) (syn_csn (.cv y)) (.cv p) (syn_c2nd)
  have p0048 :=
    @g_ceqsexv (syn_wbr (.cv p) (syn_c2nd) (.cv a)) (syn_wbr (.cv p) (syn_c2nd) (syn_csn (.cv y))) a (syn_csn (.cv y)) dv_cache_0020 dv_cache_0021 p0046 p0047
  have p0049 :=
    @g_n_3bitri (syn_wbr (.cv p) (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd)) (syn_csn (syn_cop (.cv x) (.cv y)))) (syn_wex a (syn_wa (syn_wbr (.cv p) (syn_c2nd) (.cv a)) (syn_wbr (.cv a) (syn_csi (syn_ccnv (syn_c2nd))) (syn_csn (syn_cop (.cv x) (.cv y)))))) (syn_wex a (syn_wa (.classEq (.cv a) (syn_csn (.cv y))) (syn_wbr (.cv p) (syn_c2nd) (.cv a)))) (syn_wbr (.cv p) (syn_c2nd) (syn_csn (.cv y))) p0028 p0045 p0048
  have p0050 :=
    @g_anbi12i (syn_wbr (.cv p) (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st)) (syn_csn (syn_cop (.cv x) (.cv y)))) (syn_wbr (.cv p) (syn_c1st) (syn_csn (.cv x))) (syn_wbr (.cv p) (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd)) (syn_csn (syn_cop (.cv x) (.cv y)))) (syn_wbr (.cv p) (syn_c2nd) (syn_csn (.cv y))) p0027 p0049
  have p0051 :=
    @g_op1st2nd (syn_csn (.cv x)) (syn_csn (.cv y)) (.cv p) p0024 p0046
  have p0052 :=
    @g_n_3bitri (syn_wbr (.cv p) (syn_cin (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st)) (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd))) (syn_csn (syn_cop (.cv x) (.cv y)))) (syn_wa (syn_wbr (.cv p) (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st)) (syn_csn (syn_cop (.cv x) (.cv y)))) (syn_wbr (.cv p) (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd)) (syn_csn (syn_cop (.cv x) (.cv y))))) (syn_wa (syn_wbr (.cv p) (syn_c1st) (syn_csn (.cv x))) (syn_wbr (.cv p) (syn_c2nd) (syn_csn (.cv y)))) (.classEq (.cv p) (syn_cop (syn_csn (.cv x)) (syn_csn (.cv y)))) p0005 p0050 p0051
  have p0053 :=
    @g_rexbii (syn_wbr (.cv p) (syn_cin (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st)) (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd))) (syn_csn (syn_cop (.cv x) (.cv y)))) (.classEq (.cv p) (syn_cop (syn_csn (.cv x)) (syn_csn (.cv y)))) p (.cv g) p0052
  have p0054 :=
    @g_bitri (.classMem (syn_csn (syn_cop (.cv x) (.cv y))) (syn_cima (syn_cin (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st)) (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd))) (.cv g))) (syn_wrex p (.cv g) (syn_wbr (.cv p) (syn_cin (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st)) (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd))) (syn_csn (syn_cop (.cv x) (.cv y))))) (syn_wrex p (.cv g) (.classEq (.cv p) (syn_cop (syn_csn (.cv x)) (syn_csn (.cv y))))) p0004 p0053
  have p0055 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))))
  have p0056 :=
    @g_risset p (syn_cop (syn_csn (.cv x)) (syn_csn (.cv y))) (.cv g) dv_cache_0022 dv_cache_0003
  have p0057 :=
    @g_bitr2i (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))) (.classMem (syn_cop (syn_csn (.cv x)) (syn_csn (.cv y))) (.cv g)) (syn_wrex p (.cv g) (.classEq (.cv p) (syn_cop (syn_csn (.cv x)) (syn_csn (.cv y))))) p0055 p0056
  have p0058 :=
    @g_n_3bitri (.classMem (syn_cop (.cv x) (.cv y)) (syn_cuni1 (syn_cima (syn_cin (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st)) (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd))) (.cv g)))) (.classMem (syn_csn (syn_cop (.cv x) (.cv y))) (syn_cima (syn_cin (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st)) (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd))) (.cv g))) (syn_wrex p (.cv g) (.classEq (.cv p) (syn_cop (syn_csn (.cv x)) (syn_csn (.cv y))))) (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))) p0003 p0054 p0057
  have p0059 :=
    @g_opabbi2i (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))) x y (syn_cuni1 (syn_cima (syn_cin (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st)) (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd))) (.cv g))) dv_cache_0023 dv_cache_0024 dv_cache_0025 p0058
  have p0060 :=
    @g_n_1stex
  have p0061 :=
    @g_cnvex (syn_c1st) p0060
  have p0062 :=
    @g_siex (syn_ccnv (syn_c1st)) p0061
  have p0063 :=
    @g_n_1stex
  have p0064 :=
    @g_coex (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st) p0062 p0063
  have p0065 :=
    @g_n_2ndex
  have p0066 :=
    @g_cnvex (syn_c2nd) p0065
  have p0067 :=
    @g_siex (syn_ccnv (syn_c2nd)) p0066
  have p0068 :=
    @g_n_2ndex
  have p0069 :=
    @g_coex (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd) p0067 p0068
  have p0070 :=
    @g_inex (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st)) (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd)) p0064 p0069
  have p0071 :=
    @g_vex g
  have p0072 :=
    @g_imaex (syn_cin (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st)) (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd))) (.cv g) p0070 p0071
  have p0073 :=
    @g_uni1ex (syn_cima (syn_cin (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st)) (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd))) (.cv g)) p0072
  have p0074 :=
    @g_eqeltrri (syn_cuni1 (syn_cima (syn_cin (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st)) (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd))) (.cv g))) (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (syn_cvv) p0059 p0073
  exact p0074

#print axioms g_enpw1lem1

end NFChoice.DirectNominalPrf.WPPReplay
