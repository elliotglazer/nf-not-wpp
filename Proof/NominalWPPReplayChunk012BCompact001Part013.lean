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
import NominalWPPReplayChunk012BCompact001Part012

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

noncomputable def g_eloprabga
    (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) (V : Class) (W : Class) (X : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_C_z : z ∉ C.fv) (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv) (dv_ps_z : z ∉ ps.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) (hyp_eloprabga_1 : Nominal.NPrf (.imp (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) (syn_wb ph ps))) :
    Nominal.NPrf (.imp (syn_w3a (.classMem A V) (.classMem B W) (.classMem C X)) (syn_wb (.classMem (syn_cop (syn_cop A B) C) (syn_coprab x y z ph)) ps)) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ V.fv ∪ W.fv ∪ X.fv
  let w : Var := freshVar proofSupport 0
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))))))))
  have fresh_w_not_ps : w ∉ ps.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))))))
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))))
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))))
  have fresh_y_ne_w : y ≠ w :=
    Ne.symm fresh_w_ne_y
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))
  have fresh_z_ne_w : z ≠ w :=
    Ne.symm fresh_w_ne_z
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_w_not_C : w ∉ C.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_w_not_V : w ∉ V.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_W : w ∉ W.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_X : w ∉ X.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((Wff.classEq (.cv w) (syn_cop (syn_cop A B) C))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_w, dv_A_x, dv_B_x, dv_C_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Wff.classEq (.cv w) (syn_cop (syn_cop A B) C))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_w, dv_A_y, dv_B_y, dv_C_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((Wff.classEq (.cv w) (syn_cop (syn_cop A B) C))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_w, dv_A_z, dv_B_z, dv_C_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : w ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : w ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show w ≠ x from (by exact fresh_w_ne_x))
  have dv_cache_0006 : w ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show w ≠ y from (by exact fresh_w_ne_y))
  have dv_cache_0007 : w ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show w ≠ z from (by exact fresh_w_ne_z))
  have dv_cache_0008 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : z ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((Wff.classEq (.cv z) C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_x_z, dv_C_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ ((Wff.classEq (.cv z) C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_y_z, dv_C_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : y ∉ ((Wff.classEq (.cv x) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_y), dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : z ∉ ((Wff.classEq (.cv x) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_z), dv_A_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ ((Wff.classEq (.cv y) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_x_y, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : z ∉ ((Wff.classEq (.cv y) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_y_z), dv_B_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0018 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0019 : x ∉ (ps).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ps_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : y ∉ (ps).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ps_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : z ∉ (ps).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ps_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : w ∉ ((syn_cop (syn_cop A B) C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, fresh_w_not_B, fresh_w_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : w ∉ ((Wff.imp (syn_w3a (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (syn_wb (.classMem (syn_cop (syn_cop A B) C) (syn_coprab x y z ph)) ps))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_coprab, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_C, fresh_w_not_A, fresh_w_not_B, fresh_w_not_ph, fresh_w_ne_x, fresh_w_ne_y, fresh_w_not_ps, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elex A V
  have p0001 :=
    @g_elex B W
  have p0002 :=
    @g_elex C X
  have p0003 :=
    @g_opexg A B (syn_cvv) (syn_cvv)
  have p0004 :=
    @g_opexg (syn_cop A B) C (syn_cvv) (syn_cvv)
  have p0005 :=
    @g_sylan (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (.classMem (syn_cop A B) (syn_cvv)) (.classMem C (syn_cvv)) (.classMem (syn_cop (syn_cop A B) C) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_n_3impa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv)) (.classMem (syn_cop (syn_cop A B) C) (syn_cvv)) p0005
  have p0007 :=
    @g_eqeq1 (.cv w) (syn_cop (syn_cop A B) C) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))
  have p0008 :=
    @g_eqcom (syn_cop (syn_cop A B) C) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))
  have p0009 :=
    @g_opth (.cv x) (.cv y) A B
  have p0010 :=
    @g_anbi1i (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop A B)) (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) (.classEq (.cv z) C) p0009
  have p0011 :=
    @g_opth (syn_cop (.cv x) (.cv y)) (.cv z) (syn_cop A B) C
  have p0012 :=
    (by simpa [syn_wb, syn_w3a] using (Nominal.biimpRefl (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C))))
  have p0013 :=
    @g_n_3bitr4i (syn_wa (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop A B)) (.classEq (.cv z) C)) (syn_wa (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) (.classEq (.cv z) C)) (.classEq (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) (syn_cop (syn_cop A B) C)) (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) p0010 p0011 p0012
  have p0014 :=
    @g_bitri (.classEq (syn_cop (syn_cop A B) C) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) (.classEq (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) (syn_cop (syn_cop A B) C)) (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) p0008 p0013
  have p0015 :=
    @g_syl6bb (.classEq (.cv w) (syn_cop (syn_cop A B) C)) (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) (.classEq (syn_cop (syn_cop A B) C) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) p0007 p0014
  have p0016 :=
    @g_anbi1d (.classEq (.cv w) (syn_cop (syn_cop A B) C)) (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) ph p0015
  have p0017 :=
    @g_pm5_32i (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) ph ps hyp_eloprabga_1
  have p0018 :=
    @g_syl6bb (.classEq (.cv w) (syn_cop (syn_cop A B) C)) (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph) (syn_wa (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) ph) (syn_wa (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) ps) p0016 p0017
  have p0019 :=
    @g_n_3exbidv (.classEq (.cv w) (syn_cop (syn_cop A B) C)) (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph) (syn_wa (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) ps) x y z dv_cache_0001 dv_cache_0002 dv_cache_0003 p0018
  have p0020 :=
    @g_adantl (.classEq (.cv w) (syn_cop (syn_cop A B) C)) (syn_wb (syn_wex x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph)))) (syn_wex x (syn_wex y (syn_wex z (syn_wa (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) ps))))) (syn_w3a (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) p0019
  have p0021 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_oprab ph x y z w dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0022 :=
    @g_eleq2i (syn_coprab x y z ph) (.cab w (syn_wex x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph))))) (.cv w) p0021
  have p0023 :=
    @g_abid (syn_wex x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph)))) w
  have p0024 :=
    @g_bitr2i (.classMem (.cv w) (syn_coprab x y z ph)) (.classMem (.cv w) (.cab w (syn_wex x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph)))))) (syn_wex x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph)))) p0022 p0023
  have p0025 :=
    @g_eleq1 (.cv w) (syn_cop (syn_cop A B) C) (syn_coprab x y z ph)
  have p0026 :=
    @g_syl5bb (syn_wex x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph)))) (.classMem (.cv w) (syn_coprab x y z ph)) (.classEq (.cv w) (syn_cop (syn_cop A B) C)) (.classMem (syn_cop (syn_cop A B) C) (syn_coprab x y z ph)) p0024 p0025
  have p0027 :=
    @g_adantl (.classEq (.cv w) (syn_cop (syn_cop A B) C)) (syn_wb (syn_wex x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph)))) (.classMem (syn_cop (syn_cop A B) C) (syn_coprab x y z ph))) (syn_w3a (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) p0026
  have p0028 :=
    @g_isset x A dv_cache_0008
  have p0029 :=
    @g_isset y B dv_cache_0009
  have p0030 :=
    @g_isset z C dv_cache_0010
  have p0031 :=
    @g_n_3anbi123i (.classMem A (syn_cvv)) (syn_wex x (.classEq (.cv x) A)) (.classMem B (syn_cvv)) (syn_wex y (.classEq (.cv y) B)) (.classMem C (syn_cvv)) (syn_wex z (.classEq (.cv z) C)) p0028 p0029 p0030
  have p0032 :=
    @g_eeeanv (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C) x y z dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
  have p0033 :=
    @g_bitr4i (syn_w3a (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (syn_w3a (syn_wex x (.classEq (.cv x) A)) (syn_wex y (.classEq (.cv y) B)) (syn_wex z (.classEq (.cv z) C))) (syn_wex x (syn_wex y (syn_wex z (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C))))) p0031 p0032
  have p0034 :=
    @g_biimpi (syn_w3a (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (syn_wex x (syn_wex y (syn_wex z (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C))))) p0033
  have p0035 :=
    @g_biantrurd (syn_w3a (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (syn_wex x (syn_wex y (syn_wex z (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C))))) ps p0034
  have p0036 :=
    @g_n_19_41vvv (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) ps x y z dv_cache_0019 dv_cache_0020 dv_cache_0021
  have p0037 :=
    @g_syl6rbbr (syn_w3a (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) ps (syn_wa (syn_wex x (syn_wex y (syn_wex z (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C))))) ps) (syn_wex x (syn_wex y (syn_wex z (syn_wa (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) ps)))) p0035 p0036
  have p0038 :=
    @g_adantr (syn_w3a (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (syn_wb (syn_wex x (syn_wex y (syn_wex z (syn_wa (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) ps)))) ps) (.classEq (.cv w) (syn_cop (syn_cop A B) C)) p0037
  have p0039 :=
    @g_n_3bitr3d (syn_wa (syn_w3a (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (.classEq (.cv w) (syn_cop (syn_cop A B) C))) (syn_wex x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv w) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z))) ph)))) (syn_wex x (syn_wex y (syn_wex z (syn_wa (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) ps)))) (.classMem (syn_cop (syn_cop A B) C) (syn_coprab x y z ph)) ps p0020 p0027 p0038
  have p0040 :=
    @g_expcom (syn_w3a (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (.classEq (.cv w) (syn_cop (syn_cop A B) C)) (syn_wb (.classMem (syn_cop (syn_cop A B) C) (syn_coprab x y z ph)) ps) p0039
  have p0041 :=
    @g_vtocleg (.imp (syn_w3a (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (syn_wb (.classMem (syn_cop (syn_cop A B) C) (syn_coprab x y z ph)) ps)) w (syn_cop (syn_cop A B) C) (syn_cvv) dv_cache_0022 dv_cache_0023 p0040
  have p0042 :=
    @g_mpcom (.classMem (syn_cop (syn_cop A B) C) (syn_cvv)) (syn_w3a (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (syn_wb (.classMem (syn_cop (syn_cop A B) C) (syn_coprab x y z ph)) ps) p0006 p0041
  have p0043 :=
    @g_syl3an (.classMem A V) (.classMem A (syn_cvv)) (.classMem B W) (.classMem B (syn_cvv)) (.classMem C X) (.classMem C (syn_cvv)) (syn_wb (.classMem (syn_cop (syn_cop A B) C) (syn_coprab x y z ph)) ps) p0000 p0001 p0002 p0042
  exact p0043

noncomputable def g_eloprabg
    (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) (V : Class) (W : Class) (X : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_C_z : z ∉ C.fv) (dv_th_x : x ∉ th.fv) (dv_th_y : y ∉ th.fv) (dv_th_z : z ∉ th.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) (hyp_eloprabg_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) (hyp_eloprabg_2 : Nominal.NPrf (.imp (.classEq (.cv y) B) (syn_wb ps ch))) (hyp_eloprabg_3 : Nominal.NPrf (.imp (.classEq (.cv z) C) (syn_wb ch th))) :
    Nominal.NPrf (.imp (syn_w3a (.classMem A V) (.classMem B W) (.classMem C X)) (syn_wb (.classMem (syn_cop (syn_cop A B) C) (syn_coprab x y z ph)) th)) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ th.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ V.fv ∪ W.fv ∪ X.fv
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ (th).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_th_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ (th).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_th_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : z ∉ (th).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_th_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0014 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0015 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show y ≠ z from (by exact dv_y_z))
  have p0000 :=
    @g_syl3an9b (.classEq (.cv x) A) ph ps (.classEq (.cv y) B) ch (.classEq (.cv z) C) th hyp_eloprabg_1 hyp_eloprabg_2 hyp_eloprabg_3
  have p0001 :=
    @g_eloprabga ph th x y z A B C V W X dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 p0000
  exact p0001

noncomputable def g_funoprabg
    (ph : Wff) (x : Var) (y : Var) (z : Var) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf (.imp (.all x (.all y (syn_wmo z ph))) (syn_wfun (syn_coprab x y z ph))) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var)
  let w : Var := freshVar proofSupport 0
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_w : y ≠ w :=
    Ne.symm fresh_w_ne_y
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_z_ne_w : z ≠ w :=
    Ne.symm fresh_w_ne_z
  have dv_cache_0001 : z ∉ ((Class.cv w)).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Class.cv w)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Class.cv w)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show z ≠ x from (by exact Ne.symm dv_x_z))
  have dv_cache_0005 : z ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show z ≠ y from (by exact Ne.symm dv_y_z))
  have dv_cache_0006 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0007 : w ∉ ((Wff.all x (.all y (syn_wmo z ph)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wmo, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : w ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : w ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show w ≠ x from (by exact fresh_w_ne_x))
  have dv_cache_0010 : w ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show w ≠ y from (by exact fresh_w_ne_y))
  have dv_cache_0011 : w ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show w ≠ z from (by exact fresh_w_ne_z))
  have dv_cache_0012 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0013 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show y ≠ z from (by exact dv_y_z))
  have p0000 :=
    @g_mosubopt ph z x y (.cv w) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_alrimiv (.all x (.all y (syn_wmo z ph))) (syn_wmo z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)))) w dv_cache_0007 p0000
  have p0002 :=
    @g_dfoprab2 ph x y z w dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0003 :=
    @g_funeqi (syn_coprab x y z ph) (syn_copab w z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)))) p0002
  have p0004 :=
    @g_funopab (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))) w z dv_cache_0011
  have p0005 :=
    @g_bitr2i (syn_wfun (syn_coprab x y z ph)) (syn_wfun (syn_copab w z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))))) (.all w (syn_wmo z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))))) p0003 p0004
  have p0006 :=
    @g_sylib (.all x (.all y (syn_wmo z ph))) (.all w (syn_wmo z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))))) (syn_wfun (syn_coprab x y z ph)) p0001 p0005
  exact p0006

noncomputable def g_funoprab
    (ph : Wff) (x : Var) (y : Var) (z : Var) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) (hyp_funoprab_1 : Nominal.NPrf (syn_wmo z ph)) :
    Nominal.NPrf (syn_wfun (syn_coprab x y z ph)) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var)
  have dv_cache_0001 : x ≠ y := by
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0002 : x ≠ z := by
    clear dv_cache_0001
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0003 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002
    exact (show y ≠ z from (by exact dv_y_z))
  have p0000 :=
    @g_gen2 (syn_wmo z ph) x y hyp_funoprab_1
  have p0001 :=
    @g_funoprabg ph x y z dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0002 :=
    Nominal.mp p0000 p0001
  exact p0002

noncomputable def g_fnoprabg
    (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var) (dv_ph_z : z ∉ ph.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf (.imp (.all x (.all y (.imp ph (syn_weu z ps)))) (syn_wfn (syn_coprab x y z (syn_wa ph ps)) (syn_copab x y ph))) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var)
  have dv_cache_0001 : z ∉ (ph).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ph_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ≠ y := by
    clear dv_cache_0001
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0003 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0004 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show y ≠ z from (by exact dv_y_z))
  have p0000 :=
    @g_eumo ps z
  have p0001 :=
    @g_imim2i (syn_weu z ps) (syn_wmo z ps) ph p0000
  have p0002 :=
    @g_moanimv ph ps z dv_cache_0001
  have p0003 :=
    @g_sylibr (.imp ph (syn_weu z ps)) (.imp ph (syn_wmo z ps)) (syn_wmo z (syn_wa ph ps)) p0001 p0002
  have p0004 :=
    @g_n_2alimi (.imp ph (syn_weu z ps)) (syn_wmo z (syn_wa ph ps)) x y p0003
  have p0005 :=
    @g_funoprabg (syn_wa ph ps) x y z dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0006 :=
    @g_syl (.all x (.all y (.imp ph (syn_weu z ps)))) (.all x (.all y (syn_wmo z (syn_wa ph ps)))) (syn_wfun (syn_coprab x y z (syn_wa ph ps))) p0004 p0005
  have p0007 :=
    @g_dmoprab (syn_wa ph ps) x y z dv_cache_0003 dv_cache_0004
  have p0008 :=
    @g_nfa1 (.all y (.imp ph (syn_weu z ps))) x
  have p0009 :=
    @g_nfa2 (.imp ph (syn_weu z ps)) y x
  have p0010 :=
    @g_simpl ph ps
  have p0011 :=
    @g_exlimiv (syn_wa ph ps) ph z dv_cache_0001 p0010
  have p0012 :=
    @g_euex ps z
  have p0013 :=
    @g_imim2i (syn_weu z ps) (syn_wex z ps) ph p0012
  have p0014 :=
    @g_ancld (.imp ph (syn_weu z ps)) ph (syn_wex z ps) p0013
  have p0015 :=
    @g_n_19_42v ph ps z dv_cache_0001
  have p0016 :=
    @g_syl6ibr (.imp ph (syn_weu z ps)) ph (syn_wa ph (syn_wex z ps)) (syn_wex z (syn_wa ph ps)) p0014 p0015
  have p0017 :=
    @g_impbid2 (.imp ph (syn_weu z ps)) (syn_wex z (syn_wa ph ps)) ph p0011 p0016
  have p0018 :=
    @g_sps (.imp ph (syn_weu z ps)) (syn_wb (syn_wex z (syn_wa ph ps)) ph) y p0017
  have p0019 :=
    @g_sps (.all y (.imp ph (syn_weu z ps))) (syn_wb (syn_wex z (syn_wa ph ps)) ph) x p0018
  have p0020 :=
    @g_opabbid (.all x (.all y (.imp ph (syn_weu z ps)))) (syn_wex z (syn_wa ph ps)) ph x y p0008 p0009 p0019
  have p0021 :=
    @g_syl5eq (.all x (.all y (.imp ph (syn_weu z ps)))) (syn_cdm (syn_coprab x y z (syn_wa ph ps))) (syn_copab x y (syn_wex z (syn_wa ph ps))) (syn_copab x y ph) p0007 p0020
  have p0022 :=
    (by simpa [syn_wb, syn_wfn] using (Nominal.biimpRefl (syn_wfn (syn_coprab x y z (syn_wa ph ps)) (syn_copab x y ph))))
  have p0023 :=
    @g_sylanbrc (.all x (.all y (.imp ph (syn_weu z ps)))) (syn_wfun (syn_coprab x y z (syn_wa ph ps))) (.classEq (syn_cdm (syn_coprab x y z (syn_wa ph ps))) (syn_copab x y ph)) (syn_wfn (syn_coprab x y z (syn_wa ph ps)) (syn_copab x y ph)) p0006 p0021 p0022
  exact p0023

noncomputable def g_fnoprab
    (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var) (dv_ph_z : z ∉ ph.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) (hyp_fnoprab_1 : Nominal.NPrf (.imp ph (syn_weu z ps))) :
    Nominal.NPrf (syn_wfn (syn_coprab x y z (syn_wa ph ps)) (syn_copab x y ph)) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var)
  have dv_cache_0001 : z ∉ (ph).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ph_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ≠ y := by
    clear dv_cache_0001
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0003 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0004 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show y ≠ z from (by exact dv_y_z))
  have p0000 :=
    @g_gen2 (.imp ph (syn_weu z ps)) x y hyp_fnoprab_1
  have p0001 :=
    @g_fnoprabg ph ps x y z dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0002 :=
    Nominal.mp p0000 p0001
  exact p0002

noncomputable def g_ovigg
    (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) (F : Class) (V : Class) (W : Class) (X : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_C_z : z ∉ C.fv) (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv) (dv_ps_z : z ∉ ps.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) (hyp_ovigg_1 : Nominal.NPrf (.imp (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (.classEq (.cv z) C)) (syn_wb ph ps))) (hyp_ovigg_4 : Nominal.NPrf (syn_wmo z ph)) (hyp_ovigg_5 : Nominal.NPrf (.classEq F (syn_coprab x y z ph))) :
    Nominal.NPrf (.imp (syn_w3a (.classMem A V) (.classMem B W) (.classMem C X)) (.imp ps (.classEq (syn_co A F B) C))) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ F.fv ∪ V.fv ∪ W.fv ∪ X.fv
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ (ps).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ps_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ (ps).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ps_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : z ∉ (ps).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ps_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0014 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0015 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show y ≠ z from (by exact dv_y_z))
  have p0000 :=
    @g_eloprabga ph ps x y z A B C V W X dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 hyp_ovigg_1
  have p0001 :=
    @g_funoprab ph x y z dv_cache_0013 dv_cache_0014 dv_cache_0015 hyp_ovigg_4
  have p0002 :=
    @g_funopfv (syn_cop A B) C (syn_coprab x y z ph)
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    @g_syl6bir (syn_w3a (.classMem A V) (.classMem B W) (.classMem C X)) ps (.classMem (syn_cop (syn_cop A B) C) (syn_coprab x y z ph)) (.classEq (syn_cfv (syn_coprab x y z ph) (syn_cop A B)) C) p0000 p0003
  have p0005 :=
    (by simpa [syn_co] using (Nominal.classEqRefl (syn_co A F B)))
  have p0006 :=
    @g_fveq1i (syn_cop A B) F (syn_coprab x y z ph) hyp_ovigg_5
  have p0007 :=
    @g_eqtri (syn_co A F B) (syn_cfv F (syn_cop A B)) (syn_cfv (syn_coprab x y z ph) (syn_cop A B)) p0005 p0006
  have p0008 :=
    @g_eqeq1i (syn_co A F B) (syn_cfv (syn_coprab x y z ph) (syn_cop A B)) C p0007
  have p0009 :=
    @g_syl6ibr (syn_w3a (.classMem A V) (.classMem B W) (.classMem C X)) ps (.classEq (syn_cfv (syn_coprab x y z ph) (syn_cop A B)) C) (.classEq (syn_co A F B) C) p0004 p0008
  exact p0009

#print axioms g_ovigg

end NFChoice.DirectNominalPrf.WPPReplay
