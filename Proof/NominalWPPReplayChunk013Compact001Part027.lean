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
import NominalWPPReplayChunk013Compact001Part026

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

noncomputable def g_connexd
    (ph : Wff) (A : Class) (R : Class) (X : Class) (Y : Class) (hyp_connexd_1 : Nominal.NPrf (.imp ph (syn_wbr R (syn_cconnex) A))) (hyp_connexd_2 : Nominal.NPrf (.imp ph (.classMem X A))) (hyp_connexd_3 : Nominal.NPrf (.imp ph (.classMem Y A))) :
    Nominal.NPrf (.imp ph (syn_wo (syn_wbr X R Y) (syn_wbr Y R X))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ R.fv ∪ X.fv ∪ Y.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let r : Var := freshVar proofSupport 2
  let a : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_ph : x ∉ ph.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_X : x ∉ X.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_Y : x ∉ Y.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_X : y ∉ X.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_Y : y ∉ Y.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_r_not_ph : r ∉ ph.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_r_not_R : r ∉ R.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_r_not_X : r ∉ X.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_not_Y : r ∉ Y.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_a_not_ph : a ∉ ph.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a_not_X : a ∉ X.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_Y : a ∉ Y.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_r : x ≠ r := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_r_ne_x : r ≠ x :=
    Ne.symm fresh_x_ne_r
  have fresh_x_ne_a : x ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_a_ne_x : a ≠ x :=
    Ne.symm fresh_x_ne_a
  have fresh_y_ne_r : y ≠ r := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_r_ne_y : r ≠ y :=
    Ne.symm fresh_y_ne_r
  have fresh_y_ne_a : y ≠ a := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_a_ne_y : a ≠ y :=
    Ne.symm fresh_y_ne_a
  have fresh_r_ne_a : r ≠ a := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_a_ne_r : a ≠ r :=
    Ne.symm fresh_r_ne_a
  have dv_cache_0001 : x ∉ ((Wff.classEq (.cv r) R)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_r, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Wff.classEq (.cv r) R)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_r, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : a ≠ r := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show a ≠ r from (by exact fresh_a_ne_r))
  have dv_cache_0008 : a ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0009 : a ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show a ≠ y from (by exact fresh_a_ne_y))
  have dv_cache_0010 : r ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0011 : r ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show r ≠ y from (by exact fresh_r_ne_y))
  have dv_cache_0012 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0013 : r ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : a ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : r ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : a ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : r ∉ ((syn_wral x A (syn_wral y A (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, fresh_r_ne_x, fresh_r_ne_y, fresh_r_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : a ∉ ((syn_wral x A (syn_wral y A (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, fresh_a_ne_x, fresh_a_ne_y, fresh_a_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : r ≠ a := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (show r ≠ a from (by exact fresh_r_ne_a))
  have dv_cache_0020 : x ∉ (X).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : y ∉ (X).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : y ∉ (Y).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_Y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : x ∉ ((syn_wo (syn_wbr X R (.cv y)) (syn_wbr (.cv y) R X))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_X, fresh_x_ne_y, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : y ∉ ((syn_wo (syn_wbr X R Y) (syn_wbr Y R X))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_X, fresh_y_not_Y, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_brex R A (syn_cconnex)
  have p0001 :=
    @g_breq (.cv x) (.cv y) (.cv r) R
  have p0002 :=
    @g_breq (.cv y) (.cv x) (.cv r) R
  have p0003 :=
    @g_orbi12d (.classEq (.cv r) R) (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)) (syn_wbr (.cv y) R (.cv x)) p0001 p0002
  have p0004 :=
    @g_n_2ralbidv (.classEq (.cv r) R) (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) x y (.cv a) (.cv a) dv_cache_0001 dv_cache_0002 p0003
  have p0005 :=
    @g_raleq (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) y (.cv a) A dv_cache_0003 dv_cache_0004
  have p0006 :=
    @g_raleqbi1dv (syn_wral y (.cv a) (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))) (syn_wral y A (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))) x (.cv a) A dv_cache_0005 dv_cache_0006 p0005
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_connex x y r a dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0008 :=
    @g_brabg (syn_wral x (.cv a) (syn_wral y (.cv a) (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))))) (syn_wral x (.cv a) (syn_wral y (.cv a) (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))))) (syn_wral x A (syn_wral y A (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))))) r a R A (syn_cvv) (syn_cvv) (syn_cconnex) dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 p0004 p0006 p0007
  have p0009 :=
    @g_syl (syn_wbr R (syn_cconnex) A) (syn_wa (.classMem R (syn_cvv)) (.classMem A (syn_cvv))) (syn_wb (syn_wbr R (syn_cconnex) A) (syn_wral x A (syn_wral y A (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))))) p0000 p0008
  have p0010 :=
    @g_ibi (syn_wbr R (syn_cconnex) A) (syn_wral x A (syn_wral y A (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))))) p0009
  have p0011 :=
    @g_breq1 (.cv x) X (.cv y) R
  have p0012 :=
    @g_breq2 (.cv x) X (.cv y) R
  have p0013 :=
    @g_orbi12d (.classEq (.cv x) X) (syn_wbr (.cv x) R (.cv y)) (syn_wbr X R (.cv y)) (syn_wbr (.cv y) R (.cv x)) (syn_wbr (.cv y) R X) p0011 p0012
  have p0014 :=
    @g_breq2 (.cv y) Y X R
  have p0015 :=
    @g_breq1 (.cv y) Y X R
  have p0016 :=
    @g_orbi12d (.classEq (.cv y) Y) (syn_wbr X R (.cv y)) (syn_wbr X R Y) (syn_wbr (.cv y) R X) (syn_wbr Y R X) p0014 p0015
  have p0017 :=
    @g_rspc2v (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) (syn_wo (syn_wbr X R Y) (syn_wbr Y R X)) (syn_wo (syn_wbr X R (.cv y)) (syn_wbr (.cv y) R X)) x y X Y A A dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0006 dv_cache_0006 dv_cache_0004 dv_cache_0023 dv_cache_0024 dv_cache_0012 p0013 p0016
  have p0018 :=
    @g_syl2anc ph (.classMem X A) (.classMem Y A) (.imp (syn_wral x A (syn_wral y A (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))))) (syn_wo (syn_wbr X R Y) (syn_wbr Y R X))) hyp_connexd_2 hyp_connexd_3 p0017
  have p0019 :=
    @g_syl5 (syn_wbr R (syn_cconnex) A) (syn_wral x A (syn_wral y A (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))))) ph (syn_wo (syn_wbr X R Y) (syn_wbr Y R X)) p0010 p0018
  have p0020 :=
    @g_mpd ph (syn_wbr R (syn_cconnex) A) (syn_wo (syn_wbr X R Y) (syn_wbr Y R X)) hyp_connexd_1 p0019
  exact p0020

noncomputable def g_ersymtr
    (A : Class) (R : Class) :
    Nominal.NPrf (syn_wb (syn_wbr R (syn_cer) A) (syn_wa (syn_wbr R (syn_csym) A) (syn_wbr R (syn_ctrans) A))) := by
  let proofSupport : Finset Var := A.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_cer] using (Nominal.classEqRefl (syn_cer)))
  have p0001 :=
    @g_breqi R A (syn_cer) (syn_cin (syn_csym) (syn_ctrans)) p0000
  have p0002 :=
    @g_brin R A (syn_csym) (syn_ctrans)
  have p0003 :=
    @g_bitri (syn_wbr R (syn_cer) A) (syn_wbr R (syn_cin (syn_csym) (syn_ctrans)) A) (syn_wa (syn_wbr R (syn_csym) A) (syn_wbr R (syn_ctrans) A)) p0001 p0002
  exact p0003

noncomputable def g_porta
    (A : Class) (R : Class) :
    Nominal.NPrf (syn_wb (syn_wbr R (syn_cpartial) A) (syn_w3a (syn_wbr R (syn_cref) A) (syn_wbr R (syn_ctrans) A) (syn_wbr R (syn_cantisym) A))) := by
  let proofSupport : Finset Var := A.fv ∪ R.fv
  have p0000 :=
    @g_brin R A (syn_cin (syn_cref) (syn_ctrans)) (syn_cantisym)
  have p0001 :=
    @g_brin R A (syn_cref) (syn_ctrans)
  have p0002 :=
    @g_anbi1i (syn_wbr R (syn_cin (syn_cref) (syn_ctrans)) A) (syn_wa (syn_wbr R (syn_cref) A) (syn_wbr R (syn_ctrans) A)) (syn_wbr R (syn_cantisym) A) p0001
  have p0003 :=
    @g_bitri (syn_wbr R (syn_cin (syn_cin (syn_cref) (syn_ctrans)) (syn_cantisym)) A) (syn_wa (syn_wbr R (syn_cin (syn_cref) (syn_ctrans)) A) (syn_wbr R (syn_cantisym) A)) (syn_wa (syn_wa (syn_wbr R (syn_cref) A) (syn_wbr R (syn_ctrans) A)) (syn_wbr R (syn_cantisym) A)) p0000 p0002
  have p0004 :=
    (by simpa [syn_cpartial] using (Nominal.classEqRefl (syn_cpartial)))
  have p0005 :=
    @g_breqi R A (syn_cpartial) (syn_cin (syn_cin (syn_cref) (syn_ctrans)) (syn_cantisym)) p0004
  have p0006 :=
    (by simpa [syn_wb, syn_w3a] using (Nominal.biimpRefl (syn_w3a (syn_wbr R (syn_cref) A) (syn_wbr R (syn_ctrans) A) (syn_wbr R (syn_cantisym) A))))
  have p0007 :=
    @g_n_3bitr4i (syn_wbr R (syn_cin (syn_cin (syn_cref) (syn_ctrans)) (syn_cantisym)) A) (syn_wa (syn_wa (syn_wbr R (syn_cref) A) (syn_wbr R (syn_ctrans) A)) (syn_wbr R (syn_cantisym) A)) (syn_wbr R (syn_cpartial) A) (syn_w3a (syn_wbr R (syn_cref) A) (syn_wbr R (syn_ctrans) A) (syn_wbr R (syn_cantisym) A)) p0003 p0005 p0006
  exact p0007

noncomputable def g_sopc
    (A : Class) (R : Class) :
    Nominal.NPrf (syn_wb (syn_wbr R (syn_cstrict) A) (syn_wa (syn_wbr R (syn_cpartial) A) (syn_wbr R (syn_cconnex) A))) := by
  let proofSupport : Finset Var := A.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_cstrict] using (Nominal.classEqRefl (syn_cstrict)))
  have p0001 :=
    @g_breqi R A (syn_cstrict) (syn_cin (syn_cpartial) (syn_cconnex)) p0000
  have p0002 :=
    @g_brin R A (syn_cpartial) (syn_cconnex)
  have p0003 :=
    @g_bitri (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cin (syn_cpartial) (syn_cconnex)) A) (syn_wa (syn_wbr R (syn_cpartial) A) (syn_wbr R (syn_cconnex) A)) p0001 p0002
  exact p0003

noncomputable def g_frds
    (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (x : Var) (y : Var) (z : Var) (A : Class) (R : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_ch_x : x ∉ ch.fv) (dv_ps_y : y ∉ ps.fv) (dv_ps_z : z ∉ ps.fv) (dv_th_x : x ∉ th.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) (hyp_frds_1 : Nominal.NPrf (.classMem (.cab x ps) (syn_cvv))) (hyp_frds_2 : Nominal.NPrf (.imp (.objEq x y) (syn_wb ps ch))) (hyp_frds_3 : Nominal.NPrf (.imp (.objEq x z) (syn_wb ps th))) (hyp_frds_4 : Nominal.NPrf (.imp ph (syn_wbr R (syn_cfound) A))) (hyp_frds_5 : Nominal.NPrf (.imp ph (syn_wrex x A ps))) :
    Nominal.NPrf (.imp ph (syn_wrex y A (syn_wa ch (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y)))))) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ th.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ A.fv ∪ R.fv
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (R).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Class.cab x (syn_wa (.classMem (.cv x) A) ps))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_y), dv_A_y, dv_ps_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((Class.cab x (syn_wa (.classMem (.cv x) A) ps))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_z), dv_A_z, dv_ps_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show y ≠ z from (by exact dv_y_z))
  have dv_cache_0007 : x ∉ ((syn_wa (.classMem (.cv y) A) ch)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_x_y, dv_A_x, dv_ch_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show y ≠ x from (by exact Ne.symm dv_x_y))
  have dv_cache_0009 : x ∉ ((syn_wa (.classMem (.cv z) A) th)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_x_z, dv_A_x, dv_th_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : z ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show z ≠ x from (by exact Ne.symm dv_x_z))
  have p0000 :=
    @g_dfrab2 ps x A dv_cache_0001
  have p0001 :=
    (by simpa [syn_crab] using (Nominal.classEqRefl (syn_crab x A ps)))
  have p0002 :=
    @g_eqtr3i (syn_crab x A ps) (syn_cin (.cab x ps) A) (.cab x (syn_wa (.classMem (.cv x) A) ps)) p0000 p0001
  have p0003 :=
    @g_brex R A (syn_cfound)
  have p0004 :=
    @g_syl ph (syn_wbr R (syn_cfound) A) (syn_wa (.classMem R (syn_cvv)) (.classMem A (syn_cvv))) hyp_frds_4 p0003
  have p0005 :=
    @g_simprd ph (.classMem R (syn_cvv)) (.classMem A (syn_cvv)) p0004
  have p0006 :=
    @g_inexg (.cab x ps) A (syn_cvv) (syn_cvv)
  have p0007 :=
    @g_sylancr ph (.classMem (.cab x ps) (syn_cvv)) (.classMem A (syn_cvv)) (.classMem (syn_cin (.cab x ps) A) (syn_cvv)) hyp_frds_1 p0005 p0006
  have p0008 :=
    @g_syl5eqelr ph (.cab x (syn_wa (.classMem (.cv x) A) ps)) (syn_cin (.cab x ps) A) (syn_cvv) p0002 p0007
  have p0009 :=
    @g_ssab2 ps x A dv_cache_0001
  have p0010 :=
    @g_a1i (syn_wss (.cab x (syn_wa (.classMem (.cv x) A) ps)) A) ph p0009
  have p0011 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex x A ps)))
  have p0012 :=
    @g_sylib ph (syn_wrex x A ps) (syn_wex x (syn_wa (.classMem (.cv x) A) ps)) hyp_frds_5 p0011
  have p0013 :=
    @g_abn0 (syn_wa (.classMem (.cv x) A) ps) x
  have p0014 :=
    @g_sylibr ph (syn_wex x (syn_wa (.classMem (.cv x) A) ps)) (syn_wne (.cab x (syn_wa (.classMem (.cv x) A) ps)) (syn_c0)) p0012 p0013
  have p0015 :=
    @g_frd ph y z A R (syn_cvv) (.cab x (syn_wa (.classMem (.cv x) A) ps)) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 hyp_frds_4 p0008 p0010 p0014
  have p0016 :=
    @g_eleq1 (.cv x) (.cv y) A
  have p0017_e00_recanon : Nominal.NPrf (.imp (.objEq x y) (syn_wb (.classMem (.cv x) A) (.classMem (.cv y) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0016
  have p0017 :=
    @g_anbi12d (.objEq x y) (.classMem (.cv x) A) (.classMem (.cv y) A) ps ch p0017_e00_recanon hyp_frds_2
  have p0018 :=
    @g_rexab (syn_wa (.classMem (.cv x) A) ps) (syn_wa (.classMem (.cv y) A) ch) (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y))) y x dv_cache_0007 dv_cache_0008 p0017
  have p0019 :=
    @g_anass (.classMem (.cv y) A) ch (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y)))
  have p0020 :=
    @g_exbii (syn_wa (syn_wa (.classMem (.cv y) A) ch) (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y)))) (syn_wa (.classMem (.cv y) A) (syn_wa ch (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y))))) y p0019
  have p0021 :=
    @g_bitri (syn_wrex y (.cab x (syn_wa (.classMem (.cv x) A) ps)) (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y)))) (syn_wex y (syn_wa (syn_wa (.classMem (.cv y) A) ch) (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y))))) (syn_wex y (syn_wa (.classMem (.cv y) A) (syn_wa ch (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y)))))) p0018 p0020
  have p0022 :=
    @g_impexp (.classMem (.cv z) A) th (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y))
  have p0023 :=
    @g_impexp th (syn_wbr (.cv z) R (.cv y)) (.objEq z y)
  have p0024 :=
    @g_imbi2i (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y)) (.imp th (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y))) (.classMem (.cv z) A) p0023
  have p0025 :=
    @g_bitr4i (.imp (syn_wa (.classMem (.cv z) A) th) (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y))) (.imp (.classMem (.cv z) A) (.imp th (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y)))) (.imp (.classMem (.cv z) A) (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y))) p0022 p0024
  have p0026 :=
    @g_albii (.imp (syn_wa (.classMem (.cv z) A) th) (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y))) (.imp (.classMem (.cv z) A) (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y))) z p0025
  have p0027 :=
    @g_eleq1 (.cv x) (.cv z) A
  have p0028_e00_recanon : Nominal.NPrf (.imp (.objEq x z) (syn_wb (.classMem (.cv x) A) (.classMem (.cv z) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0027
  have p0028 :=
    @g_anbi12d (.objEq x z) (.classMem (.cv x) A) (.classMem (.cv z) A) ps th p0028_e00_recanon hyp_frds_3
  have p0029 :=
    @g_ralab (syn_wa (.classMem (.cv x) A) ps) (syn_wa (.classMem (.cv z) A) th) (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y)) z x dv_cache_0009 dv_cache_0010 p0028
  have p0030 :=
    (by simpa [syn_wb, syn_wral] using (Nominal.biimpRefl (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y)))))
  have p0031 :=
    @g_n_3bitr4i (.all z (.imp (syn_wa (.classMem (.cv z) A) th) (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y)))) (.all z (.imp (.classMem (.cv z) A) (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y)))) (syn_wral z (.cab x (syn_wa (.classMem (.cv x) A) ps)) (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y))) (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y))) p0026 p0029 p0030
  have p0032 :=
    @g_rexbii (syn_wral z (.cab x (syn_wa (.classMem (.cv x) A) ps)) (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y))) (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y))) y (.cab x (syn_wa (.classMem (.cv x) A) ps)) p0031
  have p0033 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex y A (syn_wa ch (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y)))))))
  have p0034 :=
    @g_n_3bitr4i (syn_wrex y (.cab x (syn_wa (.classMem (.cv x) A) ps)) (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y)))) (syn_wex y (syn_wa (.classMem (.cv y) A) (syn_wa ch (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y)))))) (syn_wrex y (.cab x (syn_wa (.classMem (.cv x) A) ps)) (syn_wral z (.cab x (syn_wa (.classMem (.cv x) A) ps)) (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y)))) (syn_wrex y A (syn_wa ch (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y))))) p0021 p0032 p0033
  have p0035 :=
    @g_sylib ph (syn_wrex y (.cab x (syn_wa (.classMem (.cv x) A) ps)) (syn_wral z (.cab x (syn_wa (.classMem (.cv x) A) ps)) (.imp (syn_wbr (.cv z) R (.cv y)) (.objEq z y)))) (syn_wrex y A (syn_wa ch (syn_wral z A (.imp (syn_wa th (syn_wbr (.cv z) R (.cv y))) (.objEq z y))))) p0015 p0034
  exact p0035

noncomputable def g_pod
    (ph : Wff) (x : Var) (y : Var) (z : Var) (A : Class) (R : Class) (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv) (dv_ph_z : z ∉ ph.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) (hyp_pod_1 : Nominal.NPrf (.imp ph (.classMem R V))) (hyp_pod_2 : Nominal.NPrf (.imp ph (.classMem A W))) (hyp_pod_3 : Nominal.NPrf (.imp (syn_wa ph (.classMem (.cv x) A)) (syn_wbr (.cv x) R (.cv x)))) (hyp_pod_4 : Nominal.NPrf (.imp (syn_w3a ph (syn_w3a (.classMem (.cv x) A) (.classMem (.cv y) A) (.classMem (.cv z) A)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))) (syn_wbr (.cv x) R (.cv z)))) (hyp_pod_5 : Nominal.NPrf (.imp (syn_w3a ph (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))) (.objEq x y))) :
    Nominal.NPrf (.imp ph (syn_wbr R (syn_cpartial) A)) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ A.fv ∪ R.fv ∪ V.fv ∪ W.fv
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (R).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ph_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ph_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ph_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0011 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0012 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show y ≠ z from (by exact dv_y_z))
  have p0000 :=
    @g_refrd ph x A R V W dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_pod_1 hyp_pod_2 hyp_pod_3
  have p0001 :=
    @g_trrd ph x y z A R V W dv_cache_0001 dv_cache_0004 dv_cache_0005 dv_cache_0002 dv_cache_0006 dv_cache_0007 dv_cache_0003 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 hyp_pod_1 hyp_pod_2 hyp_pod_4
  have p0002 :=
    @g_antird ph x y A R V W dv_cache_0001 dv_cache_0004 dv_cache_0002 dv_cache_0006 dv_cache_0003 dv_cache_0008 dv_cache_0010 hyp_pod_1 hyp_pod_2 hyp_pod_5
  have p0003 :=
    @g_porta A R
  have p0004 :=
    @g_syl3anbrc ph (syn_wbr R (syn_cref) A) (syn_wbr R (syn_ctrans) A) (syn_wbr R (syn_cantisym) A) (syn_wbr R (syn_cpartial) A) p0000 p0001 p0002 p0003
  exact p0004

noncomputable def g_sod
    (ph : Wff) (x : Var) (y : Var) (z : Var) (A : Class) (R : Class) (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv) (dv_ph_z : z ∉ ph.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) (hyp_sod_1 : Nominal.NPrf (.imp ph (.classMem R V))) (hyp_sod_2 : Nominal.NPrf (.imp ph (.classMem A W))) (hyp_sod_3 : Nominal.NPrf (.imp (syn_wa ph (.classMem (.cv x) A)) (syn_wbr (.cv x) R (.cv x)))) (hyp_sod_4 : Nominal.NPrf (.imp (syn_w3a ph (syn_w3a (.classMem (.cv x) A) (.classMem (.cv y) A) (.classMem (.cv z) A)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))) (syn_wbr (.cv x) R (.cv z)))) (hyp_sod_5 : Nominal.NPrf (.imp (syn_w3a ph (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) A)) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))) (.objEq x y))) (hyp_sod_6 : Nominal.NPrf (.imp (syn_w3a ph (.classMem (.cv x) A) (.classMem (.cv y) A)) (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))))) :
    Nominal.NPrf (.imp ph (syn_wbr R (syn_cstrict) A)) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ A.fv ∪ R.fv ∪ V.fv ∪ W.fv
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
  have dv_cache_0004 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ph_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ph_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ph_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0011 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0012 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show y ≠ z from (by exact dv_y_z))
  have p0000 :=
    @g_pod ph x y z A R V W dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 hyp_sod_1 hyp_sod_2 hyp_sod_3 hyp_sod_4 hyp_sod_5
  have p0001 :=
    @g_connexrd ph x y A R V W dv_cache_0001 dv_cache_0002 dv_cache_0004 dv_cache_0005 dv_cache_0007 dv_cache_0008 dv_cache_0010 hyp_sod_1 hyp_sod_2 hyp_sod_6
  have p0002 :=
    @g_sopc A R
  have p0003 :=
    @g_sylanbrc ph (syn_wbr R (syn_cpartial) A) (syn_wbr R (syn_cconnex) A) (syn_wbr R (syn_cstrict) A) p0000 p0001 p0002
  exact p0003

#print axioms g_sod

end NFChoice.DirectNominalPrf.WPPReplay
