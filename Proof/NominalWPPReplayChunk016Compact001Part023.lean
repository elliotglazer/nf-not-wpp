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
import NominalWPPReplayChunk016Compact001Part022

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

noncomputable def g_wecutisogensswecutiso
    (D : Class) (R : Class) (S : Class) (E : Class) (hyp_wecutisogensswecutiso_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) (hyp_wecutisogensswecutiso_2 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) :
    Nominal.NPrf (syn_wss (syn_cwecutisogen R D S E) (syn_cwecutiso R D S E)) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  let f : Var := freshVar proofSupport 0
  let r : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  let y : Var := freshVar proofSupport 3
  have fresh_f : f ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_D : f ∉ D.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_f_not_R : f ∉ R.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_f_not_S : f ∉ S.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_f_not_E : f ∉ E.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_r_not_D : r ∉ D.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_r_not_R : r ∉ R.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_r_not_S : r ∉ S.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_not_E : r ∉ E.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_E : x ∉ E.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_E : y ∉ E.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_f_ne_r : f ≠ r := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_r_ne_f : r ≠ f :=
    Ne.symm fresh_f_ne_r
  have fresh_f_ne_x : f ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_f : x ≠ f :=
    Ne.symm fresh_f_ne_x
  have fresh_f_ne_y : f ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_y_ne_f : y ≠ f :=
    Ne.symm fresh_f_ne_y
  have fresh_r_ne_x : r ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_r : x ≠ r :=
    Ne.symm fresh_r_ne_x
  have fresh_r_ne_y : r ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_y_ne_r : y ≠ r :=
    Ne.symm fresh_r_ne_y
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : r ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : r ∉ (E).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_E, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : r ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : r ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : f ≠ r := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show f ≠ r from (by exact fresh_f_ne_r))
  have dv_cache_0006 : x ∉ ((syn_cop (.cv r) (syn_cdm (.cv f)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_r, fresh_x_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_f, fresh_y_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ (E).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_E, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : f ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : y ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : f ∉ (E).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_E, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ (E).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_E, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : f ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : f ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : x ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : f ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (show f ≠ x from (by exact fresh_f_ne_x))
  have dv_cache_0021 : f ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show f ≠ y from (by exact fresh_f_ne_y))
  have dv_cache_0022 : r ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0023 : r ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show r ≠ y from (by exact fresh_r_ne_y))
  have dv_cache_0024 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0025 : y ∉ ((Wff.classMem (.cv f) (syn_cwecutiso R D S E))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_f, fresh_y_not_D, fresh_y_not_E, fresh_y_not_R, fresh_y_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : y ∉ ((syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (.cv x) D) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_r, fresh_y_ne_f, fresh_y_not_D, fresh_y_not_R, fresh_y_not_E, fresh_y_not_S, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : x ∉ ((Wff.classMem (.cv f) (syn_cwecutiso R D S E))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_f, fresh_x_not_D, fresh_x_not_E, fresh_x_not_R, fresh_x_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0028 : x ∉ ((syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_r, fresh_x_ne_f, fresh_x_not_D, fresh_x_not_R, fresh_x_not_E, fresh_x_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0029 : r ∉ ((Wff.classMem (.cv f) (syn_cwecutiso R D S E))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_f, fresh_r_not_D, fresh_r_not_E, fresh_r_not_R, fresh_r_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0030 : r ∉ ((Wff.classMem (.cv f) (syn_cwecutisogen R D S E))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutisogen, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_f, fresh_r_not_D, fresh_r_not_E, fresh_r_not_R, fresh_r_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0031 : f ∉ ((syn_cwecutisogen R D S E)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutisogen, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_D, fresh_f_not_E, fresh_f_not_R, fresh_f_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0032 : f ∉ ((syn_cwecutiso R D S E)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_D, fresh_f_not_E, fresh_f_not_R, fresh_f_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_wecutisogenrawout D R S f E r dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @g_simpr (.classMem (.cv f) (syn_cwecutisogen R D S E)) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))
  have p0002 :=
    @g_simpr (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))
  have p0003 :=
    @g_simpr (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))
  have p0004 :=
    @g_syl (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))) p0002 p0003
  have p0005 :=
    @g_simpl (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))
  have p0006 :=
    @g_syl (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))) (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) p0004 p0005
  have p0007 :=
    @g_wecutisogenrangedecode x (syn_cop (.cv r) (syn_cdm (.cv f))) D R dv_cache_0006 dv_cache_0007 dv_cache_0008 hyp_wecutisogensswecutiso_1
  have p0008 :=
    @g_syl (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (syn_wrex x D (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))) p0006 p0007
  have p0009 :=
    @g_simpl (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (.cv x) D) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))))
  have p0010 :=
    @g_simpr (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))
  have p0011 :=
    @g_simpr (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))
  have p0012 :=
    @g_syl (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))) p0010 p0011
  have p0013 :=
    @g_simpr (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))
  have p0014 :=
    @g_syl (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))) p0012 p0013
  have p0015 :=
    @g_wecutisogenrangedecode y (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) E S dv_cache_0009 dv_cache_0010 dv_cache_0011 hyp_wecutisogensswecutiso_2
  have p0016 :=
    @g_syl (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))) (syn_wrex y E (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))) p0014 p0015
  have p0017 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (.cv x) D) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (syn_wrex y E (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))) p0009 p0016
  have p0018 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (.cv x) D) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))))) (syn_wa (.classMem (.cv y) E) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))
  have p0019 :=
    @g_simpr (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (.cv x) D) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))))
  have p0020 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (.cv x) D) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))))) (syn_wa (.classMem (.cv y) E) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))) (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (.cv x) D) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))))) (syn_wa (.classMem (.cv x) D) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))) p0018 p0019
  have p0021 :=
    @g_simpl (.classMem (.cv x) D) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
  have p0022 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (.cv x) D) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))))) (syn_wa (.classMem (.cv y) E) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))) (syn_wa (.classMem (.cv x) D) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))) (.classMem (.cv x) D) p0020 p0021
  have p0023 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (.cv x) D) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))))) (syn_wa (.classMem (.cv y) E) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))
  have p0024 :=
    @g_simpl (.classMem (.cv y) E) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))
  have p0025 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (.cv x) D) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))))) (syn_wa (.classMem (.cv y) E) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))) (syn_wa (.classMem (.cv y) E) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))) (.classMem (.cv y) E) p0023 p0024
  have p0026 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (.cv x) D) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))))) (syn_wa (.classMem (.cv y) E) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))) (.classMem (.cv x) D) (.classMem (.cv y) E) p0022 p0025
  have p0027 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (.cv x) D) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))))) (syn_wa (.classMem (.cv y) E) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))
  have p0028 :=
    @g_simpl (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (.cv x) D) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))))
  have p0029 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (.cv x) D) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))))) (syn_wa (.classMem (.cv y) E) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))) (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (.cv x) D) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) p0027 p0028
  have p0030 :=
    @g_simpr (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))
  have p0031 :=
    @g_simpl (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))
  have p0032 :=
    @g_syl (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))) (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) p0030 p0031
  have p0033 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (.cv x) D) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))))) (syn_wa (.classMem (.cv y) E) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) p0029 p0032
  have p0034 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (.cv x) D) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))))) (syn_wa (.classMem (.cv y) E) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))
  have p0035 :=
    @g_simpr (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (.cv x) D) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))))
  have p0036 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (.cv x) D) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))))) (syn_wa (.classMem (.cv y) E) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))) (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (.cv x) D) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))))) (syn_wa (.classMem (.cv x) D) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))) p0034 p0035
  have p0037 :=
    @g_simpr (.classMem (.cv x) D) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))
  have p0038 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (.cv x) D) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))))) (syn_wa (.classMem (.cv y) E) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))) (syn_wa (.classMem (.cv x) D) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x)))) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) p0036 p0037
  have p0039 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (.cv x) D) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))))) (syn_wa (.classMem (.cv y) E) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))
  have p0040 :=
    @g_simpr (.classMem (.cv y) E) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))
  have p0041 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (.cv x) D) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))))) (syn_wa (.classMem (.cv y) E) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))) (syn_wa (.classMem (.cv y) E) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))) p0039 p0040
  have p0042 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (.cv x) D) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))))) (syn_wa (.classMem (.cv y) E) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))) p0038 p0041
  have p0043 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (.cv x) D) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))))) (syn_wa (.classMem (.cv y) E) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))) (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))) p0033 p0042
  have p0044 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (.cv x) D) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))))) (syn_wa (.classMem (.cv y) E) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))) p0026 p0043
  have p0045 :=
    @g_wecutisogenfixedrev x y D R S f E r dv_cache_0012 dv_cache_0001 dv_cache_0007 dv_cache_0013 dv_cache_0014 dv_cache_0002 dv_cache_0015 dv_cache_0010 dv_cache_0016 dv_cache_0003 dv_cache_0008 dv_cache_0017 dv_cache_0018 dv_cache_0004 dv_cache_0019 dv_cache_0011 dv_cache_0005 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
  have p0046 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (.cv x) D) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))))) (syn_wa (.classMem (.cv y) E) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))))) (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y)))))) (.classMem (.cv f) (syn_cwecutiso R D S E)) p0044 p0045
  have p0047 :=
    @g_rexlimddv (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (.cv x) D) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))))) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_chnwcutcode S E (.cv y))) (.classMem (.cv f) (syn_cwecutiso R D S E)) y E dv_cache_0025 dv_cache_0026 p0017 p0046
  have p0048 :=
    @g_rexlimddv (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_chnwcutcode R D (.cv x))) (.classMem (.cv f) (syn_cwecutiso R D S E)) x D dv_cache_0027 dv_cache_0028 p0008 p0047
  have p0049 :=
    @g_syl (syn_wa (.classMem (.cv f) (syn_cwecutisogen R D S E)) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (.classMem (.cv f) (syn_cwecutiso R D S E)) p0001 p0048
  have p0050 :=
    @g_rexlimddv (.classMem (.cv f) (syn_cwecutisogen R D S E)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))) (.classMem (.cv f) (syn_cwecutiso R D S E)) r (syn_cvv) dv_cache_0029 dv_cache_0030 p0000 p0049
  have p0051 :=
    @g_ssriv f (syn_cwecutisogen R D S E) (syn_cwecutiso R D S E) dv_cache_0031 dv_cache_0032 p0050
  exact p0051

#print axioms g_wecutisogensswecutiso

end NFChoice.DirectNominalPrf.WPPReplay
