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
import NominalWPPReplayChunk014Compact001Part035

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

noncomputable def g_hwtrnisob
    (f : Var) (r : Var) :
    Nominal.NPrf (syn_wb (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f)))) := by
  let proofSupport : Finset Var := ({f} : Finset Var) ∪ ({r} : Finset Var)
  let z : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  let y : Var := freshVar proofSupport 3
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_f : z ≠ f := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_f_ne_z : f ≠ z :=
    Ne.symm fresh_z_ne_f
  have fresh_z_ne_r : z ≠ r := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_z : r ≠ z :=
    Ne.symm fresh_z_ne_r
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_ne_f : w ≠ f := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_f_ne_w : f ≠ w :=
    Ne.symm fresh_w_ne_f
  have fresh_w_ne_r : w ≠ r := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_w : r ≠ w :=
    Ne.symm fresh_w_ne_r
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_ne_f : x ≠ f := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_f_ne_x : f ≠ x :=
    Ne.symm fresh_x_ne_f
  have fresh_x_ne_r : x ≠ r := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_x : r ≠ x :=
    Ne.symm fresh_x_ne_r
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_y_ne_f : y ≠ f := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_f_ne_y : f ≠ y :=
    Ne.symm fresh_y_ne_f
  have fresh_y_ne_r : y ≠ r := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_y : r ≠ y :=
    Ne.symm fresh_y_ne_r
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have fresh_z_ne_x : z ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_w_ne_x : w ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_y_ne_w : y ≠ w :=
    Ne.symm fresh_w_ne_y
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : z ∉ ((syn_cdm (.cv f))).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : w ∉ ((syn_cdm (.cv f))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_crn (.cv f))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : w ∉ ((syn_crn (.cv f))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((Class.cv f)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : w ∉ ((Class.cv f)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((Class.cv r)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : w ∉ ((Class.cv r)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have dv_cache_0010 : z ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : z ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : z ∉ ((syn_ccom (.cv f) (.cv r))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_f, fresh_z_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : z ∉ ((syn_ccnv (.cv f))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : z ∉ ((syn_wfun (syn_ccnv (.cv f)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : z ∉ ((Wff.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : z ∉ ((syn_cfv (syn_ccnv (.cv f)) (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : z ∉ ((syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_f, fresh_z_ne_y, fresh_z_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : w ∉ ((syn_cfv (syn_ccnv (.cv f)) (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : w ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : w ∉ ((syn_wfun (syn_ccnv (.cv f)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : w ∉ ((Wff.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_y, fresh_w_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : w ∉ ((syn_cfv (syn_ccnv (.cv f)) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_y, fresh_w_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : w ∉ ((syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_f, fresh_w_ne_y, fresh_w_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : w ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : z ∉ ((syn_wa (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (.classMem (.cv y) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_f, fresh_z_ne_y, fresh_z_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : w ∉ ((syn_wa (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (.classMem (.cv y) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_f, fresh_w_ne_y, fresh_w_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : x ∉ ((syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_f, fresh_x_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0028 : y ∉ ((syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_f, fresh_y_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0029 : x ∉ ((syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv w)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, fresh_x_ne_f, fresh_x_ne_w, fresh_x_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0030 : y ∉ ((syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv w)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, fresh_y_ne_f, fresh_y_ne_w, fresh_y_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0031 : x ∉ ((syn_wfun (syn_ccnv (.cv f)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0032 : y ∉ ((syn_wfun (syn_ccnv (.cv f)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0033 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_eqid (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv w)))))
  have p0001 :=
    @g_f1oiso2 z w (syn_cdm (.cv f)) (syn_crn (.cv f)) (.cv r) (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv w))))) (.cv f) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 p0000
  have p0002 :=
    @g_f1ocnv (syn_cdm (.cv f)) (syn_crn (.cv f)) (.cv f)
  have p0003 :=
    @g_f1ofun (syn_crn (.cv f)) (syn_cdm (.cv f)) (syn_ccnv (.cv f))
  have p0004 :=
    @g_syl (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wf1o (syn_ccnv (.cv f)) (syn_crn (.cv f)) (syn_cdm (.cv f))) (syn_wfun (syn_ccnv (.cv f))) p0002 p0003
  have p0005 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y))))
  have p0006 :=
    @g_bicomi (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))) p0005
  have p0007 :=
    @g_a1i (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))) (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y))) (syn_wfun (syn_ccnv (.cv f))) p0006
  have p0008 :=
    @g_brco z (.cv x) (.cv y) (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)) dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0009 :=
    @g_a1i (syn_wb (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y)) (syn_wex z (syn_wa (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))) (syn_wfun (syn_ccnv (.cv f))) p0008
  have p0010 :=
    @g_funbrfv2b (.cv x) (.cv z) (syn_ccnv (.cv f))
  have p0011 :=
    @g_anbi1d (syn_wfun (syn_ccnv (.cv f))) (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z)) (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)) p0010
  have p0012 :=
    @g_exbidv (syn_wfun (syn_ccnv (.cv f))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))) (syn_wa (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))) z dv_cache_0014 p0011
  have p0013 :=
    @g_anass (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))
  have p0014 :=
    @g_a1i (syn_wb (syn_wa (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))) (syn_wfun (syn_ccnv (.cv f))) p0013
  have p0015 :=
    @g_exbidv (syn_wfun (syn_ccnv (.cv f))) (syn_wa (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))) z dv_cache_0014 p0014
  have p0016 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f))) (syn_wex z (syn_wa (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))) (syn_wex z (syn_wa (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))) (syn_wex z (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))) p0012 p0015
  have p0017 :=
    @g_n_19_42v (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))) z dv_cache_0015
  have p0018 :=
    @g_a1i (syn_wb (syn_wex z (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))) (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wex z (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))))) (syn_wfun (syn_ccnv (.cv f))) p0017
  have p0019 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f))) (syn_wex z (syn_wa (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))) (syn_wex z (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))) (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wex z (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))) p0016 p0018
  have p0020 :=
    @g_eqcom (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)
  have p0021 :=
    @g_anbi1i (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)) (.classEq (.cv z) (syn_cfv (syn_ccnv (.cv f)) (.cv x))) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)) p0020
  have p0022 :=
    @g_exbii (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))) (syn_wa (.classEq (.cv z) (syn_cfv (syn_ccnv (.cv f)) (.cv x))) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))) z p0021
  have p0023 :=
    @g_fvex (.cv x) (syn_ccnv (.cv f))
  have p0024 :=
    @g_breq1 (.cv z) (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv y) (syn_ccom (.cv f) (.cv r))
  have p0025 :=
    @g_ceqsexv (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y)) z (syn_cfv (syn_ccnv (.cv f)) (.cv x)) dv_cache_0016 dv_cache_0017 p0023 p0024
  have p0026 :=
    @g_bitri (syn_wex z (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))) (syn_wex z (syn_wa (.classEq (.cv z) (syn_cfv (syn_ccnv (.cv f)) (.cv x))) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y)) p0022 p0025
  have p0027 :=
    @g_anbi2i (syn_wex z (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y)) (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) p0026
  have p0028 :=
    @g_a1i (syn_wb (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wex z (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))) (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y)))) (syn_wfun (syn_ccnv (.cv f))) p0027
  have p0029 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f))) (syn_wex z (syn_wa (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))) (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wex z (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))) (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y))) p0019 p0028
  have p0030 :=
    @g_dfrn4 (.cv f)
  have p0031 :=
    @g_eleq2i (syn_crn (.cv f)) (syn_cdm (syn_ccnv (.cv f))) (.cv x) p0030
  have p0032 :=
    @g_bicomi (.classMem (.cv x) (syn_crn (.cv f))) (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) p0031
  have p0033 :=
    @g_anbi1i (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (.classMem (.cv x) (syn_crn (.cv f))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y)) p0032
  have p0034 :=
    @g_a1i (syn_wb (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y))) (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y)))) (syn_wfun (syn_ccnv (.cv f))) p0033
  have p0035 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f))) (syn_wex z (syn_wa (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))) (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y))) (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y))) p0029 p0034
  have p0036 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f))) (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y)) (syn_wex z (syn_wa (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))) (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y))) p0009 p0035
  have p0037 :=
    @g_brco w (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv y) (.cv f) (.cv r) dv_cache_0018 dv_cache_0019 dv_cache_0006 dv_cache_0008
  have p0038 :=
    @g_a1i (syn_wb (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y)) (syn_wex w (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)) (syn_wbr (.cv w) (.cv f) (.cv y))))) (syn_wfun (syn_ccnv (.cv f))) p0037
  have p0039 :=
    @g_brcnv (.cv y) (.cv w) (.cv f)
  have p0040 :=
    @g_bicomi (syn_wbr (.cv y) (syn_ccnv (.cv f)) (.cv w)) (syn_wbr (.cv w) (.cv f) (.cv y)) p0039
  have p0041 :=
    @g_a1i (syn_wb (syn_wbr (.cv w) (.cv f) (.cv y)) (syn_wbr (.cv y) (syn_ccnv (.cv f)) (.cv w))) (syn_wfun (syn_ccnv (.cv f))) p0040
  have p0042 :=
    @g_funbrfv2b (.cv y) (.cv w) (syn_ccnv (.cv f))
  have p0043 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f))) (syn_wbr (.cv w) (.cv f) (.cv y)) (syn_wbr (.cv y) (syn_ccnv (.cv f)) (.cv w)) (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))) p0041 p0042
  have p0044 :=
    @g_anbi2d (syn_wfun (syn_ccnv (.cv f))) (syn_wbr (.cv w) (.cv f) (.cv y)) (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)) p0043
  have p0045 :=
    @g_exbidv (syn_wfun (syn_ccnv (.cv f))) (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)) (syn_wbr (.cv w) (.cv f) (.cv y))) (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)) (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)))) w dv_cache_0020 p0044
  have p0046 :=
    @g_ancom (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)) (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)))
  have p0047 :=
    @g_anass (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))
  have p0048 :=
    @g_bitri (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)) (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))) (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)))) p0046 p0047
  have p0049 :=
    @g_a1i (syn_wb (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)) (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)))) (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))))) (syn_wfun (syn_ccnv (.cv f))) p0048
  have p0050 :=
    @g_exbidv (syn_wfun (syn_ccnv (.cv f))) (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)) (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)))) (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)))) w dv_cache_0020 p0049
  have p0051 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f))) (syn_wex w (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)) (syn_wbr (.cv w) (.cv f) (.cv y)))) (syn_wex w (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)) (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))))) (syn_wex w (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))))) p0045 p0050
  have p0052 :=
    @g_n_19_42v (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))) w dv_cache_0021
  have p0053 :=
    @g_a1i (syn_wb (syn_wex w (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))))) (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wex w (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)))))) (syn_wfun (syn_ccnv (.cv f))) p0052
  have p0054 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f))) (syn_wex w (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)) (syn_wbr (.cv w) (.cv f) (.cv y)))) (syn_wex w (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))))) (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wex w (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))))) p0051 p0053
  have p0055 :=
    @g_eqcom (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)
  have p0056 :=
    @g_anbi1i (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)) (.classEq (.cv w) (syn_cfv (syn_ccnv (.cv f)) (.cv y))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)) p0055
  have p0057 :=
    @g_exbii (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))) (syn_wa (.classEq (.cv w) (syn_cfv (syn_ccnv (.cv f)) (.cv y))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))) w p0056
  have p0058 :=
    @g_fvex (.cv y) (syn_ccnv (.cv f))
  have p0059 :=
    @g_breq2 (.cv w) (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
  have p0060 :=
    @g_ceqsexv (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y))) w (syn_cfv (syn_ccnv (.cv f)) (.cv y)) dv_cache_0022 dv_cache_0023 p0058 p0059
  have p0061 :=
    @g_bitri (syn_wex w (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)))) (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv (syn_ccnv (.cv f)) (.cv y))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y))) p0057 p0060
  have p0062 :=
    @g_anbi2i (syn_wex w (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y))) (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) p0061
  have p0063 :=
    @g_a1i (syn_wb (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wex w (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))))) (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y))))) (syn_wfun (syn_ccnv (.cv f))) p0062
  have p0064 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f))) (syn_wex w (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)) (syn_wbr (.cv w) (.cv f) (.cv y)))) (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wex w (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))))) (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))) p0054 p0063
  have p0065 :=
    @g_dfrn4 (.cv f)
  have p0066 :=
    @g_eleq2i (syn_crn (.cv f)) (syn_cdm (syn_ccnv (.cv f))) (.cv y) p0065
  have p0067 :=
    @g_bicomi (.classMem (.cv y) (syn_crn (.cv f))) (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) p0066
  have p0068 :=
    @g_anbi1i (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (.classMem (.cv y) (syn_crn (.cv f))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y))) p0067
  have p0069 :=
    @g_a1i (syn_wb (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))) (syn_wa (.classMem (.cv y) (syn_crn (.cv f))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y))))) (syn_wfun (syn_ccnv (.cv f))) p0068
  have p0070 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f))) (syn_wex w (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)) (syn_wbr (.cv w) (.cv f) (.cv y)))) (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))) (syn_wa (.classMem (.cv y) (syn_crn (.cv f))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))) p0064 p0069
  have p0071 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y)) (syn_wex w (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)) (syn_wbr (.cv w) (.cv f) (.cv y)))) (syn_wa (.classMem (.cv y) (syn_crn (.cv f))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))) p0038 p0070
  have p0072 :=
    @g_anbi2d (syn_wfun (syn_ccnv (.cv f))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y)) (syn_wa (.classMem (.cv y) (syn_crn (.cv f))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))) (.classMem (.cv x) (syn_crn (.cv f))) p0071
  have p0073 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f))) (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y)) (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y))) (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (syn_wa (.classMem (.cv y) (syn_crn (.cv f))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y))))) p0036 p0072
  have p0074 :=
    @g_anass (.classMem (.cv x) (syn_crn (.cv f))) (.classMem (.cv y) (syn_crn (.cv f))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
  have p0075 :=
    @g_bicomi (syn_wa (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (.classMem (.cv y) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))) (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (syn_wa (.classMem (.cv y) (syn_crn (.cv f))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y))))) p0074
  have p0076 :=
    @g_a1i (syn_wb (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (syn_wa (.classMem (.cv y) (syn_crn (.cv f))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y))))) (syn_wa (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (.classMem (.cv y) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y))))) (syn_wfun (syn_ccnv (.cv f))) p0075
  have p0077 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f))) (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y)) (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (syn_wa (.classMem (.cv y) (syn_crn (.cv f))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y))))) (syn_wa (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (.classMem (.cv y) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))) p0073 p0076
  have p0078 :=
    @g_vex x
  have p0079 :=
    @g_vex y
  have p0080 :=
    @g_simpl (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y))
  have p0081 :=
    @g_eleq1d (syn_wa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y))) (.cv z) (.cv x) (syn_crn (.cv f)) p0080
  have p0082 :=
    @g_simpr (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y))
  have p0083 :=
    @g_eleq1d (syn_wa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y))) (.cv w) (.cv y) (syn_crn (.cv f)) p0082
  have p0084 :=
    @g_anbi12d (syn_wa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y))) (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv x) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f))) (.classMem (.cv y) (syn_crn (.cv f))) p0081 p0083
  have p0085 :=
    @g_simpl (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y))
  have p0086 :=
    @g_fveq2d (syn_wa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y))) (.cv z) (.cv x) (syn_ccnv (.cv f)) p0085
  have p0087 :=
    @g_simpr (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y))
  have p0088 :=
    @g_fveq2d (syn_wa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y))) (.cv w) (.cv y) (syn_ccnv (.cv f)) p0087
  have p0089 :=
    @g_breq12d (syn_wa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y))) (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_cfv (syn_ccnv (.cv f)) (.cv w)) (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv r) p0086 p0088
  have p0090 :=
    @g_anbi12d (syn_wa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y))) (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f)))) (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (.classMem (.cv y) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv w))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y))) p0084 p0089
  have p0091 :=
    @g_eqid (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv w)))))
  have p0092 :=
    @g_braba (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv w)))) (syn_wa (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (.classMem (.cv y) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))) z w (.cv x) (.cv y) (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv w))))) dv_cache_0010 dv_cache_0024 dv_cache_0011 dv_cache_0019 dv_cache_0025 dv_cache_0026 dv_cache_0009 p0078 p0079 p0090 p0091
  have p0093 :=
    @g_bicomi (syn_wbr (.cv x) (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv w))))) (.cv y)) (syn_wa (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (.classMem (.cv y) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))) p0092
  have p0094 :=
    @g_a1i (syn_wb (syn_wa (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (.classMem (.cv y) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))) (syn_wbr (.cv x) (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv w))))) (.cv y))) (syn_wfun (syn_ccnv (.cv f))) p0093
  have p0095 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f))) (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y)) (syn_wa (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (.classMem (.cv y) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))) (syn_wbr (.cv x) (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv w))))) (.cv y)) p0077 p0094
  have p0096 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f))) (.classMem (syn_cop (.cv x) (.cv y)) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))) (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y)) (syn_wbr (.cv x) (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv w))))) (.cv y)) p0007 p0095
  have p0097 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv w))))) (.cv y))))
  have p0098 :=
    @g_a1i (syn_wb (syn_wbr (.cv x) (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv w))))) (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv w))))))) (syn_wfun (syn_ccnv (.cv f))) p0097
  have p0099 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f))) (.classMem (syn_cop (.cv x) (.cv y)) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))) (syn_wbr (.cv x) (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv w))))) (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv w)))))) p0096 p0098
  have p0100 :=
    @g_eqrelrdv (syn_wfun (syn_ccnv (.cv f))) x y (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv w))))) dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 p0099
  have p0101 :=
    @g_syl (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wfun (syn_ccnv (.cv f))) (.classEq (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv w)))))) p0004 p0100
  have p0102 :=
    @g_eqcomd (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv w))))) p0101
  have p0103 :=
    @g_isoeq3 (syn_cdm (.cv f)) (syn_crn (.cv f)) (.cv r) (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv w))))) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv f)
  have p0104 :=
    @g_syl (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) (.classEq (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv w))))) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))) (syn_wb (syn_wiso (.cv f) (.cv r) (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv w))))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f)))) p0102 p0103
  have p0105 :=
    @g_mpbid (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wiso (.cv f) (.cv r) (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv w))))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) p0001 p0104
  have p0106 :=
    @g_isof1o (syn_cdm (.cv f)) (syn_crn (.cv f)) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv f)
  have p0107 :=
    @g_impbii (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) p0105 p0106
  exact p0107

#print axioms g_hwtrnisob

end NFChoice.DirectNominalPrf.WPPReplay
