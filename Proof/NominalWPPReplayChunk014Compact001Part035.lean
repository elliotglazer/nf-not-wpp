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
import NominalWPPReplayChunk014Compact001Part034

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

noncomputable def g_hwtrnbrd
    (x : Var) (y : Var) (f : Var) (r : Var) (dv_f_x : f ≠ x) (dv_f_y : f ≠ y) :
    Nominal.NPrf (.imp (syn_wfun (syn_ccnv (.cv f))) (syn_wb (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y)) (syn_wa (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (.classMem (.cv y) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({f} : Finset Var) ∪ ({r} : Finset Var)
  let z : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_ne_f : z ≠ f := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
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
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_w : y ≠ w :=
    Ne.symm fresh_w_ne_y
  have fresh_w_ne_f : w ≠ f := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_ne_w : f ≠ w :=
    Ne.symm fresh_w_ne_f
  have fresh_w_ne_r : w ≠ r := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_w : r ≠ w :=
    Ne.symm fresh_w_ne_r
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have dv_cache_0001 : z ∉ ((Class.cv x)).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_ccom (.cv f) (.cv r))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_f, fresh_z_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((syn_ccnv (.cv f))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((syn_wfun (syn_ccnv (.cv f)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((Wff.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((syn_cfv (syn_ccnv (.cv f)) (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : z ∉ ((syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_f, fresh_z_ne_y, fresh_z_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : w ∉ ((syn_cfv (syn_ccnv (.cv f)) (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : w ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : w ∉ ((Class.cv f)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : w ∉ ((Class.cv r)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : w ∉ ((syn_wfun (syn_ccnv (.cv f)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : w ∉ ((Wff.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_y, fresh_w_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : w ∉ ((syn_cfv (syn_ccnv (.cv f)) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_y, fresh_w_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : w ∉ ((syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_f, fresh_w_ne_y, fresh_w_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_brco z (.cv x) (.cv y) (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0001 :=
    @g_a1i (syn_wb (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y)) (syn_wex z (syn_wa (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))) (syn_wfun (syn_ccnv (.cv f))) p0000
  have p0002 :=
    @g_funbrfv2b (.cv x) (.cv z) (syn_ccnv (.cv f))
  have p0003 :=
    @g_anbi1d (syn_wfun (syn_ccnv (.cv f))) (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z)) (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)) p0002
  have p0004 :=
    @g_exbidv (syn_wfun (syn_ccnv (.cv f))) (syn_wa (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))) (syn_wa (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))) z dv_cache_0005 p0003
  have p0005 :=
    @g_anass (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))
  have p0006 :=
    @g_a1i (syn_wb (syn_wa (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))) (syn_wfun (syn_ccnv (.cv f))) p0005
  have p0007 :=
    @g_exbidv (syn_wfun (syn_ccnv (.cv f))) (syn_wa (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))) (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))) z dv_cache_0005 p0006
  have p0008 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f))) (syn_wex z (syn_wa (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))) (syn_wex z (syn_wa (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))) (syn_wex z (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))) p0004 p0007
  have p0009 :=
    @g_n_19_42v (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))) z dv_cache_0006
  have p0010 :=
    @g_a1i (syn_wb (syn_wex z (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))) (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wex z (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))))) (syn_wfun (syn_ccnv (.cv f))) p0009
  have p0011 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f))) (syn_wex z (syn_wa (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))) (syn_wex z (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))) (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wex z (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))) p0008 p0010
  have p0012 :=
    @g_eqcom (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)
  have p0013 :=
    @g_anbi1i (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)) (.classEq (.cv z) (syn_cfv (syn_ccnv (.cv f)) (.cv x))) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)) p0012
  have p0014 :=
    @g_exbii (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))) (syn_wa (.classEq (.cv z) (syn_cfv (syn_ccnv (.cv f)) (.cv x))) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))) z p0013
  have p0015 :=
    @g_fvex (.cv x) (syn_ccnv (.cv f))
  have p0016 :=
    @g_breq1 (.cv z) (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv y) (syn_ccom (.cv f) (.cv r))
  have p0017 :=
    @g_ceqsexv (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y)) z (syn_cfv (syn_ccnv (.cv f)) (.cv x)) dv_cache_0007 dv_cache_0008 p0015 p0016
  have p0018 :=
    @g_bitri (syn_wex z (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))) (syn_wex z (syn_wa (.classEq (.cv z) (syn_cfv (syn_ccnv (.cv f)) (.cv x))) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y)) p0014 p0017
  have p0019 :=
    @g_anbi2i (syn_wex z (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y)) (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) p0018
  have p0020 :=
    @g_a1i (syn_wb (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wex z (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))) (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y)))) (syn_wfun (syn_ccnv (.cv f))) p0019
  have p0021 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f))) (syn_wex z (syn_wa (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))) (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wex z (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))) (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y))) p0011 p0020
  have p0022 :=
    @g_dfrn4 (.cv f)
  have p0023 :=
    @g_eleq2i (syn_crn (.cv f)) (syn_cdm (syn_ccnv (.cv f))) (.cv x) p0022
  have p0024 :=
    @g_bicomi (.classMem (.cv x) (syn_crn (.cv f))) (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) p0023
  have p0025 :=
    @g_anbi1i (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (.classMem (.cv x) (syn_crn (.cv f))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y)) p0024
  have p0026 :=
    @g_a1i (syn_wb (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y))) (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y)))) (syn_wfun (syn_ccnv (.cv f))) p0025
  have p0027 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f))) (syn_wex z (syn_wa (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))) (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y))) (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y))) p0021 p0026
  have p0028 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f))) (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y)) (syn_wex z (syn_wa (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z)) (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))) (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y))) p0001 p0027
  have p0029 :=
    @g_brco w (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv y) (.cv f) (.cv r) dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0030 :=
    @g_a1i (syn_wb (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y)) (syn_wex w (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)) (syn_wbr (.cv w) (.cv f) (.cv y))))) (syn_wfun (syn_ccnv (.cv f))) p0029
  have p0031 :=
    @g_brcnv (.cv y) (.cv w) (.cv f)
  have p0032 :=
    @g_bicomi (syn_wbr (.cv y) (syn_ccnv (.cv f)) (.cv w)) (syn_wbr (.cv w) (.cv f) (.cv y)) p0031
  have p0033 :=
    @g_a1i (syn_wb (syn_wbr (.cv w) (.cv f) (.cv y)) (syn_wbr (.cv y) (syn_ccnv (.cv f)) (.cv w))) (syn_wfun (syn_ccnv (.cv f))) p0032
  have p0034 :=
    @g_funbrfv2b (.cv y) (.cv w) (syn_ccnv (.cv f))
  have p0035 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f))) (syn_wbr (.cv w) (.cv f) (.cv y)) (syn_wbr (.cv y) (syn_ccnv (.cv f)) (.cv w)) (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))) p0033 p0034
  have p0036 :=
    @g_anbi2d (syn_wfun (syn_ccnv (.cv f))) (syn_wbr (.cv w) (.cv f) (.cv y)) (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)) p0035
  have p0037 :=
    @g_exbidv (syn_wfun (syn_ccnv (.cv f))) (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)) (syn_wbr (.cv w) (.cv f) (.cv y))) (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)) (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)))) w dv_cache_0013 p0036
  have p0038 :=
    @g_ancom (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)) (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)))
  have p0039 :=
    @g_anass (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))
  have p0040 :=
    @g_bitri (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)) (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))) (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)))) p0038 p0039
  have p0041 :=
    @g_a1i (syn_wb (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)) (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)))) (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))))) (syn_wfun (syn_ccnv (.cv f))) p0040
  have p0042 :=
    @g_exbidv (syn_wfun (syn_ccnv (.cv f))) (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)) (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)))) (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)))) w dv_cache_0013 p0041
  have p0043 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f))) (syn_wex w (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)) (syn_wbr (.cv w) (.cv f) (.cv y)))) (syn_wex w (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)) (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))))) (syn_wex w (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))))) p0037 p0042
  have p0044 :=
    @g_n_19_42v (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))) w dv_cache_0014
  have p0045 :=
    @g_a1i (syn_wb (syn_wex w (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))))) (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wex w (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)))))) (syn_wfun (syn_ccnv (.cv f))) p0044
  have p0046 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f))) (syn_wex w (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)) (syn_wbr (.cv w) (.cv f) (.cv y)))) (syn_wex w (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))))) (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wex w (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))))) p0043 p0045
  have p0047 :=
    @g_eqcom (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)
  have p0048 :=
    @g_anbi1i (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)) (.classEq (.cv w) (syn_cfv (syn_ccnv (.cv f)) (.cv y))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)) p0047
  have p0049 :=
    @g_exbii (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))) (syn_wa (.classEq (.cv w) (syn_cfv (syn_ccnv (.cv f)) (.cv y))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))) w p0048
  have p0050 :=
    @g_fvex (.cv y) (syn_ccnv (.cv f))
  have p0051 :=
    @g_breq2 (.cv w) (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
  have p0052 :=
    @g_ceqsexv (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y))) w (syn_cfv (syn_ccnv (.cv f)) (.cv y)) dv_cache_0015 dv_cache_0016 p0050 p0051
  have p0053 :=
    @g_bitri (syn_wex w (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)))) (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv (syn_ccnv (.cv f)) (.cv y))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y))) p0049 p0052
  have p0054 :=
    @g_anbi2i (syn_wex w (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y))) (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) p0053
  have p0055 :=
    @g_a1i (syn_wb (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wex w (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))))) (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y))))) (syn_wfun (syn_ccnv (.cv f))) p0054
  have p0056 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f))) (syn_wex w (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)) (syn_wbr (.cv w) (.cv f) (.cv y)))) (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wex w (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))))) (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))) p0046 p0055
  have p0057 :=
    @g_dfrn4 (.cv f)
  have p0058 :=
    @g_eleq2i (syn_crn (.cv f)) (syn_cdm (syn_ccnv (.cv f))) (.cv y) p0057
  have p0059 :=
    @g_bicomi (.classMem (.cv y) (syn_crn (.cv f))) (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) p0058
  have p0060 :=
    @g_anbi1i (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (.classMem (.cv y) (syn_crn (.cv f))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y))) p0059
  have p0061 :=
    @g_a1i (syn_wb (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))) (syn_wa (.classMem (.cv y) (syn_crn (.cv f))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y))))) (syn_wfun (syn_ccnv (.cv f))) p0060
  have p0062 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f))) (syn_wex w (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)) (syn_wbr (.cv w) (.cv f) (.cv y)))) (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))) (syn_wa (.classMem (.cv y) (syn_crn (.cv f))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))) p0056 p0061
  have p0063 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y)) (syn_wex w (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)) (syn_wbr (.cv w) (.cv f) (.cv y)))) (syn_wa (.classMem (.cv y) (syn_crn (.cv f))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))) p0030 p0062
  have p0064 :=
    @g_anbi2d (syn_wfun (syn_ccnv (.cv f))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y)) (syn_wa (.classMem (.cv y) (syn_crn (.cv f))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))) (.classMem (.cv x) (syn_crn (.cv f))) p0063
  have p0065 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f))) (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y)) (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y))) (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (syn_wa (.classMem (.cv y) (syn_crn (.cv f))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y))))) p0028 p0064
  have p0066 :=
    @g_anass (.classMem (.cv x) (syn_crn (.cv f))) (.classMem (.cv y) (syn_crn (.cv f))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
  have p0067 :=
    @g_bicomi (syn_wa (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (.classMem (.cv y) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))) (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (syn_wa (.classMem (.cv y) (syn_crn (.cv f))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y))))) p0066
  have p0068 :=
    @g_a1i (syn_wb (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (syn_wa (.classMem (.cv y) (syn_crn (.cv f))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y))))) (syn_wa (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (.classMem (.cv y) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y))))) (syn_wfun (syn_ccnv (.cv f))) p0067
  have p0069 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f))) (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y)) (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (syn_wa (.classMem (.cv y) (syn_crn (.cv f))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y))))) (syn_wa (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (.classMem (.cv y) (syn_crn (.cv f)))) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))) p0065 p0068
  exact p0069

#print axioms g_hwtrnbrd

end NFChoice.DirectNominalPrf.WPPReplay
