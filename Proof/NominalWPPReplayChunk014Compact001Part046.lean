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
import NominalWPPReplayChunk014Compact001Part045

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

noncomputable def g_strictsegnoiso
    (x : Var) (D : Class) (R : Class) (H : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (.neg (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ D.fv ∪ R.fv ∪ H.fv
  let z : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_H : z ∉ H.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_H : y ∉ H.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_w_not_D : w ∉ D.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_R : w ∉ R.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_H : w ∉ H.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_z_ne_y : z ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have fresh_y_ne_w : y ≠ w := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_w_ne_y : w ≠ y :=
    Ne.symm fresh_y_ne_w
  have dv_cache_0001 : w ∉ ((Class.cv x)).fv := by
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : w ∉ ((syn_cin H R)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_H, fresh_w_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : w ∉ ((syn_wa (syn_wfn H D) (.classMem (.cv x) D))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_H, fresh_w_not_D, fresh_w_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : w ∉ ((syn_cfv H (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, fresh_w_not_H, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : w ∉ ((syn_wbr (.cv x) R (syn_cfv H (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, fresh_w_not_H, fresh_w_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_cdif D (syn_cdm (syn_cin H R)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_D, fresh_y_not_H, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((syn_cdif D (syn_cdm (syn_cin H R)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_D, fresh_z_not_H, fresh_z_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0011 : w ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : w ∉ ((syn_wa (syn_wfn H D) (.classMem (.cv y) D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_H, fresh_w_not_D, fresh_w_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : w ∉ ((syn_cfv H (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_y, fresh_w_not_H, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : w ∉ ((syn_wbr (.cv y) R (syn_cfv H (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_y, fresh_w_not_H, fresh_w_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : z ∉ ((syn_cfv H (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, fresh_z_not_H, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : z ∉ ((Wff.imp (syn_wbr (syn_cfv H (.cv y)) R (.cv y)) (.classEq (syn_cfv H (.cv y)) (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, fresh_z_not_H, fresh_z_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : w ∉ ((syn_wa (syn_wfn H D) (.classMem (syn_cfv H (.cv y)) D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_H, fresh_w_not_D, fresh_w_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : w ∉ ((syn_cfv H (syn_cfv H (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_y, fresh_w_not_H, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : w ∉ ((syn_wbr (syn_cfv H (.cv y)) R (syn_cfv H (syn_cfv H (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_y, fresh_w_not_H, fresh_w_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : y ∉ ((Wff.neg (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_D, fresh_y_not_R, fresh_y_ne_x, fresh_y_not_H, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : y ∉ ((syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, fresh_y_not_D, fresh_y_ne_x, fresh_y_not_H, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0001 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))
  have p0002 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) p0000 p0001
  have p0003 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)
  have p0004 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wbr R (syn_cwe) D) p0002 p0003
  have p0005 :=
    (by simpa [syn_cwe] using (Nominal.classEqRefl (syn_cwe)))
  have p0006 :=
    @g_breqi R D (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0005
  have p0007 :=
    @g_brin R D (syn_cstrict) (syn_cfound)
  have p0008 :=
    @g_bitri (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_cin (syn_cstrict) (syn_cfound)) D) (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0006 p0007
  have p0009 :=
    @g_biimpi (syn_wbr R (syn_cwe) D) (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0008
  have p0010 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cwe) D) (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0004 p0009
  have p0011 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D) p0010
  have p0012 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0013 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))
  have p0014 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) p0012 p0013
  have p0015 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)
  have p0016 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wbr R (syn_cwe) D) p0014 p0015
  have p0017 :=
    @g_brex R D (syn_cwe)
  have p0018 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cwe) D) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) p0016 p0017
  have p0019 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0018
  have p0020 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0021 :=
    @g_simpr (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))
  have p0022 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (.classMem H (syn_cvv)) p0020 p0021
  have p0023 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0024 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))
  have p0025 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) p0023 p0024
  have p0026 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)
  have p0027 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wbr R (syn_cwe) D) p0025 p0026
  have p0028 :=
    @g_brex R D (syn_cwe)
  have p0029 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cwe) D) (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) p0027 p0028
  have p0030 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0029
  have p0031 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem H (syn_cvv)) (.classMem R (syn_cvv)) p0022 p0030
  have p0032 :=
    @g_inexg H R (syn_cvv) (syn_cvv)
  have p0033 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (.classMem H (syn_cvv)) (.classMem R (syn_cvv))) (.classMem (syn_cin H R) (syn_cvv)) p0031 p0032
  have p0034 :=
    @g_dmexg (syn_cin H R) (syn_cvv)
  have p0035 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (syn_cin H R) (syn_cvv)) (.classMem (syn_cdm (syn_cin H R)) (syn_cvv)) p0033 p0034
  have p0036 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem D (syn_cvv)) (.classMem (syn_cdm (syn_cin H R)) (syn_cvv)) p0019 p0035
  have p0037 :=
    @g_difexg D (syn_cdm (syn_cin H R)) (syn_cvv) (syn_cvv)
  have p0038 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (.classMem D (syn_cvv)) (.classMem (syn_cdm (syn_cin H R)) (syn_cvv))) (.classMem (syn_cdif D (syn_cdm (syn_cin H R))) (syn_cvv)) p0036 p0037
  have p0039 :=
    @g_difss D (syn_cdm (syn_cin H R))
  have p0040 :=
    @g_a1i (syn_wss (syn_cdif D (syn_cdm (syn_cin H R))) D) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) p0039
  have p0041 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0042 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))
  have p0043 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) p0041 p0042
  have p0044 :=
    @g_simpr (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)
  have p0045 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem (.cv x) D) p0043 p0044
  have p0046 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr (.cv x) R (syn_cfv H (.cv x)))
  have p0047 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0048 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))
  have p0049 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) p0047 p0048
  have p0050 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)
  have p0051 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wbr R (syn_cwe) D) p0049 p0050
  have p0052 :=
    (by simpa [syn_cwe] using (Nominal.classEqRefl (syn_cwe)))
  have p0053 :=
    @g_breqi R D (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0052
  have p0054 :=
    @g_brin R D (syn_cstrict) (syn_cfound)
  have p0055 :=
    @g_bitri (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_cin (syn_cstrict) (syn_cfound)) D) (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0053 p0054
  have p0056 :=
    @g_biimpi (syn_wbr R (syn_cwe) D) (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0055
  have p0057 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cwe) D) (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0051 p0056
  have p0058 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D) p0057
  have p0059 :=
    @g_sopc D R
  have p0060 :=
    @g_sylib (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cstrict) D) (syn_wa (syn_wbr R (syn_cpartial) D) (syn_wbr R (syn_cconnex) D)) p0058 p0059
  have p0061 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cpartial) D) (syn_wbr R (syn_cconnex) D) p0060
  have p0062 :=
    @g_porta D R
  have p0063 :=
    @g_sylib (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cpartial) D) (syn_w3a (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D) (syn_wbr R (syn_cantisym) D)) p0061 p0062
  have p0064 :=
    @g_simp3d (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D) (syn_wbr R (syn_cantisym) D) p0063
  have p0065 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr (.cv x) R (syn_cfv H (.cv x)))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cantisym) D) p0046 p0064
  have p0066 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr (.cv x) R (syn_cfv H (.cv x)))
  have p0067 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0068 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))
  have p0069 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) p0067 p0068
  have p0070 :=
    @g_simpr (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)
  have p0071 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem (.cv x) D) p0069 p0070
  have p0072 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr (.cv x) R (syn_cfv H (.cv x)))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv x) D) p0066 p0071
  have p0073 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr (.cv x) R (syn_cfv H (.cv x)))
  have p0074 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0075 :=
    @g_isof1o D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) H
  have p0076 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0074 p0075
  have p0077 :=
    @g_f1of D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) H
  have p0078 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0076 p0077
  have p0079 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0080 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))
  have p0081 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) p0079 p0080
  have p0082 :=
    @g_simpr (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)
  have p0083 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem (.cv x) D) p0081 p0082
  have p0084 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv x) D) p0078 p0083
  have p0085 :=
    @g_ffvelrn D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (.cv x) H
  have p0086 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv x) D)) (.classMem (syn_cfv H (.cv x)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0084 p0085
  have p0087 :=
    @g_elin (syn_cfv H (.cv x)) D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0088 :=
    @g_eliniseg (syn_cdif R (syn_cid)) (.cv x) (syn_cfv H (.cv x))
  have p0089 :=
    @g_brdif (syn_cfv H (.cv x)) (.cv x) R (syn_cid)
  have p0090 :=
    @g_vex x
  have p0091 :=
    @g_ideq (syn_cfv H (.cv x)) (.cv x) p0090
  have p0092 :=
    @g_notbii (syn_wbr (syn_cfv H (.cv x)) (syn_cid) (.cv x)) (.classEq (syn_cfv H (.cv x)) (.cv x)) p0091
  have p0093 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (syn_cfv H (.cv x)) (.cv x))))
  have p0094 :=
    @g_bitr4i (.neg (syn_wbr (syn_cfv H (.cv x)) (syn_cid) (.cv x))) (.neg (.classEq (syn_cfv H (.cv x)) (.cv x))) (syn_wne (syn_cfv H (.cv x)) (.cv x)) p0092 p0093
  have p0095 :=
    @g_anbi2i (.neg (syn_wbr (syn_cfv H (.cv x)) (syn_cid) (.cv x))) (syn_wne (syn_cfv H (.cv x)) (.cv x)) (syn_wbr (syn_cfv H (.cv x)) R (.cv x)) p0094
  have p0096 :=
    @g_bitri (syn_wbr (syn_cfv H (.cv x)) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (syn_cfv H (.cv x)) R (.cv x)) (.neg (syn_wbr (syn_cfv H (.cv x)) (syn_cid) (.cv x)))) (syn_wa (syn_wbr (syn_cfv H (.cv x)) R (.cv x)) (syn_wne (syn_cfv H (.cv x)) (.cv x))) p0089 p0095
  have p0097 :=
    @g_bitri (.classMem (syn_cfv H (.cv x)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wbr (syn_cfv H (.cv x)) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (syn_cfv H (.cv x)) R (.cv x)) (syn_wne (syn_cfv H (.cv x)) (.cv x))) p0088 p0096
  have p0098 :=
    @g_anbi2i (.classMem (syn_cfv H (.cv x)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wa (syn_wbr (syn_cfv H (.cv x)) R (.cv x)) (syn_wne (syn_cfv H (.cv x)) (.cv x))) (.classMem (syn_cfv H (.cv x)) D) p0097
  have p0099 :=
    @g_bitri (.classMem (syn_cfv H (.cv x)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv x)) D) (.classMem (syn_cfv H (.cv x)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv x)) D) (syn_wa (syn_wbr (syn_cfv H (.cv x)) R (.cv x)) (syn_wne (syn_cfv H (.cv x)) (.cv x)))) p0087 p0098
  have p0100 :=
    @g_biimpi (.classMem (syn_cfv H (.cv x)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv x)) D) (syn_wa (syn_wbr (syn_cfv H (.cv x)) R (.cv x)) (syn_wne (syn_cfv H (.cv x)) (.cv x)))) p0099
  have p0101 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (syn_cfv H (.cv x)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv x)) D) (syn_wa (syn_wbr (syn_cfv H (.cv x)) R (.cv x)) (syn_wne (syn_cfv H (.cv x)) (.cv x)))) p0086 p0100
  have p0102 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (syn_cfv H (.cv x)) D) (syn_wa (syn_wbr (syn_cfv H (.cv x)) R (.cv x)) (syn_wne (syn_cfv H (.cv x)) (.cv x))) p0101
  have p0103 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr (.cv x) R (syn_cfv H (.cv x)))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (syn_cfv H (.cv x)) D) p0073 p0102
  have p0104 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr (.cv x) R (syn_cfv H (.cv x)))
  have p0105 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr (.cv x) R (syn_cfv H (.cv x)))
  have p0106 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0107 :=
    @g_isof1o D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) H
  have p0108 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0106 p0107
  have p0109 :=
    @g_f1of D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) H
  have p0110 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0108 p0109
  have p0111 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0112 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))
  have p0113 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) p0111 p0112
  have p0114 :=
    @g_simpr (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)
  have p0115 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem (.cv x) D) p0113 p0114
  have p0116 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv x) D) p0110 p0115
  have p0117 :=
    @g_ffvelrn D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (.cv x) H
  have p0118 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv x) D)) (.classMem (syn_cfv H (.cv x)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0116 p0117
  have p0119 :=
    @g_elin (syn_cfv H (.cv x)) D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0120 :=
    @g_eliniseg (syn_cdif R (syn_cid)) (.cv x) (syn_cfv H (.cv x))
  have p0121 :=
    @g_brdif (syn_cfv H (.cv x)) (.cv x) R (syn_cid)
  have p0122 :=
    @g_vex x
  have p0123 :=
    @g_ideq (syn_cfv H (.cv x)) (.cv x) p0122
  have p0124 :=
    @g_notbii (syn_wbr (syn_cfv H (.cv x)) (syn_cid) (.cv x)) (.classEq (syn_cfv H (.cv x)) (.cv x)) p0123
  have p0125 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (syn_cfv H (.cv x)) (.cv x))))
  have p0126 :=
    @g_bitr4i (.neg (syn_wbr (syn_cfv H (.cv x)) (syn_cid) (.cv x))) (.neg (.classEq (syn_cfv H (.cv x)) (.cv x))) (syn_wne (syn_cfv H (.cv x)) (.cv x)) p0124 p0125
  have p0127 :=
    @g_anbi2i (.neg (syn_wbr (syn_cfv H (.cv x)) (syn_cid) (.cv x))) (syn_wne (syn_cfv H (.cv x)) (.cv x)) (syn_wbr (syn_cfv H (.cv x)) R (.cv x)) p0126
  have p0128 :=
    @g_bitri (syn_wbr (syn_cfv H (.cv x)) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (syn_cfv H (.cv x)) R (.cv x)) (.neg (syn_wbr (syn_cfv H (.cv x)) (syn_cid) (.cv x)))) (syn_wa (syn_wbr (syn_cfv H (.cv x)) R (.cv x)) (syn_wne (syn_cfv H (.cv x)) (.cv x))) p0121 p0127
  have p0129 :=
    @g_bitri (.classMem (syn_cfv H (.cv x)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wbr (syn_cfv H (.cv x)) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (syn_cfv H (.cv x)) R (.cv x)) (syn_wne (syn_cfv H (.cv x)) (.cv x))) p0120 p0128
  have p0130 :=
    @g_anbi2i (.classMem (syn_cfv H (.cv x)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wa (syn_wbr (syn_cfv H (.cv x)) R (.cv x)) (syn_wne (syn_cfv H (.cv x)) (.cv x))) (.classMem (syn_cfv H (.cv x)) D) p0129
  have p0131 :=
    @g_bitri (.classMem (syn_cfv H (.cv x)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv x)) D) (.classMem (syn_cfv H (.cv x)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv x)) D) (syn_wa (syn_wbr (syn_cfv H (.cv x)) R (.cv x)) (syn_wne (syn_cfv H (.cv x)) (.cv x)))) p0119 p0130
  have p0132 :=
    @g_biimpi (.classMem (syn_cfv H (.cv x)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv x)) D) (syn_wa (syn_wbr (syn_cfv H (.cv x)) R (.cv x)) (syn_wne (syn_cfv H (.cv x)) (.cv x)))) p0131
  have p0133 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (syn_cfv H (.cv x)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv x)) D) (syn_wa (syn_wbr (syn_cfv H (.cv x)) R (.cv x)) (syn_wne (syn_cfv H (.cv x)) (.cv x)))) p0118 p0132
  have p0134 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (syn_cfv H (.cv x)) D) (syn_wa (syn_wbr (syn_cfv H (.cv x)) R (.cv x)) (syn_wne (syn_cfv H (.cv x)) (.cv x))) p0133
  have p0135 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr (syn_cfv H (.cv x)) R (.cv x)) (syn_wne (syn_cfv H (.cv x)) (.cv x)) p0134
  have p0136 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr (.cv x) R (syn_cfv H (.cv x)))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr (syn_cfv H (.cv x)) R (.cv x)) p0105 p0135
  have p0137 :=
    @g_antid (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr (.cv x) R (syn_cfv H (.cv x)))) D R (.cv x) (syn_cfv H (.cv x)) p0065 p0072 p0103 p0104 p0136
  have p0138 :=
    @g_eqcomd (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr (.cv x) R (syn_cfv H (.cv x)))) (.cv x) (syn_cfv H (.cv x)) p0137
  have p0139 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr (.cv x) R (syn_cfv H (.cv x)))
  have p0140 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0141 :=
    @g_isof1o D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) H
  have p0142 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0140 p0141
  have p0143 :=
    @g_f1of D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) H
  have p0144 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0142 p0143
  have p0145 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0146 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))
  have p0147 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) p0145 p0146
  have p0148 :=
    @g_simpr (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)
  have p0149 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem (.cv x) D) p0147 p0148
  have p0150 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv x) D) p0144 p0149
  have p0151 :=
    @g_ffvelrn D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (.cv x) H
  have p0152 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv x) D)) (.classMem (syn_cfv H (.cv x)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0150 p0151
  have p0153 :=
    @g_elin (syn_cfv H (.cv x)) D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0154 :=
    @g_eliniseg (syn_cdif R (syn_cid)) (.cv x) (syn_cfv H (.cv x))
  have p0155 :=
    @g_brdif (syn_cfv H (.cv x)) (.cv x) R (syn_cid)
  have p0156 :=
    @g_vex x
  have p0157 :=
    @g_ideq (syn_cfv H (.cv x)) (.cv x) p0156
  have p0158 :=
    @g_notbii (syn_wbr (syn_cfv H (.cv x)) (syn_cid) (.cv x)) (.classEq (syn_cfv H (.cv x)) (.cv x)) p0157
  have p0159 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (syn_cfv H (.cv x)) (.cv x))))
  have p0160 :=
    @g_bitr4i (.neg (syn_wbr (syn_cfv H (.cv x)) (syn_cid) (.cv x))) (.neg (.classEq (syn_cfv H (.cv x)) (.cv x))) (syn_wne (syn_cfv H (.cv x)) (.cv x)) p0158 p0159
  have p0161 :=
    @g_anbi2i (.neg (syn_wbr (syn_cfv H (.cv x)) (syn_cid) (.cv x))) (syn_wne (syn_cfv H (.cv x)) (.cv x)) (syn_wbr (syn_cfv H (.cv x)) R (.cv x)) p0160
  have p0162 :=
    @g_bitri (syn_wbr (syn_cfv H (.cv x)) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (syn_cfv H (.cv x)) R (.cv x)) (.neg (syn_wbr (syn_cfv H (.cv x)) (syn_cid) (.cv x)))) (syn_wa (syn_wbr (syn_cfv H (.cv x)) R (.cv x)) (syn_wne (syn_cfv H (.cv x)) (.cv x))) p0155 p0161
  have p0163 :=
    @g_bitri (.classMem (syn_cfv H (.cv x)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wbr (syn_cfv H (.cv x)) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (syn_cfv H (.cv x)) R (.cv x)) (syn_wne (syn_cfv H (.cv x)) (.cv x))) p0154 p0162
  have p0164 :=
    @g_anbi2i (.classMem (syn_cfv H (.cv x)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wa (syn_wbr (syn_cfv H (.cv x)) R (.cv x)) (syn_wne (syn_cfv H (.cv x)) (.cv x))) (.classMem (syn_cfv H (.cv x)) D) p0163
  have p0165 :=
    @g_bitri (.classMem (syn_cfv H (.cv x)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv x)) D) (.classMem (syn_cfv H (.cv x)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv x)) D) (syn_wa (syn_wbr (syn_cfv H (.cv x)) R (.cv x)) (syn_wne (syn_cfv H (.cv x)) (.cv x)))) p0153 p0164
  have p0166 :=
    @g_biimpi (.classMem (syn_cfv H (.cv x)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv x)) D) (syn_wa (syn_wbr (syn_cfv H (.cv x)) R (.cv x)) (syn_wne (syn_cfv H (.cv x)) (.cv x)))) p0165
  have p0167 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (syn_cfv H (.cv x)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv x)) D) (syn_wa (syn_wbr (syn_cfv H (.cv x)) R (.cv x)) (syn_wne (syn_cfv H (.cv x)) (.cv x)))) p0152 p0166
  have p0168 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (syn_cfv H (.cv x)) D) (syn_wa (syn_wbr (syn_cfv H (.cv x)) R (.cv x)) (syn_wne (syn_cfv H (.cv x)) (.cv x))) p0167
  have p0169 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr (syn_cfv H (.cv x)) R (.cv x)) (syn_wne (syn_cfv H (.cv x)) (.cv x)) p0168
  have p0170 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr (.cv x) R (syn_cfv H (.cv x)))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wne (syn_cfv H (.cv x)) (.cv x)) p0139 p0169
  have p0171 :=
    @g_pm2_21ddne (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr (.cv x) R (syn_cfv H (.cv x)))) (.neg (syn_wbr (.cv x) R (syn_cfv H (.cv x)))) (syn_cfv H (.cv x)) (.cv x) p0138 p0170
  have p0172 :=
    @g_pm2_01da (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr (.cv x) R (syn_cfv H (.cv x))) p0171
  have p0173 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0174 :=
    @g_isof1o D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) H
  have p0175 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0173 p0174
  have p0176 :=
    @g_f1ofn D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) H
  have p0177 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wfn H D) p0175 p0176
  have p0178 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0179 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))
  have p0180 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) p0178 p0179
  have p0181 :=
    @g_simpr (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)
  have p0182 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem (.cv x) D) p0180 p0181
  have p0183 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wfn H D) (.classMem (.cv x) D) p0177 p0182
  have p0184 :=
    @g_eldm w (.cv x) (syn_cin H R) dv_cache_0001 dv_cache_0002
  have p0185 :=
    @g_a1i (syn_wb (.classMem (.cv x) (syn_cdm (syn_cin H R))) (syn_wex w (syn_wbr (.cv x) (syn_cin H R) (.cv w)))) (syn_wa (syn_wfn H D) (.classMem (.cv x) D)) p0184
  have p0186 :=
    @g_brin (.cv x) (.cv w) H R
  have p0187 :=
    @g_a1i (syn_wb (syn_wbr (.cv x) (syn_cin H R) (.cv w)) (syn_wa (syn_wbr (.cv x) H (.cv w)) (syn_wbr (.cv x) R (.cv w)))) (syn_wa (syn_wfn H D) (.classMem (.cv x) D)) p0186
  have p0188 :=
    @g_fnbrfvb D (.cv x) (.cv w) H
  have p0189 :=
    @g_bicomd (syn_wa (syn_wfn H D) (.classMem (.cv x) D)) (.classEq (syn_cfv H (.cv x)) (.cv w)) (syn_wbr (.cv x) H (.cv w)) p0188
  have p0190 :=
    @g_anbi1d (syn_wa (syn_wfn H D) (.classMem (.cv x) D)) (syn_wbr (.cv x) H (.cv w)) (.classEq (syn_cfv H (.cv x)) (.cv w)) (syn_wbr (.cv x) R (.cv w)) p0189
  have p0191 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (.cv x) D)) (syn_wbr (.cv x) (syn_cin H R) (.cv w)) (syn_wa (syn_wbr (.cv x) H (.cv w)) (syn_wbr (.cv x) R (.cv w))) (syn_wa (.classEq (syn_cfv H (.cv x)) (.cv w)) (syn_wbr (.cv x) R (.cv w))) p0187 p0190
  have p0192 :=
    @g_exbidv (syn_wa (syn_wfn H D) (.classMem (.cv x) D)) (syn_wbr (.cv x) (syn_cin H R) (.cv w)) (syn_wa (.classEq (syn_cfv H (.cv x)) (.cv w)) (syn_wbr (.cv x) R (.cv w))) w dv_cache_0003 p0191
  have p0193 :=
    @g_eqcom (syn_cfv H (.cv x)) (.cv w)
  have p0194 :=
    @g_anbi1i (.classEq (syn_cfv H (.cv x)) (.cv w)) (.classEq (.cv w) (syn_cfv H (.cv x))) (syn_wbr (.cv x) R (.cv w)) p0193
  have p0195 :=
    @g_exbii (syn_wa (.classEq (syn_cfv H (.cv x)) (.cv w)) (syn_wbr (.cv x) R (.cv w))) (syn_wa (.classEq (.cv w) (syn_cfv H (.cv x))) (syn_wbr (.cv x) R (.cv w))) w p0194
  have p0196 :=
    @g_a1i (syn_wb (syn_wex w (syn_wa (.classEq (syn_cfv H (.cv x)) (.cv w)) (syn_wbr (.cv x) R (.cv w)))) (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv H (.cv x))) (syn_wbr (.cv x) R (.cv w))))) (syn_wa (syn_wfn H D) (.classMem (.cv x) D)) p0195
  have p0197 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (.cv x) D)) (syn_wex w (syn_wbr (.cv x) (syn_cin H R) (.cv w))) (syn_wex w (syn_wa (.classEq (syn_cfv H (.cv x)) (.cv w)) (syn_wbr (.cv x) R (.cv w)))) (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv H (.cv x))) (syn_wbr (.cv x) R (.cv w)))) p0192 p0196
  have p0198 :=
    @g_fvex (.cv x) H
  have p0199 :=
    @g_breq2 (.cv w) (syn_cfv H (.cv x)) (.cv x) R
  have p0200 :=
    @g_ceqsexv (syn_wbr (.cv x) R (.cv w)) (syn_wbr (.cv x) R (syn_cfv H (.cv x))) w (syn_cfv H (.cv x)) dv_cache_0004 dv_cache_0005 p0198 p0199
  have p0201 :=
    @g_a1i (syn_wb (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv H (.cv x))) (syn_wbr (.cv x) R (.cv w)))) (syn_wbr (.cv x) R (syn_cfv H (.cv x)))) (syn_wa (syn_wfn H D) (.classMem (.cv x) D)) p0200
  have p0202 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (.cv x) D)) (syn_wex w (syn_wbr (.cv x) (syn_cin H R) (.cv w))) (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv H (.cv x))) (syn_wbr (.cv x) R (.cv w)))) (syn_wbr (.cv x) R (syn_cfv H (.cv x))) p0197 p0201
  have p0203 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (.cv x) D)) (.classMem (.cv x) (syn_cdm (syn_cin H R))) (syn_wex w (syn_wbr (.cv x) (syn_cin H R) (.cv w))) (syn_wbr (.cv x) R (syn_cfv H (.cv x))) p0185 p0202
  have p0204 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wfn H D) (.classMem (.cv x) D)) (syn_wb (.classMem (.cv x) (syn_cdm (syn_cin H R))) (syn_wbr (.cv x) R (syn_cfv H (.cv x)))) p0183 p0203
  have p0205 :=
    @g_biimpd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv x) (syn_cdm (syn_cin H R))) (syn_wbr (.cv x) R (syn_cfv H (.cv x))) p0204
  have p0206 :=
    @g_mtod (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv x) (syn_cdm (syn_cin H R))) (syn_wbr (.cv x) R (syn_cfv H (.cv x))) p0172 p0205
  have p0207 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv x) D) (.neg (.classMem (.cv x) (syn_cdm (syn_cin H R)))) p0045 p0206
  have p0208 :=
    @g_eldif (.cv x) D (syn_cdm (syn_cin H R))
  have p0209 :=
    @g_biimpri (.classMem (.cv x) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) (syn_cdm (syn_cin H R))))) p0208
  have p0210 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) (syn_cdm (syn_cin H R))))) (.classMem (.cv x) (syn_cdif D (syn_cdm (syn_cin H R)))) p0207 p0209
  have p0211 :=
    @g_ne0i (syn_cdif D (syn_cdm (syn_cin H R))) (.cv x)
  have p0212 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv x) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wne (syn_cdif D (syn_cdm (syn_cin H R))) (syn_c0)) p0210 p0211
  have p0213 :=
    @g_frd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) y z D R (syn_cvv) (syn_cdif D (syn_cdm (syn_cin H R))) dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 p0011 p0038 p0040 p0212
  have p0214 :=
    @g_simp1 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0215 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0216 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))
  have p0217 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) p0215 p0216
  have p0218 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)
  have p0219 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wbr R (syn_cwe) D) p0217 p0218
  have p0220 :=
    (by simpa [syn_cwe] using (Nominal.classEqRefl (syn_cwe)))
  have p0221 :=
    @g_breqi R D (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0220
  have p0222 :=
    @g_brin R D (syn_cstrict) (syn_cfound)
  have p0223 :=
    @g_bitri (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_cin (syn_cstrict) (syn_cfound)) D) (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0221 p0222
  have p0224 :=
    @g_biimpi (syn_wbr R (syn_cwe) D) (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0223
  have p0225 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cwe) D) (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0219 p0224
  have p0226 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D) p0225
  have p0227 :=
    @g_sopc D R
  have p0228 :=
    @g_sylib (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cstrict) D) (syn_wa (syn_wbr R (syn_cpartial) D) (syn_wbr R (syn_cconnex) D)) p0226 p0227
  have p0229 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cpartial) D) (syn_wbr R (syn_cconnex) D) p0228
  have p0230 :=
    @g_porta D R
  have p0231 :=
    @g_sylib (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cpartial) D) (syn_w3a (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D) (syn_wbr R (syn_cantisym) D)) p0229 p0230
  have p0232 :=
    @g_simp3d (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D) (syn_wbr R (syn_cantisym) D) p0231
  have p0233 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cantisym) D) p0214 p0232
  have p0234 :=
    @g_simp1 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0235 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0236 :=
    @g_isof1o D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) H
  have p0237 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0235 p0236
  have p0238 :=
    @g_f1of D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) H
  have p0239 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0237 p0238
  have p0240 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0234 p0239
  have p0241 :=
    @g_simp2 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0242 :=
    @g_eldifi (.cv y) D (syn_cdm (syn_cin H R))
  have p0243 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (.classMem (.cv y) D) p0241 p0242
  have p0244 :=
    @g_jca (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv y) D) p0240 p0243
  have p0245 :=
    @g_ffvelrn D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (.cv y) H
  have p0246 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv y) D)) (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0244 p0245
  have p0247 :=
    @g_elin (syn_cfv H (.cv y)) D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0248 :=
    @g_eliniseg (syn_cdif R (syn_cid)) (.cv x) (syn_cfv H (.cv y))
  have p0249 :=
    @g_brdif (syn_cfv H (.cv y)) (.cv x) R (syn_cid)
  have p0250 :=
    @g_vex x
  have p0251 :=
    @g_ideq (syn_cfv H (.cv y)) (.cv x) p0250
  have p0252 :=
    @g_notbii (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x)) (.classEq (syn_cfv H (.cv y)) (.cv x)) p0251
  have p0253 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (syn_cfv H (.cv y)) (.cv x))))
  have p0254 :=
    @g_bitr4i (.neg (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x))) (.neg (.classEq (syn_cfv H (.cv y)) (.cv x))) (syn_wne (syn_cfv H (.cv y)) (.cv x)) p0252 p0253
  have p0255 :=
    @g_anbi2i (.neg (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x))) (syn_wne (syn_cfv H (.cv y)) (.cv x)) (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) p0254
  have p0256 :=
    @g_bitri (syn_wbr (syn_cfv H (.cv y)) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (.neg (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x)))) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) p0249 p0255
  have p0257 :=
    @g_bitri (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wbr (syn_cfv H (.cv y)) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) p0248 p0256
  have p0258 :=
    @g_anbi2i (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) (.classMem (syn_cfv H (.cv y)) D) p0257
  have p0259 :=
    @g_bitri (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x)))) p0247 p0258
  have p0260 :=
    @g_biimpi (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x)))) p0259
  have p0261 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x)))) p0246 p0260
  have p0262 :=
    @g_simpld (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) p0261
  have p0263 :=
    @g_simp1 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0264 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0265 :=
    @g_isof1o D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) H
  have p0266 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0264 p0265
  have p0267 :=
    @g_f1of D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) H
  have p0268 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0266 p0267
  have p0269 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0263 p0268
  have p0270 :=
    @g_simp1 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0271 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0272 :=
    @g_isof1o D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) H
  have p0273 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0271 p0272
  have p0274 :=
    @g_f1of D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) H
  have p0275 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0273 p0274
  have p0276 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0270 p0275
  have p0277 :=
    @g_simp2 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0278 :=
    @g_eldifi (.cv y) D (syn_cdm (syn_cin H R))
  have p0279 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (.classMem (.cv y) D) p0277 p0278
  have p0280 :=
    @g_jca (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv y) D) p0276 p0279
  have p0281 :=
    @g_ffvelrn D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (.cv y) H
  have p0282 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv y) D)) (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0280 p0281
  have p0283 :=
    @g_elin (syn_cfv H (.cv y)) D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0284 :=
    @g_eliniseg (syn_cdif R (syn_cid)) (.cv x) (syn_cfv H (.cv y))
  have p0285 :=
    @g_brdif (syn_cfv H (.cv y)) (.cv x) R (syn_cid)
  have p0286 :=
    @g_vex x
  have p0287 :=
    @g_ideq (syn_cfv H (.cv y)) (.cv x) p0286
  have p0288 :=
    @g_notbii (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x)) (.classEq (syn_cfv H (.cv y)) (.cv x)) p0287
  have p0289 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (syn_cfv H (.cv y)) (.cv x))))
  have p0290 :=
    @g_bitr4i (.neg (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x))) (.neg (.classEq (syn_cfv H (.cv y)) (.cv x))) (syn_wne (syn_cfv H (.cv y)) (.cv x)) p0288 p0289
  have p0291 :=
    @g_anbi2i (.neg (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x))) (syn_wne (syn_cfv H (.cv y)) (.cv x)) (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) p0290
  have p0292 :=
    @g_bitri (syn_wbr (syn_cfv H (.cv y)) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (.neg (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x)))) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) p0285 p0291
  have p0293 :=
    @g_bitri (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wbr (syn_cfv H (.cv y)) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) p0284 p0292
  have p0294 :=
    @g_anbi2i (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) (.classMem (syn_cfv H (.cv y)) D) p0293
  have p0295 :=
    @g_bitri (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x)))) p0283 p0294
  have p0296 :=
    @g_biimpi (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x)))) p0295
  have p0297 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x)))) p0282 p0296
  have p0298 :=
    @g_simpld (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) p0297
  have p0299 :=
    @g_jca (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (syn_cfv H (.cv y)) D) p0269 p0298
  have p0300 :=
    @g_ffvelrn D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cfv H (.cv y)) H
  have p0301 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (syn_cfv H (.cv y)) D)) (.classMem (syn_cfv H (syn_cfv H (.cv y))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0299 p0300
  have p0302 :=
    @g_inss1 D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0303 :=
    @g_sseli (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) D (syn_cfv H (syn_cfv H (.cv y))) p0302
  have p0304 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (syn_cfv H (.cv y))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (syn_cfv H (syn_cfv H (.cv y))) D) p0301 p0303
  have p0305 :=
    @g_id (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R)))
  have p0306 :=
    @g_a1i (.imp (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R))) (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R)))) (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) p0305
  have p0307 :=
    @g_simpl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.neg (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R))))
  have p0308 :=
    @g_simp1 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0309 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0310 :=
    @g_isof1o D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) H
  have p0311 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0309 p0310
  have p0312 :=
    @g_f1of D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) H
  have p0313 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0311 p0312
  have p0314 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0308 p0313
  have p0315 :=
    @g_simp2 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0316 :=
    @g_eldifi (.cv y) D (syn_cdm (syn_cin H R))
  have p0317 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (.classMem (.cv y) D) p0315 p0316
  have p0318 :=
    @g_jca (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv y) D) p0314 p0317
  have p0319 :=
    @g_ffvelrn D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (.cv y) H
  have p0320 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv y) D)) (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0318 p0319
  have p0321 :=
    @g_elin (syn_cfv H (.cv y)) D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0322 :=
    @g_eliniseg (syn_cdif R (syn_cid)) (.cv x) (syn_cfv H (.cv y))
  have p0323 :=
    @g_brdif (syn_cfv H (.cv y)) (.cv x) R (syn_cid)
  have p0324 :=
    @g_vex x
  have p0325 :=
    @g_ideq (syn_cfv H (.cv y)) (.cv x) p0324
  have p0326 :=
    @g_notbii (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x)) (.classEq (syn_cfv H (.cv y)) (.cv x)) p0325
  have p0327 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (syn_cfv H (.cv y)) (.cv x))))
  have p0328 :=
    @g_bitr4i (.neg (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x))) (.neg (.classEq (syn_cfv H (.cv y)) (.cv x))) (syn_wne (syn_cfv H (.cv y)) (.cv x)) p0326 p0327
  have p0329 :=
    @g_anbi2i (.neg (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x))) (syn_wne (syn_cfv H (.cv y)) (.cv x)) (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) p0328
  have p0330 :=
    @g_bitri (syn_wbr (syn_cfv H (.cv y)) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (.neg (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x)))) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) p0323 p0329
  have p0331 :=
    @g_bitri (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wbr (syn_cfv H (.cv y)) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) p0322 p0330
  have p0332 :=
    @g_anbi2i (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) (.classMem (syn_cfv H (.cv y)) D) p0331
  have p0333 :=
    @g_bitri (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x)))) p0321 p0332
  have p0334 :=
    @g_biimpi (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x)))) p0333
  have p0335 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x)))) p0320 p0334
  have p0336 :=
    @g_simpld (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) p0335
  have p0337 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.neg (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R))))) (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) D) p0307 p0336
  have p0338 :=
    @g_simpr (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.neg (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R))))
  have p0339 :=
    @g_jca (syn_wa (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.neg (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R))))) (.classMem (syn_cfv H (.cv y)) D) (.neg (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R)))) p0337 p0338
  have p0340 :=
    @g_eldif (syn_cfv H (.cv y)) D (syn_cdm (syn_cin H R))
  have p0341 :=
    @g_biimpri (.classMem (syn_cfv H (.cv y)) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (.neg (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R))))) p0340
  have p0342 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.neg (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (.neg (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R))))) (.classMem (syn_cfv H (.cv y)) (syn_cdif D (syn_cdm (syn_cin H R)))) p0339 p0341
  have p0343 :=
    @g_simpl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.neg (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R))))
  have p0344 :=
    @g_simpl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) (syn_cdif D (syn_cdm (syn_cin H R))))
  have p0345 :=
    @g_simp2 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0346 :=
    @g_eldifn (.cv y) D (syn_cdm (syn_cin H R))
  have p0347 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (.neg (.classMem (.cv y) (syn_cdm (syn_cin H R)))) p0345 p0346
  have p0348 :=
    @g_simp1 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0349 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0350 :=
    @g_isof1o D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) H
  have p0351 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0349 p0350
  have p0352 :=
    @g_f1ofn D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) H
  have p0353 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wfn H D) p0351 p0352
  have p0354 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wfn H D) p0348 p0353
  have p0355 :=
    @g_simp2 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0356 :=
    @g_eldifi (.cv y) D (syn_cdm (syn_cin H R))
  have p0357 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (.classMem (.cv y) D) p0355 p0356
  have p0358 :=
    @g_jca (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wfn H D) (.classMem (.cv y) D) p0354 p0357
  have p0359 :=
    @g_eldm w (.cv y) (syn_cin H R) dv_cache_0011 dv_cache_0002
  have p0360 :=
    @g_a1i (syn_wb (.classMem (.cv y) (syn_cdm (syn_cin H R))) (syn_wex w (syn_wbr (.cv y) (syn_cin H R) (.cv w)))) (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) p0359
  have p0361 :=
    @g_brin (.cv y) (.cv w) H R
  have p0362 :=
    @g_a1i (syn_wb (syn_wbr (.cv y) (syn_cin H R) (.cv w)) (syn_wa (syn_wbr (.cv y) H (.cv w)) (syn_wbr (.cv y) R (.cv w)))) (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) p0361
  have p0363 :=
    @g_fnbrfvb D (.cv y) (.cv w) H
  have p0364 :=
    @g_bicomd (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) H (.cv w)) p0363
  have p0365 :=
    @g_anbi1d (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wbr (.cv y) H (.cv w)) (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w)) p0364
  have p0366 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wbr (.cv y) (syn_cin H R) (.cv w)) (syn_wa (syn_wbr (.cv y) H (.cv w)) (syn_wbr (.cv y) R (.cv w))) (syn_wa (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w))) p0362 p0365
  have p0367 :=
    @g_exbidv (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wbr (.cv y) (syn_cin H R) (.cv w)) (syn_wa (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w))) w dv_cache_0012 p0366
  have p0368 :=
    @g_eqcom (syn_cfv H (.cv y)) (.cv w)
  have p0369 :=
    @g_anbi1i (.classEq (syn_cfv H (.cv y)) (.cv w)) (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w)) p0368
  have p0370 :=
    @g_exbii (syn_wa (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w))) (syn_wa (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w))) w p0369
  have p0371 :=
    @g_a1i (syn_wb (syn_wex w (syn_wa (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w)))) (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w))))) (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) p0370
  have p0372 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wex w (syn_wbr (.cv y) (syn_cin H R) (.cv w))) (syn_wex w (syn_wa (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w)))) (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w)))) p0367 p0371
  have p0373 :=
    @g_fvex (.cv y) H
  have p0374 :=
    @g_breq2 (.cv w) (syn_cfv H (.cv y)) (.cv y) R
  have p0375 :=
    @g_ceqsexv (syn_wbr (.cv y) R (.cv w)) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) w (syn_cfv H (.cv y)) dv_cache_0013 dv_cache_0014 p0373 p0374
  have p0376 :=
    @g_a1i (syn_wb (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w)))) (syn_wbr (.cv y) R (syn_cfv H (.cv y)))) (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) p0375
  have p0377 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wex w (syn_wbr (.cv y) (syn_cin H R) (.cv w))) (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w)))) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) p0372 p0376
  have p0378 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (.classMem (.cv y) (syn_cdm (syn_cin H R))) (syn_wex w (syn_wbr (.cv y) (syn_cin H R) (.cv w))) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) p0360 p0377
  have p0379 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wb (.classMem (.cv y) (syn_cdm (syn_cin H R))) (syn_wbr (.cv y) R (syn_cfv H (.cv y)))) p0358 p0378
  have p0380 :=
    @g_biimprd (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (.cv y) (syn_cdm (syn_cin H R))) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) p0379
  have p0381 :=
    @g_mtod (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) (.classMem (.cv y) (syn_cdm (syn_cin H R))) p0347 p0380
  have p0382 :=
    @g_simp1 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0383 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0384 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))
  have p0385 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) p0383 p0384
  have p0386 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)
  have p0387 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wbr R (syn_cwe) D) p0385 p0386
  have p0388 :=
    (by simpa [syn_cwe] using (Nominal.classEqRefl (syn_cwe)))
  have p0389 :=
    @g_breqi R D (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0388
  have p0390 :=
    @g_brin R D (syn_cstrict) (syn_cfound)
  have p0391 :=
    @g_bitri (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_cin (syn_cstrict) (syn_cfound)) D) (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0389 p0390
  have p0392 :=
    @g_biimpi (syn_wbr R (syn_cwe) D) (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0391
  have p0393 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cwe) D) (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0387 p0392
  have p0394 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D) p0393
  have p0395 :=
    @g_sopc D R
  have p0396 :=
    @g_sylib (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cstrict) D) (syn_wa (syn_wbr R (syn_cpartial) D) (syn_wbr R (syn_cconnex) D)) p0394 p0395
  have p0397 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cpartial) D) (syn_wbr R (syn_cconnex) D) p0396
  have p0398 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cconnex) D) p0382 p0397
  have p0399 :=
    @g_simp2 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0400 :=
    @g_eldifi (.cv y) D (syn_cdm (syn_cin H R))
  have p0401 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (.classMem (.cv y) D) p0399 p0400
  have p0402 :=
    @g_simp1 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0403 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0404 :=
    @g_isof1o D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) H
  have p0405 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0403 p0404
  have p0406 :=
    @g_f1of D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) H
  have p0407 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0405 p0406
  have p0408 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0402 p0407
  have p0409 :=
    @g_simp2 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0410 :=
    @g_eldifi (.cv y) D (syn_cdm (syn_cin H R))
  have p0411 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (.classMem (.cv y) D) p0409 p0410
  have p0412 :=
    @g_jca (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv y) D) p0408 p0411
  have p0413 :=
    @g_ffvelrn D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (.cv y) H
  have p0414 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv y) D)) (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0412 p0413
  have p0415 :=
    @g_elin (syn_cfv H (.cv y)) D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0416 :=
    @g_eliniseg (syn_cdif R (syn_cid)) (.cv x) (syn_cfv H (.cv y))
  have p0417 :=
    @g_brdif (syn_cfv H (.cv y)) (.cv x) R (syn_cid)
  have p0418 :=
    @g_vex x
  have p0419 :=
    @g_ideq (syn_cfv H (.cv y)) (.cv x) p0418
  have p0420 :=
    @g_notbii (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x)) (.classEq (syn_cfv H (.cv y)) (.cv x)) p0419
  have p0421 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (syn_cfv H (.cv y)) (.cv x))))
  have p0422 :=
    @g_bitr4i (.neg (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x))) (.neg (.classEq (syn_cfv H (.cv y)) (.cv x))) (syn_wne (syn_cfv H (.cv y)) (.cv x)) p0420 p0421
  have p0423 :=
    @g_anbi2i (.neg (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x))) (syn_wne (syn_cfv H (.cv y)) (.cv x)) (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) p0422
  have p0424 :=
    @g_bitri (syn_wbr (syn_cfv H (.cv y)) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (.neg (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x)))) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) p0417 p0423
  have p0425 :=
    @g_bitri (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wbr (syn_cfv H (.cv y)) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) p0416 p0424
  have p0426 :=
    @g_anbi2i (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) (.classMem (syn_cfv H (.cv y)) D) p0425
  have p0427 :=
    @g_bitri (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x)))) p0415 p0426
  have p0428 :=
    @g_biimpi (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x)))) p0427
  have p0429 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x)))) p0414 p0428
  have p0430 :=
    @g_simpld (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) p0429
  have p0431 :=
    @g_connexd (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) D R (.cv y) (syn_cfv H (.cv y)) p0398 p0401 p0430
  have p0432 :=
    @g_ord (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) (syn_wbr (syn_cfv H (.cv y)) R (.cv y)) p0431
  have p0433 :=
    @g_mpd (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.neg (syn_wbr (.cv y) R (syn_cfv H (.cv y)))) (syn_wbr (syn_cfv H (.cv y)) R (.cv y)) p0381 p0432
  have p0434 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) (syn_cdif D (syn_cdm (syn_cin H R))))) (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wbr (syn_cfv H (.cv y)) R (.cv y)) p0344 p0433
  have p0435 :=
    @g_simpl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) (syn_cdif D (syn_cdm (syn_cin H R))))
  have p0436 :=
    @g_simp3 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0437 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) (syn_cdif D (syn_cdm (syn_cin H R))))) (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y)))) p0435 p0436
  have p0438 :=
    @g_simpr (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) (syn_cdif D (syn_cdm (syn_cin H R))))
  have p0439 :=
    @g_jca (syn_wa (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) (syn_cdif D (syn_cdm (syn_cin H R))))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y)))) (.classMem (syn_cfv H (.cv y)) (syn_cdif D (syn_cdm (syn_cin H R)))) p0437 p0438
  have p0440 :=
    @g_breq1 (.cv z) (syn_cfv H (.cv y)) (.cv y) R
  have p0441 :=
    @g_eqeq1 (.cv z) (syn_cfv H (.cv y)) (.cv y)
  have p0442 :=
    @g_imbi12d (.classEq (.cv z) (syn_cfv H (.cv y))) (syn_wbr (.cv z) R (.cv y)) (syn_wbr (syn_cfv H (.cv y)) R (.cv y)) (.classEq (.cv z) (.cv y)) (.classEq (syn_cfv H (.cv y)) (.cv y)) p0440 p0441
  have p0443 :=
    @g_rspccva (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))) (.imp (syn_wbr (syn_cfv H (.cv y)) R (.cv y)) (.classEq (syn_cfv H (.cv y)) (.cv y))) z (syn_cfv H (.cv y)) (syn_cdif D (syn_cdm (syn_cin H R))) dv_cache_0015 dv_cache_0009 dv_cache_0016 p0442
  have p0444 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) (syn_cdif D (syn_cdm (syn_cin H R))))) (syn_wa (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y)))) (.classMem (syn_cfv H (.cv y)) (syn_cdif D (syn_cdm (syn_cin H R))))) (.imp (syn_wbr (syn_cfv H (.cv y)) R (.cv y)) (.classEq (syn_cfv H (.cv y)) (.cv y))) p0439 p0443
  have p0445 :=
    @g_mpd (syn_wa (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) (syn_cdif D (syn_cdm (syn_cin H R))))) (syn_wbr (syn_cfv H (.cv y)) R (.cv y)) (.classEq (syn_cfv H (.cv y)) (.cv y)) p0434 p0444
  have p0446 :=
    @g_simpl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) (syn_cdif D (syn_cdm (syn_cin H R))))
  have p0447 :=
    @g_simpr (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classEq (syn_cfv H (.cv y)) (.cv y))
  have p0448 :=
    @g_simpl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classEq (syn_cfv H (.cv y)) (.cv y))
  have p0449 :=
    @g_simp2 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0450 :=
    @g_eldifn (.cv y) D (syn_cdm (syn_cin H R))
  have p0451 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (.neg (.classMem (.cv y) (syn_cdm (syn_cin H R)))) p0449 p0450
  have p0452 :=
    @g_simp1 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0453 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0454 :=
    @g_isof1o D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) H
  have p0455 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0453 p0454
  have p0456 :=
    @g_f1ofn D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) H
  have p0457 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wfn H D) p0455 p0456
  have p0458 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wfn H D) p0452 p0457
  have p0459 :=
    @g_simp2 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0460 :=
    @g_eldifi (.cv y) D (syn_cdm (syn_cin H R))
  have p0461 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (.classMem (.cv y) D) p0459 p0460
  have p0462 :=
    @g_jca (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wfn H D) (.classMem (.cv y) D) p0458 p0461
  have p0463 :=
    @g_eldm w (.cv y) (syn_cin H R) dv_cache_0011 dv_cache_0002
  have p0464 :=
    @g_a1i (syn_wb (.classMem (.cv y) (syn_cdm (syn_cin H R))) (syn_wex w (syn_wbr (.cv y) (syn_cin H R) (.cv w)))) (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) p0463
  have p0465 :=
    @g_brin (.cv y) (.cv w) H R
  have p0466 :=
    @g_a1i (syn_wb (syn_wbr (.cv y) (syn_cin H R) (.cv w)) (syn_wa (syn_wbr (.cv y) H (.cv w)) (syn_wbr (.cv y) R (.cv w)))) (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) p0465
  have p0467 :=
    @g_fnbrfvb D (.cv y) (.cv w) H
  have p0468 :=
    @g_bicomd (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) H (.cv w)) p0467
  have p0469 :=
    @g_anbi1d (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wbr (.cv y) H (.cv w)) (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w)) p0468
  have p0470 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wbr (.cv y) (syn_cin H R) (.cv w)) (syn_wa (syn_wbr (.cv y) H (.cv w)) (syn_wbr (.cv y) R (.cv w))) (syn_wa (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w))) p0466 p0469
  have p0471 :=
    @g_exbidv (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wbr (.cv y) (syn_cin H R) (.cv w)) (syn_wa (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w))) w dv_cache_0012 p0470
  have p0472 :=
    @g_eqcom (syn_cfv H (.cv y)) (.cv w)
  have p0473 :=
    @g_anbi1i (.classEq (syn_cfv H (.cv y)) (.cv w)) (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w)) p0472
  have p0474 :=
    @g_exbii (syn_wa (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w))) (syn_wa (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w))) w p0473
  have p0475 :=
    @g_a1i (syn_wb (syn_wex w (syn_wa (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w)))) (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w))))) (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) p0474
  have p0476 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wex w (syn_wbr (.cv y) (syn_cin H R) (.cv w))) (syn_wex w (syn_wa (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w)))) (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w)))) p0471 p0475
  have p0477 :=
    @g_fvex (.cv y) H
  have p0478 :=
    @g_breq2 (.cv w) (syn_cfv H (.cv y)) (.cv y) R
  have p0479 :=
    @g_ceqsexv (syn_wbr (.cv y) R (.cv w)) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) w (syn_cfv H (.cv y)) dv_cache_0013 dv_cache_0014 p0477 p0478
  have p0480 :=
    @g_a1i (syn_wb (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w)))) (syn_wbr (.cv y) R (syn_cfv H (.cv y)))) (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) p0479
  have p0481 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wex w (syn_wbr (.cv y) (syn_cin H R) (.cv w))) (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w)))) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) p0476 p0480
  have p0482 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (.classMem (.cv y) (syn_cdm (syn_cin H R))) (syn_wex w (syn_wbr (.cv y) (syn_cin H R) (.cv w))) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) p0464 p0481
  have p0483 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wb (.classMem (.cv y) (syn_cdm (syn_cin H R))) (syn_wbr (.cv y) R (syn_cfv H (.cv y)))) p0462 p0482
  have p0484 :=
    @g_biimprd (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (.cv y) (syn_cdm (syn_cin H R))) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) p0483
  have p0485 :=
    @g_mtod (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) (.classMem (.cv y) (syn_cdm (syn_cin H R))) p0451 p0484
  have p0486 :=
    @g_simp1 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0487 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0488 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))
  have p0489 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) p0487 p0488
  have p0490 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)
  have p0491 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wbr R (syn_cwe) D) p0489 p0490
  have p0492 :=
    (by simpa [syn_cwe] using (Nominal.classEqRefl (syn_cwe)))
  have p0493 :=
    @g_breqi R D (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0492
  have p0494 :=
    @g_brin R D (syn_cstrict) (syn_cfound)
  have p0495 :=
    @g_bitri (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_cin (syn_cstrict) (syn_cfound)) D) (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0493 p0494
  have p0496 :=
    @g_biimpi (syn_wbr R (syn_cwe) D) (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0495
  have p0497 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cwe) D) (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0491 p0496
  have p0498 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D) p0497
  have p0499 :=
    @g_sopc D R
  have p0500 :=
    @g_sylib (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cstrict) D) (syn_wa (syn_wbr R (syn_cpartial) D) (syn_wbr R (syn_cconnex) D)) p0498 p0499
  have p0501 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cpartial) D) (syn_wbr R (syn_cconnex) D) p0500
  have p0502 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cconnex) D) p0486 p0501
  have p0503 :=
    @g_simp2 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0504 :=
    @g_eldifi (.cv y) D (syn_cdm (syn_cin H R))
  have p0505 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (.classMem (.cv y) D) p0503 p0504
  have p0506 :=
    @g_simp1 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0507 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0508 :=
    @g_isof1o D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) H
  have p0509 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0507 p0508
  have p0510 :=
    @g_f1of D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) H
  have p0511 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0509 p0510
  have p0512 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0506 p0511
  have p0513 :=
    @g_simp2 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0514 :=
    @g_eldifi (.cv y) D (syn_cdm (syn_cin H R))
  have p0515 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (.classMem (.cv y) D) p0513 p0514
  have p0516 :=
    @g_jca (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv y) D) p0512 p0515
  have p0517 :=
    @g_ffvelrn D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (.cv y) H
  have p0518 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv y) D)) (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0516 p0517
  have p0519 :=
    @g_elin (syn_cfv H (.cv y)) D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0520 :=
    @g_eliniseg (syn_cdif R (syn_cid)) (.cv x) (syn_cfv H (.cv y))
  have p0521 :=
    @g_brdif (syn_cfv H (.cv y)) (.cv x) R (syn_cid)
  have p0522 :=
    @g_vex x
  have p0523 :=
    @g_ideq (syn_cfv H (.cv y)) (.cv x) p0522
  have p0524 :=
    @g_notbii (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x)) (.classEq (syn_cfv H (.cv y)) (.cv x)) p0523
  have p0525 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (syn_cfv H (.cv y)) (.cv x))))
  have p0526 :=
    @g_bitr4i (.neg (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x))) (.neg (.classEq (syn_cfv H (.cv y)) (.cv x))) (syn_wne (syn_cfv H (.cv y)) (.cv x)) p0524 p0525
  have p0527 :=
    @g_anbi2i (.neg (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x))) (syn_wne (syn_cfv H (.cv y)) (.cv x)) (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) p0526
  have p0528 :=
    @g_bitri (syn_wbr (syn_cfv H (.cv y)) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (.neg (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x)))) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) p0521 p0527
  have p0529 :=
    @g_bitri (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wbr (syn_cfv H (.cv y)) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) p0520 p0528
  have p0530 :=
    @g_anbi2i (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) (.classMem (syn_cfv H (.cv y)) D) p0529
  have p0531 :=
    @g_bitri (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x)))) p0519 p0530
  have p0532 :=
    @g_biimpi (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x)))) p0531
  have p0533 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x)))) p0518 p0532
  have p0534 :=
    @g_simpld (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) p0533
  have p0535 :=
    @g_connexd (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) D R (.cv y) (syn_cfv H (.cv y)) p0502 p0505 p0534
  have p0536 :=
    @g_ord (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) (syn_wbr (syn_cfv H (.cv y)) R (.cv y)) p0535
  have p0537 :=
    @g_mpd (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.neg (syn_wbr (.cv y) R (syn_cfv H (.cv y)))) (syn_wbr (syn_cfv H (.cv y)) R (.cv y)) p0485 p0536
  have p0538 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classEq (syn_cfv H (.cv y)) (.cv y))) (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wbr (syn_cfv H (.cv y)) R (.cv y)) p0448 p0537
  have p0539 :=
    @g_eqbrtrrd (syn_wa (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classEq (syn_cfv H (.cv y)) (.cv y))) (syn_cfv H (.cv y)) (.cv y) (.cv y) R p0447 p0538
  have p0540 :=
    @g_simpr (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classEq (syn_cfv H (.cv y)) (.cv y))
  have p0541 :=
    @g_breqtrrd (syn_wa (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classEq (syn_cfv H (.cv y)) (.cv y))) (.cv y) (.cv y) (syn_cfv H (.cv y)) R p0539 p0540
  have p0542 :=
    @g_simpl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classEq (syn_cfv H (.cv y)) (.cv y))
  have p0543 :=
    @g_simp2 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0544 :=
    @g_eldifn (.cv y) D (syn_cdm (syn_cin H R))
  have p0545 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (.neg (.classMem (.cv y) (syn_cdm (syn_cin H R)))) p0543 p0544
  have p0546 :=
    @g_simp1 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0547 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0548 :=
    @g_isof1o D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) H
  have p0549 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0547 p0548
  have p0550 :=
    @g_f1ofn D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) H
  have p0551 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wfn H D) p0549 p0550
  have p0552 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wfn H D) p0546 p0551
  have p0553 :=
    @g_simp2 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0554 :=
    @g_eldifi (.cv y) D (syn_cdm (syn_cin H R))
  have p0555 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (.classMem (.cv y) D) p0553 p0554
  have p0556 :=
    @g_jca (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wfn H D) (.classMem (.cv y) D) p0552 p0555
  have p0557 :=
    @g_eldm w (.cv y) (syn_cin H R) dv_cache_0011 dv_cache_0002
  have p0558 :=
    @g_a1i (syn_wb (.classMem (.cv y) (syn_cdm (syn_cin H R))) (syn_wex w (syn_wbr (.cv y) (syn_cin H R) (.cv w)))) (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) p0557
  have p0559 :=
    @g_brin (.cv y) (.cv w) H R
  have p0560 :=
    @g_a1i (syn_wb (syn_wbr (.cv y) (syn_cin H R) (.cv w)) (syn_wa (syn_wbr (.cv y) H (.cv w)) (syn_wbr (.cv y) R (.cv w)))) (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) p0559
  have p0561 :=
    @g_fnbrfvb D (.cv y) (.cv w) H
  have p0562 :=
    @g_bicomd (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) H (.cv w)) p0561
  have p0563 :=
    @g_anbi1d (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wbr (.cv y) H (.cv w)) (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w)) p0562
  have p0564 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wbr (.cv y) (syn_cin H R) (.cv w)) (syn_wa (syn_wbr (.cv y) H (.cv w)) (syn_wbr (.cv y) R (.cv w))) (syn_wa (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w))) p0560 p0563
  have p0565 :=
    @g_exbidv (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wbr (.cv y) (syn_cin H R) (.cv w)) (syn_wa (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w))) w dv_cache_0012 p0564
  have p0566 :=
    @g_eqcom (syn_cfv H (.cv y)) (.cv w)
  have p0567 :=
    @g_anbi1i (.classEq (syn_cfv H (.cv y)) (.cv w)) (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w)) p0566
  have p0568 :=
    @g_exbii (syn_wa (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w))) (syn_wa (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w))) w p0567
  have p0569 :=
    @g_a1i (syn_wb (syn_wex w (syn_wa (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w)))) (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w))))) (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) p0568
  have p0570 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wex w (syn_wbr (.cv y) (syn_cin H R) (.cv w))) (syn_wex w (syn_wa (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w)))) (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w)))) p0565 p0569
  have p0571 :=
    @g_fvex (.cv y) H
  have p0572 :=
    @g_breq2 (.cv w) (syn_cfv H (.cv y)) (.cv y) R
  have p0573 :=
    @g_ceqsexv (syn_wbr (.cv y) R (.cv w)) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) w (syn_cfv H (.cv y)) dv_cache_0013 dv_cache_0014 p0571 p0572
  have p0574 :=
    @g_a1i (syn_wb (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w)))) (syn_wbr (.cv y) R (syn_cfv H (.cv y)))) (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) p0573
  have p0575 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wex w (syn_wbr (.cv y) (syn_cin H R) (.cv w))) (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w)))) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) p0570 p0574
  have p0576 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (.classMem (.cv y) (syn_cdm (syn_cin H R))) (syn_wex w (syn_wbr (.cv y) (syn_cin H R) (.cv w))) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) p0558 p0575
  have p0577 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wb (.classMem (.cv y) (syn_cdm (syn_cin H R))) (syn_wbr (.cv y) R (syn_cfv H (.cv y)))) p0556 p0576
  have p0578 :=
    @g_biimprd (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (.cv y) (syn_cdm (syn_cin H R))) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) p0577
  have p0579 :=
    @g_mtod (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) (.classMem (.cv y) (syn_cdm (syn_cin H R))) p0545 p0578
  have p0580 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classEq (syn_cfv H (.cv y)) (.cv y))) (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.neg (syn_wbr (.cv y) R (syn_cfv H (.cv y)))) p0542 p0579
  have p0581 :=
    @g_pm2_21dd (syn_wa (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classEq (syn_cfv H (.cv y)) (.cv y))) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) (.neg (.classEq (syn_cfv H (.cv y)) (.cv y))) p0541 p0580
  have p0582 :=
    @g_pm2_01da (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classEq (syn_cfv H (.cv y)) (.cv y)) p0581
  have p0583 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (syn_cfv H (.cv y)) (.cv y))))
  have p0584 :=
    @g_biimpri (syn_wne (syn_cfv H (.cv y)) (.cv y)) (.neg (.classEq (syn_cfv H (.cv y)) (.cv y))) p0583
  have p0585 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.neg (.classEq (syn_cfv H (.cv y)) (.cv y))) (syn_wne (syn_cfv H (.cv y)) (.cv y)) p0582 p0584
  have p0586 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) (syn_cdif D (syn_cdm (syn_cin H R))))) (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wne (syn_cfv H (.cv y)) (.cv y)) p0446 p0585
  have p0587 :=
    @g_pm2_21ddne (syn_wa (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) (syn_cdif D (syn_cdm (syn_cin H R))))) (.neg (.classMem (syn_cfv H (.cv y)) (syn_cdif D (syn_cdm (syn_cin H R))))) (syn_cfv H (.cv y)) (.cv y) p0445 p0586
  have p0588 :=
    @g_pm2_01da (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) (syn_cdif D (syn_cdm (syn_cin H R)))) p0587
  have p0589 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.neg (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R))))) (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.neg (.classMem (syn_cfv H (.cv y)) (syn_cdif D (syn_cdm (syn_cin H R))))) p0343 p0588
  have p0590 :=
    @g_pm2_21dd (syn_wa (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.neg (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R))))) (.classMem (syn_cfv H (.cv y)) (syn_cdif D (syn_cdm (syn_cin H R)))) (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R))) p0342 p0589
  have p0591 :=
    @g_ex (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.neg (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R)))) (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R))) p0590
  have p0592 :=
    @g_pm2_61d (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R))) (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R))) p0306 p0591
  have p0593 :=
    @g_simp1 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0594 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0595 :=
    @g_isof1o D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) H
  have p0596 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0594 p0595
  have p0597 :=
    @g_f1ofn D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) H
  have p0598 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wfn H D) p0596 p0597
  have p0599 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wfn H D) p0593 p0598
  have p0600 :=
    @g_simp1 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0601 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0602 :=
    @g_isof1o D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) H
  have p0603 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0601 p0602
  have p0604 :=
    @g_f1of D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) H
  have p0605 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0603 p0604
  have p0606 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0600 p0605
  have p0607 :=
    @g_simp2 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0608 :=
    @g_eldifi (.cv y) D (syn_cdm (syn_cin H R))
  have p0609 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (.classMem (.cv y) D) p0607 p0608
  have p0610 :=
    @g_jca (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv y) D) p0606 p0609
  have p0611 :=
    @g_ffvelrn D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (.cv y) H
  have p0612 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv y) D)) (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0610 p0611
  have p0613 :=
    @g_elin (syn_cfv H (.cv y)) D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0614 :=
    @g_eliniseg (syn_cdif R (syn_cid)) (.cv x) (syn_cfv H (.cv y))
  have p0615 :=
    @g_brdif (syn_cfv H (.cv y)) (.cv x) R (syn_cid)
  have p0616 :=
    @g_vex x
  have p0617 :=
    @g_ideq (syn_cfv H (.cv y)) (.cv x) p0616
  have p0618 :=
    @g_notbii (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x)) (.classEq (syn_cfv H (.cv y)) (.cv x)) p0617
  have p0619 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (syn_cfv H (.cv y)) (.cv x))))
  have p0620 :=
    @g_bitr4i (.neg (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x))) (.neg (.classEq (syn_cfv H (.cv y)) (.cv x))) (syn_wne (syn_cfv H (.cv y)) (.cv x)) p0618 p0619
  have p0621 :=
    @g_anbi2i (.neg (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x))) (syn_wne (syn_cfv H (.cv y)) (.cv x)) (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) p0620
  have p0622 :=
    @g_bitri (syn_wbr (syn_cfv H (.cv y)) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (.neg (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x)))) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) p0615 p0621
  have p0623 :=
    @g_bitri (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wbr (syn_cfv H (.cv y)) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) p0614 p0622
  have p0624 :=
    @g_anbi2i (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) (.classMem (syn_cfv H (.cv y)) D) p0623
  have p0625 :=
    @g_bitri (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x)))) p0613 p0624
  have p0626 :=
    @g_biimpi (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x)))) p0625
  have p0627 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x)))) p0612 p0626
  have p0628 :=
    @g_simpld (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) p0627
  have p0629 :=
    @g_jca (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wfn H D) (.classMem (syn_cfv H (.cv y)) D) p0599 p0628
  have p0630 :=
    @g_eldm w (syn_cfv H (.cv y)) (syn_cin H R) dv_cache_0013 dv_cache_0002
  have p0631 :=
    @g_a1i (syn_wb (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R))) (syn_wex w (syn_wbr (syn_cfv H (.cv y)) (syn_cin H R) (.cv w)))) (syn_wa (syn_wfn H D) (.classMem (syn_cfv H (.cv y)) D)) p0630
  have p0632 :=
    @g_brin (syn_cfv H (.cv y)) (.cv w) H R
  have p0633 :=
    @g_a1i (syn_wb (syn_wbr (syn_cfv H (.cv y)) (syn_cin H R) (.cv w)) (syn_wa (syn_wbr (syn_cfv H (.cv y)) H (.cv w)) (syn_wbr (syn_cfv H (.cv y)) R (.cv w)))) (syn_wa (syn_wfn H D) (.classMem (syn_cfv H (.cv y)) D)) p0632
  have p0634 :=
    @g_fnbrfvb D (syn_cfv H (.cv y)) (.cv w) H
  have p0635 :=
    @g_bicomd (syn_wa (syn_wfn H D) (.classMem (syn_cfv H (.cv y)) D)) (.classEq (syn_cfv H (syn_cfv H (.cv y))) (.cv w)) (syn_wbr (syn_cfv H (.cv y)) H (.cv w)) p0634
  have p0636 :=
    @g_anbi1d (syn_wa (syn_wfn H D) (.classMem (syn_cfv H (.cv y)) D)) (syn_wbr (syn_cfv H (.cv y)) H (.cv w)) (.classEq (syn_cfv H (syn_cfv H (.cv y))) (.cv w)) (syn_wbr (syn_cfv H (.cv y)) R (.cv w)) p0635
  have p0637 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (syn_cfv H (.cv y)) D)) (syn_wbr (syn_cfv H (.cv y)) (syn_cin H R) (.cv w)) (syn_wa (syn_wbr (syn_cfv H (.cv y)) H (.cv w)) (syn_wbr (syn_cfv H (.cv y)) R (.cv w))) (syn_wa (.classEq (syn_cfv H (syn_cfv H (.cv y))) (.cv w)) (syn_wbr (syn_cfv H (.cv y)) R (.cv w))) p0633 p0636
  have p0638 :=
    @g_exbidv (syn_wa (syn_wfn H D) (.classMem (syn_cfv H (.cv y)) D)) (syn_wbr (syn_cfv H (.cv y)) (syn_cin H R) (.cv w)) (syn_wa (.classEq (syn_cfv H (syn_cfv H (.cv y))) (.cv w)) (syn_wbr (syn_cfv H (.cv y)) R (.cv w))) w dv_cache_0017 p0637
  have p0639 :=
    @g_eqcom (syn_cfv H (syn_cfv H (.cv y))) (.cv w)
  have p0640 :=
    @g_anbi1i (.classEq (syn_cfv H (syn_cfv H (.cv y))) (.cv w)) (.classEq (.cv w) (syn_cfv H (syn_cfv H (.cv y)))) (syn_wbr (syn_cfv H (.cv y)) R (.cv w)) p0639
  have p0641 :=
    @g_exbii (syn_wa (.classEq (syn_cfv H (syn_cfv H (.cv y))) (.cv w)) (syn_wbr (syn_cfv H (.cv y)) R (.cv w))) (syn_wa (.classEq (.cv w) (syn_cfv H (syn_cfv H (.cv y)))) (syn_wbr (syn_cfv H (.cv y)) R (.cv w))) w p0640
  have p0642 :=
    @g_a1i (syn_wb (syn_wex w (syn_wa (.classEq (syn_cfv H (syn_cfv H (.cv y))) (.cv w)) (syn_wbr (syn_cfv H (.cv y)) R (.cv w)))) (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv H (syn_cfv H (.cv y)))) (syn_wbr (syn_cfv H (.cv y)) R (.cv w))))) (syn_wa (syn_wfn H D) (.classMem (syn_cfv H (.cv y)) D)) p0641
  have p0643 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (syn_cfv H (.cv y)) D)) (syn_wex w (syn_wbr (syn_cfv H (.cv y)) (syn_cin H R) (.cv w))) (syn_wex w (syn_wa (.classEq (syn_cfv H (syn_cfv H (.cv y))) (.cv w)) (syn_wbr (syn_cfv H (.cv y)) R (.cv w)))) (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv H (syn_cfv H (.cv y)))) (syn_wbr (syn_cfv H (.cv y)) R (.cv w)))) p0638 p0642
  have p0644 :=
    @g_fvex (syn_cfv H (.cv y)) H
  have p0645 :=
    @g_breq2 (.cv w) (syn_cfv H (syn_cfv H (.cv y))) (syn_cfv H (.cv y)) R
  have p0646 :=
    @g_ceqsexv (syn_wbr (syn_cfv H (.cv y)) R (.cv w)) (syn_wbr (syn_cfv H (.cv y)) R (syn_cfv H (syn_cfv H (.cv y)))) w (syn_cfv H (syn_cfv H (.cv y))) dv_cache_0018 dv_cache_0019 p0644 p0645
  have p0647 :=
    @g_a1i (syn_wb (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv H (syn_cfv H (.cv y)))) (syn_wbr (syn_cfv H (.cv y)) R (.cv w)))) (syn_wbr (syn_cfv H (.cv y)) R (syn_cfv H (syn_cfv H (.cv y))))) (syn_wa (syn_wfn H D) (.classMem (syn_cfv H (.cv y)) D)) p0646
  have p0648 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (syn_cfv H (.cv y)) D)) (syn_wex w (syn_wbr (syn_cfv H (.cv y)) (syn_cin H R) (.cv w))) (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv H (syn_cfv H (.cv y)))) (syn_wbr (syn_cfv H (.cv y)) R (.cv w)))) (syn_wbr (syn_cfv H (.cv y)) R (syn_cfv H (syn_cfv H (.cv y)))) p0643 p0647
  have p0649 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (syn_cfv H (.cv y)) D)) (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R))) (syn_wex w (syn_wbr (syn_cfv H (.cv y)) (syn_cin H R) (.cv w))) (syn_wbr (syn_cfv H (.cv y)) R (syn_cfv H (syn_cfv H (.cv y)))) p0631 p0648
  have p0650 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wfn H D) (.classMem (syn_cfv H (.cv y)) D)) (syn_wb (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R))) (syn_wbr (syn_cfv H (.cv y)) R (syn_cfv H (syn_cfv H (.cv y))))) p0629 p0649
  have p0651 :=
    @g_biimpd (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R))) (syn_wbr (syn_cfv H (.cv y)) R (syn_cfv H (syn_cfv H (.cv y)))) p0650
  have p0652 :=
    @g_mpd (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R))) (syn_wbr (syn_cfv H (.cv y)) R (syn_cfv H (syn_cfv H (.cv y)))) p0592 p0651
  have p0653 :=
    @g_simp2 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0654 :=
    @g_eldifn (.cv y) D (syn_cdm (syn_cin H R))
  have p0655 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (.neg (.classMem (.cv y) (syn_cdm (syn_cin H R)))) p0653 p0654
  have p0656 :=
    @g_simp1 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0657 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0658 :=
    @g_isof1o D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) H
  have p0659 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0657 p0658
  have p0660 :=
    @g_f1ofn D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) H
  have p0661 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wfn H D) p0659 p0660
  have p0662 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wfn H D) p0656 p0661
  have p0663 :=
    @g_simp2 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0664 :=
    @g_eldifi (.cv y) D (syn_cdm (syn_cin H R))
  have p0665 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (.classMem (.cv y) D) p0663 p0664
  have p0666 :=
    @g_jca (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wfn H D) (.classMem (.cv y) D) p0662 p0665
  have p0667 :=
    @g_eldm w (.cv y) (syn_cin H R) dv_cache_0011 dv_cache_0002
  have p0668 :=
    @g_a1i (syn_wb (.classMem (.cv y) (syn_cdm (syn_cin H R))) (syn_wex w (syn_wbr (.cv y) (syn_cin H R) (.cv w)))) (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) p0667
  have p0669 :=
    @g_brin (.cv y) (.cv w) H R
  have p0670 :=
    @g_a1i (syn_wb (syn_wbr (.cv y) (syn_cin H R) (.cv w)) (syn_wa (syn_wbr (.cv y) H (.cv w)) (syn_wbr (.cv y) R (.cv w)))) (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) p0669
  have p0671 :=
    @g_fnbrfvb D (.cv y) (.cv w) H
  have p0672 :=
    @g_bicomd (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) H (.cv w)) p0671
  have p0673 :=
    @g_anbi1d (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wbr (.cv y) H (.cv w)) (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w)) p0672
  have p0674 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wbr (.cv y) (syn_cin H R) (.cv w)) (syn_wa (syn_wbr (.cv y) H (.cv w)) (syn_wbr (.cv y) R (.cv w))) (syn_wa (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w))) p0670 p0673
  have p0675 :=
    @g_exbidv (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wbr (.cv y) (syn_cin H R) (.cv w)) (syn_wa (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w))) w dv_cache_0012 p0674
  have p0676 :=
    @g_eqcom (syn_cfv H (.cv y)) (.cv w)
  have p0677 :=
    @g_anbi1i (.classEq (syn_cfv H (.cv y)) (.cv w)) (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w)) p0676
  have p0678 :=
    @g_exbii (syn_wa (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w))) (syn_wa (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w))) w p0677
  have p0679 :=
    @g_a1i (syn_wb (syn_wex w (syn_wa (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w)))) (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w))))) (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) p0678
  have p0680 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wex w (syn_wbr (.cv y) (syn_cin H R) (.cv w))) (syn_wex w (syn_wa (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w)))) (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w)))) p0675 p0679
  have p0681 :=
    @g_fvex (.cv y) H
  have p0682 :=
    @g_breq2 (.cv w) (syn_cfv H (.cv y)) (.cv y) R
  have p0683 :=
    @g_ceqsexv (syn_wbr (.cv y) R (.cv w)) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) w (syn_cfv H (.cv y)) dv_cache_0013 dv_cache_0014 p0681 p0682
  have p0684 :=
    @g_a1i (syn_wb (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w)))) (syn_wbr (.cv y) R (syn_cfv H (.cv y)))) (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) p0683
  have p0685 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wex w (syn_wbr (.cv y) (syn_cin H R) (.cv w))) (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w)))) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) p0680 p0684
  have p0686 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (.classMem (.cv y) (syn_cdm (syn_cin H R))) (syn_wex w (syn_wbr (.cv y) (syn_cin H R) (.cv w))) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) p0668 p0685
  have p0687 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wb (.classMem (.cv y) (syn_cdm (syn_cin H R))) (syn_wbr (.cv y) R (syn_cfv H (.cv y)))) p0666 p0686
  have p0688 :=
    @g_biimprd (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (.cv y) (syn_cdm (syn_cin H R))) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) p0687
  have p0689 :=
    @g_mtod (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) (.classMem (.cv y) (syn_cdm (syn_cin H R))) p0655 p0688
  have p0690 :=
    @g_simp1 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0691 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0692 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))
  have p0693 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) p0691 p0692
  have p0694 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)
  have p0695 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wbr R (syn_cwe) D) p0693 p0694
  have p0696 :=
    (by simpa [syn_cwe] using (Nominal.classEqRefl (syn_cwe)))
  have p0697 :=
    @g_breqi R D (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0696
  have p0698 :=
    @g_brin R D (syn_cstrict) (syn_cfound)
  have p0699 :=
    @g_bitri (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_cin (syn_cstrict) (syn_cfound)) D) (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0697 p0698
  have p0700 :=
    @g_biimpi (syn_wbr R (syn_cwe) D) (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0699
  have p0701 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cwe) D) (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0695 p0700
  have p0702 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D) p0701
  have p0703 :=
    @g_sopc D R
  have p0704 :=
    @g_sylib (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cstrict) D) (syn_wa (syn_wbr R (syn_cpartial) D) (syn_wbr R (syn_cconnex) D)) p0702 p0703
  have p0705 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cpartial) D) (syn_wbr R (syn_cconnex) D) p0704
  have p0706 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cconnex) D) p0690 p0705
  have p0707 :=
    @g_simp2 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0708 :=
    @g_eldifi (.cv y) D (syn_cdm (syn_cin H R))
  have p0709 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (.classMem (.cv y) D) p0707 p0708
  have p0710 :=
    @g_simp1 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0711 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0712 :=
    @g_isof1o D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) H
  have p0713 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0711 p0712
  have p0714 :=
    @g_f1of D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) H
  have p0715 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0713 p0714
  have p0716 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0710 p0715
  have p0717 :=
    @g_simp2 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0718 :=
    @g_eldifi (.cv y) D (syn_cdm (syn_cin H R))
  have p0719 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (.classMem (.cv y) D) p0717 p0718
  have p0720 :=
    @g_jca (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv y) D) p0716 p0719
  have p0721 :=
    @g_ffvelrn D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (.cv y) H
  have p0722 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv y) D)) (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0720 p0721
  have p0723 :=
    @g_elin (syn_cfv H (.cv y)) D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0724 :=
    @g_eliniseg (syn_cdif R (syn_cid)) (.cv x) (syn_cfv H (.cv y))
  have p0725 :=
    @g_brdif (syn_cfv H (.cv y)) (.cv x) R (syn_cid)
  have p0726 :=
    @g_vex x
  have p0727 :=
    @g_ideq (syn_cfv H (.cv y)) (.cv x) p0726
  have p0728 :=
    @g_notbii (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x)) (.classEq (syn_cfv H (.cv y)) (.cv x)) p0727
  have p0729 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (syn_cfv H (.cv y)) (.cv x))))
  have p0730 :=
    @g_bitr4i (.neg (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x))) (.neg (.classEq (syn_cfv H (.cv y)) (.cv x))) (syn_wne (syn_cfv H (.cv y)) (.cv x)) p0728 p0729
  have p0731 :=
    @g_anbi2i (.neg (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x))) (syn_wne (syn_cfv H (.cv y)) (.cv x)) (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) p0730
  have p0732 :=
    @g_bitri (syn_wbr (syn_cfv H (.cv y)) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (.neg (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x)))) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) p0725 p0731
  have p0733 :=
    @g_bitri (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wbr (syn_cfv H (.cv y)) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) p0724 p0732
  have p0734 :=
    @g_anbi2i (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) (.classMem (syn_cfv H (.cv y)) D) p0733
  have p0735 :=
    @g_bitri (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x)))) p0723 p0734
  have p0736 :=
    @g_biimpi (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x)))) p0735
  have p0737 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x)))) p0722 p0736
  have p0738 :=
    @g_simpld (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) p0737
  have p0739 :=
    @g_connexd (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) D R (.cv y) (syn_cfv H (.cv y)) p0706 p0709 p0738
  have p0740 :=
    @g_ord (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) (syn_wbr (syn_cfv H (.cv y)) R (.cv y)) p0739
  have p0741 :=
    @g_mpd (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.neg (syn_wbr (.cv y) R (syn_cfv H (.cv y)))) (syn_wbr (syn_cfv H (.cv y)) R (.cv y)) p0689 p0740
  have p0742 :=
    @g_simp1 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0743 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0744 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0742 p0743
  have p0745 :=
    @g_simp1 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0746 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0747 :=
    @g_isof1o D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) H
  have p0748 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0746 p0747
  have p0749 :=
    @g_f1of D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) H
  have p0750 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0748 p0749
  have p0751 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0745 p0750
  have p0752 :=
    @g_simp2 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0753 :=
    @g_eldifi (.cv y) D (syn_cdm (syn_cin H R))
  have p0754 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (.classMem (.cv y) D) p0752 p0753
  have p0755 :=
    @g_jca (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv y) D) p0751 p0754
  have p0756 :=
    @g_ffvelrn D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (.cv y) H
  have p0757 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv y) D)) (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0755 p0756
  have p0758 :=
    @g_elin (syn_cfv H (.cv y)) D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0759 :=
    @g_eliniseg (syn_cdif R (syn_cid)) (.cv x) (syn_cfv H (.cv y))
  have p0760 :=
    @g_brdif (syn_cfv H (.cv y)) (.cv x) R (syn_cid)
  have p0761 :=
    @g_vex x
  have p0762 :=
    @g_ideq (syn_cfv H (.cv y)) (.cv x) p0761
  have p0763 :=
    @g_notbii (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x)) (.classEq (syn_cfv H (.cv y)) (.cv x)) p0762
  have p0764 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (syn_cfv H (.cv y)) (.cv x))))
  have p0765 :=
    @g_bitr4i (.neg (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x))) (.neg (.classEq (syn_cfv H (.cv y)) (.cv x))) (syn_wne (syn_cfv H (.cv y)) (.cv x)) p0763 p0764
  have p0766 :=
    @g_anbi2i (.neg (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x))) (syn_wne (syn_cfv H (.cv y)) (.cv x)) (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) p0765
  have p0767 :=
    @g_bitri (syn_wbr (syn_cfv H (.cv y)) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (.neg (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x)))) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) p0760 p0766
  have p0768 :=
    @g_bitri (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wbr (syn_cfv H (.cv y)) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) p0759 p0767
  have p0769 :=
    @g_anbi2i (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) (.classMem (syn_cfv H (.cv y)) D) p0768
  have p0770 :=
    @g_bitri (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x)))) p0758 p0769
  have p0771 :=
    @g_biimpi (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x)))) p0770
  have p0772 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x)))) p0757 p0771
  have p0773 :=
    @g_simpld (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) p0772
  have p0774 :=
    @g_simp2 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0775 :=
    @g_eldifi (.cv y) D (syn_cdm (syn_cin H R))
  have p0776 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (.classMem (.cv y) D) p0774 p0775
  have p0777 :=
    @g_jca (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) D) (.classMem (.cv y) D) p0773 p0776
  have p0778 :=
    @g_jca (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (.classMem (.cv y) D)) p0744 p0777
  have p0779 :=
    @g_isorel D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cfv H (.cv y)) (.cv y) R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) H
  have p0780 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (.classMem (.cv y) D))) (syn_wb (syn_wbr (syn_cfv H (.cv y)) R (.cv y)) (syn_wbr (syn_cfv H (syn_cfv H (.cv y))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv H (.cv y)))) p0778 p0779
  have p0781 :=
    @g_simp1 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0782 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0783 :=
    @g_isof1o D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) H
  have p0784 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0782 p0783
  have p0785 :=
    @g_f1of D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) H
  have p0786 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0784 p0785
  have p0787 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0781 p0786
  have p0788 :=
    @g_simp1 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0789 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0790 :=
    @g_isof1o D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) H
  have p0791 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0789 p0790
  have p0792 :=
    @g_f1of D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) H
  have p0793 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0791 p0792
  have p0794 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0788 p0793
  have p0795 :=
    @g_simp2 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0796 :=
    @g_eldifi (.cv y) D (syn_cdm (syn_cin H R))
  have p0797 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (.classMem (.cv y) D) p0795 p0796
  have p0798 :=
    @g_jca (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv y) D) p0794 p0797
  have p0799 :=
    @g_ffvelrn D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (.cv y) H
  have p0800 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv y) D)) (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0798 p0799
  have p0801 :=
    @g_elin (syn_cfv H (.cv y)) D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0802 :=
    @g_eliniseg (syn_cdif R (syn_cid)) (.cv x) (syn_cfv H (.cv y))
  have p0803 :=
    @g_brdif (syn_cfv H (.cv y)) (.cv x) R (syn_cid)
  have p0804 :=
    @g_vex x
  have p0805 :=
    @g_ideq (syn_cfv H (.cv y)) (.cv x) p0804
  have p0806 :=
    @g_notbii (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x)) (.classEq (syn_cfv H (.cv y)) (.cv x)) p0805
  have p0807 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (syn_cfv H (.cv y)) (.cv x))))
  have p0808 :=
    @g_bitr4i (.neg (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x))) (.neg (.classEq (syn_cfv H (.cv y)) (.cv x))) (syn_wne (syn_cfv H (.cv y)) (.cv x)) p0806 p0807
  have p0809 :=
    @g_anbi2i (.neg (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x))) (syn_wne (syn_cfv H (.cv y)) (.cv x)) (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) p0808
  have p0810 :=
    @g_bitri (syn_wbr (syn_cfv H (.cv y)) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (.neg (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x)))) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) p0803 p0809
  have p0811 :=
    @g_bitri (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wbr (syn_cfv H (.cv y)) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) p0802 p0810
  have p0812 :=
    @g_anbi2i (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) (.classMem (syn_cfv H (.cv y)) D) p0811
  have p0813 :=
    @g_bitri (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x)))) p0801 p0812
  have p0814 :=
    @g_biimpi (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x)))) p0813
  have p0815 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x)))) p0800 p0814
  have p0816 :=
    @g_simpld (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) p0815
  have p0817 :=
    @g_jca (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (syn_cfv H (.cv y)) D) p0787 p0816
  have p0818 :=
    @g_ffvelrn D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cfv H (.cv y)) H
  have p0819 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (syn_cfv H (.cv y)) D)) (.classMem (syn_cfv H (syn_cfv H (.cv y))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0817 p0818
  have p0820 :=
    @g_simp1 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0821 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0822 :=
    @g_isof1o D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) H
  have p0823 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0821 p0822
  have p0824 :=
    @g_f1of D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) H
  have p0825 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0823 p0824
  have p0826 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0820 p0825
  have p0827 :=
    @g_simp2 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0828 :=
    @g_eldifi (.cv y) D (syn_cdm (syn_cin H R))
  have p0829 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (.classMem (.cv y) D) p0827 p0828
  have p0830 :=
    @g_jca (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv y) D) p0826 p0829
  have p0831 :=
    @g_ffvelrn D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (.cv y) H
  have p0832 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv y) D)) (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0830 p0831
  have p0833 :=
    @g_jca (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (syn_cfv H (.cv y))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0819 p0832
  have p0834 :=
    @g_brinxp (syn_cfv H (syn_cfv H (.cv y))) (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) R
  have p0835 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (.classMem (syn_cfv H (syn_cfv H (.cv y))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wb (syn_wbr (syn_cfv H (syn_cfv H (.cv y))) R (syn_cfv H (.cv y))) (syn_wbr (syn_cfv H (syn_cfv H (.cv y))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv H (.cv y)))) p0833 p0834
  have p0836 :=
    @g_bitr4d (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wbr (syn_cfv H (.cv y)) R (.cv y)) (syn_wbr (syn_cfv H (syn_cfv H (.cv y))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv H (.cv y))) (syn_wbr (syn_cfv H (syn_cfv H (.cv y))) R (syn_cfv H (.cv y))) p0780 p0835
  have p0837 :=
    @g_biimpd (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wbr (syn_cfv H (.cv y)) R (.cv y)) (syn_wbr (syn_cfv H (syn_cfv H (.cv y))) R (syn_cfv H (.cv y))) p0836
  have p0838 :=
    @g_mpd (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wbr (syn_cfv H (.cv y)) R (.cv y)) (syn_wbr (syn_cfv H (syn_cfv H (.cv y))) R (syn_cfv H (.cv y))) p0741 p0837
  have p0839 :=
    @g_antid (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) D R (syn_cfv H (.cv y)) (syn_cfv H (syn_cfv H (.cv y))) p0233 p0262 p0304 p0652 p0838
  have p0840 :=
    @g_eqcomd (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_cfv H (.cv y)) (syn_cfv H (syn_cfv H (.cv y))) p0839
  have p0841 :=
    @g_simp1 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0842 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0843 :=
    @g_isof1o D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) H
  have p0844 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0842 p0843
  have p0845 :=
    @g_f1of1 D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) H
  have p0846 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf1 H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0844 p0845
  have p0847 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf1 H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0841 p0846
  have p0848 :=
    @g_simp1 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0849 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0850 :=
    @g_isof1o D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) H
  have p0851 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0849 p0850
  have p0852 :=
    @g_f1of D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) H
  have p0853 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0851 p0852
  have p0854 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0848 p0853
  have p0855 :=
    @g_simp2 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0856 :=
    @g_eldifi (.cv y) D (syn_cdm (syn_cin H R))
  have p0857 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (.classMem (.cv y) D) p0855 p0856
  have p0858 :=
    @g_jca (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv y) D) p0854 p0857
  have p0859 :=
    @g_ffvelrn D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (.cv y) H
  have p0860 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv y) D)) (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0858 p0859
  have p0861 :=
    @g_elin (syn_cfv H (.cv y)) D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0862 :=
    @g_eliniseg (syn_cdif R (syn_cid)) (.cv x) (syn_cfv H (.cv y))
  have p0863 :=
    @g_brdif (syn_cfv H (.cv y)) (.cv x) R (syn_cid)
  have p0864 :=
    @g_vex x
  have p0865 :=
    @g_ideq (syn_cfv H (.cv y)) (.cv x) p0864
  have p0866 :=
    @g_notbii (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x)) (.classEq (syn_cfv H (.cv y)) (.cv x)) p0865
  have p0867 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (syn_cfv H (.cv y)) (.cv x))))
  have p0868 :=
    @g_bitr4i (.neg (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x))) (.neg (.classEq (syn_cfv H (.cv y)) (.cv x))) (syn_wne (syn_cfv H (.cv y)) (.cv x)) p0866 p0867
  have p0869 :=
    @g_anbi2i (.neg (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x))) (syn_wne (syn_cfv H (.cv y)) (.cv x)) (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) p0868
  have p0870 :=
    @g_bitri (syn_wbr (syn_cfv H (.cv y)) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (.neg (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x)))) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) p0863 p0869
  have p0871 :=
    @g_bitri (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wbr (syn_cfv H (.cv y)) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) p0862 p0870
  have p0872 :=
    @g_anbi2i (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) (.classMem (syn_cfv H (.cv y)) D) p0871
  have p0873 :=
    @g_bitri (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x)))) p0861 p0872
  have p0874 :=
    @g_biimpi (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x)))) p0873
  have p0875 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x)))) p0860 p0874
  have p0876 :=
    @g_simpld (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) p0875
  have p0877 :=
    @g_simp2 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0878 :=
    @g_eldifi (.cv y) D (syn_cdm (syn_cin H R))
  have p0879 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (.classMem (.cv y) D) p0877 p0878
  have p0880 :=
    @g_jca (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) D) (.classMem (.cv y) D) p0876 p0879
  have p0881 :=
    @g_jca (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wf1 H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (.classMem (.cv y) D)) p0847 p0880
  have p0882 :=
    @g_f1fveq D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cfv H (.cv y)) (.cv y) H
  have p0883 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wf1 H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (.classMem (.cv y) D))) (syn_wb (.classEq (syn_cfv H (syn_cfv H (.cv y))) (syn_cfv H (.cv y))) (.classEq (syn_cfv H (.cv y)) (.cv y))) p0881 p0882
  have p0884 :=
    @g_biimpd (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classEq (syn_cfv H (syn_cfv H (.cv y))) (syn_cfv H (.cv y))) (.classEq (syn_cfv H (.cv y)) (.cv y)) p0883
  have p0885 :=
    @g_mpd (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classEq (syn_cfv H (syn_cfv H (.cv y))) (syn_cfv H (.cv y))) (.classEq (syn_cfv H (.cv y)) (.cv y)) p0840 p0884
  have p0886 :=
    @g_simpr (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classEq (syn_cfv H (.cv y)) (.cv y))
  have p0887 :=
    @g_simpl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classEq (syn_cfv H (.cv y)) (.cv y))
  have p0888 :=
    @g_simp2 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0889 :=
    @g_eldifn (.cv y) D (syn_cdm (syn_cin H R))
  have p0890 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (.neg (.classMem (.cv y) (syn_cdm (syn_cin H R)))) p0888 p0889
  have p0891 :=
    @g_simp1 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0892 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0893 :=
    @g_isof1o D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) H
  have p0894 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0892 p0893
  have p0895 :=
    @g_f1ofn D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) H
  have p0896 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wfn H D) p0894 p0895
  have p0897 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wfn H D) p0891 p0896
  have p0898 :=
    @g_simp2 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0899 :=
    @g_eldifi (.cv y) D (syn_cdm (syn_cin H R))
  have p0900 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (.classMem (.cv y) D) p0898 p0899
  have p0901 :=
    @g_jca (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wfn H D) (.classMem (.cv y) D) p0897 p0900
  have p0902 :=
    @g_eldm w (.cv y) (syn_cin H R) dv_cache_0011 dv_cache_0002
  have p0903 :=
    @g_a1i (syn_wb (.classMem (.cv y) (syn_cdm (syn_cin H R))) (syn_wex w (syn_wbr (.cv y) (syn_cin H R) (.cv w)))) (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) p0902
  have p0904 :=
    @g_brin (.cv y) (.cv w) H R
  have p0905 :=
    @g_a1i (syn_wb (syn_wbr (.cv y) (syn_cin H R) (.cv w)) (syn_wa (syn_wbr (.cv y) H (.cv w)) (syn_wbr (.cv y) R (.cv w)))) (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) p0904
  have p0906 :=
    @g_fnbrfvb D (.cv y) (.cv w) H
  have p0907 :=
    @g_bicomd (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) H (.cv w)) p0906
  have p0908 :=
    @g_anbi1d (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wbr (.cv y) H (.cv w)) (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w)) p0907
  have p0909 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wbr (.cv y) (syn_cin H R) (.cv w)) (syn_wa (syn_wbr (.cv y) H (.cv w)) (syn_wbr (.cv y) R (.cv w))) (syn_wa (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w))) p0905 p0908
  have p0910 :=
    @g_exbidv (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wbr (.cv y) (syn_cin H R) (.cv w)) (syn_wa (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w))) w dv_cache_0012 p0909
  have p0911 :=
    @g_eqcom (syn_cfv H (.cv y)) (.cv w)
  have p0912 :=
    @g_anbi1i (.classEq (syn_cfv H (.cv y)) (.cv w)) (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w)) p0911
  have p0913 :=
    @g_exbii (syn_wa (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w))) (syn_wa (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w))) w p0912
  have p0914 :=
    @g_a1i (syn_wb (syn_wex w (syn_wa (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w)))) (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w))))) (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) p0913
  have p0915 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wex w (syn_wbr (.cv y) (syn_cin H R) (.cv w))) (syn_wex w (syn_wa (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w)))) (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w)))) p0910 p0914
  have p0916 :=
    @g_fvex (.cv y) H
  have p0917 :=
    @g_breq2 (.cv w) (syn_cfv H (.cv y)) (.cv y) R
  have p0918 :=
    @g_ceqsexv (syn_wbr (.cv y) R (.cv w)) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) w (syn_cfv H (.cv y)) dv_cache_0013 dv_cache_0014 p0916 p0917
  have p0919 :=
    @g_a1i (syn_wb (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w)))) (syn_wbr (.cv y) R (syn_cfv H (.cv y)))) (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) p0918
  have p0920 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wex w (syn_wbr (.cv y) (syn_cin H R) (.cv w))) (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w)))) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) p0915 p0919
  have p0921 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (.classMem (.cv y) (syn_cdm (syn_cin H R))) (syn_wex w (syn_wbr (.cv y) (syn_cin H R) (.cv w))) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) p0903 p0920
  have p0922 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wb (.classMem (.cv y) (syn_cdm (syn_cin H R))) (syn_wbr (.cv y) R (syn_cfv H (.cv y)))) p0901 p0921
  have p0923 :=
    @g_biimprd (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (.cv y) (syn_cdm (syn_cin H R))) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) p0922
  have p0924 :=
    @g_mtod (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) (.classMem (.cv y) (syn_cdm (syn_cin H R))) p0890 p0923
  have p0925 :=
    @g_simp1 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0926 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0927 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))
  have p0928 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) p0926 p0927
  have p0929 :=
    @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)
  have p0930 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wbr R (syn_cwe) D) p0928 p0929
  have p0931 :=
    (by simpa [syn_cwe] using (Nominal.classEqRefl (syn_cwe)))
  have p0932 :=
    @g_breqi R D (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0931
  have p0933 :=
    @g_brin R D (syn_cstrict) (syn_cfound)
  have p0934 :=
    @g_bitri (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_cin (syn_cstrict) (syn_cfound)) D) (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0932 p0933
  have p0935 :=
    @g_biimpi (syn_wbr R (syn_cwe) D) (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0934
  have p0936 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cwe) D) (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0930 p0935
  have p0937 :=
    @g_simpld (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D) p0936
  have p0938 :=
    @g_sopc D R
  have p0939 :=
    @g_sylib (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cstrict) D) (syn_wa (syn_wbr R (syn_cpartial) D) (syn_wbr R (syn_cconnex) D)) p0937 p0938
  have p0940 :=
    @g_simprd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cpartial) D) (syn_wbr R (syn_cconnex) D) p0939
  have p0941 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wbr R (syn_cconnex) D) p0925 p0940
  have p0942 :=
    @g_simp2 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0943 :=
    @g_eldifi (.cv y) D (syn_cdm (syn_cin H R))
  have p0944 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (.classMem (.cv y) D) p0942 p0943
  have p0945 :=
    @g_simp1 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0946 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0947 :=
    @g_isof1o D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) H
  have p0948 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0946 p0947
  have p0949 :=
    @g_f1of D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) H
  have p0950 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0948 p0949
  have p0951 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0945 p0950
  have p0952 :=
    @g_simp2 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0953 :=
    @g_eldifi (.cv y) D (syn_cdm (syn_cin H R))
  have p0954 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (.classMem (.cv y) D) p0952 p0953
  have p0955 :=
    @g_jca (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv y) D) p0951 p0954
  have p0956 :=
    @g_ffvelrn D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (.cv y) H
  have p0957 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.classMem (.cv y) D)) (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0955 p0956
  have p0958 :=
    @g_elin (syn_cfv H (.cv y)) D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0959 :=
    @g_eliniseg (syn_cdif R (syn_cid)) (.cv x) (syn_cfv H (.cv y))
  have p0960 :=
    @g_brdif (syn_cfv H (.cv y)) (.cv x) R (syn_cid)
  have p0961 :=
    @g_vex x
  have p0962 :=
    @g_ideq (syn_cfv H (.cv y)) (.cv x) p0961
  have p0963 :=
    @g_notbii (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x)) (.classEq (syn_cfv H (.cv y)) (.cv x)) p0962
  have p0964 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (syn_cfv H (.cv y)) (.cv x))))
  have p0965 :=
    @g_bitr4i (.neg (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x))) (.neg (.classEq (syn_cfv H (.cv y)) (.cv x))) (syn_wne (syn_cfv H (.cv y)) (.cv x)) p0963 p0964
  have p0966 :=
    @g_anbi2i (.neg (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x))) (syn_wne (syn_cfv H (.cv y)) (.cv x)) (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) p0965
  have p0967 :=
    @g_bitri (syn_wbr (syn_cfv H (.cv y)) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (.neg (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x)))) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) p0960 p0966
  have p0968 :=
    @g_bitri (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wbr (syn_cfv H (.cv y)) (syn_cdif R (syn_cid)) (.cv x)) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) p0959 p0967
  have p0969 :=
    @g_anbi2i (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) (.classMem (syn_cfv H (.cv y)) D) p0968
  have p0970 :=
    @g_bitri (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (.classMem (syn_cfv H (.cv y)) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x)))) p0958 p0969
  have p0971 :=
    @g_biimpi (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x)))) p0970
  have p0972 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x)))) p0957 p0971
  have p0973 :=
    @g_simpld (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (syn_cfv H (.cv y)) D) (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x))) p0972
  have p0974 :=
    @g_connexd (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) D R (.cv y) (syn_cfv H (.cv y)) p0941 p0944 p0973
  have p0975 :=
    @g_ord (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) (syn_wbr (syn_cfv H (.cv y)) R (.cv y)) p0974
  have p0976 :=
    @g_mpd (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.neg (syn_wbr (.cv y) R (syn_cfv H (.cv y)))) (syn_wbr (syn_cfv H (.cv y)) R (.cv y)) p0924 p0975
  have p0977 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classEq (syn_cfv H (.cv y)) (.cv y))) (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wbr (syn_cfv H (.cv y)) R (.cv y)) p0887 p0976
  have p0978 :=
    @g_eqbrtrrd (syn_wa (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classEq (syn_cfv H (.cv y)) (.cv y))) (syn_cfv H (.cv y)) (.cv y) (.cv y) R p0886 p0977
  have p0979 :=
    @g_simpr (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classEq (syn_cfv H (.cv y)) (.cv y))
  have p0980 :=
    @g_breqtrrd (syn_wa (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classEq (syn_cfv H (.cv y)) (.cv y))) (.cv y) (.cv y) (syn_cfv H (.cv y)) R p0978 p0979
  have p0981 :=
    @g_simpl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classEq (syn_cfv H (.cv y)) (.cv y))
  have p0982 :=
    @g_simp2 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0983 :=
    @g_eldifn (.cv y) D (syn_cdm (syn_cin H R))
  have p0984 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (.neg (.classMem (.cv y) (syn_cdm (syn_cin H R)))) p0982 p0983
  have p0985 :=
    @g_simp1 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0986 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0987 :=
    @g_isof1o D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) H
  have p0988 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0986 p0987
  have p0989 :=
    @g_f1ofn D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) H
  have p0990 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wfn H D) p0988 p0989
  have p0991 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wfn H D) p0985 p0990
  have p0992 :=
    @g_simp2 (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  have p0993 :=
    @g_eldifi (.cv y) D (syn_cdm (syn_cin H R))
  have p0994 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (.classMem (.cv y) D) p0992 p0993
  have p0995 :=
    @g_jca (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wfn H D) (.classMem (.cv y) D) p0991 p0994
  have p0996 :=
    @g_eldm w (.cv y) (syn_cin H R) dv_cache_0011 dv_cache_0002
  have p0997 :=
    @g_a1i (syn_wb (.classMem (.cv y) (syn_cdm (syn_cin H R))) (syn_wex w (syn_wbr (.cv y) (syn_cin H R) (.cv w)))) (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) p0996
  have p0998 :=
    @g_brin (.cv y) (.cv w) H R
  have p0999 :=
    @g_a1i (syn_wb (syn_wbr (.cv y) (syn_cin H R) (.cv w)) (syn_wa (syn_wbr (.cv y) H (.cv w)) (syn_wbr (.cv y) R (.cv w)))) (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) p0998
  have p1000 :=
    @g_fnbrfvb D (.cv y) (.cv w) H
  have p1001 :=
    @g_bicomd (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) H (.cv w)) p1000
  have p1002 :=
    @g_anbi1d (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wbr (.cv y) H (.cv w)) (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w)) p1001
  have p1003 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wbr (.cv y) (syn_cin H R) (.cv w)) (syn_wa (syn_wbr (.cv y) H (.cv w)) (syn_wbr (.cv y) R (.cv w))) (syn_wa (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w))) p0999 p1002
  have p1004 :=
    @g_exbidv (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wbr (.cv y) (syn_cin H R) (.cv w)) (syn_wa (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w))) w dv_cache_0012 p1003
  have p1005 :=
    @g_eqcom (syn_cfv H (.cv y)) (.cv w)
  have p1006 :=
    @g_anbi1i (.classEq (syn_cfv H (.cv y)) (.cv w)) (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w)) p1005
  have p1007 :=
    @g_exbii (syn_wa (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w))) (syn_wa (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w))) w p1006
  have p1008 :=
    @g_a1i (syn_wb (syn_wex w (syn_wa (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w)))) (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w))))) (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) p1007
  have p1009 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wex w (syn_wbr (.cv y) (syn_cin H R) (.cv w))) (syn_wex w (syn_wa (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w)))) (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w)))) p1004 p1008
  have p1010 :=
    @g_fvex (.cv y) H
  have p1011 :=
    @g_breq2 (.cv w) (syn_cfv H (.cv y)) (.cv y) R
  have p1012 :=
    @g_ceqsexv (syn_wbr (.cv y) R (.cv w)) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) w (syn_cfv H (.cv y)) dv_cache_0013 dv_cache_0014 p1010 p1011
  have p1013 :=
    @g_a1i (syn_wb (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w)))) (syn_wbr (.cv y) R (syn_cfv H (.cv y)))) (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) p1012
  have p1014 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wex w (syn_wbr (.cv y) (syn_cin H R) (.cv w))) (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w)))) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) p1009 p1013
  have p1015 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (.classMem (.cv y) (syn_cdm (syn_cin H R))) (syn_wex w (syn_wbr (.cv y) (syn_cin H R) (.cv w))) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) p0997 p1014
  have p1016 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wb (.classMem (.cv y) (syn_cdm (syn_cin H R))) (syn_wbr (.cv y) R (syn_cfv H (.cv y)))) p0995 p1015
  have p1017 :=
    @g_biimprd (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classMem (.cv y) (syn_cdm (syn_cin H R))) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) p1016
  have p1018 :=
    @g_mtod (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) (.classMem (.cv y) (syn_cdm (syn_cin H R))) p0984 p1017
  have p1019 :=
    @g_syl (syn_wa (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classEq (syn_cfv H (.cv y)) (.cv y))) (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.neg (syn_wbr (.cv y) R (syn_cfv H (.cv y)))) p0981 p1018
  have p1020 :=
    @g_pm2_21dd (syn_wa (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classEq (syn_cfv H (.cv y)) (.cv y))) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) (.neg (.classEq (syn_cfv H (.cv y)) (.cv y))) p0980 p1019
  have p1021 :=
    @g_pm2_01da (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.classEq (syn_cfv H (.cv y)) (.cv y)) p1020
  have p1022 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (syn_cfv H (.cv y)) (.cv y))))
  have p1023 :=
    @g_biimpri (syn_wne (syn_cfv H (.cv y)) (.cv y)) (.neg (.classEq (syn_cfv H (.cv y)) (.cv y))) p1022
  have p1024 :=
    @g_syl (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.neg (.classEq (syn_cfv H (.cv y)) (.cv y))) (syn_wne (syn_cfv H (.cv y)) (.cv y)) p1021 p1023
  have p1025 :=
    @g_pm2_21ddne (syn_w3a (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.neg (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv H (.cv y)) (.cv y) p0885 p1024
  have p1026 :=
    @g_n_3exp (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R)))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y)))) (.neg (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) p1025
  have p1027 :=
    @g_rexlimdv (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y)))) (.neg (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) y (syn_cdif D (syn_cdm (syn_cin H R))) dv_cache_0020 dv_cache_0021 p1026
  have p1028_e00_recanon : Nominal.NPrf (.imp (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wrex y (syn_cdif D (syn_cdm (syn_cin H R))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wiso syn_cin syn_ccompl syn_cnin syn_wnan syn_cxp syn_copab syn_wex syn_wrex syn_cdif syn_cdm syn_crn syn_cima syn_cvv syn_ccnv syn_wral syn_wbr syn_cop syn_cun
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
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
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
      )
      p0213
  have p1028 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_wrex y (syn_cdif D (syn_cdm (syn_cin H R))) (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R))) (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))) (.neg (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) p1028_e00_recanon p1027
  have p1029 :=
    @g_pm2_01da (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p1028
  exact p1029

#print axioms g_strictsegnoiso

end NFChoice.DirectNominalPrf.WPPReplay
