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
import NominalNFLiteralBaseFour
import NominalNFLiteralXpViaCompletenessDev003
import NominalNFLiteralRemainingViaCompletenessDev001
import NominalDefinitionLeafHandlersCanonical001
import NominalDefinitionLeafHandlersObjExtCompat001
import NominalRecanonTransportCompat001
import NominalWPPReplayChunk010Compact001Part023

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

noncomputable def g_vfinspss
    (x : Var) (a : Var) (dv_a_x : a ≠ x) :
    Nominal.NPrf (.imp (.classMem (syn_cvv) (syn_cfin)) (syn_wss (syn_cspfin) (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({a} : Finset Var)
  let w : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let n : Var := freshVar proofSupport 2
  let t : Var := freshVar proofSupport 3
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_w_ne_a : w ≠ a := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_a_ne_w : a ≠ w :=
    Ne.symm fresh_w_ne_a
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_a : z ≠ a := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_a_ne_z : a ≠ z :=
    Ne.symm fresh_z_ne_a
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_n_ne_x : n ≠ x := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_n : x ≠ n :=
    Ne.symm fresh_n_ne_x
  have fresh_n_ne_a : n ≠ a := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_a_ne_n : a ≠ n :=
    Ne.symm fresh_n_ne_a
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_t_ne_x : t ≠ x := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_t : x ≠ t :=
    Ne.symm fresh_t_ne_x
  have fresh_t_ne_a : t ≠ a := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_a_ne_t : a ≠ t :=
    Ne.symm fresh_t_ne_a
  have fresh_w_ne_z : w ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_w : z ≠ w :=
    Ne.symm fresh_w_ne_z
  have fresh_w_ne_n : w ≠ n := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_n_ne_w : n ≠ w :=
    Ne.symm fresh_w_ne_n
  have fresh_w_ne_t : w ≠ t := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_t_ne_w : t ≠ w :=
    Ne.symm fresh_w_ne_t
  have fresh_z_ne_n : z ≠ n := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_n_ne_z : n ≠ z :=
    Ne.symm fresh_z_ne_n
  have fresh_z_ne_t : z ≠ t := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_t_ne_z : t ≠ z :=
    Ne.symm fresh_z_ne_t
  have fresh_n_ne_t : n ≠ t := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_t_ne_n : t ≠ n :=
    Ne.symm fresh_n_ne_t
  have dv_cache_0001 : x ∉ ((syn_cspfin)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : n ∉ ((syn_cspfin)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : n ∉ ((Wff.classEq (.cv w) (syn_ctfin (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_w, fresh_n_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classEq (.cv w) (syn_ctfin (.cv n)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_w, fresh_x_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : n ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show n ≠ x from (by exact fresh_n_ne_x))
  have dv_cache_0006 : n ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show n ≠ z from (by exact fresh_n_ne_z))
  have dv_cache_0007 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0008 : n ∉ ((Wff.imp (syn_wsfin (.cv z) (.cv w)) (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_z, fresh_n_ne_w, fresh_n_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : n ∉ ((syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv w) (syn_cspfin)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ ((syn_cncfin (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((Wff.classEq (syn_cncfin (syn_c1c)) (syn_ctfin (syn_cncfin (syn_cvv))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((Wff.classEq (syn_cncfin (syn_c1c)) (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((Wff.objEq a w)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_a_x), fresh_x_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : a ∉ ((Class.cv w)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : a ∉ ((syn_wrex x (syn_cspfin) (.classEq (.cv w) (syn_ctfin (.cv x))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_w, dv_a_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : x ∉ ((Wff.objEq a z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_a_x), fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : a ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : a ∉ ((syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_z, dv_a_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : z ∉ ((syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv w) (syn_cspfin)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : w ∉ ((Wff.classMem (syn_cvv) (syn_cfin))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : t ∉ ((syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : t ∉ ((syn_cpw1 (syn_cspfin))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : t ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : x ∉ ((Class.cv t)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : x ∉ ((Wff.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_t, (Ne.symm dv_a_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : t ∉ ((syn_cspfin)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : x ≠ t := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (show x ≠ t from (by exact fresh_x_ne_t))
  have dv_cache_0028 : t ∉ ((syn_csn (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0029 : t ∉ ((Wff.classMem (syn_copk (syn_csn (.cv x)) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0030 : a ∉ ((syn_cimak (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))) (syn_cpw1 (syn_cspfin)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0031 : w ∉ ((syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_a, fresh_w_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0032 : z ∉ ((syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_a, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0033 : w ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (show w ≠ z from (by exact fresh_w_ne_z))
  have p0000 :=
    @g_tfineq (.cv x) (.cv n)
  have p0001_e00_recanon : Nominal.NPrf (.imp (.objEq x n) (.classEq (syn_ctfin (.cv x)) (syn_ctfin (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_ctfin syn_cif syn_wo syn_wa syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_cvv syn_cio syn_cuni syn_wex syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0000
  have p0001 :=
    @g_eqeq2d (.objEq x n) (syn_ctfin (.cv x)) (syn_ctfin (.cv n)) (.cv w) p0001_e00_recanon
  have p0002 :=
    @g_cbvrexv (.classEq (.cv w) (syn_ctfin (.cv x))) (.classEq (.cv w) (syn_ctfin (.cv n))) x n (syn_cspfin) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 p0001
  have p0003 :=
    @g_vfinspsslem1 x z n dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0004 :=
    @g_expr (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_ctfin (.cv n)) (syn_cspfin))) (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n))) (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))) p0003
  have p0005 :=
    @g_eleq1 (.cv w) (syn_ctfin (.cv n)) (syn_cspfin)
  have p0006 :=
    @g_anbi2d (.classEq (.cv w) (syn_ctfin (.cv n))) (.classMem (.cv w) (syn_cspfin)) (.classMem (syn_ctfin (.cv n)) (syn_cspfin)) (.classMem (syn_cvv) (syn_cfin)) p0005
  have p0007 :=
    @g_anbi1d (.classEq (.cv w) (syn_ctfin (.cv n))) (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv w) (syn_cspfin))) (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_ctfin (.cv n)) (syn_cspfin))) (.classMem (.cv n) (syn_cspfin)) p0006
  have p0008 :=
    @g_sfineq2 (.cv w) (syn_ctfin (.cv n)) (.cv z)
  have p0009 :=
    @g_imbi1d (.classEq (.cv w) (syn_ctfin (.cv n))) (syn_wsfin (.cv z) (.cv w)) (syn_wsfin (.cv z) (syn_ctfin (.cv n))) (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))) p0008
  have p0010 :=
    @g_imbi12d (.classEq (.cv w) (syn_ctfin (.cv n))) (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv w) (syn_cspfin))) (.classMem (.cv n) (syn_cspfin))) (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_ctfin (.cv n)) (syn_cspfin))) (.classMem (.cv n) (syn_cspfin))) (.imp (syn_wsfin (.cv z) (.cv w)) (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x))))) (.imp (syn_wsfin (.cv z) (syn_ctfin (.cv n))) (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x))))) p0007 p0009
  have p0011 :=
    @g_mpbiri (.classEq (.cv w) (syn_ctfin (.cv n))) (.imp (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv w) (syn_cspfin))) (.classMem (.cv n) (syn_cspfin))) (.imp (syn_wsfin (.cv z) (.cv w)) (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))))) (.imp (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_ctfin (.cv n)) (syn_cspfin))) (.classMem (.cv n) (syn_cspfin))) (.imp (syn_wsfin (.cv z) (syn_ctfin (.cv n))) (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))))) p0004 p0010
  have p0012 :=
    @g_com12 (.classEq (.cv w) (syn_ctfin (.cv n))) (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv w) (syn_cspfin))) (.classMem (.cv n) (syn_cspfin))) (.imp (syn_wsfin (.cv z) (.cv w)) (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x))))) p0011
  have p0013 :=
    @g_rexlimdva (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv w) (syn_cspfin))) (.classEq (.cv w) (syn_ctfin (.cv n))) (.imp (syn_wsfin (.cv z) (.cv w)) (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x))))) n (syn_cspfin) dv_cache_0008 dv_cache_0009 p0012
  have p0014 :=
    @g_syl5bi (syn_wrex x (syn_cspfin) (.classEq (.cv w) (syn_ctfin (.cv x)))) (syn_wrex n (syn_cspfin) (.classEq (.cv w) (syn_ctfin (.cv n)))) (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv w) (syn_cspfin))) (.imp (syn_wsfin (.cv z) (.cv w)) (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x))))) p0002 p0013
  have p0015 :=
    @g_sfineq2 (.cv w) (syn_cncfin (syn_cvv)) (.cv z)
  have p0016 :=
    @g_biimpa (.classEq (.cv w) (syn_cncfin (syn_cvv))) (syn_wsfin (.cv z) (.cv w)) (syn_wsfin (.cv z) (syn_cncfin (syn_cvv))) p0015
  have p0017 :=
    @g_n_1cvsfin
  have p0018 :=
    @g_sfin111 (syn_cncfin (syn_cvv)) (syn_cncfin (syn_c1c)) (.cv z)
  have p0019 :=
    @g_tncveqnc1fin
  have p0020 :=
    @g_eqcomd (.classMem (syn_cvv) (syn_cfin)) (syn_ctfin (syn_cncfin (syn_cvv))) (syn_cncfin (syn_c1c)) p0019
  have p0021 :=
    @g_ncvspfin
  have p0022 :=
    @g_tfineq (.cv x) (syn_cncfin (syn_cvv))
  have p0023 :=
    @g_eqeq2d (.classEq (.cv x) (syn_cncfin (syn_cvv))) (syn_ctfin (.cv x)) (syn_ctfin (syn_cncfin (syn_cvv))) (syn_cncfin (syn_c1c)) p0022
  have p0024 :=
    @g_rspcev (.classEq (syn_cncfin (syn_c1c)) (syn_ctfin (.cv x))) (.classEq (syn_cncfin (syn_c1c)) (syn_ctfin (syn_cncfin (syn_cvv)))) x (syn_cncfin (syn_cvv)) (syn_cspfin) dv_cache_0010 dv_cache_0001 dv_cache_0011 p0023
  have p0025 :=
    @g_mpan (.classMem (syn_cncfin (syn_cvv)) (syn_cspfin)) (.classEq (syn_cncfin (syn_c1c)) (syn_ctfin (syn_cncfin (syn_cvv)))) (syn_wrex x (syn_cspfin) (.classEq (syn_cncfin (syn_c1c)) (syn_ctfin (.cv x)))) p0021 p0024
  have p0026 :=
    @g_syl (.classMem (syn_cvv) (syn_cfin)) (.classEq (syn_cncfin (syn_c1c)) (syn_ctfin (syn_cncfin (syn_cvv)))) (syn_wrex x (syn_cspfin) (.classEq (syn_cncfin (syn_c1c)) (syn_ctfin (.cv x)))) p0020 p0025
  have p0027 :=
    @g_eqeq1 (syn_cncfin (syn_c1c)) (.cv z) (syn_ctfin (.cv x))
  have p0028 :=
    @g_rexbidv (.classEq (syn_cncfin (syn_c1c)) (.cv z)) (.classEq (syn_cncfin (syn_c1c)) (syn_ctfin (.cv x))) (.classEq (.cv z) (syn_ctfin (.cv x))) x (syn_cspfin) dv_cache_0012 p0027
  have p0029 :=
    @g_biimpd (.classEq (syn_cncfin (syn_c1c)) (.cv z)) (syn_wrex x (syn_cspfin) (.classEq (syn_cncfin (syn_c1c)) (syn_ctfin (.cv x)))) (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))) p0028
  have p0030 :=
    @g_com12 (.classEq (syn_cncfin (syn_c1c)) (.cv z)) (syn_wrex x (syn_cspfin) (.classEq (syn_cncfin (syn_c1c)) (syn_ctfin (.cv x)))) (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))) p0029
  have p0031 :=
    @g_syl (.classMem (syn_cvv) (syn_cfin)) (syn_wrex x (syn_cspfin) (.classEq (syn_cncfin (syn_c1c)) (syn_ctfin (.cv x)))) (.imp (.classEq (syn_cncfin (syn_c1c)) (.cv z)) (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x))))) p0026 p0030
  have p0032 :=
    @g_syl5 (syn_wa (syn_wsfin (syn_cncfin (syn_c1c)) (syn_cncfin (syn_cvv))) (syn_wsfin (.cv z) (syn_cncfin (syn_cvv)))) (.classEq (syn_cncfin (syn_c1c)) (.cv z)) (.classMem (syn_cvv) (syn_cfin)) (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))) p0018 p0031
  have p0033 :=
    @g_mpand (.classMem (syn_cvv) (syn_cfin)) (syn_wsfin (syn_cncfin (syn_c1c)) (syn_cncfin (syn_cvv))) (syn_wsfin (.cv z) (syn_cncfin (syn_cvv))) (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))) p0017 p0032
  have p0034 :=
    @g_syl5 (syn_wa (.classEq (.cv w) (syn_cncfin (syn_cvv))) (syn_wsfin (.cv z) (.cv w))) (syn_wsfin (.cv z) (syn_cncfin (syn_cvv))) (.classMem (syn_cvv) (syn_cfin)) (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))) p0016 p0033
  have p0035 :=
    @g_exp3a (.classMem (syn_cvv) (syn_cfin)) (.classEq (.cv w) (syn_cncfin (syn_cvv))) (syn_wsfin (.cv z) (.cv w)) (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))) p0034
  have p0036 :=
    @g_adantr (.classMem (syn_cvv) (syn_cfin)) (.imp (.classEq (.cv w) (syn_cncfin (syn_cvv))) (.imp (syn_wsfin (.cv z) (.cv w)) (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))))) (.classMem (.cv w) (syn_cspfin)) p0035
  have p0037 :=
    @g_jaod (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv w) (syn_cspfin))) (syn_wrex x (syn_cspfin) (.classEq (.cv w) (syn_ctfin (.cv x)))) (.imp (syn_wsfin (.cv z) (.cv w)) (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x))))) (.classEq (.cv w) (syn_cncfin (syn_cvv))) p0014 p0036
  have p0038 :=
    @g_imp3a (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv w) (syn_cspfin))) (syn_wo (syn_wrex x (syn_cspfin) (.classEq (.cv w) (syn_ctfin (.cv x)))) (.classEq (.cv w) (syn_cncfin (syn_cvv)))) (syn_wsfin (.cv z) (.cv w)) (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))) p0037
  have p0039 :=
    @g_elun (.cv w) (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv)))
  have p0040 :=
    @g_vex w
  have p0041 :=
    @g_eqeq1 (.cv a) (.cv w) (syn_ctfin (.cv x))
  have p0042_e00_recanon : Nominal.NPrf (.imp (.objEq a w) (syn_wb (.classEq (.cv a) (syn_ctfin (.cv x))) (.classEq (.cv w) (syn_ctfin (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_ctfin syn_cif syn_wo syn_wa syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_cvv syn_cio syn_cuni syn_wex syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0041
  have p0042 :=
    @g_rexbidv (.objEq a w) (.classEq (.cv a) (syn_ctfin (.cv x))) (.classEq (.cv w) (syn_ctfin (.cv x))) x (syn_cspfin) dv_cache_0013 p0042_e00_recanon
  have p0043_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv a) (.cv w)) (syn_wb (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))) (syn_wrex x (syn_cspfin) (.classEq (.cv w) (syn_ctfin (.cv x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wrex syn_wex syn_wa syn_cspfin syn_cint syn_ctfin syn_cif syn_wo syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_cvv syn_cio syn_cuni syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0042
  have p0043 :=
    @g_elab (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))) (syn_wrex x (syn_cspfin) (.classEq (.cv w) (syn_ctfin (.cv x)))) a (.cv w) dv_cache_0014 dv_cache_0015 p0040 p0043_e01_recanon
  have p0044 :=
    @g_elsnc (.cv w) (syn_cncfin (syn_cvv)) p0040
  have p0045 :=
    @g_orbi12i (.classMem (.cv w) (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))) (syn_wrex x (syn_cspfin) (.classEq (.cv w) (syn_ctfin (.cv x)))) (.classMem (.cv w) (syn_csn (syn_cncfin (syn_cvv)))) (.classEq (.cv w) (syn_cncfin (syn_cvv))) p0043 p0044
  have p0046 :=
    @g_bitri (.classMem (.cv w) (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv))))) (syn_wo (.classMem (.cv w) (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))) (.classMem (.cv w) (syn_csn (syn_cncfin (syn_cvv))))) (syn_wo (syn_wrex x (syn_cspfin) (.classEq (.cv w) (syn_ctfin (.cv x)))) (.classEq (.cv w) (syn_cncfin (syn_cvv)))) p0039 p0045
  have p0047 :=
    @g_anbi1i (.classMem (.cv w) (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv))))) (syn_wo (syn_wrex x (syn_cspfin) (.classEq (.cv w) (syn_ctfin (.cv x)))) (.classEq (.cv w) (syn_cncfin (syn_cvv)))) (syn_wsfin (.cv z) (.cv w)) p0046
  have p0048 :=
    @g_vex z
  have p0049 :=
    @g_eqeq1 (.cv a) (.cv z) (syn_ctfin (.cv x))
  have p0050_e00_recanon : Nominal.NPrf (.imp (.objEq a z) (syn_wb (.classEq (.cv a) (syn_ctfin (.cv x))) (.classEq (.cv z) (syn_ctfin (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_ctfin syn_cif syn_wo syn_wa syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_cvv syn_cio syn_cuni syn_wex syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0049
  have p0050 :=
    @g_rexbidv (.objEq a z) (.classEq (.cv a) (syn_ctfin (.cv x))) (.classEq (.cv z) (syn_ctfin (.cv x))) x (syn_cspfin) dv_cache_0016 p0050_e00_recanon
  have p0051_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv a) (.cv z)) (syn_wb (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))) (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wrex syn_wex syn_wa syn_cspfin syn_cint syn_ctfin syn_cif syn_wo syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_cvv syn_cio syn_cuni syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0050
  have p0051 :=
    @g_elab (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))) (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))) a (.cv z) dv_cache_0017 dv_cache_0018 p0048 p0051_e01_recanon
  have p0052 :=
    @g_n_3imtr4g (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv w) (syn_cspfin))) (syn_wa (syn_wo (syn_wrex x (syn_cspfin) (.classEq (.cv w) (syn_ctfin (.cv x)))) (.classEq (.cv w) (syn_cncfin (syn_cvv)))) (syn_wsfin (.cv z) (.cv w))) (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))) (syn_wa (.classMem (.cv w) (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv))))) (syn_wsfin (.cv z) (.cv w))) (.classMem (.cv z) (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))) p0038 p0047 p0051
  have p0053 :=
    @g_ssun1 (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv)))
  have p0054 :=
    @g_sseli (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv)))) (.cv z) p0053
  have p0055 :=
    @g_syl6 (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv w) (syn_cspfin))) (syn_wa (.classMem (.cv w) (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv))))) (syn_wsfin (.cv z) (.cv w))) (.classMem (.cv z) (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))) (.classMem (.cv z) (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv))))) p0052 p0054
  have p0056 :=
    @g_alrimiv (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv w) (syn_cspfin))) (.imp (syn_wa (.classMem (.cv w) (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv))))) (syn_wsfin (.cv z) (.cv w))) (.classMem (.cv z) (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv)))))) z dv_cache_0019 p0055
  have p0057 :=
    @g_ralrimiva (.classMem (syn_cvv) (syn_cfin)) (.all z (.imp (syn_wa (.classMem (.cv w) (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv))))) (syn_wsfin (.cv z) (.cv w))) (.classMem (.cv z) (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv))))))) w (syn_cspfin) dv_cache_0020 p0056
  have p0058 :=
    @g_vex a
  have p0059 :=
    @g_elimak t (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))) (syn_cpw1 (syn_cspfin)) (.cv a) dv_cache_0021 dv_cache_0022 dv_cache_0023 p0058
  have p0060 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex t (syn_cpw1 (syn_cspfin)) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))))
  have p0061 :=
    @g_elpw1 x (.cv t) (syn_cspfin) dv_cache_0024 dv_cache_0001
  have p0062 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cspfin))) (syn_wrex x (syn_cspfin) (.classEq (.cv t) (syn_csn (.cv x)))) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))) p0061
  have p0063 :=
    @g_r19_41v (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))) x (syn_cspfin) dv_cache_0025
  have p0064 :=
    @g_bitr4i (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cspfin))) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))) (syn_wa (syn_wrex x (syn_cspfin) (.classEq (.cv t) (syn_csn (.cv x)))) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))) (syn_wrex x (syn_cspfin) (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))) p0062 p0063
  have p0065 :=
    @g_exbii (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cspfin))) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))) (syn_wrex x (syn_cspfin) (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))) t p0064
  have p0066 :=
    @g_rexcom4 (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))) x t (syn_cspfin) dv_cache_0026 dv_cache_0027
  have p0067 :=
    @g_bitr4i (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cspfin))) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))) (syn_wex t (syn_wrex x (syn_cspfin) (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))))) (syn_wrex x (syn_cspfin) (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))))) p0065 p0066
  have p0068 :=
    @g_bitri (syn_wrex t (syn_cpw1 (syn_cspfin)) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))) (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cspfin))) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))) (syn_wrex x (syn_cspfin) (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))))) p0060 p0067
  have p0069 :=
    @g_bitri (.classMem (.cv a) (syn_cimak (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))) (syn_cpw1 (syn_cspfin)))) (syn_wrex t (syn_cpw1 (syn_cspfin)) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))) (syn_wrex x (syn_cspfin) (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))))) p0059 p0068
  have p0070 :=
    @g_snex (.cv x)
  have p0071 :=
    @g_opkeq1 (.cv t) (syn_csn (.cv x)) (.cv a)
  have p0072 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (.cv x))) (syn_copk (.cv t) (.cv a)) (syn_copk (syn_csn (.cv x)) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))) p0071
  have p0073 :=
    @g_ceqsexv (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))) (.classMem (syn_copk (syn_csn (.cv x)) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))) t (syn_csn (.cv x)) dv_cache_0028 dv_cache_0029 p0070 p0072
  have p0074 :=
    @g_vex x
  have p0075 :=
    @g_eqtfinrelk (.cv x) (.cv a) p0074 p0058
  have p0076 :=
    @g_bitri (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))) (.classMem (syn_copk (syn_csn (.cv x)) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))) (.classEq (.cv a) (syn_ctfin (.cv x))) p0073 p0075
  have p0077 :=
    @g_rexbii (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))) (.classEq (.cv a) (syn_ctfin (.cv x))) x (syn_cspfin) p0076
  have p0078 :=
    @g_bitri (.classMem (.cv a) (syn_cimak (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))) (syn_cpw1 (syn_cspfin)))) (syn_wrex x (syn_cspfin) (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))))) (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))) p0069 p0077
  have p0079 :=
    @g_eqabi (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))) a (syn_cimak (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))) (syn_cpw1 (syn_cspfin))) dv_cache_0030 p0078
  have p0080 :=
    @g_tfinrelkex
  have p0081 :=
    @g_spfinex
  have p0082 :=
    @g_pw1ex (syn_cspfin) p0081
  have p0083 :=
    @g_imakex (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))) (syn_cpw1 (syn_cspfin)) p0080 p0082
  have p0084 :=
    @g_eqeltrri (syn_cimak (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))) (syn_cpw1 (syn_cspfin))) (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_cvv) p0079 p0083
  have p0085 :=
    @g_snex (syn_cncfin (syn_cvv))
  have p0086 :=
    @g_unex (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv))) p0084 p0085
  have p0087 :=
    @g_ssun2 (syn_csn (syn_cncfin (syn_cvv))) (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
  have p0088 :=
    @g_ncfinex (syn_cvv)
  have p0089 :=
    @g_snid (syn_cncfin (syn_cvv)) p0088
  have p0090 :=
    @g_sselii (syn_csn (syn_cncfin (syn_cvv))) (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv)))) (syn_cncfin (syn_cvv)) p0087 p0089
  have p0091 :=
    @g_spfininduct w z (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv)))) (syn_cvv) dv_cache_0031 dv_cache_0032 dv_cache_0033
  have p0092 :=
    @g_mp3an12 (.classMem (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv)))) (syn_cvv)) (.classMem (syn_cncfin (syn_cvv)) (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv))))) (syn_wral w (syn_cspfin) (.all z (.imp (syn_wa (.classMem (.cv w) (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv))))) (syn_wsfin (.cv z) (.cv w))) (.classMem (.cv z) (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv)))))))) (syn_wss (syn_cspfin) (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv))))) p0086 p0090 p0091
  have p0093 :=
    @g_syl (.classMem (syn_cvv) (syn_cfin)) (syn_wral w (syn_cspfin) (.all z (.imp (syn_wa (.classMem (.cv w) (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv))))) (syn_wsfin (.cv z) (.cv w))) (.classMem (.cv z) (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv)))))))) (syn_wss (syn_cspfin) (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv))))) p0057 p0092
  exact p0093

#print axioms g_vfinspss

end NFChoice.DirectNominalPrf.WPPReplay
