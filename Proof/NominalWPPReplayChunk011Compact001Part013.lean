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
import NominalWPPReplayChunk011Compact001Part012

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

noncomputable def g_fununi
    (A : Class) (f : Var) (g : Var) (dv_A_f : f ∉ A.fv) (dv_A_g : g ∉ A.fv) (dv_f_g : f ≠ g) :
    Nominal.NPrf (.imp (syn_wral f A (syn_wa (syn_wfun (.cv f)) (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))))) (syn_wfun (syn_cuni A))) := by
  let proofSupport : Finset Var := A.fv ∪ ({f} : Finset Var) ∪ ({g} : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  let v : Var := freshVar proofSupport 4
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_ne_f : x ≠ f := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_ne_x : f ≠ x :=
    Ne.symm fresh_x_ne_f
  have fresh_x_ne_g : x ≠ g := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_g_ne_x : g ≠ x :=
    Ne.symm fresh_x_ne_g
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_ne_f : y ≠ f := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_ne_y : f ≠ y :=
    Ne.symm fresh_y_ne_f
  have fresh_y_ne_g : y ≠ g := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_g_ne_y : g ≠ y :=
    Ne.symm fresh_y_ne_g
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_ne_f : z ≠ f := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_ne_z : f ≠ z :=
    Ne.symm fresh_z_ne_f
  have fresh_z_ne_g : z ≠ g := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_g_ne_z : g ≠ z :=
    Ne.symm fresh_z_ne_g
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_w_ne_f : w ≠ f := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_ne_w : f ≠ w :=
    Ne.symm fresh_w_ne_f
  have fresh_w_ne_g : w ≠ g := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_g_ne_w : g ≠ w :=
    Ne.symm fresh_w_ne_g
  have fresh_v : v ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_v_ne_f : v ≠ f := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_ne_v : f ≠ v :=
    Ne.symm fresh_v_ne_f
  have fresh_v_ne_g : v ≠ g := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_g_ne_v : g ≠ v :=
    Ne.symm fresh_v_ne_g
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
  have fresh_x_ne_w : x ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_w_ne_x : w ≠ x :=
    Ne.symm fresh_x_ne_w
  have fresh_x_ne_v : x ≠ v := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_v_ne_x : v ≠ x :=
    Ne.symm fresh_x_ne_v
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_y_ne_w : y ≠ w := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_w_ne_y : w ≠ y :=
    Ne.symm fresh_y_ne_w
  have fresh_y_ne_v : y ≠ v := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_v_ne_y : v ≠ y :=
    Ne.symm fresh_y_ne_v
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have fresh_z_ne_v : z ≠ v := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_v_ne_z : v ≠ z :=
    Ne.symm fresh_z_ne_v
  have fresh_w_ne_v : w ≠ v := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_v_ne_w : v ≠ w :=
    Ne.symm fresh_w_ne_v
  have dv_cache_0001 : g ∉ ((syn_wfun (.cv f))).fv := by
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_f_g), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Class.cv v)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Class.cv v)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((Class.cv v)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0006 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0007 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0008 : x ∉ ((Class.cv w)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((Class.cv w)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : z ∉ ((Class.cv w)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : f ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : w ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : v ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : g ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : v ∉ ((syn_wa (syn_wfun (.cv w)) (syn_wo (syn_wss (.cv w) (.cv g)) (syn_wss (.cv g) (.cv w))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_w, fresh_v_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : f ∉ ((syn_wa (syn_wfun (.cv w)) (syn_wo (syn_wss (.cv w) (.cv g)) (syn_wss (.cv g) (.cv w))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_w, dv_f_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : w ∉ ((syn_wa (syn_wfun (.cv f)) (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_f, fresh_w_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : g ∉ ((syn_wa (syn_wfun (.cv w)) (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_w, fresh_g_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : f ≠ g := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (show f ≠ g from (by exact dv_f_g))
  have dv_cache_0020 : g ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (show g ≠ w from (by exact fresh_g_ne_w))
  have dv_cache_0021 : v ∉ ((syn_wa (syn_wfun (.cv f)) (syn_wo (syn_wss (.cv w) (.cv f)) (syn_wss (.cv f) (.cv w))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_f, fresh_v_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : g ∉ ((syn_wa (syn_wfun (.cv f)) (syn_wo (syn_wss (.cv w) (.cv f)) (syn_wss (.cv f) (.cv w))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_f_g), fresh_g_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : f ∉ ((syn_wa (syn_wfun (.cv v)) (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_v, fresh_f_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : g ≠ f := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show g ≠ f from (by exact Ne.symm dv_f_g))
  have dv_cache_0025 : f ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (show f ≠ w from (by exact fresh_f_ne_w))
  have dv_cache_0026 : w ∉ ((syn_cop (.cv x) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : v ∉ ((syn_cop (.cv x) (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_x, fresh_v_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0028 : v ∉ ((syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (.cv w) A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_x, fresh_v_ne_y, fresh_v_ne_w, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0029 : w ∉ ((syn_wa (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)) (.classMem (.cv v) A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_z, fresh_w_ne_v, fresh_w_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0030 : v ∉ ((Wff.objEq y z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_y, fresh_v_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0031 : w ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (show w ≠ v from (by exact fresh_w_ne_v))
  have dv_cache_0032 : w ∉ ((Wff.objEq y z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_y, fresh_w_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0033 : z ∉ ((syn_wral f A (syn_wral g A (syn_wa (syn_wfun (.cv f)) (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_f, fresh_z_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0034 : x ∉ ((syn_wral f A (syn_wral g A (syn_wa (syn_wfun (.cv f)) (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_f, fresh_x_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0035 : y ∉ ((syn_wral f A (syn_wral g A (syn_wa (syn_wfun (.cv f)) (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_f, fresh_y_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0036 : x ∉ ((syn_cuni A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0037 : y ∉ ((syn_cuni A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0038 : z ∉ ((syn_cuni A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_r19_28av (syn_wfun (.cv f)) (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))) g A dv_cache_0001
  have p0001 :=
    @g_ralimi (syn_wa (syn_wfun (.cv f)) (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))) (syn_wral g A (syn_wa (syn_wfun (.cv f)) (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))) f A p0000
  have p0002 :=
    @g_ssel (.cv w) (.cv v) (syn_cop (.cv x) (.cv y))
  have p0003 :=
    @g_anim1d (syn_wss (.cv w) (.cv v)) (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv y)) (.cv v)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)) p0002
  have p0004 :=
    @g_dffun4 x y z (.cv v) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0005 :=
    @g_sp (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv v)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z)) z
  have p0006 :=
    @g_sps (.all z (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv v)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z))) (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv v)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z)) y p0005
  have p0007 :=
    @g_sps (.all y (.all z (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv v)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z)))) (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv v)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z)) x p0006
  have p0008 :=
    @g_sylbi (syn_wfun (.cv v)) (.all x (.all y (.all z (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv v)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z))))) (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv v)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z)) p0004 p0007
  have p0009 :=
    @g_syl9r (syn_wss (.cv w) (.cv v)) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv v)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (syn_wfun (.cv v)) (.objEq y z) p0003 p0008
  have p0010 :=
    @g_adantl (syn_wfun (.cv v)) (.imp (syn_wss (.cv w) (.cv v)) (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z))) (syn_wfun (.cv w)) p0009
  have p0011 :=
    @g_ssel (.cv v) (.cv w) (syn_cop (.cv x) (.cv z))
  have p0012 :=
    @g_anim2d (syn_wss (.cv v) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) p0011
  have p0013 :=
    @g_dffun4 x y z (.cv w) dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0014 :=
    @g_sp (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv w))) (.objEq y z)) z
  have p0015 :=
    @g_sps (.all z (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv w))) (.objEq y z))) (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv w))) (.objEq y z)) y p0014
  have p0016 :=
    @g_sps (.all y (.all z (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv w))) (.objEq y z)))) (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv w))) (.objEq y z)) x p0015
  have p0017 :=
    @g_sylbi (syn_wfun (.cv w)) (.all x (.all y (.all z (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv w))) (.objEq y z))))) (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv w))) (.objEq y z)) p0013 p0016
  have p0018 :=
    @g_syl9r (syn_wss (.cv v) (.cv w)) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv w))) (syn_wfun (.cv w)) (.objEq y z) p0012 p0017
  have p0019 :=
    @g_adantr (syn_wfun (.cv w)) (.imp (syn_wss (.cv v) (.cv w)) (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z))) (syn_wfun (.cv v)) p0018
  have p0020 :=
    @g_jaod (syn_wa (syn_wfun (.cv w)) (syn_wfun (.cv v))) (syn_wss (.cv w) (.cv v)) (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z)) (syn_wss (.cv v) (.cv w)) p0010 p0019
  have p0021 :=
    @g_imp (syn_wa (syn_wfun (.cv w)) (syn_wfun (.cv v))) (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w))) (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z)) p0020
  have p0022 :=
    @g_ralimi (syn_wa (syn_wa (syn_wfun (.cv w)) (syn_wfun (.cv v))) (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w)))) (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z)) v A p0021
  have p0023 :=
    @g_ralimi (syn_wral v A (syn_wa (syn_wa (syn_wfun (.cv w)) (syn_wfun (.cv v))) (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w))))) (syn_wral v A (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z))) w A p0022
  have p0024 :=
    @g_funeq (.cv f) (.cv w)
  have p0025 :=
    @g_sseq1 (.cv f) (.cv w) (.cv g)
  have p0026 :=
    @g_sseq2 (.cv f) (.cv w) (.cv g)
  have p0027_e00_recanon : Nominal.NPrf (.imp (.objEq f w) (syn_wb (syn_wss (.cv f) (.cv g)) (syn_wss (.cv w) (.cv g)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0025
  have p0027_e01_recanon : Nominal.NPrf (.imp (.objEq f w) (syn_wb (syn_wss (.cv g) (.cv f)) (syn_wss (.cv g) (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0026
  have p0027 :=
    @g_orbi12d (.objEq f w) (syn_wss (.cv f) (.cv g)) (syn_wss (.cv w) (.cv g)) (syn_wss (.cv g) (.cv f)) (syn_wss (.cv g) (.cv w)) p0027_e00_recanon p0027_e01_recanon
  have p0028_e00_recanon : Nominal.NPrf (.imp (.objEq f w) (syn_wb (syn_wfun (.cv f)) (syn_wfun (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wfun syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_ccom syn_copab syn_wex syn_ccnv syn_cid
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0024
  have p0028 :=
    @g_anbi12d (.objEq f w) (syn_wfun (.cv f)) (syn_wfun (.cv w)) (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))) (syn_wo (syn_wss (.cv w) (.cv g)) (syn_wss (.cv g) (.cv w))) p0028_e00_recanon p0027
  have p0029 :=
    @g_sseq2 (.cv g) (.cv v) (.cv w)
  have p0030 :=
    @g_sseq1 (.cv g) (.cv v) (.cv w)
  have p0031_e00_recanon : Nominal.NPrf (.imp (.objEq g v) (syn_wb (syn_wss (.cv w) (.cv g)) (syn_wss (.cv w) (.cv v)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0029
  have p0031_e01_recanon : Nominal.NPrf (.imp (.objEq g v) (syn_wb (syn_wss (.cv g) (.cv w)) (syn_wss (.cv v) (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0030
  have p0031 :=
    @g_orbi12d (.objEq g v) (syn_wss (.cv w) (.cv g)) (syn_wss (.cv w) (.cv v)) (syn_wss (.cv g) (.cv w)) (syn_wss (.cv v) (.cv w)) p0031_e00_recanon p0031_e01_recanon
  have p0032 :=
    @g_anbi2d (.objEq g v) (syn_wo (syn_wss (.cv w) (.cv g)) (syn_wss (.cv g) (.cv w))) (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w))) (syn_wfun (.cv w)) p0031
  have p0033 :=
    @g_cbvral2v (syn_wa (syn_wfun (.cv f)) (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))) (syn_wa (syn_wfun (.cv w)) (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w)))) (syn_wa (syn_wfun (.cv w)) (syn_wo (syn_wss (.cv w) (.cv g)) (syn_wss (.cv g) (.cv w)))) f g w v A A dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0011 dv_cache_0014 dv_cache_0012 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 p0028 p0032
  have p0034 :=
    @g_ralcom (syn_wa (syn_wfun (.cv f)) (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))) f g A A dv_cache_0014 dv_cache_0011 dv_cache_0019
  have p0035 :=
    @g_orcom (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))
  have p0036 :=
    @g_sseq1 (.cv g) (.cv w) (.cv f)
  have p0037 :=
    @g_sseq2 (.cv g) (.cv w) (.cv f)
  have p0038_e00_recanon : Nominal.NPrf (.imp (.objEq g w) (syn_wb (syn_wss (.cv g) (.cv f)) (syn_wss (.cv w) (.cv f)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0036
  have p0038_e01_recanon : Nominal.NPrf (.imp (.objEq g w) (syn_wb (syn_wss (.cv f) (.cv g)) (syn_wss (.cv f) (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0037
  have p0038 :=
    @g_orbi12d (.objEq g w) (syn_wss (.cv g) (.cv f)) (syn_wss (.cv w) (.cv f)) (syn_wss (.cv f) (.cv g)) (syn_wss (.cv f) (.cv w)) p0038_e00_recanon p0038_e01_recanon
  have p0039 :=
    @g_syl5bb (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))) (syn_wo (syn_wss (.cv g) (.cv f)) (syn_wss (.cv f) (.cv g))) (.objEq g w) (syn_wo (syn_wss (.cv w) (.cv f)) (syn_wss (.cv f) (.cv w))) p0035 p0038
  have p0040 :=
    @g_anbi2d (.objEq g w) (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))) (syn_wo (syn_wss (.cv w) (.cv f)) (syn_wss (.cv f) (.cv w))) (syn_wfun (.cv f)) p0039
  have p0041 :=
    @g_funeq (.cv f) (.cv v)
  have p0042 :=
    @g_sseq2 (.cv f) (.cv v) (.cv w)
  have p0043 :=
    @g_sseq1 (.cv f) (.cv v) (.cv w)
  have p0044_e00_recanon : Nominal.NPrf (.imp (.objEq f v) (syn_wb (syn_wss (.cv w) (.cv f)) (syn_wss (.cv w) (.cv v)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0042
  have p0044_e01_recanon : Nominal.NPrf (.imp (.objEq f v) (syn_wb (syn_wss (.cv f) (.cv w)) (syn_wss (.cv v) (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0043
  have p0044 :=
    @g_orbi12d (.objEq f v) (syn_wss (.cv w) (.cv f)) (syn_wss (.cv w) (.cv v)) (syn_wss (.cv f) (.cv w)) (syn_wss (.cv v) (.cv w)) p0044_e00_recanon p0044_e01_recanon
  have p0045_e00_recanon : Nominal.NPrf (.imp (.objEq f v) (syn_wb (syn_wfun (.cv f)) (syn_wfun (.cv v)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wfun syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_ccom syn_copab syn_wex syn_ccnv syn_cid
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0041
  have p0045 :=
    @g_anbi12d (.objEq f v) (syn_wfun (.cv f)) (syn_wfun (.cv v)) (syn_wo (syn_wss (.cv w) (.cv f)) (syn_wss (.cv f) (.cv w))) (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w))) p0045_e00_recanon p0044
  have p0046 :=
    @g_cbvral2v (syn_wa (syn_wfun (.cv f)) (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))) (syn_wa (syn_wfun (.cv v)) (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w)))) (syn_wa (syn_wfun (.cv f)) (syn_wo (syn_wss (.cv w) (.cv f)) (syn_wss (.cv f) (.cv w)))) g f w v A A dv_cache_0014 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0011 dv_cache_0012 dv_cache_0021 dv_cache_0022 dv_cache_0017 dv_cache_0023 dv_cache_0024 dv_cache_0025 p0040 p0045
  have p0047 :=
    @g_bitri (syn_wral f A (syn_wral g A (syn_wa (syn_wfun (.cv f)) (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))))) (syn_wral g A (syn_wral f A (syn_wa (syn_wfun (.cv f)) (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))))) (syn_wral w A (syn_wral v A (syn_wa (syn_wfun (.cv v)) (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w)))))) p0034 p0046
  have p0048 :=
    @g_anbi12i (syn_wral f A (syn_wral g A (syn_wa (syn_wfun (.cv f)) (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))))) (syn_wral w A (syn_wral v A (syn_wa (syn_wfun (.cv w)) (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w)))))) (syn_wral f A (syn_wral g A (syn_wa (syn_wfun (.cv f)) (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))))) (syn_wral w A (syn_wral v A (syn_wa (syn_wfun (.cv v)) (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w)))))) p0033 p0047
  have p0049 :=
    @g_anidm (syn_wral f A (syn_wral g A (syn_wa (syn_wfun (.cv f)) (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))
  have p0050 :=
    @g_anandir (syn_wfun (.cv w)) (syn_wfun (.cv v)) (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w)))
  have p0051 :=
    @g_n_2ralbii (syn_wa (syn_wa (syn_wfun (.cv w)) (syn_wfun (.cv v))) (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w)))) (syn_wa (syn_wa (syn_wfun (.cv w)) (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w)))) (syn_wa (syn_wfun (.cv v)) (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w))))) w v A A p0050
  have p0052 :=
    @g_r19_26_2 (syn_wa (syn_wfun (.cv w)) (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w)))) (syn_wa (syn_wfun (.cv v)) (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w)))) w v A A
  have p0053 :=
    @g_bitr2i (syn_wral w A (syn_wral v A (syn_wa (syn_wa (syn_wfun (.cv w)) (syn_wfun (.cv v))) (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w)))))) (syn_wral w A (syn_wral v A (syn_wa (syn_wa (syn_wfun (.cv w)) (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w)))) (syn_wa (syn_wfun (.cv v)) (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w))))))) (syn_wa (syn_wral w A (syn_wral v A (syn_wa (syn_wfun (.cv w)) (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w)))))) (syn_wral w A (syn_wral v A (syn_wa (syn_wfun (.cv v)) (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w))))))) p0051 p0052
  have p0054 :=
    @g_n_3bitr3i (syn_wa (syn_wral f A (syn_wral g A (syn_wa (syn_wfun (.cv f)) (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))))) (syn_wral f A (syn_wral g A (syn_wa (syn_wfun (.cv f)) (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))) (syn_wa (syn_wral w A (syn_wral v A (syn_wa (syn_wfun (.cv w)) (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w)))))) (syn_wral w A (syn_wral v A (syn_wa (syn_wfun (.cv v)) (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w))))))) (syn_wral f A (syn_wral g A (syn_wa (syn_wfun (.cv f)) (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))))) (syn_wral w A (syn_wral v A (syn_wa (syn_wa (syn_wfun (.cv w)) (syn_wfun (.cv v))) (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w)))))) p0048 p0049 p0053
  have p0055 :=
    @g_eluni w (syn_cop (.cv x) (.cv y)) A dv_cache_0026 dv_cache_0012
  have p0056 :=
    @g_eluni v (syn_cop (.cv x) (.cv z)) A dv_cache_0027 dv_cache_0013
  have p0057 :=
    @g_anbi12i (.classMem (syn_cop (.cv x) (.cv y)) (syn_cuni A)) (syn_wex w (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (.cv w) A))) (.classMem (syn_cop (.cv x) (.cv z)) (syn_cuni A)) (syn_wex v (syn_wa (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)) (.classMem (.cv v) A))) p0055 p0056
  have p0058 :=
    @g_eeanv (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (.cv w) A)) (syn_wa (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)) (.classMem (.cv v) A)) w v dv_cache_0028 dv_cache_0029
  have p0059 :=
    @g_an4 (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (.cv w) A) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)) (.classMem (.cv v) A)
  have p0060 :=
    @g_ancom (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A))
  have p0061 :=
    @g_bitri (syn_wa (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (.cv w) A)) (syn_wa (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)) (.classMem (.cv v) A))) (syn_wa (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A))) (syn_wa (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A)) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)))) p0059 p0060
  have p0062 :=
    @g_n_2exbii (syn_wa (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (.cv w) A)) (syn_wa (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)) (.classMem (.cv v) A))) (syn_wa (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A)) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)))) w v p0061
  have p0063 :=
    @g_n_3bitr2i (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_cuni A)) (.classMem (syn_cop (.cv x) (.cv z)) (syn_cuni A))) (syn_wa (syn_wex w (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (.cv w) A))) (syn_wex v (syn_wa (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)) (.classMem (.cv v) A)))) (syn_wex w (syn_wex v (syn_wa (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (.cv w) A)) (syn_wa (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)) (.classMem (.cv v) A))))) (syn_wex w (syn_wex v (syn_wa (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A)) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)))))) p0057 p0058 p0062
  have p0064 :=
    @g_imbi1i (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_cuni A)) (.classMem (syn_cop (.cv x) (.cv z)) (syn_cuni A))) (syn_wex w (syn_wex v (syn_wa (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A)) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)))))) (.objEq y z) p0063
  have p0065 :=
    @g_n_19_23v (syn_wa (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A)) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)))) (.objEq y z) v dv_cache_0030
  have p0066 :=
    @g_albii (.all v (.imp (syn_wa (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A)) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)))) (.objEq y z))) (.imp (syn_wex v (syn_wa (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A)) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))))) (.objEq y z)) w p0065
  have p0067 :=
    @g_impexp (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A)) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z)
  have p0068 :=
    @g_n_2albii (.imp (syn_wa (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A)) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)))) (.objEq y z)) (.imp (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A)) (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z))) w v p0067
  have p0069 :=
    @g_r2al (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z)) w v A A dv_cache_0013 dv_cache_0031
  have p0070 :=
    @g_bitr4i (.all w (.all v (.imp (syn_wa (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A)) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)))) (.objEq y z)))) (.all w (.all v (.imp (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A)) (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z))))) (syn_wral w A (syn_wral v A (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z)))) p0068 p0069
  have p0071 :=
    @g_n_19_23v (syn_wex v (syn_wa (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A)) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))))) (.objEq y z) w dv_cache_0032
  have p0072 :=
    @g_n_3bitr3ri (.all w (.all v (.imp (syn_wa (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A)) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)))) (.objEq y z)))) (.all w (.imp (syn_wex v (syn_wa (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A)) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))))) (.objEq y z))) (syn_wral w A (syn_wral v A (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z)))) (.imp (syn_wex w (syn_wex v (syn_wa (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A)) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)))))) (.objEq y z)) p0066 p0070 p0071
  have p0073 :=
    @g_bitri (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_cuni A)) (.classMem (syn_cop (.cv x) (.cv z)) (syn_cuni A))) (.objEq y z)) (.imp (syn_wex w (syn_wex v (syn_wa (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A)) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)))))) (.objEq y z)) (syn_wral w A (syn_wral v A (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z)))) p0064 p0072
  have p0074 :=
    @g_n_3imtr4i (syn_wral w A (syn_wral v A (syn_wa (syn_wa (syn_wfun (.cv w)) (syn_wfun (.cv v))) (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w)))))) (syn_wral w A (syn_wral v A (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z)))) (syn_wral f A (syn_wral g A (syn_wa (syn_wfun (.cv f)) (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))))) (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_cuni A)) (.classMem (syn_cop (.cv x) (.cv z)) (syn_cuni A))) (.objEq y z)) p0023 p0054 p0073
  have p0075 :=
    @g_alrimiv (syn_wral f A (syn_wral g A (syn_wa (syn_wfun (.cv f)) (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))))) (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_cuni A)) (.classMem (syn_cop (.cv x) (.cv z)) (syn_cuni A))) (.objEq y z)) z dv_cache_0033 p0074
  have p0076 :=
    @g_alrimivv (syn_wral f A (syn_wral g A (syn_wa (syn_wfun (.cv f)) (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))))) (.all z (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_cuni A)) (.classMem (syn_cop (.cv x) (.cv z)) (syn_cuni A))) (.objEq y z))) x y dv_cache_0034 dv_cache_0035 p0075
  have p0077 :=
    @g_syl (syn_wral f A (syn_wa (syn_wfun (.cv f)) (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))))) (syn_wral f A (syn_wral g A (syn_wa (syn_wfun (.cv f)) (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))))) (.all x (.all y (.all z (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_cuni A)) (.classMem (syn_cop (.cv x) (.cv z)) (syn_cuni A))) (.objEq y z))))) p0001 p0076
  have p0078 :=
    @g_dffun4 x y z (syn_cuni A) dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0079 :=
    @g_sylibr (syn_wral f A (syn_wa (syn_wfun (.cv f)) (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))))) (.all x (.all y (.all z (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_cuni A)) (.classMem (syn_cop (.cv x) (.cv z)) (syn_cuni A))) (.objEq y z))))) (syn_wfun (syn_cuni A)) p0077 p0078
  exact p0079

#print axioms g_fununi

end NFChoice.DirectNominalPrf.WPPReplay
