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
import NominalWPPReplayChunk011Compact001Part013

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

noncomputable def g_funcnvuni
    (A : Class) (f : Var) (g : Var) (dv_A_f : f ∉ A.fv) (dv_A_g : g ∉ A.fv) (dv_f_g : f ≠ g) :
    Nominal.NPrf (.imp (syn_wral f A (syn_wa (syn_wfun (syn_ccnv (.cv f))) (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))))) (syn_wfun (syn_ccnv (syn_cuni A)))) := by
  let proofSupport : Finset Var := A.fv ∪ ({f} : Finset Var) ∪ ({g} : Finset Var)
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  let v : Var := freshVar proofSupport 4
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
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
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
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
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_y_ne_w : y ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_w_ne_y : w ≠ y :=
    Ne.symm fresh_y_ne_w
  have fresh_y_ne_v : y ≠ v := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_v_ne_y : v ≠ y :=
    Ne.symm fresh_y_ne_v
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_x_ne_w : x ≠ w := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_w_ne_x : w ≠ x :=
    Ne.symm fresh_x_ne_w
  have fresh_x_ne_v : x ≠ v := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_v_ne_x : v ≠ x :=
    Ne.symm fresh_x_ne_v
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
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : v ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : v ∉ ((Wff.classEq (.cv z) (syn_ccnv (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_z, fresh_v_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classEq (.cv z) (syn_ccnv (.cv v)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, fresh_x_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : g ∉ ((Wff.classEq (.cv f) (.cv v))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_f_g), fresh_g_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : f ∉ ((Class.cv v)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : f ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : f ∉ ((syn_wa (syn_wfun (syn_ccnv (.cv v))) (syn_wral g A (syn_wo (syn_wss (.cv v) (.cv g)) (syn_wss (.cv g) (.cv v)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_v, dv_A_f, dv_f_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : g ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : g ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : g ∉ ((syn_wo (syn_wss (.cv v) (.cv x)) (syn_wss (.cv x) (.cv v)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_v, fresh_g_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((Wff.imp (.classEq (.cv z) (syn_ccnv (.cv v))) (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, fresh_x_ne_v, fresh_x_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((syn_wral g A (syn_wo (syn_wss (.cv v) (.cv g)) (syn_wss (.cv g) (.cv v))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_v, fresh_x_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : w ∉ ((syn_wral g A (syn_wo (syn_wss (.cv v) (.cv g)) (syn_wss (.cv g) (.cv v))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, fresh_w_ne_v, fresh_w_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : w ∉ ((Wff.classEq (.cv z) (syn_ccnv (.cv v)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_z, fresh_w_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : v ∉ ((syn_wa (syn_wfun (.cv z)) (.all w (.imp (syn_wrex x A (.classEq (.cv w) (syn_ccnv (.cv x)))) (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_z, fresh_v_not_A, fresh_v_ne_w, fresh_v_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : v ∉ ((syn_wral f A (syn_wa (syn_wfun (syn_ccnv (.cv f))) (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, fresh_v_ne_f, fresh_v_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : z ∉ ((syn_wral f A (syn_wa (syn_wfun (syn_ccnv (.cv f))) (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_f, fresh_z_ne_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : x ∉ ((Wff.classEq (.cv y) (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : y ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : y ∉ ((syn_wrex x A (.classEq (.cv z) (syn_ccnv (.cv x))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_z, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : x ∉ ((Wff.classEq (.cv y) (.cv w))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, fresh_x_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : y ∉ ((syn_wrex x A (.classEq (.cv w) (syn_ccnv (.cv x))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_w, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : w ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show w ≠ y from (by exact fresh_w_ne_y))
  have dv_cache_0025 : z ∉ ((Class.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_y, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : w ∉ ((Class.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, fresh_w_ne_y, fresh_w_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : z ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have dv_cache_0028 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0029 : y ∉ ((syn_ccnv (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0030 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_cnveq (.cv x) (.cv v)
  have p0001 :=
    @g_eqeq2d (.classEq (.cv x) (.cv v)) (syn_ccnv (.cv x)) (syn_ccnv (.cv v)) (.cv z) p0000
  have p0002_e00_recanon : Nominal.NPrf (.imp (.objEq x v) (syn_wb (.classEq (.cv z) (syn_ccnv (.cv x))) (.classEq (.cv z) (syn_ccnv (.cv v))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_ccnv syn_copab syn_wex syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0001
  have p0002 :=
    @g_cbvrexv (.classEq (.cv z) (syn_ccnv (.cv x))) (.classEq (.cv z) (syn_ccnv (.cv v))) x v A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 p0002_e00_recanon
  have p0003 :=
    @g_cnveq (.cv f) (.cv v)
  have p0004 :=
    @g_funeqd (.classEq (.cv f) (.cv v)) (syn_ccnv (.cv f)) (syn_ccnv (.cv v)) p0003
  have p0005 :=
    @g_sseq1 (.cv f) (.cv v) (.cv g)
  have p0006 :=
    @g_sseq2 (.cv f) (.cv v) (.cv g)
  have p0007 :=
    @g_orbi12d (.classEq (.cv f) (.cv v)) (syn_wss (.cv f) (.cv g)) (syn_wss (.cv v) (.cv g)) (syn_wss (.cv g) (.cv f)) (syn_wss (.cv g) (.cv v)) p0005 p0006
  have p0008 :=
    @g_ralbidv (.classEq (.cv f) (.cv v)) (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))) (syn_wo (syn_wss (.cv v) (.cv g)) (syn_wss (.cv g) (.cv v))) g A dv_cache_0005 p0007
  have p0009 :=
    @g_anbi12d (.classEq (.cv f) (.cv v)) (syn_wfun (syn_ccnv (.cv f))) (syn_wfun (syn_ccnv (.cv v))) (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))) (syn_wral g A (syn_wo (syn_wss (.cv v) (.cv g)) (syn_wss (.cv g) (.cv v)))) p0004 p0008
  have p0010 :=
    @g_rspcv (syn_wa (syn_wfun (syn_ccnv (.cv f))) (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))) (syn_wa (syn_wfun (syn_ccnv (.cv v))) (syn_wral g A (syn_wo (syn_wss (.cv v) (.cv g)) (syn_wss (.cv g) (.cv v))))) f (.cv v) A dv_cache_0006 dv_cache_0007 dv_cache_0008 p0009
  have p0011 :=
    @g_funeq (.cv z) (syn_ccnv (.cv v))
  have p0012 :=
    @g_biimprcd (.classEq (.cv z) (syn_ccnv (.cv v))) (syn_wfun (.cv z)) (syn_wfun (syn_ccnv (.cv v))) p0011
  have p0013 :=
    @g_sseq2 (.cv g) (.cv x) (.cv v)
  have p0014 :=
    @g_sseq1 (.cv g) (.cv x) (.cv v)
  have p0015 :=
    @g_orbi12d (.classEq (.cv g) (.cv x)) (syn_wss (.cv v) (.cv g)) (syn_wss (.cv v) (.cv x)) (syn_wss (.cv g) (.cv v)) (syn_wss (.cv x) (.cv v)) p0013 p0014
  have p0016 :=
    @g_rspcv (syn_wo (syn_wss (.cv v) (.cv g)) (syn_wss (.cv g) (.cv v))) (syn_wo (syn_wss (.cv v) (.cv x)) (syn_wss (.cv x) (.cv v))) g (.cv x) A dv_cache_0009 dv_cache_0010 dv_cache_0011 p0015
  have p0017 :=
    @g_cnvss (.cv v) (.cv x)
  have p0018 :=
    @g_cnvss (.cv x) (.cv v)
  have p0019 :=
    @g_orim12i (syn_wss (.cv v) (.cv x)) (syn_wss (syn_ccnv (.cv v)) (syn_ccnv (.cv x))) (syn_wss (.cv x) (.cv v)) (syn_wss (syn_ccnv (.cv x)) (syn_ccnv (.cv v))) p0017 p0018
  have p0020 :=
    @g_sseq12 (.cv z) (syn_ccnv (.cv v)) (.cv w) (syn_ccnv (.cv x))
  have p0021 :=
    @g_ancoms (.classEq (.cv z) (syn_ccnv (.cv v))) (.classEq (.cv w) (syn_ccnv (.cv x))) (syn_wb (syn_wss (.cv z) (.cv w)) (syn_wss (syn_ccnv (.cv v)) (syn_ccnv (.cv x)))) p0020
  have p0022 :=
    @g_sseq12 (.cv w) (syn_ccnv (.cv x)) (.cv z) (syn_ccnv (.cv v))
  have p0023 :=
    @g_orbi12d (syn_wa (.classEq (.cv w) (syn_ccnv (.cv x))) (.classEq (.cv z) (syn_ccnv (.cv v)))) (syn_wss (.cv z) (.cv w)) (syn_wss (syn_ccnv (.cv v)) (syn_ccnv (.cv x))) (syn_wss (.cv w) (.cv z)) (syn_wss (syn_ccnv (.cv x)) (syn_ccnv (.cv v))) p0021 p0022
  have p0024 :=
    @g_syl5ibrcom (syn_wo (syn_wss (.cv v) (.cv x)) (syn_wss (.cv x) (.cv v))) (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z))) (syn_wa (.classEq (.cv w) (syn_ccnv (.cv x))) (.classEq (.cv z) (syn_ccnv (.cv v)))) (syn_wo (syn_wss (syn_ccnv (.cv v)) (syn_ccnv (.cv x))) (syn_wss (syn_ccnv (.cv x)) (syn_ccnv (.cv v)))) p0019 p0023
  have p0025 :=
    @g_exp3a (syn_wo (syn_wss (.cv v) (.cv x)) (syn_wss (.cv x) (.cv v))) (.classEq (.cv w) (syn_ccnv (.cv x))) (.classEq (.cv z) (syn_ccnv (.cv v))) (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z))) p0024
  have p0026 :=
    @g_syl6com (.classMem (.cv x) A) (syn_wral g A (syn_wo (syn_wss (.cv v) (.cv g)) (syn_wss (.cv g) (.cv v)))) (syn_wo (syn_wss (.cv v) (.cv x)) (syn_wss (.cv x) (.cv v))) (.imp (.classEq (.cv w) (syn_ccnv (.cv x))) (.imp (.classEq (.cv z) (syn_ccnv (.cv v))) (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z))))) p0016 p0025
  have p0027 :=
    @g_rexlimdv (syn_wral g A (syn_wo (syn_wss (.cv v) (.cv g)) (syn_wss (.cv g) (.cv v)))) (.classEq (.cv w) (syn_ccnv (.cv x))) (.imp (.classEq (.cv z) (syn_ccnv (.cv v))) (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z)))) x A dv_cache_0012 dv_cache_0013 p0026
  have p0028 :=
    @g_com23 (syn_wral g A (syn_wo (syn_wss (.cv v) (.cv g)) (syn_wss (.cv g) (.cv v)))) (syn_wrex x A (.classEq (.cv w) (syn_ccnv (.cv x)))) (.classEq (.cv z) (syn_ccnv (.cv v))) (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z))) p0027
  have p0029 :=
    @g_alrimdv (syn_wral g A (syn_wo (syn_wss (.cv v) (.cv g)) (syn_wss (.cv g) (.cv v)))) (.classEq (.cv z) (syn_ccnv (.cv v))) (.imp (syn_wrex x A (.classEq (.cv w) (syn_ccnv (.cv x)))) (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z)))) w dv_cache_0014 dv_cache_0015 p0028
  have p0030 :=
    @g_anim12ii (syn_wfun (syn_ccnv (.cv v))) (.classEq (.cv z) (syn_ccnv (.cv v))) (syn_wfun (.cv z)) (syn_wral g A (syn_wo (syn_wss (.cv v) (.cv g)) (syn_wss (.cv g) (.cv v)))) (.all w (.imp (syn_wrex x A (.classEq (.cv w) (syn_ccnv (.cv x)))) (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z))))) p0012 p0029
  have p0031 :=
    @g_syl6com (.classMem (.cv v) A) (syn_wral f A (syn_wa (syn_wfun (syn_ccnv (.cv f))) (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))))) (syn_wa (syn_wfun (syn_ccnv (.cv v))) (syn_wral g A (syn_wo (syn_wss (.cv v) (.cv g)) (syn_wss (.cv g) (.cv v))))) (.imp (.classEq (.cv z) (syn_ccnv (.cv v))) (syn_wa (syn_wfun (.cv z)) (.all w (.imp (syn_wrex x A (.classEq (.cv w) (syn_ccnv (.cv x)))) (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z))))))) p0010 p0030
  have p0032 :=
    @g_rexlimdv (syn_wral f A (syn_wa (syn_wfun (syn_ccnv (.cv f))) (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))))) (.classEq (.cv z) (syn_ccnv (.cv v))) (syn_wa (syn_wfun (.cv z)) (.all w (.imp (syn_wrex x A (.classEq (.cv w) (syn_ccnv (.cv x)))) (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z)))))) v A dv_cache_0016 dv_cache_0017 p0031
  have p0033 :=
    @g_syl5bi (syn_wrex x A (.classEq (.cv z) (syn_ccnv (.cv x)))) (syn_wrex v A (.classEq (.cv z) (syn_ccnv (.cv v)))) (syn_wral f A (syn_wa (syn_wfun (syn_ccnv (.cv f))) (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))))) (syn_wa (syn_wfun (.cv z)) (.all w (.imp (syn_wrex x A (.classEq (.cv w) (syn_ccnv (.cv x)))) (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z)))))) p0002 p0032
  have p0034 :=
    @g_alrimiv (syn_wral f A (syn_wa (syn_wfun (syn_ccnv (.cv f))) (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))))) (.imp (syn_wrex x A (.classEq (.cv z) (syn_ccnv (.cv x)))) (syn_wa (syn_wfun (.cv z)) (.all w (.imp (syn_wrex x A (.classEq (.cv w) (syn_ccnv (.cv x)))) (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z))))))) z dv_cache_0018 p0033
  have p0035 :=
    (by simpa [syn_wb, syn_wral] using (Nominal.biimpRefl (syn_wral z (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x))))) (syn_wa (syn_wfun (.cv z)) (syn_wral w (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x))))) (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z))))))))
  have p0036 :=
    @g_vex z
  have p0037 :=
    @g_eqeq1 (.cv y) (.cv z) (syn_ccnv (.cv x))
  have p0038 :=
    @g_rexbidv (.classEq (.cv y) (.cv z)) (.classEq (.cv y) (syn_ccnv (.cv x))) (.classEq (.cv z) (syn_ccnv (.cv x))) x A dv_cache_0019 p0037
  have p0039 :=
    @g_elab (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x)))) (syn_wrex x A (.classEq (.cv z) (syn_ccnv (.cv x)))) y (.cv z) dv_cache_0020 dv_cache_0021 p0036 p0038
  have p0040 :=
    @g_eqeq1 (.cv y) (.cv w) (syn_ccnv (.cv x))
  have p0041 :=
    @g_rexbidv (.classEq (.cv y) (.cv w)) (.classEq (.cv y) (syn_ccnv (.cv x))) (.classEq (.cv w) (syn_ccnv (.cv x))) x A dv_cache_0022 p0040
  have p0042_e00_recanon : Nominal.NPrf (.imp (.objEq y w) (syn_wb (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x)))) (syn_wrex x A (.classEq (.cv w) (syn_ccnv (.cv x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wrex syn_wex syn_wa syn_ccnv syn_copab syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0041
  have p0042 :=
    @g_ralab (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x)))) (syn_wrex x A (.classEq (.cv w) (syn_ccnv (.cv x)))) (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z))) w y dv_cache_0023 dv_cache_0024 p0042_e00_recanon
  have p0043 :=
    @g_anbi2i (syn_wral w (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x))))) (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z)))) (.all w (.imp (syn_wrex x A (.classEq (.cv w) (syn_ccnv (.cv x)))) (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z))))) (syn_wfun (.cv z)) p0042
  have p0044 :=
    @g_imbi12i (.classMem (.cv z) (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x)))))) (syn_wrex x A (.classEq (.cv z) (syn_ccnv (.cv x)))) (syn_wa (syn_wfun (.cv z)) (syn_wral w (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x))))) (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z))))) (syn_wa (syn_wfun (.cv z)) (.all w (.imp (syn_wrex x A (.classEq (.cv w) (syn_ccnv (.cv x)))) (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z)))))) p0039 p0043
  have p0045 :=
    @g_albii (.imp (.classMem (.cv z) (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x)))))) (syn_wa (syn_wfun (.cv z)) (syn_wral w (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x))))) (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z)))))) (.imp (syn_wrex x A (.classEq (.cv z) (syn_ccnv (.cv x)))) (syn_wa (syn_wfun (.cv z)) (.all w (.imp (syn_wrex x A (.classEq (.cv w) (syn_ccnv (.cv x)))) (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z))))))) z p0044
  have p0046 :=
    @g_bitr2i (syn_wral z (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x))))) (syn_wa (syn_wfun (.cv z)) (syn_wral w (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x))))) (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z)))))) (.all z (.imp (.classMem (.cv z) (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x)))))) (syn_wa (syn_wfun (.cv z)) (syn_wral w (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x))))) (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z))))))) (.all z (.imp (syn_wrex x A (.classEq (.cv z) (syn_ccnv (.cv x)))) (syn_wa (syn_wfun (.cv z)) (.all w (.imp (syn_wrex x A (.classEq (.cv w) (syn_ccnv (.cv x)))) (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z)))))))) p0035 p0045
  have p0047 :=
    @g_sylib (syn_wral f A (syn_wa (syn_wfun (syn_ccnv (.cv f))) (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))))) (.all z (.imp (syn_wrex x A (.classEq (.cv z) (syn_ccnv (.cv x)))) (syn_wa (syn_wfun (.cv z)) (.all w (.imp (syn_wrex x A (.classEq (.cv w) (syn_ccnv (.cv x)))) (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z)))))))) (syn_wral z (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x))))) (syn_wa (syn_wfun (.cv z)) (syn_wral w (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x))))) (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z)))))) p0034 p0046
  have p0048 :=
    @g_fununi (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x))))) z w dv_cache_0025 dv_cache_0026 dv_cache_0027
  have p0049 :=
    @g_syl (syn_wral f A (syn_wa (syn_wfun (syn_ccnv (.cv f))) (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))))) (syn_wral z (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x))))) (syn_wa (syn_wfun (.cv z)) (syn_wral w (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x))))) (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z)))))) (syn_wfun (syn_cuni (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x))))))) p0047 p0048
  have p0050 :=
    @g_cnvuni x A dv_cache_0001
  have p0051 :=
    @g_vex x
  have p0052 :=
    @g_cnvex (.cv x) p0051
  have p0053 :=
    @g_dfiun2 x y A (syn_ccnv (.cv x)) dv_cache_0028 dv_cache_0029 dv_cache_0030 p0052
  have p0054 :=
    @g_eqtri (syn_ccnv (syn_cuni A)) (syn_ciun x A (syn_ccnv (.cv x))) (syn_cuni (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x)))))) p0050 p0053
  have p0055 :=
    @g_funeqi (syn_ccnv (syn_cuni A)) (syn_cuni (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x)))))) p0054
  have p0056 :=
    @g_sylibr (syn_wral f A (syn_wa (syn_wfun (syn_ccnv (.cv f))) (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))))) (syn_wfun (syn_cuni (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x))))))) (syn_wfun (syn_ccnv (syn_cuni A))) p0049 p0055
  exact p0056

noncomputable def g_fun11uni
    (A : Class) (f : Var) (g : Var) (dv_A_f : f ∉ A.fv) (dv_A_g : g ∉ A.fv) (dv_f_g : f ≠ g) :
    Nominal.NPrf (.imp (syn_wral f A (syn_wa (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f)))) (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))))) (syn_wa (syn_wfun (syn_cuni A)) (syn_wfun (syn_ccnv (syn_cuni A))))) := by
  let proofSupport : Finset Var := A.fv ∪ ({f} : Finset Var) ∪ ({g} : Finset Var)
  have dv_cache_0001 : f ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : g ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_g, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : f ≠ g := by
    clear dv_cache_0001 dv_cache_0002
    exact (show f ≠ g from (by exact dv_f_g))
  have p0000 :=
    @g_simpl (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f)))
  have p0001 :=
    @g_anim1i (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f)))) (syn_wfun (.cv f)) (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))) p0000
  have p0002 :=
    @g_ralimi (syn_wa (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f)))) (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))) (syn_wa (syn_wfun (.cv f)) (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))) f A p0001
  have p0003 :=
    @g_fununi A f g dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0004 :=
    @g_syl (syn_wral f A (syn_wa (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f)))) (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))))) (syn_wral f A (syn_wa (syn_wfun (.cv f)) (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))))) (syn_wfun (syn_cuni A)) p0002 p0003
  have p0005 :=
    @g_simpr (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f)))
  have p0006 :=
    @g_anim1i (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f)))) (syn_wfun (syn_ccnv (.cv f))) (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))) p0005
  have p0007 :=
    @g_ralimi (syn_wa (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f)))) (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))) (syn_wa (syn_wfun (syn_ccnv (.cv f))) (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))) f A p0006
  have p0008 :=
    @g_funcnvuni A f g dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0009 :=
    @g_syl (syn_wral f A (syn_wa (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f)))) (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))))) (syn_wral f A (syn_wa (syn_wfun (syn_ccnv (.cv f))) (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))))) (syn_wfun (syn_ccnv (syn_cuni A))) p0007 p0008
  have p0010 :=
    @g_jca (syn_wral f A (syn_wa (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f)))) (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))))) (syn_wfun (syn_cuni A)) (syn_wfun (syn_ccnv (syn_cuni A))) p0004 p0009
  exact p0010

noncomputable def g_funres11
    (A : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfun (syn_ccnv F)) (syn_wfun (syn_ccnv (syn_cres F A)))) := by
  let proofSupport : Finset Var := A.fv ∪ F.fv
  have p0000 :=
    @g_resss F A
  have p0001 :=
    @g_cnvss (syn_cres F A) F
  have p0002 :=
    @g_funss (syn_ccnv (syn_cres F A)) (syn_ccnv F)
  have p0003 :=
    @g_mp2b (syn_wss (syn_cres F A) F) (syn_wss (syn_ccnv (syn_cres F A)) (syn_ccnv F)) (.imp (syn_wfun (syn_ccnv F)) (syn_wfun (syn_ccnv (syn_cres F A)))) p0000 p0001 p0002
  exact p0003

noncomputable def g_funcnvres
    (A : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfun (syn_ccnv F)) (.classEq (syn_ccnv (syn_cres F A)) (syn_cres (syn_ccnv F) (syn_cima F A)))) := by
  let proofSupport : Finset Var := A.fv ∪ F.fv
  have p0000 :=
    @g_dfima3 F A
  have p0001 :=
    @g_dfrn4 (syn_cres F A)
  have p0002 :=
    @g_eqtri (syn_cima F A) (syn_crn (syn_cres F A)) (syn_cdm (syn_ccnv (syn_cres F A))) p0000 p0001
  have p0003 :=
    @g_reseq2i (syn_cima F A) (syn_cdm (syn_ccnv (syn_cres F A))) (syn_ccnv F) p0002
  have p0004 :=
    @g_resss F A
  have p0005 :=
    @g_cnvss (syn_cres F A) F
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_funssres (syn_ccnv F) (syn_ccnv (syn_cres F A))
  have p0008 :=
    @g_mpan2 (syn_wfun (syn_ccnv F)) (syn_wss (syn_ccnv (syn_cres F A)) (syn_ccnv F)) (.classEq (syn_cres (syn_ccnv F) (syn_cdm (syn_ccnv (syn_cres F A)))) (syn_ccnv (syn_cres F A))) p0006 p0007
  have p0009 :=
    @g_syl5req (syn_wfun (syn_ccnv F)) (syn_cres (syn_ccnv F) (syn_cima F A)) (syn_cres (syn_ccnv F) (syn_cdm (syn_ccnv (syn_cres F A)))) (syn_ccnv (syn_cres F A)) p0003 p0008
  exact p0009

noncomputable def g_cnvresid
    (A : Class) :
    Nominal.NPrf (.classEq (syn_ccnv (syn_cres (syn_cid) A)) (syn_cres (syn_cid) A)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_cnvi
  have p0001 :=
    @g_eqcomi (syn_ccnv (syn_cid)) (syn_cid) p0000
  have p0002 :=
    @g_funi
  have p0003 :=
    @g_funeq (syn_cid) (syn_ccnv (syn_cid))
  have p0004 :=
    @g_mpbii (.classEq (syn_cid) (syn_ccnv (syn_cid))) (syn_wfun (syn_cid)) (syn_wfun (syn_ccnv (syn_cid))) p0002 p0003
  have p0005 :=
    Nominal.mp p0001 p0004
  have p0006 :=
    @g_funcnvres A (syn_cid)
  have p0007 :=
    @g_cnvi
  have p0008 :=
    @g_imai A
  have p0009 :=
    @g_reseq12i (syn_ccnv (syn_cid)) (syn_cid) (syn_cima (syn_cid) A) A p0007 p0008
  have p0010 :=
    @g_syl6eq (syn_wfun (syn_ccnv (syn_cid))) (syn_ccnv (syn_cres (syn_cid) A)) (syn_cres (syn_ccnv (syn_cid)) (syn_cima (syn_cid) A)) (syn_cres (syn_cid) A) p0006 p0009
  have p0011 :=
    Nominal.mp p0005 p0010
  exact p0011

noncomputable def g_funcnvres2
    (A : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfun F) (.classEq (syn_ccnv (syn_cres (syn_ccnv F) A)) (syn_cres F (syn_cima (syn_ccnv F) A)))) := by
  let proofSupport : Finset Var := A.fv ∪ F.fv
  have p0000 :=
    @g_cnvcnv F
  have p0001 :=
    @g_funeqi (syn_ccnv (syn_ccnv F)) F p0000
  have p0002 :=
    @g_funcnvres A (syn_ccnv F)
  have p0003 :=
    @g_sylbir (syn_wfun F) (syn_wfun (syn_ccnv (syn_ccnv F))) (.classEq (syn_ccnv (syn_cres (syn_ccnv F) A)) (syn_cres (syn_ccnv (syn_ccnv F)) (syn_cima (syn_ccnv F) A))) p0001 p0002
  have p0004 :=
    @g_reseq1i (syn_ccnv (syn_ccnv F)) F (syn_cima (syn_ccnv F) A) p0000
  have p0005 :=
    @g_syl6eq (syn_wfun F) (syn_ccnv (syn_cres (syn_ccnv F) A)) (syn_cres (syn_ccnv (syn_ccnv F)) (syn_cima (syn_ccnv F) A)) (syn_cres F (syn_cima (syn_ccnv F) A)) p0003 p0004
  exact p0005

noncomputable def g_funimacnv
    (A : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfun F) (.classEq (syn_cima F (syn_cima (syn_ccnv F) A)) (syn_cin A (syn_crn F)))) := by
  let proofSupport : Finset Var := A.fv ∪ F.fv
  have p0000 :=
    @g_funcnvres2 A F
  have p0001 :=
    @g_rneqd (syn_wfun F) (syn_ccnv (syn_cres (syn_ccnv F) A)) (syn_cres F (syn_cima (syn_ccnv F) A)) p0000
  have p0002 :=
    @g_dfima3 F (syn_cima (syn_ccnv F) A)
  have p0003 :=
    @g_syl6reqr (syn_wfun F) (syn_crn (syn_ccnv (syn_cres (syn_ccnv F) A))) (syn_crn (syn_cres F (syn_cima (syn_ccnv F) A))) (syn_cima F (syn_cima (syn_ccnv F) A)) p0001 p0002
  have p0004 :=
    @g_dfrn4 F
  have p0005 :=
    @g_ineq2i (syn_crn F) (syn_cdm (syn_ccnv F)) A p0004
  have p0006 :=
    @g_dmres (syn_ccnv F) A
  have p0007 :=
    (by simpa [syn_cdm] using (Nominal.classEqRefl (syn_cdm (syn_cres (syn_ccnv F) A))))
  have p0008 :=
    @g_n_3eqtr2ri (syn_cin A (syn_crn F)) (syn_cin A (syn_cdm (syn_ccnv F))) (syn_cdm (syn_cres (syn_ccnv F) A)) (syn_crn (syn_ccnv (syn_cres (syn_ccnv F) A))) p0005 p0006 p0007
  have p0009 :=
    @g_syl6eq (syn_wfun F) (syn_cima F (syn_cima (syn_ccnv F) A)) (syn_crn (syn_ccnv (syn_cres (syn_ccnv F) A))) (syn_cin A (syn_crn F)) p0003 p0008
  exact p0009

noncomputable def g_funimass2
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wfun F) (syn_wss A (syn_cima (syn_ccnv F) B))) (syn_wss (syn_cima F A) B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_imass2 A (syn_cima (syn_ccnv F) B) F
  have p0001 :=
    @g_funimacnv B F
  have p0002 :=
    @g_sseq2d (syn_wfun F) (syn_cima F (syn_cima (syn_ccnv F) B)) (syn_cin B (syn_crn F)) (syn_cima F A) p0001
  have p0003 :=
    @g_inss1 B (syn_crn F)
  have p0004 :=
    @g_sstr2 (syn_cima F A) (syn_cin B (syn_crn F)) B
  have p0005 :=
    @g_mpi (syn_wss (syn_cima F A) (syn_cin B (syn_crn F))) (syn_wss (syn_cin B (syn_crn F)) B) (syn_wss (syn_cima F A) B) p0003 p0004
  have p0006 :=
    @g_syl6bi (syn_wfun F) (syn_wss (syn_cima F A) (syn_cima F (syn_cima (syn_ccnv F) B))) (syn_wss (syn_cima F A) (syn_cin B (syn_crn F))) (syn_wss (syn_cima F A) B) p0002 p0005
  have p0007 :=
    @g_imp (syn_wfun F) (syn_wss (syn_cima F A) (syn_cima F (syn_cima (syn_ccnv F) B))) (syn_wss (syn_cima F A) B) p0006
  have p0008 :=
    @g_sylan2 (syn_wss A (syn_cima (syn_ccnv F) B)) (syn_wfun F) (syn_wss (syn_cima F A) (syn_cima F (syn_cima (syn_ccnv F) B))) (syn_wss (syn_cima F A) B) p0000 p0007
  exact p0008

#print axioms g_funimass2

end NFChoice.DirectNominalPrf.WPPReplay
