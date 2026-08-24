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
import NominalWPPReplayChunk011Compact001Part010

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

noncomputable def g_dffun6f
    (x : Var) (y : Var) (A : Class) (dv_x_y : x ≠ y) (hyp_dffun6f_1 : Nominal.NPrf (syn_wnfc x A)) (hyp_dffun6f_2 : Nominal.NPrf (syn_wnfc y A)) :
    Nominal.NPrf (syn_wb (syn_wfun A) (.all x (syn_wmo y (syn_wbr (.cv x) A (.cv y))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv
  let w : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
  let u : Var := freshVar proofSupport 2
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_w : y ≠ w :=
    Ne.symm fresh_w_ne_y
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_v : v ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_v_ne_x : v ≠ x := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_v : x ≠ v :=
    Ne.symm fresh_v_ne_x
  have fresh_v_ne_y : v ≠ y := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_v : y ≠ v :=
    Ne.symm fresh_v_ne_y
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_u_ne_x : u ≠ x := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_u : x ≠ u :=
    Ne.symm fresh_u_ne_x
  have fresh_u_ne_y : u ≠ y := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_u : y ≠ u :=
    Ne.symm fresh_u_ne_y
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_w_ne_v : w ≠ v := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_v_ne_w : v ≠ w :=
    Ne.symm fresh_w_ne_v
  have fresh_w_ne_u : w ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_u_ne_w : u ≠ w :=
    Ne.symm fresh_w_ne_u
  have fresh_v_ne_u : v ≠ u := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_u_ne_v : u ≠ v :=
    Ne.symm fresh_v_ne_u
  have dv_cache_0001 : w ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : v ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : u ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : w ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show w ≠ v from (by exact fresh_w_ne_v))
  have dv_cache_0005 : w ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show w ≠ u from (by exact fresh_w_ne_u))
  have dv_cache_0006 : v ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show v ≠ u from (by exact fresh_v_ne_u))
  have dv_cache_0007 : y ∉ ((Class.cv w)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((Class.cv v)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : v ∉ ((syn_wbr (.cv w) A (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_w, fresh_v_ne_y, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : u ∉ ((syn_wbr (.cv w) A (.cv v))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_w, fresh_u_ne_v, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((Class.cv w)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_x_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : w ∉ ((syn_wmo y (syn_wbr (.cv x) A (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wmo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, fresh_w_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : y ∉ ((Wff.objEq w x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_w, (Ne.symm dv_x_y), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_dffun3 w v u A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_nfcv y (.cv w) dv_cache_0007
  have p0002 :=
    @g_nfcv y (.cv v) dv_cache_0008
  have p0003 :=
    @g_nfbr y (.cv w) (.cv v) A p0001 hyp_dffun6f_2 p0002
  have p0004 :=
    @g_nfv (syn_wbr (.cv w) A (.cv y)) v dv_cache_0009
  have p0005 :=
    @g_breq2 (.cv v) (.cv y) (.cv w) A
  have p0006_e02_recanon : Nominal.NPrf (.imp (.objEq v y) (syn_wb (syn_wbr (.cv w) A (.cv v)) (syn_wbr (.cv w) A (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0005
  have p0006 :=
    @g_cbvmo (syn_wbr (.cv w) A (.cv v)) (syn_wbr (.cv w) A (.cv y)) v y p0003 p0004 p0006_e02_recanon
  have p0007 :=
    @g_albii (syn_wmo v (syn_wbr (.cv w) A (.cv v))) (syn_wmo y (syn_wbr (.cv w) A (.cv y))) w p0006
  have p0008 :=
    @g_nfv (syn_wbr (.cv w) A (.cv v)) u dv_cache_0010
  have p0009 :=
    @g_mo2 (syn_wbr (.cv w) A (.cv v)) v u dv_cache_0006 p0008
  have p0010 :=
    @g_albii (syn_wmo v (syn_wbr (.cv w) A (.cv v))) (syn_wex u (.all v (.imp (syn_wbr (.cv w) A (.cv v)) (.objEq v u)))) w p0009
  have p0011 :=
    @g_nfcv x (.cv w) dv_cache_0011
  have p0012 :=
    @g_nfcv x (.cv y) dv_cache_0012
  have p0013 :=
    @g_nfbr x (.cv w) (.cv y) A p0011 hyp_dffun6f_1 p0012
  have p0014 :=
    @g_nfmo (syn_wbr (.cv w) A (.cv y)) x y p0013
  have p0015 :=
    @g_nfv (syn_wmo y (syn_wbr (.cv x) A (.cv y))) w dv_cache_0013
  have p0016 :=
    @g_breq1 (.cv w) (.cv x) (.cv y) A
  have p0017_e00_recanon : Nominal.NPrf (.imp (.objEq w x) (syn_wb (syn_wbr (.cv w) A (.cv y)) (syn_wbr (.cv x) A (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0016
  have p0017 :=
    @g_mobidv (.objEq w x) (syn_wbr (.cv w) A (.cv y)) (syn_wbr (.cv x) A (.cv y)) y dv_cache_0014 p0017_e00_recanon
  have p0018 :=
    @g_cbval (syn_wmo y (syn_wbr (.cv w) A (.cv y))) (syn_wmo y (syn_wbr (.cv x) A (.cv y))) w x p0014 p0015 p0017
  have p0019 :=
    @g_n_3bitr3ri (.all w (syn_wmo v (syn_wbr (.cv w) A (.cv v)))) (.all w (syn_wmo y (syn_wbr (.cv w) A (.cv y)))) (.all w (syn_wex u (.all v (.imp (syn_wbr (.cv w) A (.cv v)) (.objEq v u))))) (.all x (syn_wmo y (syn_wbr (.cv x) A (.cv y)))) p0007 p0010 p0018
  have p0020 :=
    @g_bitr4i (syn_wfun A) (.all w (syn_wex u (.all v (.imp (syn_wbr (.cv w) A (.cv v)) (.objEq v u))))) (.all x (syn_wmo y (syn_wbr (.cv x) A (.cv y)))) p0000 p0019
  exact p0020

noncomputable def g_dffun6
    (x : Var) (y : Var) (F : Class) (dv_F_x : x ∉ F.fv) (dv_F_y : y ∉ F.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (syn_wb (syn_wfun F) (.all x (syn_wmo y (syn_wbr (.cv x) F (.cv y))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ F.fv
  have dv_cache_0001 : x ∉ (F).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (F).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @g_nfcv x F dv_cache_0001
  have p0001 :=
    @g_nfcv y F dv_cache_0002
  have p0002 :=
    @g_dffun6f x y F dv_cache_0003 p0000 p0001
  exact p0002

noncomputable def g_funmo
    (y : Var) (A : Class) (F : Class) (dv_A_y : y ∉ A.fv) (dv_F_y : y ∉ F.fv) :
    Nominal.NPrf (.imp (syn_wfun F) (syn_wmo y (syn_wbr A F (.cv y)))) := by
  let proofSupport : Finset Var := ({y} : Finset Var) ∪ A.fv ∪ F.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_y : x ≠ y := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ ((Wff.classEq (.cv x) A)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_wmo y (syn_wbr A F (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wmo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_y, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0007 : y ∉ ((Wff.classMem A (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_brreldmex A (.cv y) F
  have p0001 :=
    @g_ancri (syn_wbr A F (.cv y)) (.classMem A (syn_cvv)) p0000
  have p0002 :=
    Nominal.gen p0001 y
  have p0003 :=
    @g_breq1 (.cv x) A (.cv y) F
  have p0004 :=
    @g_mobidv (.classEq (.cv x) A) (syn_wbr (.cv x) F (.cv y)) (syn_wbr A F (.cv y)) y dv_cache_0001 p0003
  have p0005 :=
    @g_spcgv (syn_wmo y (syn_wbr (.cv x) F (.cv y))) (syn_wmo y (syn_wbr A F (.cv y))) x A (syn_cvv) dv_cache_0002 dv_cache_0003 p0004
  have p0006 :=
    @g_com12 (.classMem A (syn_cvv)) (.all x (syn_wmo y (syn_wbr (.cv x) F (.cv y)))) (syn_wmo y (syn_wbr A F (.cv y))) p0005
  have p0007 :=
    @g_dffun6 x y F dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0008 :=
    @g_moanimv (.classMem A (syn_cvv)) (syn_wbr A F (.cv y)) y dv_cache_0007
  have p0009 :=
    @g_n_3imtr4i (.all x (syn_wmo y (syn_wbr (.cv x) F (.cv y)))) (.imp (.classMem A (syn_cvv)) (syn_wmo y (syn_wbr A F (.cv y)))) (syn_wfun F) (syn_wmo y (syn_wa (.classMem A (syn_cvv)) (syn_wbr A F (.cv y)))) p0006 p0007 p0008
  have p0010 :=
    @g_moim (syn_wbr A F (.cv y)) (syn_wa (.classMem A (syn_cvv)) (syn_wbr A F (.cv y))) y
  have p0011 :=
    @g_mpsyl (.all y (.imp (syn_wbr A F (.cv y)) (syn_wa (.classMem A (syn_cvv)) (syn_wbr A F (.cv y))))) (syn_wfun F) (syn_wmo y (syn_wa (.classMem A (syn_cvv)) (syn_wbr A F (.cv y)))) (syn_wmo y (syn_wbr A F (.cv y))) p0002 p0009 p0010
  exact p0011

noncomputable def g_funss
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wss A B) (.imp (syn_wfun B) (syn_wfun A))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_coss1 A B (syn_ccnv A)
  have p0001 :=
    @g_cnvss A B
  have p0002 :=
    @g_coss2 (syn_ccnv A) (syn_ccnv B) B
  have p0003 :=
    @g_syl (syn_wss A B) (syn_wss (syn_ccnv A) (syn_ccnv B)) (syn_wss (syn_ccom B (syn_ccnv A)) (syn_ccom B (syn_ccnv B))) p0001 p0002
  have p0004 :=
    @g_sstrd (syn_wss A B) (syn_ccom A (syn_ccnv A)) (syn_ccom B (syn_ccnv A)) (syn_ccom B (syn_ccnv B)) p0000 p0003
  have p0005 :=
    @g_sstr2 (syn_ccom A (syn_ccnv A)) (syn_ccom B (syn_ccnv B)) (syn_cid)
  have p0006 :=
    @g_syl (syn_wss A B) (syn_wss (syn_ccom A (syn_ccnv A)) (syn_ccom B (syn_ccnv B))) (.imp (syn_wss (syn_ccom B (syn_ccnv B)) (syn_cid)) (syn_wss (syn_ccom A (syn_ccnv A)) (syn_cid))) p0004 p0005
  have p0007 :=
    (by simpa [syn_wb, syn_wfun] using (Nominal.biimpRefl (syn_wfun B)))
  have p0008 :=
    (by simpa [syn_wb, syn_wfun] using (Nominal.biimpRefl (syn_wfun A)))
  have p0009 :=
    @g_n_3imtr4g (syn_wss A B) (syn_wss (syn_ccom B (syn_ccnv B)) (syn_cid)) (syn_wss (syn_ccom A (syn_ccnv A)) (syn_cid)) (syn_wfun B) (syn_wfun A) p0006 p0007 p0008
  exact p0009

noncomputable def g_funeq
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wfun A) (syn_wfun B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_funss B A
  have p0001 :=
    @g_funss A B
  have p0002 :=
    @g_anim12i (syn_wss B A) (.imp (syn_wfun A) (syn_wfun B)) (syn_wss A B) (.imp (syn_wfun B) (syn_wfun A)) p0000 p0001
  have p0003 :=
    @g_ancoms (syn_wss B A) (syn_wss A B) (syn_wa (.imp (syn_wfun A) (syn_wfun B)) (.imp (syn_wfun B) (syn_wfun A))) p0002
  have p0004 :=
    @g_eqss A B
  have p0005 :=
    @g_dfbi2 (syn_wfun A) (syn_wfun B)
  have p0006 :=
    @g_n_3imtr4i (syn_wa (syn_wss A B) (syn_wss B A)) (syn_wa (.imp (syn_wfun A) (syn_wfun B)) (.imp (syn_wfun B) (syn_wfun A))) (.classEq A B) (syn_wb (syn_wfun A) (syn_wfun B)) p0003 p0004 p0005
  exact p0006

noncomputable def g_funeqi
    (A : Class) (B : Class) (hyp_funeqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (syn_wb (syn_wfun A) (syn_wfun B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_funeq A B
  have p0001 :=
    Nominal.mp hyp_funeqi_1 p0000
  exact p0001

noncomputable def g_funeqd
    (ph : Wff) (A : Class) (B : Class) (hyp_funeqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wfun A) (syn_wfun B))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_funeq A B
  have p0001 :=
    @g_syl ph (.classEq A B) (syn_wb (syn_wfun A) (syn_wfun B)) hyp_funeqd_1 p0000
  exact p0001

noncomputable def g_funeu
    (y : Var) (A : Class) (B : Class) (F : Class) (dv_A_y : y ∉ A.fv) (dv_F_y : y ∉ F.fv) :
    Nominal.NPrf (.imp (syn_wa (syn_wfun F) (syn_wbr A F B)) (syn_weu y (syn_wbr A F (.cv y)))) := by
  let proofSupport : Finset Var := ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ F.fv
  have dv_cache_0001 : y ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (F).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_breldm A B F
  have p0001 :=
    @g_eldm y A F dv_cache_0001 dv_cache_0002
  have p0002 :=
    @g_sylib (syn_wbr A F B) (.classMem A (syn_cdm F)) (syn_wex y (syn_wbr A F (.cv y))) p0000 p0001
  have p0003 :=
    @g_adantl (syn_wbr A F B) (syn_wex y (syn_wbr A F (.cv y))) (syn_wfun F) p0002
  have p0004 :=
    @g_funmo y A F dv_cache_0001 dv_cache_0002
  have p0005 :=
    @g_adantr (syn_wfun F) (syn_wmo y (syn_wbr A F (.cv y))) (syn_wbr A F B) p0004
  have p0006 :=
    @g_jca (syn_wa (syn_wfun F) (syn_wbr A F B)) (syn_wex y (syn_wbr A F (.cv y))) (syn_wmo y (syn_wbr A F (.cv y))) p0003 p0005
  have p0007 :=
    @g_eu5 (syn_wbr A F (.cv y)) y
  have p0008 :=
    @g_sylibr (syn_wa (syn_wfun F) (syn_wbr A F B)) (syn_wa (syn_wex y (syn_wbr A F (.cv y))) (syn_wmo y (syn_wbr A F (.cv y)))) (syn_weu y (syn_wbr A F (.cv y))) p0006 p0007
  exact p0008

noncomputable def g_funeu2
    (y : Var) (A : Class) (B : Class) (F : Class) (dv_A_y : y ∉ A.fv) (dv_F_y : y ∉ F.fv) :
    Nominal.NPrf (.imp (syn_wa (syn_wfun F) (.classMem (syn_cop A B) F)) (syn_weu y (.classMem (syn_cop A (.cv y)) F))) := by
  let proofSupport : Finset Var := ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ F.fv
  have dv_cache_0001 : y ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (F).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr A F B)))
  have p0001 :=
    @g_funeu y A B F dv_cache_0001 dv_cache_0002
  have p0002 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr A F (.cv y))))
  have p0003 :=
    @g_eubii (syn_wbr A F (.cv y)) (.classMem (syn_cop A (.cv y)) F) y p0002
  have p0004 :=
    @g_sylib (syn_wa (syn_wfun F) (syn_wbr A F B)) (syn_weu y (syn_wbr A F (.cv y))) (syn_weu y (.classMem (syn_cop A (.cv y)) F)) p0001 p0003
  have p0005 :=
    @g_sylan2br (.classMem (syn_cop A B) F) (syn_wfun F) (syn_wbr A F B) (syn_weu y (.classMem (syn_cop A (.cv y)) F)) p0000 p0004
  exact p0005

noncomputable def g_funfn
    (A : Class) :
    Nominal.NPrf (syn_wb (syn_wfun A) (syn_wfn A (syn_cdm A))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_eqid (syn_cdm A)
  have p0001 :=
    @g_biantru (.classEq (syn_cdm A) (syn_cdm A)) (syn_wfun A) p0000
  have p0002 :=
    (by simpa [syn_wb, syn_wfn] using (Nominal.biimpRefl (syn_wfn A (syn_cdm A))))
  have p0003 :=
    @g_bitr4i (syn_wfun A) (syn_wa (syn_wfun A) (.classEq (syn_cdm A) (syn_cdm A))) (syn_wfn A (syn_cdm A)) p0001 p0002
  exact p0003

noncomputable def g_funi
     :
    Nominal.NPrf (syn_wfun (syn_cid)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_cnvi
  have p0001 :=
    @g_coeq2i (syn_ccnv (syn_cid)) (syn_cid) (syn_cid) p0000
  have p0002 :=
    @g_coi1 (syn_cid)
  have p0003 :=
    @g_eqtri (syn_ccom (syn_cid) (syn_ccnv (syn_cid))) (syn_ccom (syn_cid) (syn_cid)) (syn_cid) p0001 p0002
  have p0004 :=
    @g_eqimssi (syn_ccom (syn_cid) (syn_ccnv (syn_cid))) (syn_cid) p0003
  have p0005 :=
    (by simpa [syn_wb, syn_wfun] using (Nominal.biimpRefl (syn_wfun (syn_cid))))
  have p0006 :=
    @g_mpbir (syn_wfun (syn_cid)) (syn_wss (syn_ccom (syn_cid) (syn_ccnv (syn_cid))) (syn_cid)) p0004 p0005
  exact p0006

noncomputable def g_funopab
    (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (syn_wb (syn_wfun (syn_copab x y ph)) (.all x (syn_wmo y ph))) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var)
  have dv_cache_0001 : x ≠ y := by
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @g_nfopab1 ph x y
  have p0001 :=
    @g_nfopab2 ph x y
  have p0002 :=
    @g_dffun6f x y (syn_copab x y ph) dv_cache_0001 p0000 p0001
  have p0003 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) (syn_copab x y ph) (.cv y))))
  have p0004 :=
    @g_opabid ph x y
  have p0005 :=
    @g_bitri (syn_wbr (.cv x) (syn_copab x y ph) (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) (syn_copab x y ph)) ph p0003 p0004
  have p0006 :=
    @g_mobii (syn_wbr (.cv x) (syn_copab x y ph) (.cv y)) ph y p0005
  have p0007 :=
    @g_albii (syn_wmo y (syn_wbr (.cv x) (syn_copab x y ph) (.cv y))) (syn_wmo y ph) x p0006
  have p0008 :=
    @g_bitri (syn_wfun (syn_copab x y ph)) (.all x (syn_wmo y (syn_wbr (.cv x) (syn_copab x y ph) (.cv y)))) (.all x (syn_wmo y ph)) p0002 p0007
  exact p0008

noncomputable def g_funco
    (F : Class) (G : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wfun F) (syn_wfun G)) (syn_wfun (syn_ccom F G))) := by
  let proofSupport : Finset Var := F.fv ∪ G.fv
  let x : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_G : x ∉ G.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_G : z ∉ G.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_G : y ∉ G.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_z_ne_y : z ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have dv_cache_0001 : z ∉ ((Class.cv x)).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ (G).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((syn_wfun F)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_wbr (.cv x) G (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_z, fresh_y_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_wa (syn_wfun F) (syn_wfun G))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, fresh_x_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0009 : x ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : z ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : x ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0014 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    @g_funmo z (.cv x) G dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_funmo y (.cv z) F dv_cache_0003 dv_cache_0004
  have p0002 :=
    @g_alrimiv (syn_wfun F) (syn_wmo y (syn_wbr (.cv z) F (.cv y))) z dv_cache_0005 p0001
  have p0003 :=
    @g_moexexv (syn_wbr (.cv x) G (.cv z)) (syn_wbr (.cv z) F (.cv y)) z y dv_cache_0006
  have p0004 :=
    @g_syl2anr (syn_wfun G) (syn_wmo z (syn_wbr (.cv x) G (.cv z))) (.all z (syn_wmo y (syn_wbr (.cv z) F (.cv y)))) (syn_wmo y (syn_wex z (syn_wa (syn_wbr (.cv x) G (.cv z)) (syn_wbr (.cv z) F (.cv y))))) (syn_wfun F) p0000 p0002 p0003
  have p0005 :=
    @g_alrimiv (syn_wa (syn_wfun F) (syn_wfun G)) (syn_wmo y (syn_wex z (syn_wa (syn_wbr (.cv x) G (.cv z)) (syn_wbr (.cv z) F (.cv y))))) x dv_cache_0007 p0004
  have p0006 :=
    @g_funopab (syn_wex z (syn_wa (syn_wbr (.cv x) G (.cv z)) (syn_wbr (.cv z) F (.cv y)))) x y dv_cache_0008
  have p0007 :=
    @g_sylibr (syn_wa (syn_wfun F) (syn_wfun G)) (.all x (syn_wmo y (syn_wex z (syn_wa (syn_wbr (.cv x) G (.cv z)) (syn_wbr (.cv z) F (.cv y)))))) (syn_wfun (syn_copab x y (syn_wex z (syn_wa (syn_wbr (.cv x) G (.cv z)) (syn_wbr (.cv z) F (.cv y)))))) p0005 p0006
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_co x y z F G dv_cache_0009 dv_cache_0004 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0002 dv_cache_0008 dv_cache_0013 dv_cache_0014
  have p0009 :=
    @g_funeqi (syn_ccom F G) (syn_copab x y (syn_wex z (syn_wa (syn_wbr (.cv x) G (.cv z)) (syn_wbr (.cv z) F (.cv y))))) p0008
  have p0010 :=
    @g_sylibr (syn_wa (syn_wfun F) (syn_wfun G)) (syn_wfun (syn_copab x y (syn_wex z (syn_wa (syn_wbr (.cv x) G (.cv z)) (syn_wbr (.cv z) F (.cv y)))))) (syn_wfun (syn_ccom F G)) p0007 p0009
  exact p0010

noncomputable def g_funres
    (A : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfun F) (syn_wfun (syn_cres F A))) := by
  let proofSupport : Finset Var := A.fv ∪ F.fv
  have p0000 :=
    @g_resss F A
  have p0001 :=
    @g_funss (syn_cres F A) F
  have p0002 :=
    Nominal.mp p0000 p0001
  exact p0002

noncomputable def g_funssres
    (F : Class) (G : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wfun F) (syn_wss G F)) (.classEq (syn_cres F (syn_cdm G)) G)) := by
  let proofSupport : Finset Var := F.fv ∪ G.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_G : x ∉ G.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_G : y ∉ G.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : y ∉ ((Class.cv x)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (F).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_wss G F)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_G, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_cres F (syn_cdm G))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, fresh_x_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_cres F (syn_cdm G))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, fresh_y_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_wa (syn_wfun F) (syn_wss G F))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, fresh_x_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((syn_wa (syn_wfun F) (syn_wss G F))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, fresh_y_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_ssel G F (syn_cop (.cv x) (.cv y))
  have p0001 :=
    @g_adantl (syn_wss G F) (.imp (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (syn_cop (.cv x) (.cv y)) F)) (syn_wfun F) p0000
  have p0002 :=
    @g_opeldm (.cv x) (.cv y) G
  have p0003 :=
    @g_a1i (.imp (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (.cv x) (syn_cdm G))) (syn_wa (syn_wfun F) (syn_wss G F)) p0002
  have p0004 :=
    @g_jcad (syn_wa (syn_wfun F) (syn_wss G F)) (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (.cv x) (syn_cdm G)) p0001 p0003
  have p0005 :=
    @g_funeu2 y (.cv x) (.cv y) F dv_cache_0001 dv_cache_0002
  have p0006 :=
    @g_eldm2 y (.cv x) G dv_cache_0001 dv_cache_0003
  have p0007 :=
    @g_ancrd (syn_wss G F) (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (syn_cop (.cv x) (.cv y)) F) p0000
  have p0008 :=
    @g_eximdv (syn_wss G F) (.classMem (syn_cop (.cv x) (.cv y)) G) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv y)) G)) y dv_cache_0004 p0007
  have p0009 :=
    @g_syl5bi (.classMem (.cv x) (syn_cdm G)) (syn_wex y (.classMem (syn_cop (.cv x) (.cv y)) G)) (syn_wss G F) (syn_wex y (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv y)) G))) p0006 p0008
  have p0010 :=
    @g_imp (syn_wss G F) (.classMem (.cv x) (syn_cdm G)) (syn_wex y (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv y)) G))) p0009
  have p0011 :=
    @g_eupick (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv y)) G) y
  have p0012 :=
    @g_syl2an (syn_wa (syn_wfun F) (.classMem (syn_cop (.cv x) (.cv y)) F)) (syn_weu y (.classMem (syn_cop (.cv x) (.cv y)) F)) (syn_wex y (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv y)) G))) (.imp (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv y)) G)) (syn_wa (syn_wss G F) (.classMem (.cv x) (syn_cdm G))) p0005 p0010 p0011
  have p0013 :=
    @g_exp43 (syn_wfun F) (.classMem (syn_cop (.cv x) (.cv y)) F) (syn_wss G F) (.classMem (.cv x) (syn_cdm G)) (.imp (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv y)) G)) p0012
  have p0014 :=
    @g_com23 (syn_wfun F) (.classMem (syn_cop (.cv x) (.cv y)) F) (syn_wss G F) (.imp (.classMem (.cv x) (syn_cdm G)) (.imp (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv y)) G))) p0013
  have p0015 :=
    @g_imp (syn_wfun F) (syn_wss G F) (.imp (.classMem (syn_cop (.cv x) (.cv y)) F) (.imp (.classMem (.cv x) (syn_cdm G)) (.imp (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv y)) G)))) p0014
  have p0016 :=
    @g_com34 (syn_wa (syn_wfun F) (syn_wss G F)) (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (.cv x) (syn_cdm G)) (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv y)) G) p0015
  have p0017 :=
    @g_pm2_43d (syn_wa (syn_wfun F) (syn_wss G F)) (.classMem (syn_cop (.cv x) (.cv y)) F) (.imp (.classMem (.cv x) (syn_cdm G)) (.classMem (syn_cop (.cv x) (.cv y)) G)) p0016
  have p0018 :=
    @g_imp3a (syn_wa (syn_wfun F) (syn_wss G F)) (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (.cv x) (syn_cdm G)) (.classMem (syn_cop (.cv x) (.cv y)) G) p0017
  have p0019 :=
    @g_impbid (syn_wa (syn_wfun F) (syn_wss G F)) (.classMem (syn_cop (.cv x) (.cv y)) G) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (.cv x) (syn_cdm G))) p0004 p0018
  have p0020 :=
    @g_opelres (.cv x) (.cv y) F (syn_cdm G)
  have p0021 :=
    @g_syl6rbbr (syn_wa (syn_wfun F) (syn_wss G F)) (.classMem (syn_cop (.cv x) (.cv y)) G) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (.cv x) (syn_cdm G))) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cres F (syn_cdm G))) p0019 p0020
  have p0022 :=
    @g_eqrelrdv (syn_wa (syn_wfun F) (syn_wss G F)) x y (syn_cres F (syn_cdm G)) G dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0003 dv_cache_0008 dv_cache_0009 dv_cache_0010 p0021
  exact p0022

#print axioms g_funssres

end NFChoice.DirectNominalPrf.WPPReplay
