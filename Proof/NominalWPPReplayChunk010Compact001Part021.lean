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
import NominalWPPReplayChunk010Compact001Part020

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

noncomputable def g_ncvspfin
     :
    Nominal.NPrf (.classMem (syn_cncfin (syn_cvv)) (syn_cspfin)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let a : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_a_ne_z : a ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_a : z ≠ a :=
    Ne.symm fresh_a_ne_z
  have fresh_a_ne_x : a ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_a : x ≠ a :=
    Ne.symm fresh_a_ne_x
  have fresh_z_ne_x : z ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have dv_cache_0001 : a ∉ ((syn_cncfin (syn_cvv))).fv := by
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : a ≠ x := by
    clear dv_cache_0001
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0003 : a ≠ z := by
    clear dv_cache_0001 dv_cache_0002
    exact (show a ≠ z from (by exact fresh_a_ne_z))
  have dv_cache_0004 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have p0000 :=
    @g_ncfinex (syn_cvv)
  have p0001 :=
    @g_elintab (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral x (.cv a) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a))))) a (syn_cncfin (syn_cvv)) dv_cache_0001 p0000
  have p0002 :=
    @g_simpl (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral x (.cv a) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a))))
  have p0003 :=
    @g_mpgbir (.classMem (syn_cncfin (syn_cvv)) (syn_cint (.cab a (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral x (.cv a) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a)))))))) (.imp (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral x (.cv a) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a))))) (.classMem (syn_cncfin (syn_cvv)) (.cv a))) a p0001 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_spfin x z a dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0005 :=
    @g_eleqtrri (syn_cncfin (syn_cvv)) (syn_cint (.cab a (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral x (.cv a) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a))))))) (syn_cspfin) p0003 p0004
  exact p0005

noncomputable def g_spfinsfincl
    (X : Class) (Z : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem X (syn_cspfin)) (syn_wsfin Z X)) (.classMem Z (syn_cspfin))) := by
  let proofSupport : Finset Var := X.fv ∪ Z.fv
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  let a : Var := freshVar proofSupport 3
  let q : Var := freshVar proofSupport 4
  let p : Var := freshVar proofSupport 5
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_X : y ∉ X.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_Z : y ∉ Z.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_X : z ∉ X.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_Z : z ∉ Z.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_X : x ∉ X.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_Z : x ∉ Z.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_a_not_X : a ∉ X.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (h))
  have fresh_a_not_Z : a ∉ Z.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_q_not_X : q ∉ X.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (h))
  have fresh_q_not_Z : q ∉ Z.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_p_not_X : p ∉ X.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (h))
  have fresh_p_not_Z : p ∉ Z.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_ne_a : y ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_a_ne_y : a ≠ y :=
    Ne.symm fresh_y_ne_a
  have fresh_y_ne_q : y ≠ q := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_q_ne_y : q ≠ y :=
    Ne.symm fresh_y_ne_q
  have fresh_y_ne_p : y ≠ p := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_p_ne_y : p ≠ y :=
    Ne.symm fresh_y_ne_p
  have fresh_z_ne_x : z ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_a : z ≠ a := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_a_ne_z : a ≠ z :=
    Ne.symm fresh_z_ne_a
  have fresh_z_ne_q : z ≠ q := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_q_ne_z : q ≠ z :=
    Ne.symm fresh_z_ne_q
  have fresh_z_ne_p : z ≠ p := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_p_ne_z : p ≠ z :=
    Ne.symm fresh_z_ne_p
  have fresh_x_ne_a : x ≠ a := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_a_ne_x : a ≠ x :=
    Ne.symm fresh_x_ne_a
  have fresh_x_ne_q : x ≠ q := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_q_ne_x : q ≠ x :=
    Ne.symm fresh_x_ne_q
  have fresh_x_ne_p : x ≠ p := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_p_ne_x : p ≠ x :=
    Ne.symm fresh_x_ne_p
  have fresh_a_ne_q : a ≠ q := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_q_ne_a : q ≠ a :=
    Ne.symm fresh_a_ne_q
  have fresh_a_ne_p : a ≠ p := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_p_ne_a : p ≠ a :=
    Ne.symm fresh_a_ne_p
  have fresh_q_ne_p : q ≠ p := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_p_ne_q : p ≠ q :=
    Ne.symm fresh_q_ne_p
  have dv_cache_0001 : y ∉ (Z).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_Z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (X).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((Wff.objEq p x)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_p, fresh_q_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : p ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : p ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : p ∉ ((Wff.all q (.imp (syn_wsfin (.cv q) (.cv x)) (.objMem q a)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_q, fresh_p_ne_x, fresh_p_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : q ∉ ((Wff.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_z, fresh_q_ne_x, fresh_q_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : a ∉ ((syn_wsfin (.cv z) (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_z, fresh_a_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : a ≠ p := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show a ≠ p from (by exact fresh_a_ne_p))
  have dv_cache_0010 : a ≠ q := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show a ≠ q from (by exact fresh_a_ne_q))
  have dv_cache_0011 : p ≠ q := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show p ≠ q from (by exact fresh_p_ne_q))
  have dv_cache_0012 : a ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : a ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : z ∉ (Z).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_Z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ (Z).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_Z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : x ∉ (X).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : x ∉ ((Wff.imp (syn_wsfin Z X) (.imp (.classMem X (syn_cspfin)) (.classMem Z (syn_cspfin))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_Z, fresh_x_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : z ∉ ((Wff.imp (syn_wsfin Z (.cv x)) (.imp (.classMem (.cv x) (syn_cspfin)) (.classMem Z (syn_cspfin))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_Z, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin Z X y dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_sfineq1 (.cv z) Z (.cv x)
  have p0002 :=
    @g_eleq1 (.cv z) Z (syn_cspfin)
  have p0003 :=
    @g_imbi2d (.classEq (.cv z) Z) (.classMem (.cv z) (syn_cspfin)) (.classMem Z (syn_cspfin)) (.classMem (.cv x) (syn_cspfin)) p0002
  have p0004 :=
    @g_imbi12d (.classEq (.cv z) Z) (syn_wsfin (.cv z) (.cv x)) (syn_wsfin Z (.cv x)) (.imp (.classMem (.cv x) (syn_cspfin)) (.classMem (.cv z) (syn_cspfin))) (.imp (.classMem (.cv x) (syn_cspfin)) (.classMem Z (syn_cspfin))) p0001 p0003
  have p0005 :=
    @g_sfineq2 (.cv x) X Z
  have p0006 :=
    @g_eleq1 (.cv x) X (syn_cspfin)
  have p0007 :=
    @g_imbi1d (.classEq (.cv x) X) (.classMem (.cv x) (syn_cspfin)) (.classMem X (syn_cspfin)) (.classMem Z (syn_cspfin)) p0006
  have p0008 :=
    @g_imbi12d (.classEq (.cv x) X) (syn_wsfin Z (.cv x)) (syn_wsfin Z X) (.imp (.classMem (.cv x) (syn_cspfin)) (.classMem Z (syn_cspfin))) (.imp (.classMem X (syn_cspfin)) (.classMem Z (syn_cspfin))) p0005 p0007
  have p0009 :=
    @g_sfineq2 (.cv p) (.cv x) (.cv q)
  have p0010_e00_recanon : Nominal.NPrf (.imp (.objEq p x) (syn_wb (syn_wsfin (.cv q) (.cv p)) (syn_wsfin (.cv q) (.cv x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wsfin syn_w3a syn_wa syn_cnnc syn_cint syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0009
  have p0010 :=
    @g_imbi1d (.objEq p x) (syn_wsfin (.cv q) (.cv p)) (syn_wsfin (.cv q) (.cv x)) (.objMem q a) p0010_e00_recanon
  have p0011 :=
    @g_albidv (.objEq p x) (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a)) (.imp (syn_wsfin (.cv q) (.cv x)) (.objMem q a)) q dv_cache_0003 p0010
  have p0012_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv p) (.cv x)) (syn_wb (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a))) (.all q (.imp (syn_wsfin (.cv q) (.cv x)) (.objMem q a))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wsfin syn_w3a syn_wa syn_cnnc syn_cint syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0011
  have p0012 :=
    @g_rspcv (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a))) (.all q (.imp (syn_wsfin (.cv q) (.cv x)) (.objMem q a))) p (.cv x) (.cv a) dv_cache_0004 dv_cache_0005 dv_cache_0006 p0012_e00_recanon
  have p0013 :=
    @g_sfineq1 (.cv q) (.cv z) (.cv x)
  have p0014 :=
    @g_eleq1 (.cv q) (.cv z) (.cv a)
  have p0015_e00_recanon : Nominal.NPrf (.imp (.objEq q z) (syn_wb (syn_wsfin (.cv q) (.cv x)) (syn_wsfin (.cv z) (.cv x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wsfin syn_w3a syn_wa syn_cnnc syn_cint syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0013
  have p0015_e01_recanon : Nominal.NPrf (.imp (.objEq q z) (syn_wb (.objMem q a) (.objMem z a))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
      )
      p0014
  have p0015 :=
    @g_imbi12d (.objEq q z) (syn_wsfin (.cv q) (.cv x)) (syn_wsfin (.cv z) (.cv x)) (.objMem q a) (.objMem z a) p0015_e00_recanon p0015_e01_recanon
  have p0016 :=
    @g_spv (.imp (syn_wsfin (.cv q) (.cv x)) (.objMem q a)) (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a)) q z dv_cache_0007 p0015
  have p0017 :=
    @g_com12 (.all q (.imp (syn_wsfin (.cv q) (.cv x)) (.objMem q a))) (syn_wsfin (.cv z) (.cv x)) (.objMem z a) p0016
  have p0018_e00_recanon : Nominal.NPrf (.imp (.objMem x a) (.imp (syn_wral p (.cv a) (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a)))) (.all q (.imp (syn_wsfin (.cv q) (.cv x)) (.objMem q a))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wral syn_wsfin syn_w3a syn_wa syn_cnnc syn_cint syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0012
  have p0018 :=
    @g_syl9r (.objMem x a) (syn_wral p (.cv a) (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a)))) (.all q (.imp (syn_wsfin (.cv q) (.cv x)) (.objMem q a))) (syn_wsfin (.cv z) (.cv x)) (.objMem z a) p0018_e00_recanon p0017
  have p0019 :=
    @g_com23 (syn_wsfin (.cv z) (.cv x)) (.objMem x a) (syn_wral p (.cv a) (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a)))) (.objMem z a) p0018
  have p0020 :=
    @g_adantld (syn_wsfin (.cv z) (.cv x)) (syn_wral p (.cv a) (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a)))) (.imp (.objMem x a) (.objMem z a)) (.classMem (syn_cncfin (syn_cvv)) (.cv a)) p0019
  have p0021 :=
    @g_a2d (syn_wsfin (.cv z) (.cv x)) (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral p (.cv a) (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a))))) (.objMem x a) (.objMem z a) p0020
  have p0022 :=
    @g_alimdv (syn_wsfin (.cv z) (.cv x)) (.imp (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral p (.cv a) (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a))))) (.objMem x a)) (.imp (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral p (.cv a) (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a))))) (.objMem z a)) a dv_cache_0008 p0021
  have p0023 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_spfin p q a dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0024 :=
    @g_eleq2i (syn_cspfin) (syn_cint (.cab a (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral p (.cv a) (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a))))))) (.cv x) p0023
  have p0025 :=
    @g_vex x
  have p0026 :=
    @g_elintab (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral p (.cv a) (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a))))) a (.cv x) dv_cache_0012 p0025
  have p0027_e01_recanon : Nominal.NPrf (syn_wb (.classMem (.cv x) (syn_cint (.cab a (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral p (.cv a) (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a)))))))) (.all a (.imp (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral p (.cv a) (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a))))) (.objMem x a)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cint syn_wa syn_cncfin syn_cio syn_cuni syn_wex syn_csn syn_cvv syn_wral syn_wsfin syn_w3a syn_cnnc
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cint, NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0026
  have p0027 :=
    @g_bitri (.classMem (.cv x) (syn_cspfin)) (.classMem (.cv x) (syn_cint (.cab a (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral p (.cv a) (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a)))))))) (.all a (.imp (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral p (.cv a) (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a))))) (.objMem x a))) p0024 p0027_e01_recanon
  have p0028 :=
    @g_eleq2i (syn_cspfin) (syn_cint (.cab a (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral p (.cv a) (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a))))))) (.cv z) p0023
  have p0029 :=
    @g_vex z
  have p0030 :=
    @g_elintab (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral p (.cv a) (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a))))) a (.cv z) dv_cache_0013 p0029
  have p0031_e01_recanon : Nominal.NPrf (syn_wb (.classMem (.cv z) (syn_cint (.cab a (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral p (.cv a) (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a)))))))) (.all a (.imp (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral p (.cv a) (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a))))) (.objMem z a)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cint syn_wa syn_cncfin syn_cio syn_cuni syn_wex syn_csn syn_cvv syn_wral syn_wsfin syn_w3a syn_cnnc
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cint, NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0030
  have p0031 :=
    @g_bitri (.classMem (.cv z) (syn_cspfin)) (.classMem (.cv z) (syn_cint (.cab a (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral p (.cv a) (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a)))))))) (.all a (.imp (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral p (.cv a) (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a))))) (.objMem z a))) p0028 p0031_e01_recanon
  have p0032 :=
    @g_n_3imtr4g (syn_wsfin (.cv z) (.cv x)) (.all a (.imp (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral p (.cv a) (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a))))) (.objMem x a))) (.all a (.imp (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral p (.cv a) (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a))))) (.objMem z a))) (.classMem (.cv x) (syn_cspfin)) (.classMem (.cv z) (syn_cspfin)) p0022 p0027 p0031
  have p0033 :=
    @g_vtocl2g (.imp (syn_wsfin (.cv z) (.cv x)) (.imp (.classMem (.cv x) (syn_cspfin)) (.classMem (.cv z) (syn_cspfin)))) (.imp (syn_wsfin Z (.cv x)) (.imp (.classMem (.cv x) (syn_cspfin)) (.classMem Z (syn_cspfin)))) (.imp (syn_wsfin Z X) (.imp (.classMem X (syn_cspfin)) (.classMem Z (syn_cspfin)))) z x Z X (syn_cnnc) (syn_cnnc) dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 p0004 p0008 p0032
  have p0034 :=
    @g_n_3adant3 (.classMem Z (syn_cnnc)) (.classMem X (syn_cnnc)) (.imp (syn_wsfin Z X) (.imp (.classMem X (syn_cspfin)) (.classMem Z (syn_cspfin)))) (syn_wex y (syn_wa (.classMem (syn_cpw1 (.cv y)) Z) (.classMem (syn_cpw (.cv y)) X))) p0033
  have p0035 :=
    @g_sylbi (syn_wsfin Z X) (syn_w3a (.classMem Z (syn_cnnc)) (.classMem X (syn_cnnc)) (syn_wex y (syn_wa (.classMem (syn_cpw1 (.cv y)) Z) (.classMem (syn_cpw (.cv y)) X)))) (.imp (syn_wsfin Z X) (.imp (.classMem X (syn_cspfin)) (.classMem Z (syn_cspfin)))) p0000 p0034
  have p0036 :=
    @g_pm2_43i (syn_wsfin Z X) (.imp (.classMem X (syn_cspfin)) (.classMem Z (syn_cspfin))) p0035
  have p0037 :=
    @g_impcom (syn_wsfin Z X) (.classMem X (syn_cspfin)) (.classMem Z (syn_cspfin)) p0036
  exact p0037

noncomputable def g_spfininduct
    (x : Var) (z : Var) (B : Class) (V : Class) (dv_B_x : x ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_x_z : x ≠ z) :
    Nominal.NPrf (.imp (syn_w3a (.classMem B V) (.classMem (syn_cncfin (syn_cvv)) B) (syn_wral x (syn_cspfin) (.all z (.imp (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x))) (.classMem (.cv z) B))))) (syn_wss (syn_cspfin) B)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({z} : Finset Var) ∪ B.fv ∪ V.fv
  let a : Var := freshVar proofSupport 0
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_ne_x : a ≠ x := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_a : x ≠ a :=
    Ne.symm fresh_a_ne_x
  have fresh_a_ne_z : a ≠ z := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_z_ne_a : z ≠ a :=
    Ne.symm fresh_a_ne_z
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_V : a ∉ V.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have dv_cache_0001 : z ∉ ((Wff.classMem (.cv x) (syn_cspfin))).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_z), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((Wff.classMem (.cv x) (syn_cin (syn_cspfin) B))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_z), dv_B_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : a ≠ x := by
    clear dv_cache_0001 dv_cache_0002
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0004 : a ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show a ≠ z from (by exact fresh_a_ne_z))
  have dv_cache_0005 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0006 : z ∉ ((Wff.classEq (.cv a) (syn_cin (syn_cspfin) B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_a, dv_B_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_cin (syn_cspfin) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : a ∉ ((syn_cin (syn_cspfin) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : a ∉ ((syn_wa (.classMem (syn_cncfin (syn_cvv)) (syn_cin (syn_cspfin) B)) (syn_wral x (syn_cin (syn_cspfin) B) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_B, fresh_a_ne_z, fresh_a_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_spfinex
  have p0001 :=
    @g_inexg (syn_cspfin) B (syn_cvv) V
  have p0002 :=
    @g_mpan (.classMem (syn_cspfin) (syn_cvv)) (.classMem B V) (.classMem (syn_cin (syn_cspfin) B) (syn_cvv)) p0000 p0001
  have p0003 :=
    @g_ncvspfin
  have p0004 :=
    @g_elin (syn_cncfin (syn_cvv)) (syn_cspfin) B
  have p0005 :=
    @g_biimpri (.classMem (syn_cncfin (syn_cvv)) (syn_cin (syn_cspfin) B)) (syn_wa (.classMem (syn_cncfin (syn_cvv)) (syn_cspfin)) (.classMem (syn_cncfin (syn_cvv)) B)) p0004
  have p0006 :=
    @g_mpan (.classMem (syn_cncfin (syn_cvv)) (syn_cspfin)) (.classMem (syn_cncfin (syn_cvv)) B) (.classMem (syn_cncfin (syn_cvv)) (syn_cin (syn_cspfin) B)) p0003 p0005
  have p0007 :=
    @g_elin (.cv x) (syn_cspfin) B
  have p0008 :=
    @g_spfinsfincl (.cv x) (.cv z)
  have p0009 :=
    @g_adantrl (.classMem (.cv x) (syn_cspfin)) (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cspfin)) (.classMem (.cv x) B) p0008
  have p0010 :=
    @g_a1d (syn_wa (.classMem (.cv x) (syn_cspfin)) (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x)))) (.classMem (.cv z) (syn_cspfin)) (.classMem (.cv z) B) p0009
  have p0011 :=
    @g_ancrd (syn_wa (.classMem (.cv x) (syn_cspfin)) (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x)))) (.classMem (.cv z) B) (.classMem (.cv z) (syn_cspfin)) p0010
  have p0012 :=
    @g_elin (.cv z) (syn_cspfin) B
  have p0013 :=
    @g_syl6ibr (syn_wa (.classMem (.cv x) (syn_cspfin)) (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x)))) (.classMem (.cv z) B) (syn_wa (.classMem (.cv z) (syn_cspfin)) (.classMem (.cv z) B)) (.classMem (.cv z) (syn_cin (syn_cspfin) B)) p0011 p0012
  have p0014 :=
    @g_ex (.classMem (.cv x) (syn_cspfin)) (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x))) (.imp (.classMem (.cv z) B) (.classMem (.cv z) (syn_cin (syn_cspfin) B))) p0013
  have p0015 :=
    @g_a2d (.classMem (.cv x) (syn_cspfin)) (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x))) (.classMem (.cv z) B) (.classMem (.cv z) (syn_cin (syn_cspfin) B)) p0014
  have p0016 :=
    @g_exp4a (.classMem (.cv x) (syn_cspfin)) (.imp (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x))) (.classMem (.cv z) B)) (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B)) p0015
  have p0017 :=
    @g_a2i (.classMem (.cv x) (syn_cspfin)) (.imp (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x))) (.classMem (.cv z) B)) (.imp (.classMem (.cv x) B) (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B)))) p0016
  have p0018 :=
    @g_imp3a (.imp (.classMem (.cv x) (syn_cspfin)) (.imp (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x))) (.classMem (.cv z) B))) (.classMem (.cv x) (syn_cspfin)) (.classMem (.cv x) B) (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B))) p0017
  have p0019 :=
    @g_syl5bi (.classMem (.cv x) (syn_cin (syn_cspfin) B)) (syn_wa (.classMem (.cv x) (syn_cspfin)) (.classMem (.cv x) B)) (.imp (.classMem (.cv x) (syn_cspfin)) (.imp (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x))) (.classMem (.cv z) B))) (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B))) p0007 p0018
  have p0020 :=
    @g_n_2alimi (.imp (.classMem (.cv x) (syn_cspfin)) (.imp (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x))) (.classMem (.cv z) B))) (.imp (.classMem (.cv x) (syn_cin (syn_cspfin) B)) (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B)))) x z p0019
  have p0021 :=
    (by simpa [syn_wb, syn_wral] using (Nominal.biimpRefl (syn_wral x (syn_cspfin) (.all z (.imp (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x))) (.classMem (.cv z) B))))))
  have p0022 :=
    @g_n_19_21v (.classMem (.cv x) (syn_cspfin)) (.imp (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x))) (.classMem (.cv z) B)) z dv_cache_0001
  have p0023 :=
    @g_albii (.all z (.imp (.classMem (.cv x) (syn_cspfin)) (.imp (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x))) (.classMem (.cv z) B)))) (.imp (.classMem (.cv x) (syn_cspfin)) (.all z (.imp (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x))) (.classMem (.cv z) B)))) x p0022
  have p0024 :=
    @g_bitr4i (syn_wral x (syn_cspfin) (.all z (.imp (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x))) (.classMem (.cv z) B)))) (.all x (.imp (.classMem (.cv x) (syn_cspfin)) (.all z (.imp (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x))) (.classMem (.cv z) B))))) (.all x (.all z (.imp (.classMem (.cv x) (syn_cspfin)) (.imp (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x))) (.classMem (.cv z) B))))) p0021 p0023
  have p0025 :=
    (by simpa [syn_wb, syn_wral] using (Nominal.biimpRefl (syn_wral x (syn_cin (syn_cspfin) B) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B)))))))
  have p0026 :=
    @g_n_19_21v (.classMem (.cv x) (syn_cin (syn_cspfin) B)) (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B))) z dv_cache_0002
  have p0027 :=
    @g_albii (.all z (.imp (.classMem (.cv x) (syn_cin (syn_cspfin) B)) (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B))))) (.imp (.classMem (.cv x) (syn_cin (syn_cspfin) B)) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B))))) x p0026
  have p0028 :=
    @g_bitr4i (syn_wral x (syn_cin (syn_cspfin) B) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B))))) (.all x (.imp (.classMem (.cv x) (syn_cin (syn_cspfin) B)) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B)))))) (.all x (.all z (.imp (.classMem (.cv x) (syn_cin (syn_cspfin) B)) (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B)))))) p0025 p0027
  have p0029 :=
    @g_n_3imtr4i (.all x (.all z (.imp (.classMem (.cv x) (syn_cspfin)) (.imp (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x))) (.classMem (.cv z) B))))) (.all x (.all z (.imp (.classMem (.cv x) (syn_cin (syn_cspfin) B)) (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B)))))) (syn_wral x (syn_cspfin) (.all z (.imp (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x))) (.classMem (.cv z) B)))) (syn_wral x (syn_cin (syn_cspfin) B) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B))))) p0020 p0024 p0028
  have p0030 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_spfin x z a dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0031 :=
    @g_eleq2 (.cv a) (syn_cin (syn_cspfin) B) (syn_cncfin (syn_cvv))
  have p0032 :=
    @g_eleq2 (.cv a) (syn_cin (syn_cspfin) B) (.cv z)
  have p0033_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv a) (syn_cin (syn_cspfin) B)) (syn_wb (.objMem z a) (.classMem (.cv z) (syn_cin (syn_cspfin) B)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cspfin syn_cint syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
      )
      p0032
  have p0033 :=
    @g_imbi2d (.classEq (.cv a) (syn_cin (syn_cspfin) B)) (.objMem z a) (.classMem (.cv z) (syn_cin (syn_cspfin) B)) (syn_wsfin (.cv z) (.cv x)) p0033_e00_recanon
  have p0034 :=
    @g_albidv (.classEq (.cv a) (syn_cin (syn_cspfin) B)) (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a)) (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B))) z dv_cache_0006 p0033
  have p0035 :=
    @g_raleqbi1dv (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a))) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B)))) x (.cv a) (syn_cin (syn_cspfin) B) dv_cache_0007 dv_cache_0008 p0034
  have p0036 :=
    @g_anbi12d (.classEq (.cv a) (syn_cin (syn_cspfin) B)) (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (.classMem (syn_cncfin (syn_cvv)) (syn_cin (syn_cspfin) B)) (syn_wral x (.cv a) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a)))) (syn_wral x (syn_cin (syn_cspfin) B) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B))))) p0031 p0035
  have p0037 :=
    @g_elabg (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral x (.cv a) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a))))) (syn_wa (.classMem (syn_cncfin (syn_cvv)) (syn_cin (syn_cspfin) B)) (syn_wral x (syn_cin (syn_cspfin) B) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B)))))) a (syn_cin (syn_cspfin) B) (syn_cvv) dv_cache_0009 dv_cache_0010 p0036
  have p0038 :=
    @g_biimprd (.classMem (syn_cin (syn_cspfin) B) (syn_cvv)) (.classMem (syn_cin (syn_cspfin) B) (.cab a (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral x (.cv a) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a))))))) (syn_wa (.classMem (syn_cncfin (syn_cvv)) (syn_cin (syn_cspfin) B)) (syn_wral x (syn_cin (syn_cspfin) B) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B)))))) p0037
  have p0039 :=
    @g_n_3impib (.classMem (syn_cin (syn_cspfin) B) (syn_cvv)) (.classMem (syn_cncfin (syn_cvv)) (syn_cin (syn_cspfin) B)) (syn_wral x (syn_cin (syn_cspfin) B) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B))))) (.classMem (syn_cin (syn_cspfin) B) (.cab a (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral x (.cv a) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a))))))) p0038
  have p0040 :=
    @g_intss1 (syn_cin (syn_cspfin) B) (.cab a (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral x (.cv a) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a))))))
  have p0041 :=
    @g_syl (syn_w3a (.classMem (syn_cin (syn_cspfin) B) (syn_cvv)) (.classMem (syn_cncfin (syn_cvv)) (syn_cin (syn_cspfin) B)) (syn_wral x (syn_cin (syn_cspfin) B) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B)))))) (.classMem (syn_cin (syn_cspfin) B) (.cab a (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral x (.cv a) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a))))))) (syn_wss (syn_cint (.cab a (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral x (.cv a) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a))))))) (syn_cin (syn_cspfin) B)) p0039 p0040
  have p0042 :=
    @g_syl5eqss (syn_w3a (.classMem (syn_cin (syn_cspfin) B) (syn_cvv)) (.classMem (syn_cncfin (syn_cvv)) (syn_cin (syn_cspfin) B)) (syn_wral x (syn_cin (syn_cspfin) B) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B)))))) (syn_cspfin) (syn_cint (.cab a (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral x (.cv a) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a))))))) (syn_cin (syn_cspfin) B) p0030 p0041
  have p0043 :=
    @g_inss2 (syn_cspfin) B
  have p0044 :=
    @g_syl6ss (syn_w3a (.classMem (syn_cin (syn_cspfin) B) (syn_cvv)) (.classMem (syn_cncfin (syn_cvv)) (syn_cin (syn_cspfin) B)) (syn_wral x (syn_cin (syn_cspfin) B) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B)))))) (syn_cspfin) (syn_cin (syn_cspfin) B) B p0042 p0043
  have p0045 :=
    @g_syl3an (.classMem B V) (.classMem (syn_cin (syn_cspfin) B) (syn_cvv)) (.classMem (syn_cncfin (syn_cvv)) B) (.classMem (syn_cncfin (syn_cvv)) (syn_cin (syn_cspfin) B)) (syn_wral x (syn_cspfin) (.all z (.imp (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x))) (.classMem (.cv z) B)))) (syn_wral x (syn_cin (syn_cspfin) B) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B))))) (syn_wss (syn_cspfin) B) p0002 p0006 p0029 p0044
  exact p0045

#print axioms g_spfininduct

end NFChoice.DirectNominalPrf.WPPReplay
