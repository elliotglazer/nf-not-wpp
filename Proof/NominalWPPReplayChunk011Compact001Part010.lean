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
import NominalWPPReplayChunk011Compact001Part009

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

noncomputable def g_dfxp2
    (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cxp A B) (syn_cin (syn_cima (syn_ccnv (syn_c1st)) A) (syn_cima (syn_ccnv (syn_c2nd)) B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
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
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (h))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_v : v ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (h))
  have fresh_v_not_B : v ∉ B.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
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
  have dv_cache_0001 : v ∉ ((Wff.classEq (.cv x) (syn_cop (.cv y) (.cv w)))).fv := by
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_x, fresh_v_ne_y, fresh_v_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : w ∉ ((Wff.classEq (.cv x) (syn_cop (.cv v) (.cv z)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_v, fresh_w_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : w ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : v ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : w ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : v ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : w ∉ ((syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) (.classEq (.cv x) (syn_cop (.cv y) (.cv z))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, fresh_w_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : v ∉ ((syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) (.classEq (.cv x) (syn_cop (.cv y) (.cv z))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_x, fresh_v_ne_y, fresh_v_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : w ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show w ≠ v from (by exact fresh_w_ne_v))
  have dv_cache_0010 : w ∉ ((Wff.classEq (.cv x) (syn_cop (.cv y) (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, fresh_w_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : v ∉ ((Wff.classEq (.cv x) (syn_cop (.cv y) (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_x, fresh_v_ne_y, fresh_v_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : w ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : v ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : z ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : z ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0021 : y ∉ ((syn_ccnv (syn_c1st))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : z ∉ ((syn_ccnv (syn_c2nd))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : z ∉ ((syn_wbr (.cv y) (syn_ccnv (syn_c1st)) (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : y ∉ ((syn_wbr (.cv z) (syn_ccnv (syn_c2nd)) (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : x ∉ ((syn_cxp A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : x ∉ ((syn_cin (syn_cima (syn_ccnv (syn_c1st)) A) (syn_cima (syn_ccnv (syn_c2nd)) B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eeanv (.classEq (.cv x) (syn_cop (.cv y) (.cv w))) (.classEq (.cv x) (syn_cop (.cv v) (.cv z))) w v dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_vex z
  have p0002 :=
    @g_vex y
  have p0003 :=
    @g_opeq2 (.cv w) (.cv z) (.cv y)
  have p0004_e00_recanon : Nominal.NPrf (.imp (.objEq w z) (.classEq (syn_cop (.cv y) (.cv w)) (syn_cop (.cv y) (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0003
  have p0004 :=
    @g_eqeq2d (.objEq w z) (syn_cop (.cv y) (.cv w)) (syn_cop (.cv y) (.cv z)) (.cv x) p0004_e00_recanon
  have p0005 :=
    @g_opeq1 (.cv v) (.cv y) (.cv z)
  have p0006_e00_recanon : Nominal.NPrf (.imp (.objEq v y) (.classEq (syn_cop (.cv v) (.cv z)) (syn_cop (.cv y) (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0005
  have p0006 :=
    @g_eqeq2d (.objEq v y) (syn_cop (.cv v) (.cv z)) (syn_cop (.cv y) (.cv z)) (.cv x) p0006_e00_recanon
  have p0007 :=
    @g_bi2anan9 (.objEq w z) (.classEq (.cv x) (syn_cop (.cv y) (.cv w))) (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) (.objEq v y) (.classEq (.cv x) (syn_cop (.cv v) (.cv z))) (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) p0004 p0006
  have p0008_e02_recanon : Nominal.NPrf (.imp (syn_wa (.classEq (.cv w) (.cv z)) (.classEq (.cv v) (.cv y))) (syn_wb (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv w))) (.classEq (.cv x) (syn_cop (.cv v) (.cv z)))) (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) (.classEq (.cv x) (syn_cop (.cv y) (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0007
  have p0008 :=
    @g_spc2ev (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv w))) (.classEq (.cv x) (syn_cop (.cv v) (.cv z)))) (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) (.classEq (.cv x) (syn_cop (.cv y) (.cv z)))) w v (.cv z) (.cv y) dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 p0001 p0002 p0008_e02_recanon
  have p0009 :=
    @g_anidms (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) (syn_wex w (syn_wex v (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv w))) (.classEq (.cv x) (syn_cop (.cv v) (.cv z)))))) p0008
  have p0010 :=
    @g_simpl (.classEq (.cv x) (syn_cop (.cv y) (.cv w))) (.classEq (.cv x) (syn_cop (.cv v) (.cv z)))
  have p0011 :=
    @g_eqtr2 (.cv x) (syn_cop (.cv y) (.cv w)) (syn_cop (.cv v) (.cv z))
  have p0012 :=
    @g_opth (.cv y) (.cv w) (.cv v) (.cv z)
  have p0013_e00_recanon : Nominal.NPrf (.imp (.objEq w z) (.classEq (syn_cop (.cv y) (.cv w)) (syn_cop (.cv y) (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0003
  have p0013 :=
    @g_adantl (.objEq w z) (.classEq (syn_cop (.cv y) (.cv w)) (syn_cop (.cv y) (.cv z))) (.objEq y v) p0013_e00_recanon
  have p0014_e00_recanon : Nominal.NPrf (syn_wb (.classEq (syn_cop (.cv y) (.cv w)) (syn_cop (.cv v) (.cv z))) (syn_wa (.objEq y v) (.objEq w z))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0012
  have p0014 :=
    @g_sylbi (.classEq (syn_cop (.cv y) (.cv w)) (syn_cop (.cv v) (.cv z))) (syn_wa (.objEq y v) (.objEq w z)) (.classEq (syn_cop (.cv y) (.cv w)) (syn_cop (.cv y) (.cv z))) p0014_e00_recanon p0013
  have p0015 :=
    @g_syl (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv w))) (.classEq (.cv x) (syn_cop (.cv v) (.cv z)))) (.classEq (syn_cop (.cv y) (.cv w)) (syn_cop (.cv v) (.cv z))) (.classEq (syn_cop (.cv y) (.cv w)) (syn_cop (.cv y) (.cv z))) p0011 p0014
  have p0016 :=
    @g_eqtrd (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv w))) (.classEq (.cv x) (syn_cop (.cv v) (.cv z)))) (.cv x) (syn_cop (.cv y) (.cv w)) (syn_cop (.cv y) (.cv z)) p0010 p0015
  have p0017 :=
    @g_exlimivv (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv w))) (.classEq (.cv x) (syn_cop (.cv v) (.cv z)))) (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) w v dv_cache_0010 dv_cache_0011 p0016
  have p0018 :=
    @g_impbii (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) (syn_wex w (syn_wex v (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv w))) (.classEq (.cv x) (syn_cop (.cv v) (.cv z)))))) p0009 p0017
  have p0019 :=
    @g_brcnv (.cv y) (.cv x) (syn_c1st)
  have p0020 :=
    @g_br1st w (.cv x) (.cv y) dv_cache_0012 dv_cache_0005 p0002
  have p0021 :=
    @g_bitri (syn_wbr (.cv y) (syn_ccnv (syn_c1st)) (.cv x)) (syn_wbr (.cv x) (syn_c1st) (.cv y)) (syn_wex w (.classEq (.cv x) (syn_cop (.cv y) (.cv w)))) p0019 p0020
  have p0022 :=
    @g_brcnv (.cv z) (.cv x) (syn_c2nd)
  have p0023 :=
    @g_br2nd v (.cv x) (.cv z) dv_cache_0013 dv_cache_0004 p0001
  have p0024 :=
    @g_bitri (syn_wbr (.cv z) (syn_ccnv (syn_c2nd)) (.cv x)) (syn_wbr (.cv x) (syn_c2nd) (.cv z)) (syn_wex v (.classEq (.cv x) (syn_cop (.cv v) (.cv z)))) p0022 p0023
  have p0025 :=
    @g_anbi12i (syn_wbr (.cv y) (syn_ccnv (syn_c1st)) (.cv x)) (syn_wex w (.classEq (.cv x) (syn_cop (.cv y) (.cv w)))) (syn_wbr (.cv z) (syn_ccnv (syn_c2nd)) (.cv x)) (syn_wex v (.classEq (.cv x) (syn_cop (.cv v) (.cv z)))) p0021 p0024
  have p0026 :=
    @g_n_3bitr4i (syn_wex w (syn_wex v (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv w))) (.classEq (.cv x) (syn_cop (.cv v) (.cv z)))))) (syn_wa (syn_wex w (.classEq (.cv x) (syn_cop (.cv y) (.cv w)))) (syn_wex v (.classEq (.cv x) (syn_cop (.cv v) (.cv z))))) (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_c1st)) (.cv x)) (syn_wbr (.cv z) (syn_ccnv (syn_c2nd)) (.cv x))) p0000 p0018 p0025
  have p0027 :=
    @g_n_2rexbii (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_c1st)) (.cv x)) (syn_wbr (.cv z) (syn_ccnv (syn_c2nd)) (.cv x))) y z A B p0026
  have p0028 :=
    @g_elxp2 y z (.cv x) A B dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
  have p0029 :=
    @g_elima y (.cv x) (syn_ccnv (syn_c1st)) A dv_cache_0014 dv_cache_0021 dv_cache_0016
  have p0030 :=
    @g_elima z (.cv x) (syn_ccnv (syn_c2nd)) B dv_cache_0015 dv_cache_0022 dv_cache_0019
  have p0031 :=
    @g_anbi12i (.classMem (.cv x) (syn_cima (syn_ccnv (syn_c1st)) A)) (syn_wrex y A (syn_wbr (.cv y) (syn_ccnv (syn_c1st)) (.cv x))) (.classMem (.cv x) (syn_cima (syn_ccnv (syn_c2nd)) B)) (syn_wrex z B (syn_wbr (.cv z) (syn_ccnv (syn_c2nd)) (.cv x))) p0029 p0030
  have p0032 :=
    @g_elin (.cv x) (syn_cima (syn_ccnv (syn_c1st)) A) (syn_cima (syn_ccnv (syn_c2nd)) B)
  have p0033 :=
    @g_reeanv (syn_wbr (.cv y) (syn_ccnv (syn_c1st)) (.cv x)) (syn_wbr (.cv z) (syn_ccnv (syn_c2nd)) (.cv x)) y z A B dv_cache_0017 dv_cache_0018 dv_cache_0023 dv_cache_0024 dv_cache_0020
  have p0034 :=
    @g_n_3bitr4i (syn_wa (.classMem (.cv x) (syn_cima (syn_ccnv (syn_c1st)) A)) (.classMem (.cv x) (syn_cima (syn_ccnv (syn_c2nd)) B))) (syn_wa (syn_wrex y A (syn_wbr (.cv y) (syn_ccnv (syn_c1st)) (.cv x))) (syn_wrex z B (syn_wbr (.cv z) (syn_ccnv (syn_c2nd)) (.cv x)))) (.classMem (.cv x) (syn_cin (syn_cima (syn_ccnv (syn_c1st)) A) (syn_cima (syn_ccnv (syn_c2nd)) B))) (syn_wrex y A (syn_wrex z B (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_c1st)) (.cv x)) (syn_wbr (.cv z) (syn_ccnv (syn_c2nd)) (.cv x))))) p0031 p0032 p0033
  have p0035 :=
    @g_n_3bitr4i (syn_wrex y A (syn_wrex z B (.classEq (.cv x) (syn_cop (.cv y) (.cv z))))) (syn_wrex y A (syn_wrex z B (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_c1st)) (.cv x)) (syn_wbr (.cv z) (syn_ccnv (syn_c2nd)) (.cv x))))) (.classMem (.cv x) (syn_cxp A B)) (.classMem (.cv x) (syn_cin (syn_cima (syn_ccnv (syn_c1st)) A) (syn_cima (syn_ccnv (syn_c2nd)) B))) p0027 p0028 p0034
  have p0036 :=
    @g_eqriv x (syn_cxp A B) (syn_cin (syn_cima (syn_ccnv (syn_c1st)) A) (syn_cima (syn_ccnv (syn_c2nd)) B)) dv_cache_0025 dv_cache_0026 p0035
  exact p0036

noncomputable def g_xpexg
    (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem B W)) (.classMem (syn_cxp A B) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  have p0000 :=
    @g_dfxp2 A B
  have p0001 :=
    @g_n_1stex
  have p0002 :=
    @g_cnvex (syn_c1st) p0001
  have p0003 :=
    @g_imaexg (syn_ccnv (syn_c1st)) A (syn_cvv) V
  have p0004 :=
    @g_mpan (.classMem (syn_ccnv (syn_c1st)) (syn_cvv)) (.classMem A V) (.classMem (syn_cima (syn_ccnv (syn_c1st)) A) (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_n_2ndex
  have p0006 :=
    @g_cnvex (syn_c2nd) p0005
  have p0007 :=
    @g_imaexg (syn_ccnv (syn_c2nd)) B (syn_cvv) W
  have p0008 :=
    @g_mpan (.classMem (syn_ccnv (syn_c2nd)) (syn_cvv)) (.classMem B W) (.classMem (syn_cima (syn_ccnv (syn_c2nd)) B) (syn_cvv)) p0006 p0007
  have p0009 :=
    @g_inexg (syn_cima (syn_ccnv (syn_c1st)) A) (syn_cima (syn_ccnv (syn_c2nd)) B) (syn_cvv) (syn_cvv)
  have p0010 :=
    @g_syl2an (.classMem A V) (.classMem (syn_cima (syn_ccnv (syn_c1st)) A) (syn_cvv)) (.classMem (syn_cima (syn_ccnv (syn_c2nd)) B) (syn_cvv)) (.classMem (syn_cin (syn_cima (syn_ccnv (syn_c1st)) A) (syn_cima (syn_ccnv (syn_c2nd)) B)) (syn_cvv)) (.classMem B W) p0004 p0008 p0009
  have p0011 :=
    @g_syl5eqel (syn_wa (.classMem A V) (.classMem B W)) (syn_cxp A B) (syn_cin (syn_cima (syn_ccnv (syn_c1st)) A) (syn_cima (syn_ccnv (syn_c2nd)) B)) (syn_cvv) p0000 p0010
  exact p0011

noncomputable def g_xpex
    (A : Class) (B : Class) (hyp_xpex_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_xpex_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cxp A B) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_xpexg A B (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem (syn_cxp A B) (syn_cvv)) hyp_xpex_1 hyp_xpex_2 p0000
  exact p0001

noncomputable def g_resexg
    (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem B W)) (.classMem (syn_cres A B) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  have p0000 :=
    (by simpa [syn_cres] using (Nominal.classEqRefl (syn_cres A B)))
  have p0001 :=
    @g_vvex
  have p0002 :=
    @g_xpexg B (syn_cvv) W (syn_cvv)
  have p0003 :=
    @g_mpan2 (.classMem B W) (.classMem (syn_cvv) (syn_cvv)) (.classMem (syn_cxp B (syn_cvv)) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_inexg A (syn_cxp B (syn_cvv)) V (syn_cvv)
  have p0005 :=
    @g_sylan2 (.classMem B W) (.classMem A V) (.classMem (syn_cxp B (syn_cvv)) (syn_cvv)) (.classMem (syn_cin A (syn_cxp B (syn_cvv))) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_syl5eqel (syn_wa (.classMem A V) (.classMem B W)) (syn_cres A B) (syn_cin A (syn_cxp B (syn_cvv))) (syn_cvv) p0000 p0005
  exact p0006

noncomputable def g_resex
    (A : Class) (B : Class) (hyp_resex_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_resex_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cres A B) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_resexg A B (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem (syn_cres A B) (syn_cvv)) hyp_resex_1 hyp_resex_2 p0000
  exact p0001

noncomputable def g_dffun2
    (x : Var) (y : Var) (z : Var) (A : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf (syn_wb (syn_wfun A) (.all x (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z))) (.objEq y z)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ A.fv
  have dv_cache_0001 : y ∉ ((syn_ccom A (syn_ccnv A))).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((syn_ccom A (syn_ccnv A))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_cid)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((syn_cid)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show y ≠ z from (by exact dv_y_z))
  have dv_cache_0006 : x ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_x_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_x_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((syn_ccnv A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ ((Wff.objEq y z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_x_y, dv_x_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    (by simpa [syn_wb, syn_wfun] using (Nominal.biimpRefl (syn_wfun A)))
  have p0001 :=
    @g_ssrel y z (syn_ccom A (syn_ccnv A)) (syn_cid) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0002 :=
    @g_opelco x (.cv y) (.cv z) A (syn_ccnv A) dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0003 :=
    @g_brcnv (.cv y) (.cv x) A
  have p0004 :=
    @g_anbi1i (syn_wbr (.cv y) (syn_ccnv A) (.cv x)) (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z)) p0003
  have p0005 :=
    @g_exbii (syn_wa (syn_wbr (.cv y) (syn_ccnv A) (.cv x)) (syn_wbr (.cv x) A (.cv z))) (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z))) x p0004
  have p0006 :=
    @g_bitri (.classMem (syn_cop (.cv y) (.cv z)) (syn_ccom A (syn_ccnv A))) (syn_wex x (syn_wa (syn_wbr (.cv y) (syn_ccnv A) (.cv x)) (syn_wbr (.cv x) A (.cv z)))) (syn_wex x (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z)))) p0002 p0005
  have p0007 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv y) (syn_cid) (.cv z))))
  have p0008 :=
    @g_vex z
  have p0009 :=
    @g_ideq (.cv y) (.cv z) p0008
  have p0010_e01_recanon : Nominal.NPrf (syn_wb (syn_wbr (.cv y) (syn_cid) (.cv z)) (.objEq y z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_cid syn_copab
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0009
  have p0010 :=
    @g_bitr3i (.classMem (syn_cop (.cv y) (.cv z)) (syn_cid)) (syn_wbr (.cv y) (syn_cid) (.cv z)) (.objEq y z) p0007 p0010_e01_recanon
  have p0011 :=
    @g_imbi12i (.classMem (syn_cop (.cv y) (.cv z)) (syn_ccom A (syn_ccnv A))) (syn_wex x (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z)))) (.classMem (syn_cop (.cv y) (.cv z)) (syn_cid)) (.objEq y z) p0006 p0010
  have p0012 :=
    @g_n_19_23v (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z))) (.objEq y z) x dv_cache_0010
  have p0013 :=
    @g_bitr4i (.imp (.classMem (syn_cop (.cv y) (.cv z)) (syn_ccom A (syn_ccnv A))) (.classMem (syn_cop (.cv y) (.cv z)) (syn_cid))) (.imp (syn_wex x (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z)))) (.objEq y z)) (.all x (.imp (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z))) (.objEq y z))) p0011 p0012
  have p0014 :=
    @g_n_2albii (.imp (.classMem (syn_cop (.cv y) (.cv z)) (syn_ccom A (syn_ccnv A))) (.classMem (syn_cop (.cv y) (.cv z)) (syn_cid))) (.all x (.imp (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z))) (.objEq y z))) y z p0013
  have p0015 :=
    @g_alrot3 (.imp (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z))) (.objEq y z)) x y z
  have p0016 :=
    @g_bitr4i (.all y (.all z (.imp (.classMem (syn_cop (.cv y) (.cv z)) (syn_ccom A (syn_ccnv A))) (.classMem (syn_cop (.cv y) (.cv z)) (syn_cid))))) (.all y (.all z (.all x (.imp (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z))) (.objEq y z))))) (.all x (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z))) (.objEq y z))))) p0014 p0015
  have p0017 :=
    @g_n_3bitri (syn_wfun A) (syn_wss (syn_ccom A (syn_ccnv A)) (syn_cid)) (.all y (.all z (.imp (.classMem (syn_cop (.cv y) (.cv z)) (syn_ccom A (syn_ccnv A))) (.classMem (syn_cop (.cv y) (.cv z)) (syn_cid))))) (.all x (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z))) (.objEq y z))))) p0000 p0001 p0016
  exact p0017

noncomputable def g_dffun3
    (x : Var) (y : Var) (z : Var) (A : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf (syn_wb (syn_wfun A) (.all x (syn_wex z (.all y (.imp (syn_wbr (.cv x) A (.cv y)) (.objEq y z)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ A.fv
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
  have dv_cache_0004 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0005 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0006 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show y ≠ z from (by exact dv_y_z))
  have dv_cache_0007 : z ∉ ((syn_wbr (.cv x) A (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_z), (Ne.symm dv_y_z), dv_A_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_wbr (.cv x) A (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_y), dv_y_z, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_dffun2 x y z A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_breq2 (.cv y) (.cv z) (.cv x) A
  have p0002_e00_recanon : Nominal.NPrf (.imp (.objEq y z) (syn_wb (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z)))) :=
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
      p0001
  have p0002 :=
    @g_mo4 (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z)) y z dv_cache_0007 dv_cache_0008 dv_cache_0006 p0002_e00_recanon
  have p0003 :=
    @g_nfv (syn_wbr (.cv x) A (.cv y)) z dv_cache_0007
  have p0004 :=
    @g_mo2 (syn_wbr (.cv x) A (.cv y)) y z dv_cache_0006 p0003
  have p0005 :=
    @g_bitr3i (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z))) (.objEq y z)))) (syn_wmo y (syn_wbr (.cv x) A (.cv y))) (syn_wex z (.all y (.imp (syn_wbr (.cv x) A (.cv y)) (.objEq y z)))) p0002 p0004
  have p0006 :=
    @g_albii (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z))) (.objEq y z)))) (syn_wex z (.all y (.imp (syn_wbr (.cv x) A (.cv y)) (.objEq y z)))) x p0005
  have p0007 :=
    @g_bitri (syn_wfun A) (.all x (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z))) (.objEq y z))))) (.all x (syn_wex z (.all y (.imp (syn_wbr (.cv x) A (.cv y)) (.objEq y z))))) p0000 p0006
  exact p0007

noncomputable def g_dffun4
    (x : Var) (y : Var) (z : Var) (A : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf (syn_wb (syn_wfun A) (.all x (.all y (.all z (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (syn_cop (.cv x) (.cv z)) A)) (.objEq y z)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ A.fv
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
  have dv_cache_0004 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0005 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0006 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show y ≠ z from (by exact dv_y_z))
  have p0000 :=
    @g_dffun2 x y z A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) A (.cv y))))
  have p0002 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) A (.cv z))))
  have p0003 :=
    @g_anbi12i (syn_wbr (.cv x) A (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) A) (syn_wbr (.cv x) A (.cv z)) (.classMem (syn_cop (.cv x) (.cv z)) A) p0001 p0002
  have p0004 :=
    @g_imbi1i (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z))) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (syn_cop (.cv x) (.cv z)) A)) (.objEq y z) p0003
  have p0005 :=
    @g_albii (.imp (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z))) (.objEq y z)) (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (syn_cop (.cv x) (.cv z)) A)) (.objEq y z)) z p0004
  have p0006 :=
    @g_n_2albii (.all z (.imp (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z))) (.objEq y z))) (.all z (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (syn_cop (.cv x) (.cv z)) A)) (.objEq y z))) x y p0005
  have p0007 :=
    @g_bitri (syn_wfun A) (.all x (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z))) (.objEq y z))))) (.all x (.all y (.all z (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (syn_cop (.cv x) (.cv z)) A)) (.objEq y z))))) p0000 p0006
  exact p0007

#print axioms g_dffun4

end NFChoice.DirectNominalPrf.WPPReplay
