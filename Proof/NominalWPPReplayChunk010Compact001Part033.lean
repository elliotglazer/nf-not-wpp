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
import NominalWPPReplayChunk010Compact001Part032

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

noncomputable def g_phi11lem1
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq (syn_cphi A) (syn_cphi B)) (syn_wss A B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let z : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_z_ne_y : z ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_ne_x : z ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have dv_cache_0001 : y ∉ ((Class.cv z)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Wff.classEq (syn_cplc (.cv z) (syn_c1c)) (syn_cif (.classMem (.cv z) (syn_cnnc)) (syn_cplc (.cv z) (syn_c1c)) (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Wff.classEq (.cv x) (syn_cplc (.cv z) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have dv_cache_0007 : x ∉ ((syn_cplc (.cv z) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_wrex y A (.classEq (syn_cplc (.cv z) (syn_c1c)) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_z, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((syn_wrex y B (.classEq (syn_cplc (.cv z) (syn_c1c)) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, fresh_x_ne_z, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ ((Wff.classMem (.cv z) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : y ∉ ((Wff.classMem (.cv z) (syn_cnnc))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : y ∉ ((Wff.classEq (.cv z) (syn_cif (.classMem (.cv z) (syn_cnnc)) (syn_cplc (.cv z) (syn_c1c)) (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : y ∉ ((Wff.objEq x z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : x ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : x ∉ ((syn_wrex y A (.classEq (.cv z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_z, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : x ∉ ((syn_wrex y B (.classEq (.cv z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, fresh_x_ne_z, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : y ∉ ((Wff.neg (.classMem (.cv z) (syn_cnnc)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : z ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : z ∉ ((Wff.classEq (syn_cphi A) (syn_cphi B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_iftrue (.classMem (.cv z) (syn_cnnc)) (syn_cplc (.cv z) (syn_c1c)) (.cv z)
  have p0001 :=
    @g_eqcomd (.classMem (.cv z) (syn_cnnc)) (syn_cif (.classMem (.cv z) (syn_cnnc)) (syn_cplc (.cv z) (syn_c1c)) (.cv z)) (syn_cplc (.cv z) (syn_c1c)) p0000
  have p0002 :=
    @g_eleq1 (.cv y) (.cv z) (syn_cnnc)
  have p0003 :=
    @g_addceq1 (.cv y) (.cv z) (syn_c1c)
  have p0004 :=
    @g_id (.objEq y z)
  have p0005_e00_recanon : Nominal.NPrf (.imp (.objEq y z) (syn_wb (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cnnc syn_cint syn_wa syn_c0c syn_csn syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_cvv syn_wral syn_cplc syn_wrex syn_wex syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0002
  have p0005_e01_recanon : Nominal.NPrf (.imp (.objEq y z) (.classEq (syn_cplc (.cv y) (syn_c1c)) (syn_cplc (.cv z) (syn_c1c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cplc syn_wrex syn_wex syn_wa syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0003
  have p0005_e02_recanon : Nominal.NPrf (.imp (.objEq y z) (.classEq (.cv y) (.cv z))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
      )
      p0004
  have p0005 :=
    @g_ifbieq12d (.objEq y z) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y) (syn_cplc (.cv z) (syn_c1c)) (.cv z) p0005_e00_recanon p0005_e01_recanon p0005_e02_recanon
  have p0006 :=
    @g_eqeq2d (.objEq y z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)) (syn_cif (.classMem (.cv z) (syn_cnnc)) (syn_cplc (.cv z) (syn_c1c)) (.cv z)) (syn_cplc (.cv z) (syn_c1c)) p0005
  have p0007_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv y) (.cv z)) (syn_wb (.classEq (syn_cplc (.cv z) (syn_c1c)) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.classEq (syn_cplc (.cv z) (syn_c1c)) (syn_cif (.classMem (.cv z) (syn_cnnc)) (syn_cplc (.cv z) (syn_c1c)) (.cv z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cplc syn_wrex syn_wex syn_wa syn_c1c syn_cif syn_wo syn_cnnc syn_cint
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0006
  have p0007 :=
    @g_rspcev (.classEq (syn_cplc (.cv z) (syn_c1c)) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.classEq (syn_cplc (.cv z) (syn_c1c)) (syn_cif (.classMem (.cv z) (syn_cnnc)) (syn_cplc (.cv z) (syn_c1c)) (.cv z))) y (.cv z) A dv_cache_0001 dv_cache_0002 dv_cache_0003 p0007_e00_recanon
  have p0008 :=
    @g_sylan2 (.classMem (.cv z) (syn_cnnc)) (.classMem (.cv z) A) (.classEq (syn_cplc (.cv z) (syn_c1c)) (syn_cif (.classMem (.cv z) (syn_cnnc)) (syn_cplc (.cv z) (syn_c1c)) (.cv z))) (syn_wrex y A (.classEq (syn_cplc (.cv z) (syn_c1c)) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) p0001 p0007
  have p0009 :=
    @g_ancoms (.classMem (.cv z) A) (.classMem (.cv z) (syn_cnnc)) (syn_wrex y A (.classEq (syn_cplc (.cv z) (syn_c1c)) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) p0008
  have p0010 :=
    @g_vex z
  have p0011 :=
    @g_n_1cex
  have p0012 :=
    @g_addcex (.cv z) (syn_c1c) p0010 p0011
  have p0013 :=
    @g_eqeq1 (.cv x) (syn_cplc (.cv z) (syn_c1c)) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))
  have p0014 :=
    @g_rexbidv (.classEq (.cv x) (syn_cplc (.cv z) (syn_c1c))) (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.classEq (syn_cplc (.cv z) (syn_c1c)) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) y A dv_cache_0004 p0013
  have p0015 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_phi y x A dv_cache_0002 dv_cache_0005 dv_cache_0006
  have p0016 :=
    @g_elab2 (syn_wrex y A (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) (syn_wrex y A (.classEq (syn_cplc (.cv z) (syn_c1c)) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) x (syn_cplc (.cv z) (syn_c1c)) (syn_cphi A) dv_cache_0007 dv_cache_0008 p0012 p0014 p0015
  have p0017 :=
    @g_sylibr (syn_wa (.classMem (.cv z) (syn_cnnc)) (.classMem (.cv z) A)) (syn_wrex y A (.classEq (syn_cplc (.cv z) (syn_c1c)) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) (.classMem (syn_cplc (.cv z) (syn_c1c)) (syn_cphi A)) p0009 p0016
  have p0018 :=
    @g_eleq2 (syn_cphi A) (syn_cphi B) (syn_cplc (.cv z) (syn_c1c))
  have p0019 :=
    @g_biimpac (.classEq (syn_cphi A) (syn_cphi B)) (.classMem (syn_cplc (.cv z) (syn_c1c)) (syn_cphi A)) (.classMem (syn_cplc (.cv z) (syn_c1c)) (syn_cphi B)) p0018
  have p0020 :=
    @g_rexbidv (.classEq (.cv x) (syn_cplc (.cv z) (syn_c1c))) (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.classEq (syn_cplc (.cv z) (syn_c1c)) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) y B dv_cache_0004 p0013
  have p0021 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_phi y x B dv_cache_0009 dv_cache_0010 dv_cache_0006
  have p0022 :=
    @g_elab2 (syn_wrex y B (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) (syn_wrex y B (.classEq (syn_cplc (.cv z) (syn_c1c)) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) x (syn_cplc (.cv z) (syn_c1c)) (syn_cphi B) dv_cache_0007 dv_cache_0011 p0012 p0020 p0021
  have p0023 :=
    @g_iffalse (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)
  have p0024 :=
    @g_eqeq2d (.neg (.classMem (.cv y) (syn_cnnc))) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)) (.cv y) (syn_cplc (.cv z) (syn_c1c)) p0023
  have p0025 :=
    @g_biimpac (.neg (.classMem (.cv y) (syn_cnnc))) (.classEq (syn_cplc (.cv z) (syn_c1c)) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.classEq (syn_cplc (.cv z) (syn_c1c)) (.cv y)) p0024
  have p0026 :=
    @g_peano2 (.cv z)
  have p0027 :=
    @g_eleq1 (syn_cplc (.cv z) (syn_c1c)) (.cv y) (syn_cnnc)
  have p0028 :=
    @g_syl5ibcom (.classMem (.cv z) (syn_cnnc)) (.classMem (syn_cplc (.cv z) (syn_c1c)) (syn_cnnc)) (.classEq (syn_cplc (.cv z) (syn_c1c)) (.cv y)) (.classMem (.cv y) (syn_cnnc)) p0026 p0027
  have p0029 :=
    @g_syl5 (syn_wa (.classEq (syn_cplc (.cv z) (syn_c1c)) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.neg (.classMem (.cv y) (syn_cnnc)))) (.classEq (syn_cplc (.cv z) (syn_c1c)) (.cv y)) (.classMem (.cv z) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) p0025 p0028
  have p0030 :=
    @g_expdimp (.classMem (.cv z) (syn_cnnc)) (.classEq (syn_cplc (.cv z) (syn_c1c)) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.neg (.classMem (.cv y) (syn_cnnc))) (.classMem (.cv y) (syn_cnnc)) p0029
  have p0031 :=
    @g_pm2_18d (syn_wa (.classMem (.cv z) (syn_cnnc)) (.classEq (syn_cplc (.cv z) (syn_c1c)) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) (.classMem (.cv y) (syn_cnnc)) p0030
  have p0032 :=
    @g_simpl (.classMem (.cv z) (syn_cnnc)) (.classEq (syn_cplc (.cv z) (syn_c1c)) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))
  have p0033 :=
    @g_simpr (.classMem (.cv z) (syn_cnnc)) (.classEq (syn_cplc (.cv z) (syn_c1c)) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))
  have p0034 :=
    @g_iftrue (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)
  have p0035 :=
    @g_syl (syn_wa (.classMem (.cv z) (syn_cnnc)) (.classEq (syn_cplc (.cv z) (syn_c1c)) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) (.classMem (.cv y) (syn_cnnc)) (.classEq (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)) (syn_cplc (.cv y) (syn_c1c))) p0031 p0034
  have p0036 :=
    @g_eqtr2d (syn_wa (.classMem (.cv z) (syn_cnnc)) (.classEq (syn_cplc (.cv z) (syn_c1c)) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) (syn_cplc (.cv z) (syn_c1c)) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)) (syn_cplc (.cv y) (syn_c1c)) p0033 p0035
  have p0037 :=
    @g_peano4 (.cv y) (.cv z)
  have p0038_e03_recanon : Nominal.NPrf (.imp (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc)) (.classEq (syn_cplc (.cv y) (syn_c1c)) (syn_cplc (.cv z) (syn_c1c)))) (.objEq y z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_cnnc syn_cint syn_cplc syn_wrex syn_wex syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0037
  have p0038 :=
    @g_syl3anc (syn_wa (.classMem (.cv z) (syn_cnnc)) (.classEq (syn_cplc (.cv z) (syn_c1c)) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc)) (.classEq (syn_cplc (.cv y) (syn_c1c)) (syn_cplc (.cv z) (syn_c1c))) (.objEq y z) p0031 p0032 p0036 p0038_e03_recanon
  have p0039 :=
    @g_n_3adant2 (.classMem (.cv z) (syn_cnnc)) (.classEq (syn_cplc (.cv z) (syn_c1c)) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.objEq y z) (.classMem (.cv y) B) p0038
  have p0040 :=
    @g_simp2 (.classMem (.cv z) (syn_cnnc)) (.classMem (.cv y) B) (.classEq (syn_cplc (.cv z) (syn_c1c)) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))
  have p0041_e00_recanon : Nominal.NPrf (.imp (syn_w3a (.classMem (.cv z) (syn_cnnc)) (.classMem (.cv y) B) (.classEq (syn_cplc (.cv z) (syn_c1c)) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) (.classEq (.cv y) (.cv z))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_cnnc syn_cint syn_cplc syn_wrex syn_wex syn_c1c syn_cif syn_wo
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
      )
      p0039
  have p0041 :=
    @g_eqeltrrd (syn_w3a (.classMem (.cv z) (syn_cnnc)) (.classMem (.cv y) B) (.classEq (syn_cplc (.cv z) (syn_c1c)) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) (.cv y) (.cv z) B p0041_e00_recanon p0040
  have p0042 :=
    @g_n_3expia (.classMem (.cv z) (syn_cnnc)) (.classMem (.cv y) B) (.classEq (syn_cplc (.cv z) (syn_c1c)) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.classMem (.cv z) B) p0041
  have p0043 :=
    @g_rexlimdva (.classMem (.cv z) (syn_cnnc)) (.classEq (syn_cplc (.cv z) (syn_c1c)) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.classMem (.cv z) B) y B dv_cache_0012 dv_cache_0013 p0042
  have p0044 :=
    @g_syl5bi (.classMem (syn_cplc (.cv z) (syn_c1c)) (syn_cphi B)) (syn_wrex y B (.classEq (syn_cplc (.cv z) (syn_c1c)) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) (.classMem (.cv z) (syn_cnnc)) (.classMem (.cv z) B) p0022 p0043
  have p0045 :=
    @g_syl5 (syn_wa (.classMem (syn_cplc (.cv z) (syn_c1c)) (syn_cphi A)) (.classEq (syn_cphi A) (syn_cphi B))) (.classMem (syn_cplc (.cv z) (syn_c1c)) (syn_cphi B)) (.classMem (.cv z) (syn_cnnc)) (.classMem (.cv z) B) p0019 p0044
  have p0046 :=
    @g_exp3a (.classMem (.cv z) (syn_cnnc)) (.classMem (syn_cplc (.cv z) (syn_c1c)) (syn_cphi A)) (.classEq (syn_cphi A) (syn_cphi B)) (.classMem (.cv z) B) p0045
  have p0047 :=
    @g_adantr (.classMem (.cv z) (syn_cnnc)) (.imp (.classMem (syn_cplc (.cv z) (syn_c1c)) (syn_cphi A)) (.imp (.classEq (syn_cphi A) (syn_cphi B)) (.classMem (.cv z) B))) (.classMem (.cv z) A) p0046
  have p0048 :=
    @g_mpd (syn_wa (.classMem (.cv z) (syn_cnnc)) (.classMem (.cv z) A)) (.classMem (syn_cplc (.cv z) (syn_c1c)) (syn_cphi A)) (.imp (.classEq (syn_cphi A) (syn_cphi B)) (.classMem (.cv z) B)) p0017 p0047
  have p0049 :=
    @g_iffalse (.classMem (.cv z) (syn_cnnc)) (syn_cplc (.cv z) (syn_c1c)) (.cv z)
  have p0050 :=
    @g_eqcomd (.neg (.classMem (.cv z) (syn_cnnc))) (syn_cif (.classMem (.cv z) (syn_cnnc)) (syn_cplc (.cv z) (syn_c1c)) (.cv z)) (.cv z) p0049
  have p0051 :=
    @g_eqeq2d (.objEq y z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)) (syn_cif (.classMem (.cv z) (syn_cnnc)) (syn_cplc (.cv z) (syn_c1c)) (.cv z)) (.cv z) p0005
  have p0052_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv y) (.cv z)) (syn_wb (.classEq (.cv z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.classEq (.cv z) (syn_cif (.classMem (.cv z) (syn_cnnc)) (syn_cplc (.cv z) (syn_c1c)) (.cv z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cif syn_wo syn_wa syn_cnnc syn_cint syn_cplc syn_wrex syn_wex syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0051
  have p0052 :=
    @g_rspcev (.classEq (.cv z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.classEq (.cv z) (syn_cif (.classMem (.cv z) (syn_cnnc)) (syn_cplc (.cv z) (syn_c1c)) (.cv z))) y (.cv z) A dv_cache_0001 dv_cache_0002 dv_cache_0014 p0052_e00_recanon
  have p0053 :=
    @g_sylan2 (.neg (.classMem (.cv z) (syn_cnnc))) (.classMem (.cv z) A) (.classEq (.cv z) (syn_cif (.classMem (.cv z) (syn_cnnc)) (syn_cplc (.cv z) (syn_c1c)) (.cv z))) (syn_wrex y A (.classEq (.cv z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) p0050 p0052
  have p0054 :=
    @g_ancoms (.classMem (.cv z) A) (.neg (.classMem (.cv z) (syn_cnnc))) (syn_wrex y A (.classEq (.cv z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) p0053
  have p0055 :=
    @g_eqeq1 (.cv x) (.cv z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))
  have p0056_e00_recanon : Nominal.NPrf (.imp (.objEq x z) (syn_wb (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.classEq (.cv z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cif syn_wo syn_wa syn_cnnc syn_cint syn_cplc syn_wrex syn_wex syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0055
  have p0056 :=
    @g_rexbidv (.objEq x z) (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.classEq (.cv z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) y A dv_cache_0015 p0056_e00_recanon
  have p0057_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv x) (.cv z)) (syn_wb (syn_wrex y A (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) (syn_wrex y A (.classEq (.cv z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wrex syn_wex syn_wa syn_cif syn_wo syn_cnnc syn_cint syn_cplc syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0056
  have p0057 :=
    @g_elab2 (syn_wrex y A (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) (syn_wrex y A (.classEq (.cv z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) x (.cv z) (syn_cphi A) dv_cache_0016 dv_cache_0017 p0010 p0057_e01_recanon p0015
  have p0058 :=
    @g_sylibr (syn_wa (.neg (.classMem (.cv z) (syn_cnnc))) (.classMem (.cv z) A)) (syn_wrex y A (.classEq (.cv z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) (.classMem (.cv z) (syn_cphi A)) p0054 p0057
  have p0059 :=
    @g_eleq2 (syn_cphi A) (syn_cphi B) (.cv z)
  have p0060 :=
    @g_biimpac (.classEq (syn_cphi A) (syn_cphi B)) (.classMem (.cv z) (syn_cphi A)) (.classMem (.cv z) (syn_cphi B)) p0059
  have p0061_e00_recanon : Nominal.NPrf (.imp (.objEq x z) (syn_wb (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.classEq (.cv z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cif syn_wo syn_wa syn_cnnc syn_cint syn_cplc syn_wrex syn_wex syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0055
  have p0061 :=
    @g_rexbidv (.objEq x z) (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.classEq (.cv z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) y B dv_cache_0015 p0061_e00_recanon
  have p0062_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv x) (.cv z)) (syn_wb (syn_wrex y B (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) (syn_wrex y B (.classEq (.cv z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wrex syn_wex syn_wa syn_cif syn_wo syn_cnnc syn_cint syn_cplc syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0061
  have p0062 :=
    @g_elab2 (syn_wrex y B (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) (syn_wrex y B (.classEq (.cv z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) x (.cv z) (syn_cphi B) dv_cache_0016 dv_cache_0018 p0010 p0062_e01_recanon p0021
  have p0063 :=
    @g_simpr (.neg (.classMem (.cv z) (syn_cnnc))) (.classEq (.cv z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))
  have p0064 :=
    @g_eqeq2d (.classMem (.cv y) (syn_cnnc)) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)) (syn_cplc (.cv y) (syn_c1c)) (.cv z) p0034
  have p0065 :=
    @g_peano2 (.cv y)
  have p0066 :=
    @g_eleq1a (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc) (.cv z)
  have p0067 :=
    @g_syl (.classMem (.cv y) (syn_cnnc)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.imp (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c))) (.classMem (.cv z) (syn_cnnc))) p0065 p0066
  have p0068 :=
    @g_sylbid (.classMem (.cv y) (syn_cnnc)) (.classEq (.cv z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c))) (.classMem (.cv z) (syn_cnnc)) p0064 p0067
  have p0069 :=
    @g_com12 (.classMem (.cv y) (syn_cnnc)) (.classEq (.cv z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.classMem (.cv z) (syn_cnnc)) p0068
  have p0070 :=
    @g_con3d (.classEq (.cv z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc)) p0069
  have p0071 :=
    @g_impcom (.classEq (.cv z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.neg (.classMem (.cv z) (syn_cnnc))) (.neg (.classMem (.cv y) (syn_cnnc))) p0070
  have p0072 :=
    @g_syl (syn_wa (.neg (.classMem (.cv z) (syn_cnnc))) (.classEq (.cv z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) (.neg (.classMem (.cv y) (syn_cnnc))) (.classEq (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)) (.cv y)) p0071 p0023
  have p0073 :=
    @g_eqtr2d (syn_wa (.neg (.classMem (.cv z) (syn_cnnc))) (.classEq (.cv z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) (.cv z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)) (.cv y) p0063 p0072
  have p0074_e00_recanon : Nominal.NPrf (.imp (syn_wa (.neg (.classMem (.cv z) (syn_cnnc))) (.classEq (.cv z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) (.objEq y z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cnnc syn_cint syn_cif syn_wo syn_cplc syn_wrex syn_wex syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0073
  have p0074 :=
    @g_adantlr (.neg (.classMem (.cv z) (syn_cnnc))) (.classEq (.cv z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.objEq y z) (.classMem (.cv y) B) p0074_e00_recanon
  have p0075 :=
    @g_simplr (.neg (.classMem (.cv z) (syn_cnnc))) (.classMem (.cv y) B) (.classEq (.cv z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))
  have p0076_e00_recanon : Nominal.NPrf (.imp (syn_wa (syn_wa (.neg (.classMem (.cv z) (syn_cnnc))) (.classMem (.cv y) B)) (.classEq (.cv z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) (.classEq (.cv y) (.cv z))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cif syn_wo syn_cnnc syn_cint syn_cplc syn_wrex syn_wex syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
      )
      p0074
  have p0076 :=
    @g_eqeltrrd (syn_wa (syn_wa (.neg (.classMem (.cv z) (syn_cnnc))) (.classMem (.cv y) B)) (.classEq (.cv z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) (.cv y) (.cv z) B p0076_e00_recanon p0075
  have p0077 :=
    @g_ex (syn_wa (.neg (.classMem (.cv z) (syn_cnnc))) (.classMem (.cv y) B)) (.classEq (.cv z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.classMem (.cv z) B) p0076
  have p0078 :=
    @g_rexlimdva (.neg (.classMem (.cv z) (syn_cnnc))) (.classEq (.cv z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.classMem (.cv z) B) y B dv_cache_0012 dv_cache_0019 p0077
  have p0079 :=
    @g_syl5bi (.classMem (.cv z) (syn_cphi B)) (syn_wrex y B (.classEq (.cv z) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) (.neg (.classMem (.cv z) (syn_cnnc))) (.classMem (.cv z) B) p0062 p0078
  have p0080 :=
    @g_syl5 (syn_wa (.classMem (.cv z) (syn_cphi A)) (.classEq (syn_cphi A) (syn_cphi B))) (.classMem (.cv z) (syn_cphi B)) (.neg (.classMem (.cv z) (syn_cnnc))) (.classMem (.cv z) B) p0060 p0079
  have p0081 :=
    @g_exp3a (.neg (.classMem (.cv z) (syn_cnnc))) (.classMem (.cv z) (syn_cphi A)) (.classEq (syn_cphi A) (syn_cphi B)) (.classMem (.cv z) B) p0080
  have p0082 :=
    @g_adantr (.neg (.classMem (.cv z) (syn_cnnc))) (.imp (.classMem (.cv z) (syn_cphi A)) (.imp (.classEq (syn_cphi A) (syn_cphi B)) (.classMem (.cv z) B))) (.classMem (.cv z) A) p0081
  have p0083 :=
    @g_mpd (syn_wa (.neg (.classMem (.cv z) (syn_cnnc))) (.classMem (.cv z) A)) (.classMem (.cv z) (syn_cphi A)) (.imp (.classEq (syn_cphi A) (syn_cphi B)) (.classMem (.cv z) B)) p0058 p0082
  have p0084 :=
    @g_pm2_61ian (.classMem (.cv z) (syn_cnnc)) (.classMem (.cv z) A) (.imp (.classEq (syn_cphi A) (syn_cphi B)) (.classMem (.cv z) B)) p0048 p0083
  have p0085 :=
    @g_com12 (.classMem (.cv z) A) (.classEq (syn_cphi A) (syn_cphi B)) (.classMem (.cv z) B) p0084
  have p0086 :=
    @g_ssrdv (.classEq (syn_cphi A) (syn_cphi B)) z A B dv_cache_0020 dv_cache_0021 dv_cache_0022 p0085
  exact p0086

noncomputable def g_phi11
    (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (.classEq A B) (.classEq (syn_cphi A) (syn_cphi B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_phieq A B
  have p0001 :=
    @g_phi11lem1 A B
  have p0002 :=
    @g_phi11lem1 B A
  have p0003 :=
    @g_eqcoms (syn_wss B A) (syn_cphi B) (syn_cphi A) p0002
  have p0004 :=
    @g_eqssd (.classEq (syn_cphi A) (syn_cphi B)) A B p0001 p0003
  have p0005 :=
    @g_impbii (.classEq A B) (.classEq (syn_cphi A) (syn_cphi B)) p0000 p0004
  exact p0005

noncomputable def g_n_0cnelphi
    (A : Class) :
    Nominal.NPrf (.neg (.classMem (syn_c0c) (syn_cphi A))) := by
  let proofSupport : Finset Var := A.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have dv_cache_0001 : y ∉ ((Wff.classEq (.cv x) (syn_c0c))).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have dv_cache_0005 : x ∉ ((syn_c0c)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_wrex y A (.classEq (syn_c0c) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_n_0cnsuc (.cv y)
  have p0001 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (syn_cplc (.cv y) (syn_c1c)) (syn_c0c))))
  have p0002 :=
    @g_mpbi (syn_wne (syn_cplc (.cv y) (syn_c1c)) (syn_c0c)) (.neg (.classEq (syn_cplc (.cv y) (syn_c1c)) (syn_c0c))) p0000 p0001
  have p0003 :=
    @g_iffalse (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)
  have p0004 :=
    @g_eqeq2d (.neg (.classMem (.cv y) (syn_cnnc))) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)) (.cv y) (syn_c0c) p0003
  have p0005 :=
    @g_biimpac (.neg (.classMem (.cv y) (syn_cnnc))) (.classEq (syn_c0c) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.classEq (syn_c0c) (.cv y)) p0004
  have p0006 :=
    @g_peano1
  have p0007 :=
    @g_syl6eqelr (syn_wa (.classEq (syn_c0c) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.neg (.classMem (.cv y) (syn_cnnc)))) (.cv y) (syn_c0c) (syn_cnnc) p0005 p0006
  have p0008 :=
    @g_ex (.classEq (syn_c0c) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.neg (.classMem (.cv y) (syn_cnnc))) (.classMem (.cv y) (syn_cnnc)) p0007
  have p0009 :=
    @g_pm2_18d (.classEq (syn_c0c) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.classMem (.cv y) (syn_cnnc)) p0008
  have p0010 :=
    @g_iftrue (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)
  have p0011 :=
    @g_eqeq2d (.classMem (.cv y) (syn_cnnc)) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)) (syn_cplc (.cv y) (syn_c1c)) (syn_c0c) p0010
  have p0012 :=
    @g_eqcom (syn_c0c) (syn_cplc (.cv y) (syn_c1c))
  have p0013 :=
    @g_syl6bb (.classMem (.cv y) (syn_cnnc)) (.classEq (syn_c0c) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.classEq (syn_c0c) (syn_cplc (.cv y) (syn_c1c))) (.classEq (syn_cplc (.cv y) (syn_c1c)) (syn_c0c)) p0011 p0012
  have p0014 :=
    @g_biimpd (.classMem (.cv y) (syn_cnnc)) (.classEq (syn_c0c) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.classEq (syn_cplc (.cv y) (syn_c1c)) (syn_c0c)) p0013
  have p0015 :=
    @g_mpcom (.classMem (.cv y) (syn_cnnc)) (.classEq (syn_c0c) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.classEq (syn_cplc (.cv y) (syn_c1c)) (syn_c0c)) p0009 p0014
  have p0016 :=
    @g_mto (.classEq (syn_c0c) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.classEq (syn_cplc (.cv y) (syn_c1c)) (syn_c0c)) p0002 p0015
  have p0017 :=
    @g_a1i (.neg (.classEq (syn_c0c) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) (.classMem (.cv y) A) p0016
  have p0018 :=
    @g_nrex (.classEq (syn_c0c) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) y A p0017
  have p0019 :=
    @g_n_0cex
  have p0020 :=
    @g_eqeq1 (.cv x) (syn_c0c) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))
  have p0021 :=
    @g_rexbidv (.classEq (.cv x) (syn_c0c)) (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.classEq (syn_c0c) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) y A dv_cache_0001 p0020
  have p0022 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_phi y x A dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0023 :=
    @g_elab2 (syn_wrex y A (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) (syn_wrex y A (.classEq (syn_c0c) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) x (syn_c0c) (syn_cphi A) dv_cache_0005 dv_cache_0006 p0019 p0021 p0022
  have p0024 :=
    @g_mtbir (.classMem (syn_c0c) (syn_cphi A)) (syn_wrex y A (.classEq (syn_c0c) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) p0018 p0023
  exact p0024

#print axioms g_n_0cnelphi

end NFChoice.DirectNominalPrf.WPPReplay
