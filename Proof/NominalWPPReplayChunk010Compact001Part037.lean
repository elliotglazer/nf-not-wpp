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
import NominalWPPReplayChunk010Compact001Part036

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

noncomputable def g_phialllem1
    (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) (hyp_phiall_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wa (syn_wss A (syn_cnnc)) (.neg (.classMem (syn_c0c) A))) (syn_wex x (.classEq A (syn_cphi (.cv x))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv
  let z : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_w_not_A : w ∉ A.fv := by
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
  have dv_cache_0001 : x ∉ ((Class.cv z)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.objEq z w)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, fresh_x_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_wa (syn_wss A (syn_cnnc)) (.neg (.classMem (syn_c0c) A)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((Class.cv w)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0009 : w ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : w ∉ ((syn_wa (syn_wss A (syn_cnnc)) (.neg (.classMem (syn_c0c) A)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((syn_crab y (syn_cnnc) (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, fresh_x_ne_z, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : w ∉ ((syn_crab y (syn_cnnc) (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, fresh_w_ne_z, fresh_w_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show x ≠ w from (by exact fresh_x_ne_w))
  have dv_cache_0014 : z ∉ ((Wff.objEq y x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : y ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : y ∉ ((syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_z, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0018 : z ∉ ((Wff.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_w, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : z ∉ ((syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : z ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : y ∉ ((syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : x ∉ ((Wff.classEq A (syn_cphi (syn_crab y (syn_cnnc) (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, fresh_x_ne_z, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eleq1 (.cv z) (syn_c0c) A
  have p0001 :=
    @g_biimpcd (.classEq (.cv z) (syn_c0c)) (.classMem (.cv z) A) (.classMem (syn_c0c) A) p0000
  have p0002 :=
    @g_con3d (.classMem (.cv z) A) (.classEq (.cv z) (syn_c0c)) (.classMem (syn_c0c) A) p0001
  have p0003 :=
    @g_impcom (.classMem (.cv z) A) (.neg (.classMem (syn_c0c) A)) (.neg (.classEq (.cv z) (syn_c0c))) p0002
  have p0004 :=
    @g_adantll (.neg (.classMem (syn_c0c) A)) (.classMem (.cv z) A) (.neg (.classEq (.cv z) (syn_c0c))) (syn_wss A (syn_cnnc)) p0003
  have p0005 :=
    @g_ssel2 A (syn_cnnc) (.cv z)
  have p0006 :=
    @g_adantlr (syn_wss A (syn_cnnc)) (.classMem (.cv z) A) (.classMem (.cv z) (syn_cnnc)) (.neg (.classMem (syn_c0c) A)) p0005
  have p0007 :=
    @g_nnc0suc x (.cv z) dv_cache_0001
  have p0008 :=
    @g_sylib (syn_wa (syn_wa (syn_wss A (syn_cnnc)) (.neg (.classMem (syn_c0c) A))) (.classMem (.cv z) A)) (.classMem (.cv z) (syn_cnnc)) (syn_wo (.classEq (.cv z) (syn_c0c)) (syn_wrex x (syn_cnnc) (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))))) p0006 p0007
  have p0009 :=
    @g_orel1 (.classEq (.cv z) (syn_c0c)) (syn_wrex x (syn_cnnc) (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))))
  have p0010 :=
    @g_sylc (syn_wa (syn_wa (syn_wss A (syn_cnnc)) (.neg (.classMem (syn_c0c) A))) (.classMem (.cv z) A)) (.neg (.classEq (.cv z) (syn_c0c))) (syn_wo (.classEq (.cv z) (syn_c0c)) (syn_wrex x (syn_cnnc) (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))))) (syn_wrex x (syn_cnnc) (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))) p0004 p0008 p0009
  have p0011 :=
    @g_anidm (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))
  have p0012 :=
    @g_eqeq1 (.cv z) (.cv w) (syn_cplc (.cv x) (syn_c1c))
  have p0013_e00_recanon : Nominal.NPrf (.imp (.objEq z w) (syn_wb (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))) (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cplc syn_wrex syn_wex syn_wa syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0012
  have p0013 :=
    @g_anbi2d (.objEq z w) (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))) (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c))) (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))) p0013_e00_recanon
  have p0014 :=
    @g_syl5bbr (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))) (syn_wa (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))) (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))) (.objEq z w) (syn_wa (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))) (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c)))) p0011 p0013
  have p0015 :=
    @g_rexbidv (.objEq z w) (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))) (syn_wa (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))) (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c)))) x (syn_cnnc) dv_cache_0002 p0014
  have p0016 :=
    @g_syl5ibcom (syn_wa (syn_wa (syn_wss A (syn_cnnc)) (.neg (.classMem (syn_c0c) A))) (.classMem (.cv z) A)) (syn_wrex x (syn_cnnc) (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))) (.objEq z w) (syn_wrex x (syn_cnnc) (syn_wa (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))) (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c))))) p0010 p0015
  have p0017 :=
    @g_eqtr3 (.cv z) (.cv w) (syn_cplc (.cv x) (syn_c1c))
  have p0018_e00_recanon : Nominal.NPrf (.imp (syn_wa (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))) (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c)))) (.objEq z w)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cplc syn_wrex syn_wex syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0017
  have p0018 :=
    @g_rexlimivw (syn_wa (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))) (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c)))) (.objEq z w) x (syn_cnnc) dv_cache_0002 p0018_e00_recanon
  have p0019 :=
    @g_impbid1 (syn_wa (syn_wa (syn_wss A (syn_cnnc)) (.neg (.classMem (syn_c0c) A))) (.classMem (.cv z) A)) (.objEq z w) (syn_wrex x (syn_cnnc) (syn_wa (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))) (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c))))) p0016 p0018
  have p0020 :=
    @g_rexbidva (syn_wa (syn_wss A (syn_cnnc)) (.neg (.classMem (syn_c0c) A))) (.objEq z w) (syn_wrex x (syn_cnnc) (syn_wa (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))) (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c))))) z A dv_cache_0003 p0019
  have p0021 :=
    @g_risset z (.cv w) A dv_cache_0004 dv_cache_0005
  have p0022 :=
    @g_rexcom (syn_wa (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))) (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c)))) x z (syn_cnnc) A dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0023_e01_recanon : Nominal.NPrf (syn_wb (.classMem (.cv w) A) (syn_wrex z A (.objEq z w))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wrex syn_wex syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
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
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
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
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0021
  have p0023 :=
    @g_n_3bitr4g (syn_wa (syn_wss A (syn_cnnc)) (.neg (.classMem (syn_c0c) A))) (syn_wrex z A (.objEq z w)) (syn_wrex z A (syn_wrex x (syn_cnnc) (syn_wa (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))) (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c)))))) (.classMem (.cv w) A) (syn_wrex x (syn_cnnc) (syn_wrex z A (syn_wa (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))) (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c)))))) p0020 p0023_e01_recanon p0022
  have p0024 :=
    @g_eqabdv (syn_wa (syn_wss A (syn_cnnc)) (.neg (.classMem (syn_c0c) A))) (syn_wrex x (syn_cnnc) (syn_wrex z A (syn_wa (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))) (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c)))))) w A dv_cache_0009 dv_cache_0010 p0023
  have p0025 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_phi x w (syn_crab y (syn_cnnc) (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c))))) dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0026 :=
    @g_addceq1 (.cv y) (.cv x) (syn_c1c)
  have p0027_e00_recanon : Nominal.NPrf (.imp (.objEq y x) (.classEq (syn_cplc (.cv y) (syn_c1c)) (syn_cplc (.cv x) (syn_c1c)))) :=
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
      p0026
  have p0027 :=
    @g_eqeq2d (.objEq y x) (syn_cplc (.cv y) (syn_c1c)) (syn_cplc (.cv x) (syn_c1c)) (.cv z) p0027_e00_recanon
  have p0028 :=
    @g_rexbidv (.objEq y x) (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c))) (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))) z A dv_cache_0014 p0027
  have p0029 :=
    @g_rexrab (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c)))) (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))) (.classEq (.cv w) (syn_cif (.classMem (.cv x) (syn_cnnc)) (syn_cplc (.cv x) (syn_c1c)) (.cv x))) x y (syn_cnnc) dv_cache_0015 dv_cache_0016 dv_cache_0017 p0028
  have p0030 :=
    @g_iftrue (.classMem (.cv x) (syn_cnnc)) (syn_cplc (.cv x) (syn_c1c)) (.cv x)
  have p0031 :=
    @g_eqeq2d (.classMem (.cv x) (syn_cnnc)) (syn_cif (.classMem (.cv x) (syn_cnnc)) (syn_cplc (.cv x) (syn_c1c)) (.cv x)) (syn_cplc (.cv x) (syn_c1c)) (.cv w) p0030
  have p0032 :=
    @g_anbi2d (.classMem (.cv x) (syn_cnnc)) (.classEq (.cv w) (syn_cif (.classMem (.cv x) (syn_cnnc)) (syn_cplc (.cv x) (syn_c1c)) (.cv x))) (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c))) (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))) p0031
  have p0033 :=
    @g_r19_41v (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))) (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c))) z A dv_cache_0018
  have p0034 :=
    @g_syl6bbr (.classMem (.cv x) (syn_cnnc)) (syn_wa (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))) (.classEq (.cv w) (syn_cif (.classMem (.cv x) (syn_cnnc)) (syn_cplc (.cv x) (syn_c1c)) (.cv x)))) (syn_wa (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))) (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c)))) (syn_wrex z A (syn_wa (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))) (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c))))) p0032 p0033
  have p0035 :=
    @g_rexbiia (syn_wa (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))) (.classEq (.cv w) (syn_cif (.classMem (.cv x) (syn_cnnc)) (syn_cplc (.cv x) (syn_c1c)) (.cv x)))) (syn_wrex z A (syn_wa (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))) (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c))))) x (syn_cnnc) p0034
  have p0036 :=
    @g_bitri (syn_wrex x (syn_crab y (syn_cnnc) (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c))))) (.classEq (.cv w) (syn_cif (.classMem (.cv x) (syn_cnnc)) (syn_cplc (.cv x) (syn_c1c)) (.cv x)))) (syn_wrex x (syn_cnnc) (syn_wa (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))) (.classEq (.cv w) (syn_cif (.classMem (.cv x) (syn_cnnc)) (syn_cplc (.cv x) (syn_c1c)) (.cv x))))) (syn_wrex x (syn_cnnc) (syn_wrex z A (syn_wa (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))) (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c)))))) p0029 p0035
  have p0037 :=
    @g_abbii (syn_wrex x (syn_crab y (syn_cnnc) (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c))))) (.classEq (.cv w) (syn_cif (.classMem (.cv x) (syn_cnnc)) (syn_cplc (.cv x) (syn_c1c)) (.cv x)))) (syn_wrex x (syn_cnnc) (syn_wrex z A (syn_wa (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))) (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c)))))) w p0036
  have p0038 :=
    @g_eqtri (syn_cphi (syn_crab y (syn_cnnc) (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c)))))) (.cab w (syn_wrex x (syn_crab y (syn_cnnc) (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c))))) (.classEq (.cv w) (syn_cif (.classMem (.cv x) (syn_cnnc)) (syn_cplc (.cv x) (syn_c1c)) (.cv x))))) (.cab w (syn_wrex x (syn_cnnc) (syn_wrex z A (syn_wa (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))) (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c))))))) p0025 p0037
  have p0039 :=
    @g_syl6eqr (syn_wa (syn_wss A (syn_cnnc)) (.neg (.classMem (syn_c0c) A))) A (.cab w (syn_wrex x (syn_cnnc) (syn_wrex z A (syn_wa (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))) (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c))))))) (syn_cphi (syn_crab y (syn_cnnc) (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c)))))) p0024 p0038
  have p0040 :=
    @g_dfrab2 (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c)))) y (syn_cnnc) dv_cache_0015
  have p0041 :=
    @g_vex y
  have p0042 :=
    @g_elimak z (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) A (.cv y) dv_cache_0019 dv_cache_0005 dv_cache_0020 p0041
  have p0043 :=
    @g_vex z
  have p0044 :=
    @g_opkelimagek (.cv y) (.cv z) (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0041 p0043
  have p0045 :=
    @g_opkelcnvk (.cv z) (.cv y) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0043 p0041
  have p0046 :=
    @g_dfaddc2 (.cv y) (syn_c1c)
  have p0047 :=
    @g_eqeq2i (syn_cplc (.cv y) (syn_c1c)) (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.cv y)) (.cv z) p0046
  have p0048 :=
    @g_n_3bitr4i (.classMem (syn_copk (.cv y) (.cv z)) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (.classEq (.cv z) (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.cv y))) (.classMem (syn_copk (.cv z) (.cv y)) (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c))) p0044 p0045 p0047
  have p0049 :=
    @g_rexbii (.classMem (syn_copk (.cv z) (.cv y)) (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c))) z A p0048
  have p0050 :=
    @g_bitri (.classMem (.cv y) (syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) A)) (syn_wrex z A (.classMem (syn_copk (.cv z) (.cv y)) (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c)))) p0042 p0049
  have p0051 :=
    @g_eqabi (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c)))) y (syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) A) dv_cache_0021 p0050
  have p0052 :=
    @g_addcexlem
  have p0053 :=
    @g_n_1cex
  have p0054 :=
    @g_pw1ex (syn_c1c) p0053
  have p0055 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0054
  have p0056 :=
    @g_imakex (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))) p0052 p0055
  have p0057 :=
    @g_imagekex (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0056
  have p0058 :=
    @g_cnvkex (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0057
  have p0059 :=
    @g_imakex (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) A p0058 hyp_phiall_1
  have p0060 :=
    @g_eqeltrri (syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) A) (.cab y (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c))))) (syn_cvv) p0051 p0059
  have p0061 :=
    @g_nncex
  have p0062 :=
    @g_inex (.cab y (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c))))) (syn_cnnc) p0060 p0061
  have p0063 :=
    @g_eqeltri (syn_crab y (syn_cnnc) (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c))))) (syn_cin (.cab y (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c))))) (syn_cnnc)) (syn_cvv) p0040 p0062
  have p0064 :=
    @g_phieq (.cv x) (syn_crab y (syn_cnnc) (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c)))))
  have p0065 :=
    @g_eqeq2d (.classEq (.cv x) (syn_crab y (syn_cnnc) (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c)))))) (syn_cphi (.cv x)) (syn_cphi (syn_crab y (syn_cnnc) (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c)))))) A p0064
  have p0066 :=
    @g_spcev (.classEq A (syn_cphi (.cv x))) (.classEq A (syn_cphi (syn_crab y (syn_cnnc) (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c))))))) x (syn_crab y (syn_cnnc) (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c))))) dv_cache_0011 dv_cache_0022 p0063 p0065
  have p0067 :=
    @g_syl (syn_wa (syn_wss A (syn_cnnc)) (.neg (.classMem (syn_c0c) A))) (.classEq A (syn_cphi (syn_crab y (syn_cnnc) (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c))))))) (syn_wex x (.classEq A (syn_cphi (.cv x)))) p0039 p0066
  exact p0067

noncomputable def g_phialllem2
    (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) (hyp_phiall_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (.neg (.classMem (syn_c0c) A)) (syn_wex x (.classEq A (syn_cphi (.cv x))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ ((syn_cin A (syn_cnnc))).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cun (syn_cdif A (syn_cnnc)) (.cv y))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classEq A (syn_cphi (syn_cun (syn_cdif A (syn_cnnc)) (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_wex x (.classEq A (syn_cphi (.cv x))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_inss2 A (syn_cnnc)
  have p0001 :=
    @g_inss1 A (syn_cnnc)
  have p0002 :=
    @g_sseli (syn_cin A (syn_cnnc)) A (syn_c0c) p0001
  have p0003 :=
    @g_con3i (.classMem (syn_c0c) (syn_cin A (syn_cnnc))) (.classMem (syn_c0c) A) p0002
  have p0004 :=
    @g_nncex
  have p0005 :=
    @g_inex A (syn_cnnc) hyp_phiall_1 p0004
  have p0006 :=
    @g_phialllem1 y (syn_cin A (syn_cnnc)) dv_cache_0001 p0005
  have p0007 :=
    @g_sylancr (.neg (.classMem (syn_c0c) A)) (syn_wss (syn_cin A (syn_cnnc)) (syn_cnnc)) (.neg (.classMem (syn_c0c) (syn_cin A (syn_cnnc)))) (syn_wex y (.classEq (syn_cin A (syn_cnnc)) (syn_cphi (.cv y)))) p0000 p0003 p0006
  have p0008 :=
    @g_uncom (syn_cdif A (syn_cnnc)) (syn_cin A (syn_cnnc))
  have p0009 :=
    @g_inundif A (syn_cnnc)
  have p0010 :=
    @g_eqtri (syn_cun (syn_cdif A (syn_cnnc)) (syn_cin A (syn_cnnc))) (syn_cun (syn_cin A (syn_cnnc)) (syn_cdif A (syn_cnnc))) A p0008 p0009
  have p0011 :=
    @g_uneq2 (syn_cin A (syn_cnnc)) (syn_cphi (.cv y)) (syn_cdif A (syn_cnnc))
  have p0012 :=
    @g_syl5eqr (.classEq (syn_cin A (syn_cnnc)) (syn_cphi (.cv y))) A (syn_cun (syn_cdif A (syn_cnnc)) (syn_cin A (syn_cnnc))) (syn_cun (syn_cdif A (syn_cnnc)) (syn_cphi (.cv y))) p0010 p0011
  have p0013 :=
    @g_phiun (syn_cdif A (syn_cnnc)) (.cv y)
  have p0014 :=
    @g_incom (syn_cdif A (syn_cnnc)) (syn_cnnc)
  have p0015 :=
    @g_disjdif (syn_cnnc) A
  have p0016 :=
    @g_eqtri (syn_cin (syn_cdif A (syn_cnnc)) (syn_cnnc)) (syn_cin (syn_cnnc) (syn_cdif A (syn_cnnc))) (syn_c0) p0014 p0015
  have p0017 :=
    @g_phidisjnn (syn_cdif A (syn_cnnc))
  have p0018 :=
    Nominal.mp p0016 p0017
  have p0019 :=
    @g_uneq1i (syn_cphi (syn_cdif A (syn_cnnc))) (syn_cdif A (syn_cnnc)) (syn_cphi (.cv y)) p0018
  have p0020 :=
    @g_eqtri (syn_cphi (syn_cun (syn_cdif A (syn_cnnc)) (.cv y))) (syn_cun (syn_cphi (syn_cdif A (syn_cnnc))) (syn_cphi (.cv y))) (syn_cun (syn_cdif A (syn_cnnc)) (syn_cphi (.cv y))) p0013 p0019
  have p0021 :=
    @g_syl6eqr (.classEq (syn_cin A (syn_cnnc)) (syn_cphi (.cv y))) A (syn_cun (syn_cdif A (syn_cnnc)) (syn_cphi (.cv y))) (syn_cphi (syn_cun (syn_cdif A (syn_cnnc)) (.cv y))) p0012 p0020
  have p0022 :=
    @g_nncex
  have p0023 :=
    @g_difex A (syn_cnnc) hyp_phiall_1 p0022
  have p0024 :=
    @g_vex y
  have p0025 :=
    @g_unex (syn_cdif A (syn_cnnc)) (.cv y) p0023 p0024
  have p0026 :=
    @g_phieq (.cv x) (syn_cun (syn_cdif A (syn_cnnc)) (.cv y))
  have p0027 :=
    @g_eqeq2d (.classEq (.cv x) (syn_cun (syn_cdif A (syn_cnnc)) (.cv y))) (syn_cphi (.cv x)) (syn_cphi (syn_cun (syn_cdif A (syn_cnnc)) (.cv y))) A p0026
  have p0028 :=
    @g_spcev (.classEq A (syn_cphi (.cv x))) (.classEq A (syn_cphi (syn_cun (syn_cdif A (syn_cnnc)) (.cv y)))) x (syn_cun (syn_cdif A (syn_cnnc)) (.cv y)) dv_cache_0002 dv_cache_0003 p0025 p0027
  have p0029 :=
    @g_syl (.classEq (syn_cin A (syn_cnnc)) (syn_cphi (.cv y))) (.classEq A (syn_cphi (syn_cun (syn_cdif A (syn_cnnc)) (.cv y)))) (syn_wex x (.classEq A (syn_cphi (.cv x)))) p0021 p0028
  have p0030 :=
    @g_exlimiv (.classEq (syn_cin A (syn_cnnc)) (syn_cphi (.cv y))) (syn_wex x (.classEq A (syn_cphi (.cv x)))) y dv_cache_0004 p0029
  have p0031 :=
    @g_syl (.neg (.classMem (syn_c0c) A)) (syn_wex y (.classEq (syn_cin A (syn_cnnc)) (syn_cphi (.cv y)))) (syn_wex x (.classEq A (syn_cphi (.cv x)))) p0007 p0030
  exact p0031

noncomputable def g_phiall
    (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) (hyp_phiall_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wex x (syn_wo (.classEq A (syn_cphi (.cv x))) (.classEq A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv
  have dv_cache_0001 : x ∉ ((syn_cdif A (syn_csn (syn_c0c)))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classMem (syn_c0c) A)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_neldifsn (syn_c0c) A
  have p0001 :=
    @g_snex (syn_c0c)
  have p0002 :=
    @g_difex A (syn_csn (syn_c0c)) hyp_phiall_1 p0001
  have p0003 :=
    @g_phialllem2 x (syn_cdif A (syn_csn (syn_c0c))) dv_cache_0001 p0002
  have p0004 :=
    Nominal.mp p0000 p0003
  have p0005 :=
    @g_disjsn (syn_cdif A (syn_csn (syn_c0c))) (syn_c0c)
  have p0006 :=
    @g_mpbir (.classEq (syn_cin (syn_cdif A (syn_csn (syn_c0c))) (syn_csn (syn_c0c))) (syn_c0)) (.neg (.classMem (syn_c0c) (syn_cdif A (syn_csn (syn_c0c))))) p0000 p0005
  have p0007 :=
    @g_n_0cnelphi (.cv x)
  have p0008 :=
    @g_disjsn (syn_cphi (.cv x)) (syn_c0c)
  have p0009 :=
    @g_mpbir (.classEq (syn_cin (syn_cphi (.cv x)) (syn_csn (syn_c0c))) (syn_c0)) (.neg (.classMem (syn_c0c) (syn_cphi (.cv x)))) p0007 p0008
  have p0010 :=
    @g_eqtr4i (syn_cin (syn_cdif A (syn_csn (syn_c0c))) (syn_csn (syn_c0c))) (syn_c0) (syn_cin (syn_cphi (.cv x)) (syn_csn (syn_c0c))) p0006 p0009
  have p0011 :=
    @g_biantru (.classEq (syn_cin (syn_cdif A (syn_csn (syn_c0c))) (syn_csn (syn_c0c))) (syn_cin (syn_cphi (.cv x)) (syn_csn (syn_c0c)))) (.classEq (syn_cun (syn_cdif A (syn_csn (syn_c0c))) (syn_csn (syn_c0c))) (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))) p0010
  have p0012 :=
    @g_unineq (syn_cdif A (syn_csn (syn_c0c))) (syn_cphi (.cv x)) (syn_csn (syn_c0c))
  have p0013 :=
    @g_bitri (.classEq (syn_cun (syn_cdif A (syn_csn (syn_c0c))) (syn_csn (syn_c0c))) (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))) (syn_wa (.classEq (syn_cun (syn_cdif A (syn_csn (syn_c0c))) (syn_csn (syn_c0c))) (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))) (.classEq (syn_cin (syn_cdif A (syn_csn (syn_c0c))) (syn_csn (syn_c0c))) (syn_cin (syn_cphi (.cv x)) (syn_csn (syn_c0c))))) (.classEq (syn_cdif A (syn_csn (syn_c0c))) (syn_cphi (.cv x))) p0011 p0012
  have p0014 :=
    @g_difsnid A (syn_c0c)
  have p0015 :=
    @g_eqeq1d (.classMem (syn_c0c) A) (syn_cun (syn_cdif A (syn_csn (syn_c0c))) (syn_csn (syn_c0c))) A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))) p0014
  have p0016 :=
    @g_syl5bbr (.classEq (syn_cdif A (syn_csn (syn_c0c))) (syn_cphi (.cv x))) (.classEq (syn_cun (syn_cdif A (syn_csn (syn_c0c))) (syn_csn (syn_c0c))) (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))) (.classMem (syn_c0c) A) (.classEq A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))) p0013 p0015
  have p0017 :=
    @g_exbidv (.classMem (syn_c0c) A) (.classEq (syn_cdif A (syn_csn (syn_c0c))) (syn_cphi (.cv x))) (.classEq A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))) x dv_cache_0002 p0016
  have p0018 :=
    @g_mpbii (.classMem (syn_c0c) A) (syn_wex x (.classEq (syn_cdif A (syn_csn (syn_c0c))) (syn_cphi (.cv x)))) (syn_wex x (.classEq A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))))) p0004 p0017
  have p0019 :=
    @g_olc (.classEq A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))) (.classEq A (syn_cphi (.cv x)))
  have p0020 :=
    @g_eximi (.classEq A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))) (syn_wo (.classEq A (syn_cphi (.cv x))) (.classEq A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))))) x p0019
  have p0021 :=
    @g_syl (.classMem (syn_c0c) A) (syn_wex x (.classEq A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))))) (syn_wex x (syn_wo (.classEq A (syn_cphi (.cv x))) (.classEq A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))))) p0018 p0020
  have p0022 :=
    @g_phialllem2 x A dv_cache_0003 hyp_phiall_1
  have p0023 :=
    @g_orc (.classEq A (syn_cphi (.cv x))) (.classEq A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))))
  have p0024 :=
    @g_eximi (.classEq A (syn_cphi (.cv x))) (syn_wo (.classEq A (syn_cphi (.cv x))) (.classEq A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))))) x p0023
  have p0025 :=
    @g_syl (.neg (.classMem (syn_c0c) A)) (syn_wex x (.classEq A (syn_cphi (.cv x)))) (syn_wex x (syn_wo (.classEq A (syn_cphi (.cv x))) (.classEq A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))))) p0022 p0024
  have p0026 :=
    @g_pm2_61i (.classMem (syn_c0c) A) (syn_wex x (syn_wo (.classEq A (syn_cphi (.cv x))) (.classEq A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))))) p0021 p0025
  exact p0026

#print axioms g_phiall

end NFChoice.DirectNominalPrf.WPPReplay
