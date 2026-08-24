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
import NominalWPPReplayChunk010Compact001Part024

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

noncomputable def g_vfinspclt
    (X : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem X (syn_cspfin))) (.classMem (syn_ctfin X) (syn_cspfin))) := by
  let proofSupport : Finset Var := X.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_X : x ∉ X.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_X : y ∉ X.fv := by
    intro h
    exact fresh_y (h)
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_X : z ∉ X.fv := by
    intro h
    exact fresh_z (h)
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
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have dv_cache_0001 : x ∉ ((syn_cncfin (syn_cvv))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classMem (syn_ctfin (syn_cncfin (syn_cvv))) (syn_cspfin))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classMem (syn_ctfin (.cv y)) (syn_cspfin))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((Wff.classMem (syn_ctfin (.cv z)) (syn_cspfin))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv y) (syn_cspfin)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((Wff.classMem (syn_cvv) (syn_cfin))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((syn_ccnvk (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((syn_cspfin)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((syn_csn (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ ((syn_ctfin (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((syn_cuni1 (syn_cimak (syn_ccnvk (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))) (syn_cspfin)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : y ∉ ((Class.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : z ∉ ((Class.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0017 : x ∉ (X).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : x ∉ ((Wff.classMem (syn_ctfin X) (syn_cspfin))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_tncveqnc1fin
  have p0001 :=
    @g_n_1cspfin
  have p0002 :=
    @g_eqeltrd (.classMem (syn_cvv) (syn_cfin)) (syn_ctfin (syn_cncfin (syn_cvv))) (syn_cncfin (syn_c1c)) (syn_cspfin) p0000 p0001
  have p0003 :=
    @g_ncfinex (syn_cvv)
  have p0004 :=
    @g_tfineq (.cv x) (syn_cncfin (syn_cvv))
  have p0005 :=
    @g_eleq1d (.classEq (.cv x) (syn_cncfin (syn_cvv))) (syn_ctfin (.cv x)) (syn_ctfin (syn_cncfin (syn_cvv))) (syn_cspfin) p0004
  have p0006 :=
    @g_elab (.classMem (syn_ctfin (.cv x)) (syn_cspfin)) (.classMem (syn_ctfin (syn_cncfin (syn_cvv))) (syn_cspfin)) x (syn_cncfin (syn_cvv)) dv_cache_0001 dv_cache_0002 p0003 p0005
  have p0007 :=
    @g_sylibr (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_ctfin (syn_cncfin (syn_cvv))) (syn_cspfin)) (.classMem (syn_cncfin (syn_cvv)) (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin)))) p0002 p0006
  have p0008 :=
    @g_simprl (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv y) (syn_cspfin))) (.classMem (syn_ctfin (.cv y)) (syn_cspfin)) (syn_wsfin (.cv z) (.cv y))
  have p0009 :=
    @g_sfintfin (.cv z) (.cv y)
  have p0010 :=
    @g_ad2antll (syn_wsfin (.cv z) (.cv y)) (syn_wsfin (syn_ctfin (.cv z)) (syn_ctfin (.cv y))) (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv y) (syn_cspfin))) (.classMem (syn_ctfin (.cv y)) (syn_cspfin)) p0009
  have p0011 :=
    @g_spfinsfincl (syn_ctfin (.cv y)) (syn_ctfin (.cv z))
  have p0012 :=
    @g_syl2anc (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv y) (syn_cspfin))) (syn_wa (.classMem (syn_ctfin (.cv y)) (syn_cspfin)) (syn_wsfin (.cv z) (.cv y)))) (.classMem (syn_ctfin (.cv y)) (syn_cspfin)) (syn_wsfin (syn_ctfin (.cv z)) (syn_ctfin (.cv y))) (.classMem (syn_ctfin (.cv z)) (syn_cspfin)) p0008 p0010 p0011
  have p0013 :=
    @g_ex (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv y) (syn_cspfin))) (syn_wa (.classMem (syn_ctfin (.cv y)) (syn_cspfin)) (syn_wsfin (.cv z) (.cv y))) (.classMem (syn_ctfin (.cv z)) (syn_cspfin)) p0012
  have p0014 :=
    @g_vex y
  have p0015 :=
    @g_tfineq (.cv x) (.cv y)
  have p0016_e00_recanon : Nominal.NPrf (.imp (.objEq x y) (.classEq (syn_ctfin (.cv x)) (syn_ctfin (.cv y)))) :=
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
      p0015
  have p0016 :=
    @g_eleq1d (.objEq x y) (syn_ctfin (.cv x)) (syn_ctfin (.cv y)) (syn_cspfin) p0016_e00_recanon
  have p0017_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv x) (.cv y)) (syn_wb (.classMem (syn_ctfin (.cv x)) (syn_cspfin)) (.classMem (syn_ctfin (.cv y)) (syn_cspfin)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_ctfin syn_cif syn_wo syn_wa syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_cvv syn_cio syn_cuni syn_wex syn_csn syn_cspfin syn_cint
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0016
  have p0017 :=
    @g_elab (.classMem (syn_ctfin (.cv x)) (syn_cspfin)) (.classMem (syn_ctfin (.cv y)) (syn_cspfin)) x (.cv y) dv_cache_0003 dv_cache_0004 p0014 p0017_e01_recanon
  have p0018 :=
    @g_anbi1i (.classMem (.cv y) (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin)))) (.classMem (syn_ctfin (.cv y)) (syn_cspfin)) (syn_wsfin (.cv z) (.cv y)) p0017
  have p0019 :=
    @g_vex z
  have p0020 :=
    @g_tfineq (.cv x) (.cv z)
  have p0021_e00_recanon : Nominal.NPrf (.imp (.objEq x z) (.classEq (syn_ctfin (.cv x)) (syn_ctfin (.cv z)))) :=
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
      p0020
  have p0021 :=
    @g_eleq1d (.objEq x z) (syn_ctfin (.cv x)) (syn_ctfin (.cv z)) (syn_cspfin) p0021_e00_recanon
  have p0022_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv x) (.cv z)) (syn_wb (.classMem (syn_ctfin (.cv x)) (syn_cspfin)) (.classMem (syn_ctfin (.cv z)) (syn_cspfin)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_ctfin syn_cif syn_wo syn_wa syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_cvv syn_cio syn_cuni syn_wex syn_csn syn_cspfin syn_cint
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0021
  have p0022 :=
    @g_elab (.classMem (syn_ctfin (.cv x)) (syn_cspfin)) (.classMem (syn_ctfin (.cv z)) (syn_cspfin)) x (.cv z) dv_cache_0005 dv_cache_0006 p0019 p0022_e01_recanon
  have p0023 :=
    @g_n_3imtr4g (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv y) (syn_cspfin))) (syn_wa (.classMem (syn_ctfin (.cv y)) (syn_cspfin)) (syn_wsfin (.cv z) (.cv y))) (.classMem (syn_ctfin (.cv z)) (syn_cspfin)) (syn_wa (.classMem (.cv y) (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin)))) (syn_wsfin (.cv z) (.cv y))) (.classMem (.cv z) (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin)))) p0013 p0018 p0022
  have p0024 :=
    @g_alrimiv (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv y) (syn_cspfin))) (.imp (syn_wa (.classMem (.cv y) (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin)))) (syn_wsfin (.cv z) (.cv y))) (.classMem (.cv z) (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin))))) z dv_cache_0007 p0023
  have p0025 :=
    @g_ralrimiva (.classMem (syn_cvv) (syn_cfin)) (.all z (.imp (syn_wa (.classMem (.cv y) (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin)))) (syn_wsfin (.cv z) (.cv y))) (.classMem (.cv z) (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin)))))) y (syn_cspfin) dv_cache_0008 p0024
  have p0026 :=
    @g_snex (.cv x)
  have p0027 :=
    @g_elimak y (syn_ccnvk (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))) (syn_cspfin) (syn_csn (.cv x)) dv_cache_0009 dv_cache_0010 dv_cache_0011 p0026
  have p0028 :=
    @g_opkelcnvk (.cv y) (syn_csn (.cv x)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))) p0014 p0026
  have p0029 :=
    @g_vex x
  have p0030 :=
    @g_eqtfinrelk (.cv x) (.cv y) p0029 p0014
  have p0031 :=
    @g_bitri (.classMem (syn_copk (.cv y) (syn_csn (.cv x))) (syn_ccnvk (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))) (.classMem (syn_copk (syn_csn (.cv x)) (.cv y)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))) (.classEq (.cv y) (syn_ctfin (.cv x))) p0028 p0030
  have p0032 :=
    @g_rexbii (.classMem (syn_copk (.cv y) (syn_csn (.cv x))) (syn_ccnvk (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))) (.classEq (.cv y) (syn_ctfin (.cv x))) y (syn_cspfin) p0031
  have p0033 :=
    @g_bitri (.classMem (syn_csn (.cv x)) (syn_cimak (syn_ccnvk (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))) (syn_cspfin))) (syn_wrex y (syn_cspfin) (.classMem (syn_copk (.cv y) (syn_csn (.cv x))) (syn_ccnvk (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))) (syn_wrex y (syn_cspfin) (.classEq (.cv y) (syn_ctfin (.cv x)))) p0027 p0032
  have p0034 :=
    @g_eluni1 (.cv x) (syn_cimak (syn_ccnvk (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))) (syn_cspfin)) p0029
  have p0035 :=
    @g_risset y (syn_ctfin (.cv x)) (syn_cspfin) dv_cache_0012 dv_cache_0010
  have p0036 :=
    @g_n_3bitr4i (.classMem (syn_csn (.cv x)) (syn_cimak (syn_ccnvk (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))) (syn_cspfin))) (syn_wrex y (syn_cspfin) (.classEq (.cv y) (syn_ctfin (.cv x)))) (.classMem (.cv x) (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))) (syn_cspfin)))) (.classMem (syn_ctfin (.cv x)) (syn_cspfin)) p0033 p0034 p0035
  have p0037 :=
    @g_eqabi (.classMem (syn_ctfin (.cv x)) (syn_cspfin)) x (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))) (syn_cspfin))) dv_cache_0013 p0036
  have p0038 :=
    @g_tfinrelkex
  have p0039 :=
    @g_cnvkex (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))) p0038
  have p0040 :=
    @g_spfinex
  have p0041 :=
    @g_imakex (syn_ccnvk (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))) (syn_cspfin) p0039 p0040
  have p0042 :=
    @g_uni1ex (syn_cimak (syn_ccnvk (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))) (syn_cspfin)) p0041
  have p0043 :=
    @g_eqeltrri (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))) (syn_cspfin))) (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin))) (syn_cvv) p0037 p0042
  have p0044 :=
    @g_spfininduct y z (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin))) (syn_cvv) dv_cache_0014 dv_cache_0015 dv_cache_0016
  have p0045 :=
    @g_mp3an1 (.classMem (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin))) (syn_cvv)) (.classMem (syn_cncfin (syn_cvv)) (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin)))) (syn_wral y (syn_cspfin) (.all z (.imp (syn_wa (.classMem (.cv y) (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin)))) (syn_wsfin (.cv z) (.cv y))) (.classMem (.cv z) (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin))))))) (syn_wss (syn_cspfin) (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin)))) p0043 p0044
  have p0046 :=
    @g_syl2anc (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_cvv)) (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin)))) (syn_wral y (syn_cspfin) (.all z (.imp (syn_wa (.classMem (.cv y) (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin)))) (syn_wsfin (.cv z) (.cv y))) (.classMem (.cv z) (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin))))))) (syn_wss (syn_cspfin) (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin)))) p0007 p0025 p0045
  have p0047 :=
    @g_sselda (.classMem (syn_cvv) (syn_cfin)) (syn_cspfin) (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin))) X p0046
  have p0048 :=
    @g_tfineq (.cv x) X
  have p0049 :=
    @g_eleq1d (.classEq (.cv x) X) (syn_ctfin (.cv x)) (syn_ctfin X) (syn_cspfin) p0048
  have p0050 :=
    @g_elabg (.classMem (syn_ctfin (.cv x)) (syn_cspfin)) (.classMem (syn_ctfin X) (syn_cspfin)) x X (syn_cspfin) dv_cache_0017 dv_cache_0018 p0049
  have p0051 :=
    @g_adantl (.classMem X (syn_cspfin)) (syn_wb (.classMem X (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin)))) (.classMem (syn_ctfin X) (syn_cspfin))) (.classMem (syn_cvv) (syn_cfin)) p0050
  have p0052 :=
    @g_mpbid (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem X (syn_cspfin))) (.classMem X (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin)))) (.classMem (syn_ctfin X) (syn_cspfin)) p0047 p0051
  exact p0052

noncomputable def g_vfinspeqtncv
    (x : Var) (a : Var) (dv_a_x : a ≠ x) :
    Nominal.NPrf (.imp (.classMem (syn_cvv) (syn_cfin)) (.classEq (syn_cspfin) (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({a} : Finset Var)
  have dv_cache_0001 : a ≠ x := by
    exact (show a ≠ x from (by exact dv_a_x))
  have dv_cache_0002 : x ∉ ((Wff.classMem (.cv a) (syn_cspfin))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_a_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classMem (syn_cvv) (syn_cfin))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : a ∉ ((syn_cspfin)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : a ∉ ((Wff.classMem (syn_cvv) (syn_cfin))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_vfinspss x a dv_cache_0001
  have p0001 :=
    @g_vfinspclt (.cv x)
  have p0002 :=
    @g_eleq1 (.cv a) (syn_ctfin (.cv x)) (syn_cspfin)
  have p0003 :=
    @g_biimprd (.classEq (.cv a) (syn_ctfin (.cv x))) (.classMem (.cv a) (syn_cspfin)) (.classMem (syn_ctfin (.cv x)) (syn_cspfin)) p0002
  have p0004 :=
    @g_com12 (.classEq (.cv a) (syn_ctfin (.cv x))) (.classMem (syn_ctfin (.cv x)) (syn_cspfin)) (.classMem (.cv a) (syn_cspfin)) p0003
  have p0005 :=
    @g_syl (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv x) (syn_cspfin))) (.classMem (syn_ctfin (.cv x)) (syn_cspfin)) (.imp (.classEq (.cv a) (syn_ctfin (.cv x))) (.classMem (.cv a) (syn_cspfin))) p0001 p0004
  have p0006 :=
    @g_rexlimdva (.classMem (syn_cvv) (syn_cfin)) (.classEq (.cv a) (syn_ctfin (.cv x))) (.classMem (.cv a) (syn_cspfin)) x (syn_cspfin) dv_cache_0002 dv_cache_0003 p0005
  have p0007 :=
    @g_abssdv (.classMem (syn_cvv) (syn_cfin)) (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))) a (syn_cspfin) dv_cache_0004 dv_cache_0005 p0006
  have p0008 :=
    @g_ncvspfin
  have p0009 :=
    @g_ncfinex (syn_cvv)
  have p0010 :=
    @g_snss (syn_cncfin (syn_cvv)) (syn_cspfin) p0009
  have p0011 :=
    @g_mpbi (.classMem (syn_cncfin (syn_cvv)) (syn_cspfin)) (syn_wss (syn_csn (syn_cncfin (syn_cvv))) (syn_cspfin)) p0008 p0010
  have p0012 :=
    @g_jctir (.classMem (syn_cvv) (syn_cfin)) (syn_wss (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_cspfin)) (syn_wss (syn_csn (syn_cncfin (syn_cvv))) (syn_cspfin)) p0007 p0011
  have p0013 :=
    @g_unss (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv))) (syn_cspfin)
  have p0014 :=
    @g_sylib (.classMem (syn_cvv) (syn_cfin)) (syn_wa (syn_wss (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_cspfin)) (syn_wss (syn_csn (syn_cncfin (syn_cvv))) (syn_cspfin))) (syn_wss (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv)))) (syn_cspfin)) p0012 p0013
  have p0015 :=
    @g_eqssd (.classMem (syn_cvv) (syn_cfin)) (syn_cspfin) (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv)))) p0000 p0014
  exact p0015

#print axioms g_vfinspeqtncv

end NFChoice.DirectNominalPrf.WPPReplay
