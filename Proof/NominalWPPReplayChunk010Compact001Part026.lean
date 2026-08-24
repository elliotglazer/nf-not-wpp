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
import NominalWPPReplayChunk010Compact001Part025

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

noncomputable def g_vfinncsp
     :
    Nominal.NPrf (.imp (.classMem (syn_cvv) (syn_cfin)) (.classEq (syn_cncfin (syn_cspfin)) (syn_cplc (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_c1c)))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let a : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let t : Var := freshVar proofSupport 2
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_a_ne_x : a ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_a : x ≠ a :=
    Ne.symm fresh_a_ne_x
  have fresh_a_ne_t : a ≠ t := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_t_ne_a : t ≠ a :=
    Ne.symm fresh_a_ne_t
  have fresh_x_ne_t : x ≠ t := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_t_ne_x : t ≠ x :=
    Ne.symm fresh_x_ne_t
  have dv_cache_0001 : a ≠ x := by
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0002 : t ∉ ((syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : t ∉ ((syn_cpw1 (syn_cspfin))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : t ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Class.cv t)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_cspfin)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Wff.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_t, fresh_x_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : t ∉ ((syn_cspfin)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ≠ t := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show x ≠ t from (by exact fresh_x_ne_t))
  have dv_cache_0010 : t ∉ ((syn_csn (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : t ∉ ((Wff.classMem (syn_copk (syn_csn (.cv x)) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : a ∉ ((syn_cimak (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))) (syn_cpw1 (syn_cspfin)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : a ∉ ((syn_cspfin)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : a ∉ ((syn_cncfin (syn_cspfin))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ ((syn_cncfin (syn_cspfin))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_vfinspeqtncv x a dv_cache_0001
  have p0001 :=
    @g_ncfineq (syn_cspfin) (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv))))
  have p0002 :=
    @g_syl (.classMem (syn_cvv) (syn_cfin)) (.classEq (syn_cspfin) (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv))))) (.classEq (syn_cncfin (syn_cspfin)) (syn_cncfin (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv)))))) p0000 p0001
  have p0003 :=
    @g_vfinncvntsp x a dv_cache_0001
  have p0004 :=
    @g_disjsn (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_cncfin (syn_cvv))
  have p0005 :=
    @g_sylibr (.classMem (syn_cvv) (syn_cfin)) (.neg (.classMem (syn_cncfin (syn_cvv)) (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))))) (.classEq (syn_cin (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv)))) (syn_c0)) p0003 p0004
  have p0006 :=
    @g_vex a
  have p0007 :=
    @g_elimak t (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))) (syn_cpw1 (syn_cspfin)) (.cv a) dv_cache_0002 dv_cache_0003 dv_cache_0004 p0006
  have p0008 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex t (syn_cpw1 (syn_cspfin)) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))))
  have p0009 :=
    @g_elpw1 x (.cv t) (syn_cspfin) dv_cache_0005 dv_cache_0006
  have p0010 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cspfin))) (syn_wrex x (syn_cspfin) (.classEq (.cv t) (syn_csn (.cv x)))) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))) p0009
  have p0011 :=
    @g_r19_41v (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))) x (syn_cspfin) dv_cache_0007
  have p0012 :=
    @g_bitr4i (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cspfin))) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))) (syn_wa (syn_wrex x (syn_cspfin) (.classEq (.cv t) (syn_csn (.cv x)))) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))) (syn_wrex x (syn_cspfin) (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))) p0010 p0011
  have p0013 :=
    @g_exbii (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cspfin))) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))) (syn_wrex x (syn_cspfin) (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))) t p0012
  have p0014 :=
    @g_rexcom4 (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))) x t (syn_cspfin) dv_cache_0008 dv_cache_0009
  have p0015 :=
    @g_bitr4i (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cspfin))) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))) (syn_wex t (syn_wrex x (syn_cspfin) (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))))) (syn_wrex x (syn_cspfin) (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))))) p0013 p0014
  have p0016 :=
    @g_bitri (syn_wrex t (syn_cpw1 (syn_cspfin)) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))) (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cspfin))) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))) (syn_wrex x (syn_cspfin) (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))))) p0008 p0015
  have p0017 :=
    @g_bitri (.classMem (.cv a) (syn_cimak (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))) (syn_cpw1 (syn_cspfin)))) (syn_wrex t (syn_cpw1 (syn_cspfin)) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))) (syn_wrex x (syn_cspfin) (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))))) p0007 p0016
  have p0018 :=
    @g_snex (.cv x)
  have p0019 :=
    @g_opkeq1 (.cv t) (syn_csn (.cv x)) (.cv a)
  have p0020 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (.cv x))) (syn_copk (.cv t) (.cv a)) (syn_copk (syn_csn (.cv x)) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))) p0019
  have p0021 :=
    @g_ceqsexv (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))) (.classMem (syn_copk (syn_csn (.cv x)) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))) t (syn_csn (.cv x)) dv_cache_0010 dv_cache_0011 p0018 p0020
  have p0022 :=
    @g_vex x
  have p0023 :=
    @g_eqtfinrelk (.cv x) (.cv a) p0022 p0006
  have p0024 :=
    @g_bitri (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))) (.classMem (syn_copk (syn_csn (.cv x)) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))) (.classEq (.cv a) (syn_ctfin (.cv x))) p0021 p0023
  have p0025 :=
    @g_rexbii (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))) (.classEq (.cv a) (syn_ctfin (.cv x))) x (syn_cspfin) p0024
  have p0026 :=
    @g_bitri (.classMem (.cv a) (syn_cimak (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))) (syn_cpw1 (syn_cspfin)))) (syn_wrex x (syn_cspfin) (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))))) (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))) p0017 p0025
  have p0027 :=
    @g_eqabi (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))) a (syn_cimak (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))) (syn_cpw1 (syn_cspfin))) dv_cache_0012 p0026
  have p0028 :=
    @g_tfinrelkex
  have p0029 :=
    @g_spfinex
  have p0030 :=
    @g_pw1ex (syn_cspfin) p0029
  have p0031 :=
    @g_imakex (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))) (syn_cpw1 (syn_cspfin)) p0028 p0030
  have p0032 :=
    @g_eqeltrri (syn_cimak (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))) (syn_cpw1 (syn_cspfin))) (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_cvv) p0027 p0031
  have p0033 :=
    @g_snex (syn_cncfin (syn_cvv))
  have p0034 :=
    @g_ncfindi (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv))) (syn_cvv) (syn_cvv)
  have p0035 :=
    @g_mp3an2 (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_cvv))) (.classMem (syn_csn (syn_cncfin (syn_cvv))) (syn_cvv)) (.classEq (syn_cin (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv)))) (syn_c0)) (.classEq (syn_cncfin (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv))))) (syn_cplc (syn_cncfin (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))) (syn_cncfin (syn_csn (syn_cncfin (syn_cvv)))))) p0033 p0034
  have p0036 :=
    @g_mpanl2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_cvv)) (.classEq (syn_cin (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv)))) (syn_c0)) (.classEq (syn_cncfin (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv))))) (syn_cplc (syn_cncfin (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))) (syn_cncfin (syn_csn (syn_cncfin (syn_cvv)))))) p0032 p0035
  have p0037 :=
    @g_mpdan (.classMem (syn_cvv) (syn_cfin)) (.classEq (syn_cin (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv)))) (syn_c0)) (.classEq (syn_cncfin (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv))))) (syn_cplc (syn_cncfin (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))) (syn_cncfin (syn_csn (syn_cncfin (syn_cvv)))))) p0005 p0036
  have p0038 :=
    @g_ncfinprop (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_cvv)
  have p0039 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_cvv)) (syn_wa (.classMem (syn_cncfin (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))) (syn_cnnc)) (.classMem (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_cncfin (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))))) p0032 p0038
  have p0040 :=
    @g_simpld (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))) (syn_cnnc)) (.classMem (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_cncfin (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))))) p0039
  have p0041 :=
    @g_spfinex
  have p0042 :=
    @g_ncfinprop (syn_cspfin) (syn_cvv)
  have p0043 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cspfin) (syn_cvv)) (syn_wa (.classMem (syn_cncfin (syn_cspfin)) (syn_cnnc)) (.classMem (syn_cspfin) (syn_cncfin (syn_cspfin)))) p0041 p0042
  have p0044 :=
    @g_simpld (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_cspfin)) (syn_cnnc)) (.classMem (syn_cspfin) (syn_cncfin (syn_cspfin))) p0043
  have p0045 :=
    @g_tfincl (syn_cncfin (syn_cspfin))
  have p0046 :=
    @g_syl (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_cspfin)) (syn_cnnc)) (.classMem (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_cnnc)) p0044 p0045
  have p0047 :=
    @g_simprd (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))) (syn_cnnc)) (.classMem (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_cncfin (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))))) p0039
  have p0048 :=
    @g_vfinspnn
  have p0049 :=
    @g_difss (syn_cnnc) (syn_csn (syn_c0))
  have p0050 :=
    @g_syl6ss (.classMem (syn_cvv) (syn_cfin)) (syn_cspfin) (syn_cdif (syn_cnnc) (syn_csn (syn_c0))) (syn_cnnc) p0048 p0049
  have p0051 :=
    @g_simprd (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_cspfin)) (syn_cnnc)) (.classMem (syn_cspfin) (syn_cncfin (syn_cspfin))) p0043
  have p0052 :=
    @g_tfinnn x (syn_cspfin) (syn_cncfin (syn_cspfin)) a dv_cache_0013 dv_cache_0006 dv_cache_0014 dv_cache_0015 dv_cache_0001
  have p0053 :=
    @g_syl3anc (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_cspfin)) (syn_cnnc)) (syn_wss (syn_cspfin) (syn_cnnc)) (.classMem (syn_cspfin) (syn_cncfin (syn_cspfin))) (.classMem (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_ctfin (syn_cncfin (syn_cspfin)))) p0044 p0050 p0051 p0052
  have p0054 :=
    @g_nnceleq (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_cncfin (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))) (syn_ctfin (syn_cncfin (syn_cspfin)))
  have p0055 :=
    @g_syl22anc (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))) (syn_cnnc)) (.classMem (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_cnnc)) (.classMem (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_cncfin (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))))) (.classMem (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_ctfin (syn_cncfin (syn_cspfin)))) (.classEq (syn_cncfin (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))) (syn_ctfin (syn_cncfin (syn_cspfin)))) p0040 p0046 p0047 p0053 p0054
  have p0056 :=
    @g_ncfinex (syn_cvv)
  have p0057 :=
    @g_ncfinsn (syn_cncfin (syn_cvv)) (syn_cvv)
  have p0058 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_cvv)) (syn_cvv)) (.classEq (syn_cncfin (syn_csn (syn_cncfin (syn_cvv)))) (syn_c1c)) p0056 p0057
  have p0059 :=
    @g_addceq12d (.classMem (syn_cvv) (syn_cfin)) (syn_cncfin (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))) (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_cncfin (syn_csn (syn_cncfin (syn_cvv)))) (syn_c1c) p0055 p0058
  have p0060 :=
    @g_n_3eqtrd (.classMem (syn_cvv) (syn_cfin)) (syn_cncfin (syn_cspfin)) (syn_cncfin (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_csn (syn_cncfin (syn_cvv))))) (syn_cplc (syn_cncfin (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))) (syn_cncfin (syn_csn (syn_cncfin (syn_cvv))))) (syn_cplc (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_c1c)) p0002 p0037 p0059
  exact p0060

#print axioms g_vfinncsp

end NFChoice.DirectNominalPrf.WPPReplay
