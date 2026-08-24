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
import NominalWPPReplayChunk010Compact001Part040

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

noncomputable def g_setconslem1
    (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (hyp_setconslem1_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_setconslem1_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem (syn_copk (syn_csn A) B) (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_wrex x B (.classEq A (syn_cphi (.cv x))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv
  let t : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_t_ne_x : t ≠ x := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_t : x ≠ t :=
    Ne.symm fresh_t_ne_x
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_t_ne_z : t ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_t : z ≠ t :=
    Ne.symm fresh_t_ne_z
  have dv_cache_0001 : z ∉ ((syn_csn A)).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_csn A)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((Class.cv t)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Class.cv t)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show z ≠ x from (by exact fresh_z_ne_x))
  have dv_cache_0008 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_t, fresh_z_ne_x, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ ((Wff.classMem (syn_copk (.cv t) B) (syn_cssetk))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_t, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : t ∉ ((syn_csn (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : t ∉ ((syn_wa (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))) (.classMem (syn_copk (syn_csn (.cv x)) B) (syn_cssetk)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_A, fresh_t_ne_x, fresh_t_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : t ∉ ((syn_csn A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : t ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : t ∉ ((syn_cssetk)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : t ∉ ((syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_snex A
  have p0001 :=
    @g_vex t
  have p0002 :=
    @g_opkelsikg z x (syn_csn A) (.cv t) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cvv) (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0003 :=
    @g_mp2an (.classMem (syn_csn A) (syn_cvv)) (.classMem (.cv t) (syn_cvv)) (syn_wb (.classMem (syn_copk (syn_csn A) (.cv t)) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))) (syn_wex z (syn_wex x (syn_w3a (.classEq (syn_csn A) (syn_csn (.cv z))) (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv z) (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))) p0000 p0001 p0002
  have p0004 :=
    @g_excom (syn_w3a (.classEq (syn_csn A) (syn_csn (.cv z))) (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv z) (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))) z x
  have p0005 :=
    @g_n_3anass (.classEq (syn_csn A) (syn_csn (.cv z))) (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv z) (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))
  have p0006 :=
    @g_eqcom (syn_csn A) (syn_csn (.cv z))
  have p0007 :=
    @g_vex z
  have p0008 :=
    @g_sneqb (.cv z) A p0007
  have p0009 :=
    @g_bitri (.classEq (syn_csn A) (syn_csn (.cv z))) (.classEq (syn_csn (.cv z)) (syn_csn A)) (.classEq (.cv z) A) p0006 p0008
  have p0010 :=
    @g_anbi1i (.classEq (syn_csn A) (syn_csn (.cv z))) (.classEq (.cv z) A) (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv z) (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))) p0009
  have p0011 :=
    @g_bitri (syn_w3a (.classEq (syn_csn A) (syn_csn (.cv z))) (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv z) (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))) (syn_wa (.classEq (syn_csn A) (syn_csn (.cv z))) (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv z) (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_wa (.classEq (.cv z) A) (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv z) (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) p0005 p0010
  have p0012 :=
    @g_exbii (syn_w3a (.classEq (syn_csn A) (syn_csn (.cv z))) (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv z) (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))) (syn_wa (.classEq (.cv z) A) (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv z) (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) z p0011
  have p0013 :=
    @g_opkeq1 (.cv z) A (.cv x)
  have p0014 :=
    @g_eleq1d (.classEq (.cv z) A) (syn_copk (.cv z) (.cv x)) (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) p0013
  have p0015 :=
    @g_anbi2d (.classEq (.cv z) A) (.classMem (syn_copk (.cv z) (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))) (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))) (.classEq (.cv t) (syn_csn (.cv x))) p0014
  have p0016 :=
    @g_ceqsexv (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv z) (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))) (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))) z A dv_cache_0008 dv_cache_0009 hyp_setconslem1_1 p0015
  have p0017 :=
    @g_bitri (syn_wex z (syn_w3a (.classEq (syn_csn A) (syn_csn (.cv z))) (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv z) (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_wex z (syn_wa (.classEq (.cv z) A) (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv z) (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))) (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))) p0012 p0016
  have p0018 :=
    @g_exbii (syn_wex z (syn_w3a (.classEq (syn_csn A) (syn_csn (.cv z))) (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv z) (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))) x p0017
  have p0019 :=
    @g_n_3bitri (.classMem (syn_copk (syn_csn A) (.cv t)) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))) (syn_wex z (syn_wex x (syn_w3a (.classEq (syn_csn A) (syn_csn (.cv z))) (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv z) (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))) (syn_wex x (syn_wex z (syn_w3a (.classEq (syn_csn A) (syn_csn (.cv z))) (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv z) (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))) (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) p0003 p0004 p0018
  have p0020 :=
    @g_anbi1i (.classMem (syn_copk (syn_csn A) (.cv t)) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))) (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (.classMem (syn_copk (.cv t) B) (syn_cssetk)) p0019
  have p0021 :=
    @g_n_19_41v (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))) (.classMem (syn_copk (.cv t) B) (syn_cssetk)) x dv_cache_0010
  have p0022 :=
    @g_anass (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))) (.classMem (syn_copk (.cv t) B) (syn_cssetk))
  have p0023 :=
    @g_exbii (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))) (.classMem (syn_copk (.cv t) B) (syn_cssetk))) (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (syn_wa (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))) (.classMem (syn_copk (.cv t) B) (syn_cssetk)))) x p0022
  have p0024 :=
    @g_n_3bitr2i (syn_wa (.classMem (syn_copk (syn_csn A) (.cv t)) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))) (.classMem (syn_copk (.cv t) B) (syn_cssetk))) (syn_wa (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (.classMem (syn_copk (.cv t) B) (syn_cssetk))) (syn_wex x (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))) (.classMem (syn_copk (.cv t) B) (syn_cssetk)))) (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (syn_wa (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))) (.classMem (syn_copk (.cv t) B) (syn_cssetk))))) p0020 p0021 p0023
  have p0025 :=
    @g_exbii (syn_wa (.classMem (syn_copk (syn_csn A) (.cv t)) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))) (.classMem (syn_copk (.cv t) B) (syn_cssetk))) (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (syn_wa (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))) (.classMem (syn_copk (.cv t) B) (syn_cssetk))))) t p0024
  have p0026 :=
    @g_excom (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (syn_wa (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))) (.classMem (syn_copk (.cv t) B) (syn_cssetk)))) x t
  have p0027 :=
    @g_snex (.cv x)
  have p0028 :=
    @g_opkeq1 (.cv t) (syn_csn (.cv x)) B
  have p0029 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (.cv x))) (syn_copk (.cv t) B) (syn_copk (syn_csn (.cv x)) B) (syn_cssetk) p0028
  have p0030 :=
    @g_anbi2d (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv t) B) (syn_cssetk)) (.classMem (syn_copk (syn_csn (.cv x)) B) (syn_cssetk)) (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))) p0029
  have p0031 :=
    @g_ceqsexv (syn_wa (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))) (.classMem (syn_copk (.cv t) B) (syn_cssetk))) (syn_wa (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))) (.classMem (syn_copk (syn_csn (.cv x)) B) (syn_cssetk))) t (syn_csn (.cv x)) dv_cache_0011 dv_cache_0012 p0027 p0030
  have p0032 :=
    @g_vex x
  have p0033 :=
    @g_opkelimagek (.cv x) A (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))) p0032 hyp_setconslem1_1
  have p0034 :=
    @g_opkelcnvk A (.cv x) (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))) hyp_setconslem1_1 p0032
  have p0035 :=
    @g_dfphi2 (.cv x)
  have p0036 :=
    @g_eqeq2i (syn_cphi (.cv x)) (syn_cimak (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))) (.cv x)) A p0035
  have p0037 :=
    @g_n_3bitr4i (.classMem (syn_copk (.cv x) A) (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (.classEq A (syn_cimak (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))) (.cv x))) (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))) (.classEq A (syn_cphi (.cv x))) p0033 p0034 p0036
  have p0038 :=
    @g_elssetk (.cv x) B p0032 hyp_setconslem1_2
  have p0039 :=
    @g_anbi12i (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))) (.classEq A (syn_cphi (.cv x))) (.classMem (syn_copk (syn_csn (.cv x)) B) (syn_cssetk)) (.classMem (.cv x) B) p0037 p0038
  have p0040 :=
    @g_ancom (.classEq A (syn_cphi (.cv x))) (.classMem (.cv x) B)
  have p0041 :=
    @g_n_3bitri (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (syn_wa (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))) (.classMem (syn_copk (.cv t) B) (syn_cssetk))))) (syn_wa (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))) (.classMem (syn_copk (syn_csn (.cv x)) B) (syn_cssetk))) (syn_wa (.classEq A (syn_cphi (.cv x))) (.classMem (.cv x) B)) (syn_wa (.classMem (.cv x) B) (.classEq A (syn_cphi (.cv x)))) p0031 p0039 p0040
  have p0042 :=
    @g_exbii (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (syn_wa (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))) (.classMem (syn_copk (.cv t) B) (syn_cssetk))))) (syn_wa (.classMem (.cv x) B) (.classEq A (syn_cphi (.cv x)))) x p0041
  have p0043 :=
    @g_n_3bitr2i (syn_wex t (syn_wa (.classMem (syn_copk (syn_csn A) (.cv t)) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))) (.classMem (syn_copk (.cv t) B) (syn_cssetk)))) (syn_wex t (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (syn_wa (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))) (.classMem (syn_copk (.cv t) B) (syn_cssetk)))))) (syn_wex x (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (syn_wa (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))) (.classMem (syn_copk (.cv t) B) (syn_cssetk)))))) (syn_wex x (syn_wa (.classMem (.cv x) B) (.classEq A (syn_cphi (.cv x))))) p0025 p0026 p0042
  have p0044 :=
    @g_opkelcok t (syn_csn A) B (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))) dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 p0000 hyp_setconslem1_2
  have p0045 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex x B (.classEq A (syn_cphi (.cv x))))))
  have p0046 :=
    @g_n_3bitr4i (syn_wex t (syn_wa (.classMem (syn_copk (syn_csn A) (.cv t)) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))) (.classMem (syn_copk (.cv t) B) (syn_cssetk)))) (syn_wex x (syn_wa (.classMem (.cv x) B) (.classEq A (syn_cphi (.cv x))))) (.classMem (syn_copk (syn_csn A) B) (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_wrex x B (.classEq A (syn_cphi (.cv x)))) p0043 p0044 p0045
  exact p0046

#print axioms g_setconslem1

end NFChoice.DirectNominalPrf.WPPReplay
