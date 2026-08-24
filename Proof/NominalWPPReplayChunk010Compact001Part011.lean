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
import NominalWPPReplayChunk010Compact001Part010

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

noncomputable def g_srelk
    (A : Class) (B : Class) (hyp_srelk_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_srelk_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem (syn_copk A B) (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_wsfin A B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let t : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  let z : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (h))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x_ne_t : x ≠ t := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_t_ne_x : t ≠ x :=
    Ne.symm fresh_x_ne_t
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_t_ne_y : t ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_t : y ≠ t :=
    Ne.symm fresh_t_ne_y
  have fresh_t_ne_z : t ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_z_ne_t : z ≠ t :=
    Ne.symm fresh_t_ne_z
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have dv_cache_0001 : t ∉ ((syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv := by
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : t ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : t ∉ ((syn_copk A B)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_A, fresh_t_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Class.cv t)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_t, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : t ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : t ∉ ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_x, fresh_t_not_A, fresh_t_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : t ∉ ((syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : t ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : t ∉ ((syn_copk (syn_csn (syn_csn (.cv x))) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_x, fresh_t_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((Class.cv t)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ ((Wff.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) A)) (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_t, fresh_y_ne_x, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : t ∉ ((syn_csn (syn_csn (syn_csn (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : t ∉ ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (syn_csn (syn_csn (.cv x))) A)) (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_x, fresh_t_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : y ∉ ((syn_cpw1 (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : t ∉ ((syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : t ∉ ((syn_copk (syn_csn (syn_csn (.cv x))) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_x, fresh_t_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : y ∉ ((Wff.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) B)) (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_t, fresh_y_ne_x, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : t ∉ ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (syn_csn (syn_csn (.cv x))) B)) (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_x, fresh_t_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : t ∉ ((syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : t ∉ ((syn_copk (.cv y) (syn_csn (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : z ∉ ((Class.cv t)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : z ∉ ((Wff.classMem (syn_copk (.cv t) (syn_copk (.cv y) (syn_csn (.cv x)))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_t, fresh_z_ne_y, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : t ∉ ((syn_csn (syn_csn (syn_csn (.cv z))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : t ∉ ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv y) (syn_csn (.cv x)))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_z, fresh_t_ne_y, fresh_t_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : z ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0028 : z ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0029 : y ∉ ((syn_cpw (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0030 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0031 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0032 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_opkelxpk A B (syn_cnnc) (syn_cnnc) hyp_srelk_1 hyp_srelk_2
  have p0001 :=
    @g_opkex A B
  have p0002 :=
    @g_elimak t (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) (syn_copk A B) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0001
  have p0003 :=
    @g_elpw131c x (.cv t) dv_cache_0004
  have p0004 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))) (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) p0003
  have p0005 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) x dv_cache_0005
  have p0006 :=
    @g_bitr4i (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_wa (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))) (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) p0004 p0005
  have p0007 :=
    @g_exbii (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) t p0006
  have p0008 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
  have p0009 :=
    @g_excom (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) x t
  have p0010 :=
    @g_n_3bitr4i (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_wex t (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_wex x (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) p0007 p0008 p0009
  have p0011 :=
    @g_snex (syn_csn (syn_csn (syn_csn (.cv x))))
  have p0012 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_copk A B)
  have p0013 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) (syn_copk (.cv t) (syn_copk A B)) (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0012
  have p0014 :=
    @g_ceqsexv (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) t (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) dv_cache_0006 dv_cache_0007 p0011 p0013
  have p0015 :=
    @g_elin (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_copk A B)) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
  have p0016 :=
    @g_opkex (syn_csn (syn_csn (.cv x))) A
  have p0017 :=
    @g_elimak t (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))) (syn_copk (syn_csn (syn_csn (.cv x))) A) dv_cache_0008 dv_cache_0009 dv_cache_0010 p0016
  have p0018 :=
    @g_elpw121c y (.cv t) dv_cache_0011
  have p0019 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (syn_wex y (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y)))))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) A)) (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))) p0018
  have p0020 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y))))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) A)) (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))) y dv_cache_0012
  have p0021 :=
    @g_bitr4i (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) A)) (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))))) (syn_wa (syn_wex y (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y)))))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) A)) (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))))) (syn_wex y (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y))))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) A)) (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))))) p0019 p0020
  have p0022 :=
    @g_exbii (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) A)) (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))))) (syn_wex y (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y))))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) A)) (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))))) t p0021
  have p0023 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) A)) (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))))))
  have p0024 :=
    @g_excom (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y))))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) A)) (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))))) y t
  have p0025 :=
    @g_n_3bitr4i (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) A)) (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))))) (syn_wex t (syn_wex y (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y))))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) A)) (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))))))) (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) A)) (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))))) (syn_wex y (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y))))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) A)) (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))))))) p0022 p0023 p0024
  have p0026 :=
    @g_snex (syn_csn (syn_csn (.cv y)))
  have p0027 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (syn_csn (syn_csn (.cv x))) A)
  have p0028 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y))))) (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) A)) (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (syn_csn (syn_csn (.cv x))) A)) (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) p0027
  have p0029 :=
    @g_ceqsexv (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) A)) (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (syn_csn (syn_csn (.cv x))) A)) (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))) t (syn_csn (syn_csn (syn_csn (.cv y)))) dv_cache_0013 dv_cache_0014 p0026 p0028
  have p0030 :=
    @g_elin (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (syn_csn (syn_csn (.cv x))) A)) (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))
  have p0031 :=
    @g_snex (.cv y)
  have p0032 :=
    @g_snex (syn_csn (.cv x))
  have p0033 :=
    @g_otkelins3k (syn_csn (.cv y)) (syn_csn (syn_csn (.cv x))) A (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) p0031 p0032 hyp_srelk_1
  have p0034 :=
    @g_vex y
  have p0035 :=
    @g_snex (.cv x)
  have p0036 :=
    @g_opksnelsik (.cv y) (syn_csn (.cv x)) (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0034 p0035
  have p0037 :=
    @g_vex x
  have p0038 :=
    @g_eqpw1relk (.cv y) (.cv x) p0034 p0037
  have p0039 :=
    @g_n_3bitri (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (syn_csn (syn_csn (.cv x))) A)) (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (.classMem (syn_copk (syn_csn (.cv y)) (syn_csn (syn_csn (.cv x)))) (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (.classMem (syn_copk (.cv y) (syn_csn (.cv x))) (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (.classEq (.cv y) (syn_cpw1 (.cv x))) p0033 p0036 p0038
  have p0040 :=
    @g_otkelins2k (syn_csn (.cv y)) (syn_csn (syn_csn (.cv x))) A (syn_cssetk) p0031 p0032 hyp_srelk_1
  have p0041 :=
    @g_elssetk (.cv y) A p0034 hyp_srelk_1
  have p0042 :=
    @g_bitri (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (syn_csn (syn_csn (.cv x))) A)) (syn_cins2k (syn_cssetk))) (.classMem (syn_copk (syn_csn (.cv y)) A) (syn_cssetk)) (.classMem (.cv y) A) p0040 p0041
  have p0043 :=
    @g_anbi12i (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (syn_csn (syn_csn (.cv x))) A)) (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (.classEq (.cv y) (syn_cpw1 (.cv x))) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (syn_csn (syn_csn (.cv x))) A)) (syn_cins2k (syn_cssetk))) (.classMem (.cv y) A) p0039 p0042
  have p0044 :=
    @g_n_3bitri (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y))))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) A)) (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))))) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (syn_csn (syn_csn (.cv x))) A)) (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))) (syn_wa (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (syn_csn (syn_csn (.cv x))) A)) (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (syn_csn (syn_csn (.cv x))) A)) (syn_cins2k (syn_cssetk)))) (syn_wa (.classEq (.cv y) (syn_cpw1 (.cv x))) (.classMem (.cv y) A)) p0029 p0030 p0043
  have p0045 :=
    @g_exbii (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y))))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) A)) (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))))) (syn_wa (.classEq (.cv y) (syn_cpw1 (.cv x))) (.classMem (.cv y) A)) y p0044
  have p0046 :=
    @g_n_3bitri (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) A) (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) A)) (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))))) (syn_wex y (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y))))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) A)) (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))))))) (syn_wex y (syn_wa (.classEq (.cv y) (syn_cpw1 (.cv x))) (.classMem (.cv y) A))) p0017 p0025 p0045
  have p0047 :=
    @g_otkelins3k (syn_csn (syn_csn (.cv x))) A B (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0032 hyp_srelk_1 hyp_srelk_2
  have p0048 :=
    (by simpa [NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfClelGoal, syn_wb, syn_wex, syn_wa, Wff.biimp, Wff.ex, Wff.conj, Wff.neg] using (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV y (syn_cpw1 (.cv x)) A dv_cache_0015 dv_cache_0016))
  have p0049 :=
    @g_n_3bitr4i (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) A) (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_wex y (syn_wa (.classEq (.cv y) (syn_cpw1 (.cv x))) (.classMem (.cv y) A))) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_copk A B)) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (.classMem (syn_cpw1 (.cv x)) A) p0046 p0047 p0048
  have p0050 :=
    @g_opkex (syn_csn (syn_csn (.cv x))) B
  have p0051 :=
    @g_elimak t (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))) (syn_copk (syn_csn (syn_csn (.cv x))) B) dv_cache_0017 dv_cache_0009 dv_cache_0018 p0050
  have p0052 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (syn_wex y (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y)))))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) B)) (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))) p0018
  have p0053 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y))))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) B)) (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))) y dv_cache_0019
  have p0054 :=
    @g_bitr4i (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) B)) (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))))) (syn_wa (syn_wex y (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y)))))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) B)) (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))))) (syn_wex y (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y))))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) B)) (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))))) p0052 p0053
  have p0055 :=
    @g_exbii (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) B)) (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))))) (syn_wex y (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y))))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) B)) (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))))) t p0054
  have p0056 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) B)) (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))))))
  have p0057 :=
    @g_excom (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y))))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) B)) (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))))) y t
  have p0058 :=
    @g_n_3bitr4i (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) B)) (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))))) (syn_wex t (syn_wex y (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y))))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) B)) (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))))))) (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) B)) (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))))) (syn_wex y (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y))))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) B)) (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))))))) p0055 p0056 p0057
  have p0059 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (syn_csn (syn_csn (.cv x))) B)
  have p0060 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y))))) (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) B)) (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (syn_csn (syn_csn (.cv x))) B)) (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) p0059
  have p0061 :=
    @g_ceqsexv (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) B)) (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (syn_csn (syn_csn (.cv x))) B)) (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))) t (syn_csn (syn_csn (syn_csn (.cv y)))) dv_cache_0013 dv_cache_0020 p0026 p0060
  have p0062 :=
    @g_elin (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (syn_csn (syn_csn (.cv x))) B)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))
  have p0063 :=
    @g_otkelins3k (syn_csn (.cv y)) (syn_csn (syn_csn (.cv x))) B (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0031 p0032 hyp_srelk_2
  have p0064 :=
    @g_opksnelsik (.cv y) (syn_csn (.cv x)) (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0034 p0035
  have p0065 :=
    @g_opkex (.cv y) (syn_csn (.cv x))
  have p0066 :=
    @g_elimak t (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))) (syn_copk (.cv y) (syn_csn (.cv x))) dv_cache_0021 dv_cache_0009 dv_cache_0022 p0065
  have p0067 :=
    @g_elpw121c z (.cv t) dv_cache_0023
  have p0068 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (syn_wex z (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))) (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (syn_csn (.cv x)))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))) p0067
  have p0069 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z))))) (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (syn_csn (.cv x)))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))) z dv_cache_0024
  have p0070 :=
    @g_bitr4i (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (syn_csn (.cv x)))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))))) (syn_wa (syn_wex z (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))) (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (syn_csn (.cv x)))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))))) (syn_wex z (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z))))) (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (syn_csn (.cv x)))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))))) p0068 p0069
  have p0071 :=
    @g_exbii (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (syn_csn (.cv x)))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))))) (syn_wex z (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z))))) (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (syn_csn (.cv x)))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))))) t p0070
  have p0072 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c))) (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (syn_csn (.cv x)))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))))))
  have p0073 :=
    @g_excom (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z))))) (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (syn_csn (.cv x)))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))))) z t
  have p0074 :=
    @g_n_3bitr4i (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (syn_csn (.cv x)))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))))) (syn_wex t (syn_wex z (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z))))) (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (syn_csn (.cv x)))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))))))) (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c))) (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (syn_csn (.cv x)))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))))) (syn_wex z (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z))))) (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (syn_csn (.cv x)))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))))))) p0071 p0072 p0073
  have p0075 :=
    @g_snex (syn_csn (syn_csn (.cv z)))
  have p0076 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv y) (syn_csn (.cv x)))
  have p0077 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z))))) (syn_copk (.cv t) (syn_copk (.cv y) (syn_csn (.cv x)))) (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv y) (syn_csn (.cv x)))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) p0076
  have p0078 :=
    @g_ceqsexv (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (syn_csn (.cv x)))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv y) (syn_csn (.cv x)))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))) t (syn_csn (syn_csn (syn_csn (.cv z)))) dv_cache_0025 dv_cache_0026 p0075 p0077
  have p0079 :=
    @g_elsymdif (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv y) (syn_csn (.cv x)))) (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))
  have p0080 :=
    @g_snex (.cv z)
  have p0081 :=
    @g_otkelins3k (syn_csn (.cv z)) (.cv y) (syn_csn (.cv x)) (syn_cssetk) p0080 p0034 p0035
  have p0082 :=
    @g_vex z
  have p0083 :=
    @g_elssetk (.cv z) (.cv y) p0082 p0034
  have p0084_e01_recanon : Nominal.NPrf (syn_wb (.classMem (syn_copk (syn_csn (.cv z)) (.cv y)) (syn_cssetk)) (.objMem z y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn syn_cssetk syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0083
  have p0084 :=
    @g_bitri (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv y) (syn_csn (.cv x)))) (syn_cins3k (syn_cssetk))) (.classMem (syn_copk (syn_csn (.cv z)) (.cv y)) (syn_cssetk)) (.objMem z y) p0081 p0084_e01_recanon
  have p0085 :=
    @g_otkelins2k (syn_csn (.cv z)) (.cv y) (syn_csn (.cv x)) (syn_csik (syn_cssetk)) p0080 p0034 p0035
  have p0086 :=
    @g_opksnelsik (.cv z) (.cv x) (syn_cssetk) p0082 p0037
  have p0087 :=
    @g_opkelssetkg (.cv z) (.cv x) (syn_cvv) (syn_cvv)
  have p0088 :=
    @g_mp2an (.classMem (.cv z) (syn_cvv)) (.classMem (.cv x) (syn_cvv)) (syn_wb (.classMem (syn_copk (.cv z) (.cv x)) (syn_cssetk)) (syn_wss (.cv z) (.cv x))) p0082 p0037 p0087
  have p0089 :=
    @g_n_3bitri (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv y) (syn_csn (.cv x)))) (syn_cins2k (syn_csik (syn_cssetk)))) (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv x))) (syn_csik (syn_cssetk))) (.classMem (syn_copk (.cv z) (.cv x)) (syn_cssetk)) (syn_wss (.cv z) (.cv x)) p0085 p0086 p0088
  have p0090 :=
    @g_bibi12i (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv y) (syn_csn (.cv x)))) (syn_cins3k (syn_cssetk))) (.objMem z y) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv y) (syn_csn (.cv x)))) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_wss (.cv z) (.cv x)) p0084 p0089
  have p0091 :=
    @g_notbii (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv y) (syn_csn (.cv x)))) (syn_cins3k (syn_cssetk))) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv y) (syn_csn (.cv x)))) (syn_cins2k (syn_csik (syn_cssetk))))) (syn_wb (.objMem z y) (syn_wss (.cv z) (.cv x))) p0090
  have p0092 :=
    @g_n_3bitri (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z))))) (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (syn_csn (.cv x)))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))))) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv y) (syn_csn (.cv x)))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))) (.neg (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv y) (syn_csn (.cv x)))) (syn_cins3k (syn_cssetk))) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv y) (syn_csn (.cv x)))) (syn_cins2k (syn_csik (syn_cssetk)))))) (.neg (syn_wb (.objMem z y) (syn_wss (.cv z) (.cv x)))) p0078 p0079 p0091
  have p0093 :=
    @g_exbii (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z))))) (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (syn_csn (.cv x)))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))))) (.neg (syn_wb (.objMem z y) (syn_wss (.cv z) (.cv x)))) z p0092
  have p0094 :=
    @g_n_3bitri (.classMem (syn_copk (.cv y) (syn_csn (.cv x))) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c))) (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (syn_csn (.cv x)))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))))) (syn_wex z (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z))))) (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (syn_csn (.cv x)))) (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))))))) (syn_wex z (.neg (syn_wb (.objMem z y) (syn_wss (.cv z) (.cv x))))) p0066 p0074 p0093
  have p0095 :=
    @g_notbii (.classMem (syn_copk (.cv y) (syn_csn (.cv x))) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_wex z (.neg (syn_wb (.objMem z y) (syn_wss (.cv z) (.cv x))))) p0094
  have p0096 :=
    @g_elcompl (syn_copk (.cv y) (syn_csn (.cv x))) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0065
  have p0097 :=
    @g_alex (syn_wb (.objMem z y) (syn_wss (.cv z) (.cv x))) z
  have p0098 :=
    @g_n_3bitr4i (.neg (.classMem (syn_copk (.cv y) (syn_csn (.cv x))) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (.neg (syn_wex z (.neg (syn_wb (.objMem z y) (syn_wss (.cv z) (.cv x)))))) (.classMem (syn_copk (.cv y) (syn_csn (.cv x))) (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (.all z (syn_wb (.objMem z y) (syn_wss (.cv z) (.cv x)))) p0095 p0096 p0097
  have p0099 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_pw z (.cv x) dv_cache_0027
  have p0100 :=
    @g_eqeq2i (syn_cpw (.cv x)) (.cab z (syn_wss (.cv z) (.cv x))) (.cv y) p0099
  have p0101 :=
    @g_eqabb (syn_wss (.cv z) (.cv x)) z (.cv y) dv_cache_0028
  have p0102_e01_recanon : Nominal.NPrf (syn_wb (.classEq (.cv y) (.cab z (syn_wss (.cv z) (.cv x)))) (.all z (syn_wb (.objMem z y) (syn_wss (.cv z) (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
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
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
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
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0101
  have p0102 :=
    @g_bitri (.classEq (.cv y) (syn_cpw (.cv x))) (.classEq (.cv y) (.cab z (syn_wss (.cv z) (.cv x)))) (.all z (syn_wb (.objMem z y) (syn_wss (.cv z) (.cv x)))) p0100 p0102_e01_recanon
  have p0103 :=
    @g_bitr4i (.classMem (syn_copk (.cv y) (syn_csn (.cv x))) (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (.all z (syn_wb (.objMem z y) (syn_wss (.cv z) (.cv x)))) (.classEq (.cv y) (syn_cpw (.cv x))) p0098 p0102
  have p0104 :=
    @g_n_3bitri (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (syn_csn (syn_csn (.cv x))) B)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (.classMem (syn_copk (syn_csn (.cv y)) (syn_csn (syn_csn (.cv x)))) (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (.classMem (syn_copk (.cv y) (syn_csn (.cv x))) (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (.classEq (.cv y) (syn_cpw (.cv x))) p0063 p0064 p0103
  have p0105 :=
    @g_otkelins2k (syn_csn (.cv y)) (syn_csn (syn_csn (.cv x))) B (syn_cssetk) p0031 p0032 hyp_srelk_2
  have p0106 :=
    @g_elssetk (.cv y) B p0034 hyp_srelk_2
  have p0107 :=
    @g_bitri (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (syn_csn (syn_csn (.cv x))) B)) (syn_cins2k (syn_cssetk))) (.classMem (syn_copk (syn_csn (.cv y)) B) (syn_cssetk)) (.classMem (.cv y) B) p0105 p0106
  have p0108 :=
    @g_anbi12i (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (syn_csn (syn_csn (.cv x))) B)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (.classEq (.cv y) (syn_cpw (.cv x))) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (syn_csn (syn_csn (.cv x))) B)) (syn_cins2k (syn_cssetk))) (.classMem (.cv y) B) p0104 p0107
  have p0109 :=
    @g_n_3bitri (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y))))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) B)) (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))))) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (syn_csn (syn_csn (.cv x))) B)) (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))) (syn_wa (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (syn_csn (syn_csn (.cv x))) B)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (syn_csn (syn_csn (.cv x))) B)) (syn_cins2k (syn_cssetk)))) (syn_wa (.classEq (.cv y) (syn_cpw (.cv x))) (.classMem (.cv y) B)) p0061 p0062 p0108
  have p0110 :=
    @g_exbii (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y))))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) B)) (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))))) (syn_wa (.classEq (.cv y) (syn_cpw (.cv x))) (.classMem (.cv y) B)) y p0109
  have p0111 :=
    @g_n_3bitri (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) B) (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) B)) (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))))) (syn_wex y (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y))))) (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv x))) B)) (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))))))) (syn_wex y (syn_wa (.classEq (.cv y) (syn_cpw (.cv x))) (.classMem (.cv y) B))) p0051 p0058 p0110
  have p0112 :=
    @g_otkelins2k (syn_csn (syn_csn (.cv x))) A B (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0032 hyp_srelk_1 hyp_srelk_2
  have p0113 :=
    (by simpa [NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfClelGoal, syn_wb, syn_wex, syn_wa, Wff.biimp, Wff.ex, Wff.conj, Wff.neg] using (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV y (syn_cpw (.cv x)) B dv_cache_0029 dv_cache_0030))
  have p0114 :=
    @g_n_3bitr4i (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) B) (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_wex y (syn_wa (.classEq (.cv y) (syn_cpw (.cv x))) (.classMem (.cv y) B))) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_copk A B)) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (.classMem (syn_cpw (.cv x)) B) p0111 p0112 p0113
  have p0115 :=
    @g_anbi12i (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_copk A B)) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (.classMem (syn_cpw1 (.cv x)) A) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_copk A B)) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (.classMem (syn_cpw (.cv x)) B) p0049 p0114
  have p0116 :=
    @g_n_3bitri (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_wa (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_copk A B)) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_copk A B)) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_wa (.classMem (syn_cpw1 (.cv x)) A) (.classMem (syn_cpw (.cv x)) B)) p0014 p0015 p0115
  have p0117 :=
    @g_exbii (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_wa (.classMem (syn_cpw1 (.cv x)) A) (.classMem (syn_cpw (.cv x)) B)) x p0116
  have p0118 :=
    @g_n_3bitri (.classMem (syn_copk A B) (syn_cimak (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_wex x (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) (.classMem (syn_copk (.cv t) (syn_copk A B)) (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_wex x (syn_wa (.classMem (syn_cpw1 (.cv x)) A) (.classMem (syn_cpw (.cv x)) B))) p0002 p0010 p0117
  have p0119 :=
    @g_anbi12i (.classMem (syn_copk A B) (syn_cxpk (syn_cnnc) (syn_cnnc))) (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk A B) (syn_cimak (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_wex x (syn_wa (.classMem (syn_cpw1 (.cv x)) A) (.classMem (syn_cpw (.cv x)) B))) p0000 p0118
  have p0120 :=
    (by simpa [syn_wb, syn_w3a] using (Nominal.biimpRefl (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (syn_wex x (syn_wa (.classMem (syn_cpw1 (.cv x)) A) (.classMem (syn_cpw (.cv x)) B))))))
  have p0121 :=
    @g_bitr4i (syn_wa (.classMem (syn_copk A B) (syn_cxpk (syn_cnnc) (syn_cnnc))) (.classMem (syn_copk A B) (syn_cimak (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wex x (syn_wa (.classMem (syn_cpw1 (.cv x)) A) (.classMem (syn_cpw (.cv x)) B)))) (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (syn_wex x (syn_wa (.classMem (syn_cpw1 (.cv x)) A) (.classMem (syn_cpw (.cv x)) B)))) p0119 p0120
  have p0122 :=
    @g_elin (syn_copk A B) (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
  have p0123 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin A B x dv_cache_0031 dv_cache_0032
  have p0124 :=
    @g_n_3bitr4i (syn_wa (.classMem (syn_copk A B) (syn_cxpk (syn_cnnc) (syn_cnnc))) (.classMem (syn_copk A B) (syn_cimak (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (syn_wex x (syn_wa (.classMem (syn_cpw1 (.cv x)) A) (.classMem (syn_cpw (.cv x)) B)))) (.classMem (syn_copk A B) (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_wsfin A B) p0121 p0122 p0123
  exact p0124

#print axioms g_srelk

end NFChoice.DirectNominalPrf.WPPReplay
