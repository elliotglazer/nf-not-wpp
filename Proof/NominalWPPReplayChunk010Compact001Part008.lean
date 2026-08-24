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
import NominalWPPReplayChunk010Compact001Part007

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

noncomputable def g_nnadjoinpw
    (A : Class) (M : Class) (N : Class) (X : Class) :
    Nominal.NPrf (.imp (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (.classMem A M) (.classMem X (syn_ccompl A))) (.classMem (syn_cpw A) N)) (.classMem (syn_cpw (syn_cun A (syn_csn X))) (syn_cplc N N))) := by
  let proofSupport : Finset Var := A.fv ∪ M.fv ∪ N.fv ∪ X.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let t : Var := freshVar proofSupport 2
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_a_not_M : a ∉ M.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a_not_N : a ∉ N.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_X : a ∉ X.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_b_not_M : b ∉ M.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_b_not_N : b ∉ N.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_not_X : b ∉ X.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_t_not_M : t ∉ M.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_t_not_N : t ∉ N.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_t_not_X : t ∉ X.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have fresh_a_ne_t : a ≠ t := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_t_ne_a : t ≠ a :=
    Ne.symm fresh_a_ne_t
  have fresh_b_ne_t : b ≠ t := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_t_ne_b : t ≠ b :=
    Ne.symm fresh_b_ne_t
  have dv_cache_0001 : a ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : b ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : a ∉ (X).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : b ∉ (X).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : a ≠ b := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0006 : b ∉ ((syn_cpw A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : a ∉ ((syn_cpw A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : b ≠ a := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show b ≠ a from (by exact fresh_b_ne_a))
  have dv_cache_0009 : b ∉ ((syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (.classMem A M) (.classMem X (syn_ccompl A))) (.classMem (syn_cpw A) N))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_A, fresh_b_not_N, fresh_b_not_M, fresh_b_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : t ∉ ((syn_cpw A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : t ∉ ((Class.cab a (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_A, fresh_t_ne_a, fresh_t_ne_b, fresh_t_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : b ∉ ((Wff.objEq a t)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_a, fresh_b_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : a ∉ ((syn_wrex b (syn_cpw A) (.classEq (.cv t) (syn_cun (.cv b) (syn_csn X))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, fresh_a_ne_t, fresh_a_ne_b, fresh_a_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : t ≠ a := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show t ≠ a from (by exact fresh_t_ne_a))
  have dv_cache_0015 : b ≠ t := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show b ≠ t from (by exact fresh_b_ne_t))
  have dv_cache_0016 : t ∉ ((syn_cun (.cv b) (syn_csn X))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_b, fresh_t_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : t ∉ ((Wff.neg (.classMem (syn_cun (.cv b) (syn_csn X)) (syn_cpw A)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_b, fresh_t_not_X, fresh_t_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : b ∉ ((Wff.neg (.classMem (.cv t) (syn_cpw A)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_t, fresh_b_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_pwadjoin A X a b dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @g_simp3 (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (.classMem A M) (.classMem X (syn_ccompl A))) (.classMem (syn_cpw A) N)
  have p0002 :=
    @g_simp1r (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wa (.classMem A M) (.classMem X (syn_ccompl A))) (.classMem (syn_cpw A) N)
  have p0003 :=
    @g_simp2r (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classMem A M) (.classMem X (syn_ccompl A)) (.classMem (syn_cpw A) N)
  have p0004 :=
    @g_unipw A
  have p0005 :=
    @g_compleqi (syn_cuni (syn_cpw A)) A p0004
  have p0006 :=
    @g_syl6eleqr (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (.classMem A M) (.classMem X (syn_ccompl A))) (.classMem (syn_cpw A) N)) X (syn_ccompl A) (syn_ccompl (syn_cuni (syn_cpw A))) p0003 p0005
  have p0007 :=
    @g_nnadjoin a (syn_cpw A) N X b dv_cache_0006 dv_cache_0007 dv_cache_0004 dv_cache_0003 dv_cache_0008
  have p0008 :=
    @g_syl3anc (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (.classMem A M) (.classMem X (syn_ccompl A))) (.classMem (syn_cpw A) N)) (.classMem N (syn_cnnc)) (.classMem (syn_cpw A) N) (.classMem X (syn_ccompl (syn_cuni (syn_cpw A)))) (.classMem (.cab a (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X))))) N) p0002 p0001 p0006 p0007
  have p0009 :=
    @g_elcomplg X A (syn_ccompl A)
  have p0010 :=
    @g_ibi (.classMem X (syn_ccompl A)) (.neg (.classMem X A)) p0009
  have p0011 :=
    @g_syl (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (.classMem A M) (.classMem X (syn_ccompl A))) (.classMem (syn_cpw A) N)) (.classMem X (syn_ccompl A)) (.neg (.classMem X A)) p0003 p0010
  have p0012 :=
    @g_snssg X A (syn_ccompl A)
  have p0013 :=
    @g_syl (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (.classMem A M) (.classMem X (syn_ccompl A))) (.classMem (syn_cpw A) N)) (.classMem X (syn_ccompl A)) (syn_wb (.classMem X A) (syn_wss (syn_csn X) A)) p0003 p0012
  have p0014 :=
    @g_mtbid (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (.classMem A M) (.classMem X (syn_ccompl A))) (.classMem (syn_cpw A) N)) (.classMem X A) (syn_wss (syn_csn X) A) p0011 p0013
  have p0015 :=
    @g_intnand (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (.classMem A M) (.classMem X (syn_ccompl A))) (.classMem (syn_cpw A) N)) (syn_wss (syn_csn X) A) (syn_wss (.cv b) A) p0014
  have p0016 :=
    @g_ralrimivw (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (.classMem A M) (.classMem X (syn_ccompl A))) (.classMem (syn_cpw A) N)) (.neg (syn_wa (syn_wss (.cv b) A) (syn_wss (syn_csn X) A))) b (syn_cpw A) dv_cache_0009 p0015
  have p0017 :=
    @g_disjr t (syn_cpw A) (.cab a (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X))))) dv_cache_0010 dv_cache_0011
  have p0018 :=
    @g_eqeq1 (.cv a) (.cv t) (syn_cun (.cv b) (syn_csn X))
  have p0019_e00_recanon : Nominal.NPrf (.imp (.objEq a t) (syn_wb (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X))) (.classEq (.cv t) (syn_cun (.cv b) (syn_csn X))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0018
  have p0019 :=
    @g_rexbidv (.objEq a t) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X))) (.classEq (.cv t) (syn_cun (.cv b) (syn_csn X))) b (syn_cpw A) dv_cache_0012 p0019_e00_recanon
  have p0020 :=
    @g_ralab (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X)))) (syn_wrex b (syn_cpw A) (.classEq (.cv t) (syn_cun (.cv b) (syn_csn X)))) (.neg (.classMem (.cv t) (syn_cpw A))) t a dv_cache_0013 dv_cache_0014 p0019
  have p0021 :=
    @g_ralcom4 (.imp (.classEq (.cv t) (syn_cun (.cv b) (syn_csn X))) (.neg (.classMem (.cv t) (syn_cpw A)))) b t (syn_cpw A) dv_cache_0010 dv_cache_0015
  have p0022 :=
    @g_vex b
  have p0023 :=
    @g_snex X
  have p0024 :=
    @g_unex (.cv b) (syn_csn X) p0022 p0023
  have p0025 :=
    @g_eleq1 (.cv t) (syn_cun (.cv b) (syn_csn X)) (syn_cpw A)
  have p0026 :=
    @g_notbid (.classEq (.cv t) (syn_cun (.cv b) (syn_csn X))) (.classMem (.cv t) (syn_cpw A)) (.classMem (syn_cun (.cv b) (syn_csn X)) (syn_cpw A)) p0025
  have p0027 :=
    @g_ceqsalv (.neg (.classMem (.cv t) (syn_cpw A))) (.neg (.classMem (syn_cun (.cv b) (syn_csn X)) (syn_cpw A))) t (syn_cun (.cv b) (syn_csn X)) dv_cache_0016 dv_cache_0017 p0024 p0026
  have p0028 :=
    @g_elpw (syn_cun (.cv b) (syn_csn X)) A p0024
  have p0029 :=
    @g_unss (.cv b) (syn_csn X) A
  have p0030 :=
    @g_bitr4i (.classMem (syn_cun (.cv b) (syn_csn X)) (syn_cpw A)) (syn_wss (syn_cun (.cv b) (syn_csn X)) A) (syn_wa (syn_wss (.cv b) A) (syn_wss (syn_csn X) A)) p0028 p0029
  have p0031 :=
    @g_xchbinx (.all t (.imp (.classEq (.cv t) (syn_cun (.cv b) (syn_csn X))) (.neg (.classMem (.cv t) (syn_cpw A))))) (.classMem (syn_cun (.cv b) (syn_csn X)) (syn_cpw A)) (syn_wa (syn_wss (.cv b) A) (syn_wss (syn_csn X) A)) p0027 p0030
  have p0032 :=
    @g_ralbii (.all t (.imp (.classEq (.cv t) (syn_cun (.cv b) (syn_csn X))) (.neg (.classMem (.cv t) (syn_cpw A))))) (.neg (syn_wa (syn_wss (.cv b) A) (syn_wss (syn_csn X) A))) b (syn_cpw A) p0031
  have p0033 :=
    @g_r19_23v (.classEq (.cv t) (syn_cun (.cv b) (syn_csn X))) (.neg (.classMem (.cv t) (syn_cpw A))) b (syn_cpw A) dv_cache_0018
  have p0034 :=
    @g_albii (syn_wral b (syn_cpw A) (.imp (.classEq (.cv t) (syn_cun (.cv b) (syn_csn X))) (.neg (.classMem (.cv t) (syn_cpw A))))) (.imp (syn_wrex b (syn_cpw A) (.classEq (.cv t) (syn_cun (.cv b) (syn_csn X)))) (.neg (.classMem (.cv t) (syn_cpw A)))) t p0033
  have p0035 :=
    @g_n_3bitr3ri (syn_wral b (syn_cpw A) (.all t (.imp (.classEq (.cv t) (syn_cun (.cv b) (syn_csn X))) (.neg (.classMem (.cv t) (syn_cpw A)))))) (.all t (syn_wral b (syn_cpw A) (.imp (.classEq (.cv t) (syn_cun (.cv b) (syn_csn X))) (.neg (.classMem (.cv t) (syn_cpw A)))))) (syn_wral b (syn_cpw A) (.neg (syn_wa (syn_wss (.cv b) A) (syn_wss (syn_csn X) A)))) (.all t (.imp (syn_wrex b (syn_cpw A) (.classEq (.cv t) (syn_cun (.cv b) (syn_csn X)))) (.neg (.classMem (.cv t) (syn_cpw A))))) p0021 p0032 p0034
  have p0036 :=
    @g_n_3bitri (.classEq (syn_cin (syn_cpw A) (.cab a (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X)))))) (syn_c0)) (syn_wral t (.cab a (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X))))) (.neg (.classMem (.cv t) (syn_cpw A)))) (.all t (.imp (syn_wrex b (syn_cpw A) (.classEq (.cv t) (syn_cun (.cv b) (syn_csn X)))) (.neg (.classMem (.cv t) (syn_cpw A))))) (syn_wral b (syn_cpw A) (.neg (syn_wa (syn_wss (.cv b) A) (syn_wss (syn_csn X) A)))) p0017 p0020 p0035
  have p0037 :=
    @g_sylibr (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (.classMem A M) (.classMem X (syn_ccompl A))) (.classMem (syn_cpw A) N)) (syn_wral b (syn_cpw A) (.neg (syn_wa (syn_wss (.cv b) A) (syn_wss (syn_csn X) A)))) (.classEq (syn_cin (syn_cpw A) (.cab a (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X)))))) (syn_c0)) p0016 p0036
  have p0038 :=
    @g_eladdci (syn_cpw A) (.cab a (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X))))) N N
  have p0039 :=
    @g_syl3anc (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (.classMem A M) (.classMem X (syn_ccompl A))) (.classMem (syn_cpw A) N)) (.classMem (syn_cpw A) N) (.classMem (.cab a (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X))))) N) (.classEq (syn_cin (syn_cpw A) (.cab a (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X)))))) (syn_c0)) (.classMem (syn_cun (syn_cpw A) (.cab a (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X)))))) (syn_cplc N N)) p0001 p0008 p0037 p0038
  have p0040 :=
    @g_syl5eqel (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (.classMem A M) (.classMem X (syn_ccompl A))) (.classMem (syn_cpw A) N)) (syn_cpw (syn_cun A (syn_csn X))) (syn_cun (syn_cpw A) (.cab a (syn_wrex b (syn_cpw A) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn X)))))) (syn_cplc N N) p0000 p0039
  exact p0040

#print axioms g_nnadjoinpw

end NFChoice.DirectNominalPrf.WPPReplay
