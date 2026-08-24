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
import NominalWPPReplayChunk011Compact001Part003

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

noncomputable def g_elimapw1
    (x : Var) (A : Class) (B : Class) (C : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cima B (syn_cpw1 C))) (syn_wrex x C (.classMem (syn_cop (syn_csn (.cv x)) A) B))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  let t : Var := freshVar proofSupport 0
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_t_ne_x : t ≠ x := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_t : x ≠ t :=
    Ne.symm fresh_t_ne_x
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_t_not_C : t ∉ C.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have dv_cache_0001 : t ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : t ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : t ∉ ((syn_cpw1 C)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Class.cv t)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_wbr (.cv t) B A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_t, dv_A_x, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : t ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ≠ t := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show x ≠ t from (by exact fresh_x_ne_t))
  have dv_cache_0009 : t ∉ ((syn_csn (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : t ∉ ((syn_wbr (syn_csn (.cv x)) B A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_x, fresh_t_not_A, fresh_t_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elima t A B (syn_cpw1 C) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex t (syn_cpw1 C) (syn_wbr (.cv t) B A))))
  have p0002 :=
    @g_elpw1 x (.cv t) C dv_cache_0004 dv_cache_0005
  have p0003 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 C)) (syn_wrex x C (.classEq (.cv t) (syn_csn (.cv x)))) (syn_wbr (.cv t) B A) p0002
  have p0004 :=
    @g_r19_41v (.classEq (.cv t) (syn_csn (.cv x))) (syn_wbr (.cv t) B A) x C dv_cache_0006
  have p0005 :=
    @g_bitr4i (syn_wa (.classMem (.cv t) (syn_cpw1 C)) (syn_wbr (.cv t) B A)) (syn_wa (syn_wrex x C (.classEq (.cv t) (syn_csn (.cv x)))) (syn_wbr (.cv t) B A)) (syn_wrex x C (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (syn_wbr (.cv t) B A))) p0003 p0004
  have p0006 :=
    @g_exbii (syn_wa (.classMem (.cv t) (syn_cpw1 C)) (syn_wbr (.cv t) B A)) (syn_wrex x C (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (syn_wbr (.cv t) B A))) t p0005
  have p0007 :=
    @g_rexcom4 (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (syn_wbr (.cv t) B A)) x t C dv_cache_0007 dv_cache_0008
  have p0008 :=
    @g_bitr4i (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 C)) (syn_wbr (.cv t) B A))) (syn_wex t (syn_wrex x C (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (syn_wbr (.cv t) B A)))) (syn_wrex x C (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (syn_wbr (.cv t) B A)))) p0006 p0007
  have p0009 :=
    @g_bitri (syn_wrex t (syn_cpw1 C) (syn_wbr (.cv t) B A)) (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 C)) (syn_wbr (.cv t) B A))) (syn_wrex x C (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (syn_wbr (.cv t) B A)))) p0001 p0008
  have p0010 :=
    @g_snex (.cv x)
  have p0011 :=
    @g_breq1 (.cv t) (syn_csn (.cv x)) A B
  have p0012 :=
    @g_ceqsexv (syn_wbr (.cv t) B A) (syn_wbr (syn_csn (.cv x)) B A) t (syn_csn (.cv x)) dv_cache_0009 dv_cache_0010 p0010 p0011
  have p0013 :=
    @g_rexbii (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (syn_wbr (.cv t) B A))) (syn_wbr (syn_csn (.cv x)) B A) x C p0012
  have p0014 :=
    @g_bitri (syn_wrex t (syn_cpw1 C) (syn_wbr (.cv t) B A)) (syn_wrex x C (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (syn_wbr (.cv t) B A)))) (syn_wrex x C (syn_wbr (syn_csn (.cv x)) B A)) p0009 p0013
  have p0015 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (syn_csn (.cv x)) B A)))
  have p0016 :=
    @g_rexbii (syn_wbr (syn_csn (.cv x)) B A) (.classMem (syn_cop (syn_csn (.cv x)) A) B) x C p0015
  have p0017 :=
    @g_bitri (syn_wrex t (syn_cpw1 C) (syn_wbr (.cv t) B A)) (syn_wrex x C (syn_wbr (syn_csn (.cv x)) B A)) (syn_wrex x C (.classMem (syn_cop (syn_csn (.cv x)) A) B)) p0014 p0016
  have p0018 :=
    @g_bitri (.classMem A (syn_cima B (syn_cpw1 C))) (syn_wrex t (syn_cpw1 C) (syn_wbr (.cv t) B A)) (syn_wrex x C (.classMem (syn_cop (syn_csn (.cv x)) A) B)) p0000 p0017
  exact p0018

noncomputable def g_elimapw12
    (x : Var) (A : Class) (B : Class) (C : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cima B (syn_cpw1 (syn_cpw1 C)))) (syn_wrex x C (.classMem (syn_cop (syn_csn (syn_csn (.cv x))) A) B))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  let t : Var := freshVar proofSupport 0
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_t_ne_x : t ≠ x := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_t : x ≠ t :=
    Ne.symm fresh_t_ne_x
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_t_not_C : t ∉ C.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have dv_cache_0001 : t ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : t ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : t ∉ ((syn_cpw1 C)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Class.cv t)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((Wff.classMem (syn_cop (syn_csn (.cv t)) A) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_t, dv_A_x, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : t ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ≠ t := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show x ≠ t from (by exact fresh_x_ne_t))
  have dv_cache_0009 : t ∉ ((syn_csn (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : t ∉ ((Wff.classMem (syn_cop (syn_csn (syn_csn (.cv x))) A) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_x, fresh_t_not_A, fresh_t_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elimapw1 t A B (syn_cpw1 C) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex t (syn_cpw1 C) (.classMem (syn_cop (syn_csn (.cv t)) A) B))))
  have p0002 :=
    @g_elpw1 x (.cv t) C dv_cache_0004 dv_cache_0005
  have p0003 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 C)) (syn_wrex x C (.classEq (.cv t) (syn_csn (.cv x)))) (.classMem (syn_cop (syn_csn (.cv t)) A) B) p0002
  have p0004 :=
    @g_r19_41v (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_cop (syn_csn (.cv t)) A) B) x C dv_cache_0006
  have p0005 :=
    @g_bitr4i (syn_wa (.classMem (.cv t) (syn_cpw1 C)) (.classMem (syn_cop (syn_csn (.cv t)) A) B)) (syn_wa (syn_wrex x C (.classEq (.cv t) (syn_csn (.cv x)))) (.classMem (syn_cop (syn_csn (.cv t)) A) B)) (syn_wrex x C (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_cop (syn_csn (.cv t)) A) B))) p0003 p0004
  have p0006 :=
    @g_exbii (syn_wa (.classMem (.cv t) (syn_cpw1 C)) (.classMem (syn_cop (syn_csn (.cv t)) A) B)) (syn_wrex x C (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_cop (syn_csn (.cv t)) A) B))) t p0005
  have p0007 :=
    @g_rexcom4 (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_cop (syn_csn (.cv t)) A) B)) x t C dv_cache_0007 dv_cache_0008
  have p0008 :=
    @g_snex (.cv x)
  have p0009 :=
    @g_sneq (.cv t) (syn_csn (.cv x))
  have p0010 :=
    @g_opeq1d (.classEq (.cv t) (syn_csn (.cv x))) (syn_csn (.cv t)) (syn_csn (syn_csn (.cv x))) A p0009
  have p0011 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (.cv x))) (syn_cop (syn_csn (.cv t)) A) (syn_cop (syn_csn (syn_csn (.cv x))) A) B p0010
  have p0012 :=
    @g_ceqsexv (.classMem (syn_cop (syn_csn (.cv t)) A) B) (.classMem (syn_cop (syn_csn (syn_csn (.cv x))) A) B) t (syn_csn (.cv x)) dv_cache_0009 dv_cache_0010 p0008 p0011
  have p0013 :=
    @g_rexbii (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_cop (syn_csn (.cv t)) A) B))) (.classMem (syn_cop (syn_csn (syn_csn (.cv x))) A) B) x C p0012
  have p0014 :=
    @g_bitr3i (syn_wex t (syn_wrex x C (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_cop (syn_csn (.cv t)) A) B)))) (syn_wrex x C (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_cop (syn_csn (.cv t)) A) B)))) (syn_wrex x C (.classMem (syn_cop (syn_csn (syn_csn (.cv x))) A) B)) p0007 p0013
  have p0015 :=
    @g_bitri (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 C)) (.classMem (syn_cop (syn_csn (.cv t)) A) B))) (syn_wex t (syn_wrex x C (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_cop (syn_csn (.cv t)) A) B)))) (syn_wrex x C (.classMem (syn_cop (syn_csn (syn_csn (.cv x))) A) B)) p0006 p0014
  have p0016 :=
    @g_bitri (syn_wrex t (syn_cpw1 C) (.classMem (syn_cop (syn_csn (.cv t)) A) B)) (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 C)) (.classMem (syn_cop (syn_csn (.cv t)) A) B))) (syn_wrex x C (.classMem (syn_cop (syn_csn (syn_csn (.cv x))) A) B)) p0001 p0015
  have p0017 :=
    @g_bitri (.classMem A (syn_cima B (syn_cpw1 (syn_cpw1 C)))) (syn_wrex t (syn_cpw1 C) (.classMem (syn_cop (syn_csn (.cv t)) A) B)) (syn_wrex x C (.classMem (syn_cop (syn_csn (syn_csn (.cv x))) A) B)) p0000 p0016
  exact p0017

noncomputable def g_elima1c
    (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cima B (syn_c1c))) (syn_wex x (.classMem (syn_cop (syn_csn (.cv x)) A) B))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_df1c2
  have p0001 :=
    @g_imaeq2i (syn_c1c) (syn_cpw1 (syn_cvv)) B p0000
  have p0002 :=
    @g_eleq2i (syn_cima B (syn_c1c)) (syn_cima B (syn_cpw1 (syn_cvv))) A p0001
  have p0003 :=
    @g_elimapw1 x A B (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0004 :=
    @g_rexv (.classMem (syn_cop (syn_csn (.cv x)) A) B) x
  have p0005 :=
    @g_n_3bitri (.classMem A (syn_cima B (syn_c1c))) (.classMem A (syn_cima B (syn_cpw1 (syn_cvv)))) (syn_wrex x (syn_cvv) (.classMem (syn_cop (syn_csn (.cv x)) A) B)) (syn_wex x (.classMem (syn_cop (syn_csn (.cv x)) A) B)) p0002 p0003 p0004
  exact p0005

noncomputable def g_elimapw11c
    (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cima B (syn_cpw1 (syn_c1c)))) (syn_wex x (.classMem (syn_cop (syn_csn (syn_csn (.cv x))) A) B))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv
  let t : Var := freshVar proofSupport 0
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
  have dv_cache_0001 : t ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : t ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : t ∉ ((syn_c1c)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Class.cv t)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classMem (syn_cop (syn_csn (.cv t)) A) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_t, dv_A_x, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : t ∉ ((syn_csn (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : t ∉ ((Wff.classMem (syn_cop (syn_csn (syn_csn (.cv x))) A) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_x, fresh_t_not_A, fresh_t_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elimapw1 t A B (syn_c1c) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex t (syn_c1c) (.classMem (syn_cop (syn_csn (.cv t)) A) B))))
  have p0002 :=
    @g_el1c x (.cv t) dv_cache_0004
  have p0003 :=
    @g_anbi1i (.classMem (.cv t) (syn_c1c)) (syn_wex x (.classEq (.cv t) (syn_csn (.cv x)))) (.classMem (syn_cop (syn_csn (.cv t)) A) B) p0002
  have p0004 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_cop (syn_csn (.cv t)) A) B) x dv_cache_0005
  have p0005 :=
    @g_bitr4i (syn_wa (.classMem (.cv t) (syn_c1c)) (.classMem (syn_cop (syn_csn (.cv t)) A) B)) (syn_wa (syn_wex x (.classEq (.cv t) (syn_csn (.cv x)))) (.classMem (syn_cop (syn_csn (.cv t)) A) B)) (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_cop (syn_csn (.cv t)) A) B))) p0003 p0004
  have p0006 :=
    @g_exbii (syn_wa (.classMem (.cv t) (syn_c1c)) (.classMem (syn_cop (syn_csn (.cv t)) A) B)) (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_cop (syn_csn (.cv t)) A) B))) t p0005
  have p0007 :=
    @g_excom (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_cop (syn_csn (.cv t)) A) B)) t x
  have p0008 :=
    @g_bitri (syn_wex t (syn_wa (.classMem (.cv t) (syn_c1c)) (.classMem (syn_cop (syn_csn (.cv t)) A) B))) (syn_wex t (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_cop (syn_csn (.cv t)) A) B)))) (syn_wex x (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_cop (syn_csn (.cv t)) A) B)))) p0006 p0007
  have p0009 :=
    @g_snex (.cv x)
  have p0010 :=
    @g_sneq (.cv t) (syn_csn (.cv x))
  have p0011 :=
    @g_opeq1d (.classEq (.cv t) (syn_csn (.cv x))) (syn_csn (.cv t)) (syn_csn (syn_csn (.cv x))) A p0010
  have p0012 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (.cv x))) (syn_cop (syn_csn (.cv t)) A) (syn_cop (syn_csn (syn_csn (.cv x))) A) B p0011
  have p0013 :=
    @g_ceqsexv (.classMem (syn_cop (syn_csn (.cv t)) A) B) (.classMem (syn_cop (syn_csn (syn_csn (.cv x))) A) B) t (syn_csn (.cv x)) dv_cache_0006 dv_cache_0007 p0009 p0012
  have p0014 :=
    @g_exbii (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_cop (syn_csn (.cv t)) A) B))) (.classMem (syn_cop (syn_csn (syn_csn (.cv x))) A) B) x p0013
  have p0015 :=
    @g_n_3bitri (syn_wrex t (syn_c1c) (.classMem (syn_cop (syn_csn (.cv t)) A) B)) (syn_wex t (syn_wa (.classMem (.cv t) (syn_c1c)) (.classMem (syn_cop (syn_csn (.cv t)) A) B))) (syn_wex x (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_cop (syn_csn (.cv t)) A) B)))) (syn_wex x (.classMem (syn_cop (syn_csn (syn_csn (.cv x))) A) B)) p0001 p0008 p0014
  have p0016 :=
    @g_bitri (.classMem A (syn_cima B (syn_cpw1 (syn_c1c)))) (syn_wrex t (syn_c1c) (.classMem (syn_cop (syn_csn (.cv t)) A) B)) (syn_wex x (.classMem (syn_cop (syn_csn (syn_csn (.cv x))) A) B)) p0000 p0015
  exact p0016

noncomputable def g_brres
    (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf (syn_wb (syn_wbr A (syn_cres C D) B) (syn_wa (syn_wbr A C B) (.classMem A D))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  have p0000 :=
    (by simpa [syn_cres] using (Nominal.classEqRefl (syn_cres C D)))
  have p0001 :=
    @g_breqi A B (syn_cres C D) (syn_cin C (syn_cxp D (syn_cvv))) p0000
  have p0002 :=
    @g_brin A B C (syn_cxp D (syn_cvv))
  have p0003 :=
    @g_anass (syn_wbr A C B) (.classMem A D) (.classMem B (syn_cvv))
  have p0004 :=
    @g_brex A B C
  have p0005 :=
    @g_simprd (syn_wbr A C B) (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) p0004
  have p0006 :=
    @g_adantr (syn_wbr A C B) (.classMem B (syn_cvv)) (.classMem A D) p0005
  have p0007 :=
    @g_pm4_71i (syn_wa (syn_wbr A C B) (.classMem A D)) (.classMem B (syn_cvv)) p0006
  have p0008 :=
    @g_brxp A B D (syn_cvv)
  have p0009 :=
    @g_anbi2i (syn_wbr A (syn_cxp D (syn_cvv)) B) (syn_wa (.classMem A D) (.classMem B (syn_cvv))) (syn_wbr A C B) p0008
  have p0010 :=
    @g_n_3bitr4ri (syn_wa (syn_wa (syn_wbr A C B) (.classMem A D)) (.classMem B (syn_cvv))) (syn_wa (syn_wbr A C B) (syn_wa (.classMem A D) (.classMem B (syn_cvv)))) (syn_wa (syn_wbr A C B) (.classMem A D)) (syn_wa (syn_wbr A C B) (syn_wbr A (syn_cxp D (syn_cvv)) B)) p0003 p0007 p0009
  have p0011 :=
    @g_n_3bitri (syn_wbr A (syn_cres C D) B) (syn_wbr A (syn_cin C (syn_cxp D (syn_cvv))) B) (syn_wa (syn_wbr A C B) (syn_wbr A (syn_cxp D (syn_cvv)) B)) (syn_wa (syn_wbr A C B) (.classMem A D)) p0001 p0002 p0010
  exact p0011

noncomputable def g_opelres
    (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf (syn_wb (.classMem (syn_cop A B) (syn_cres C D)) (syn_wa (.classMem (syn_cop A B) C) (.classMem A D))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  have p0000 :=
    @g_brres A B C D
  have p0001 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr A (syn_cres C D) B)))
  have p0002 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr A C B)))
  have p0003 :=
    @g_anbi1i (syn_wbr A C B) (.classMem (syn_cop A B) C) (.classMem A D) p0002
  have p0004 :=
    @g_n_3bitr3i (syn_wbr A (syn_cres C D) B) (syn_wa (syn_wbr A C B) (.classMem A D)) (.classMem (syn_cop A B) (syn_cres C D)) (syn_wa (.classMem (syn_cop A B) C) (.classMem A D)) p0000 p0001 p0003
  exact p0004

noncomputable def g_dfima3
    (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cima A B) (syn_crn (syn_cres A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
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
  have dv_cache_0002 : y ∉ ((syn_cres A B)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_cima A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_crn (syn_cres A B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_opelres (.cv y) (.cv x) A B
  have p0001 :=
    @g_ancom (.classMem (syn_cop (.cv y) (.cv x)) A) (.classMem (.cv y) B)
  have p0002 :=
    @g_bitri (.classMem (syn_cop (.cv y) (.cv x)) (syn_cres A B)) (syn_wa (.classMem (syn_cop (.cv y) (.cv x)) A) (.classMem (.cv y) B)) (syn_wa (.classMem (.cv y) B) (.classMem (syn_cop (.cv y) (.cv x)) A)) p0000 p0001
  have p0003 :=
    @g_exbii (.classMem (syn_cop (.cv y) (.cv x)) (syn_cres A B)) (syn_wa (.classMem (.cv y) B) (.classMem (syn_cop (.cv y) (.cv x)) A)) y p0002
  have p0004 :=
    @g_elrn2 y (.cv x) (syn_cres A B) dv_cache_0001 dv_cache_0002
  have p0005 :=
    @g_elima3 y (.cv x) A B dv_cache_0001 dv_cache_0003 dv_cache_0004
  have p0006 :=
    @g_n_3bitr4ri (syn_wex y (.classMem (syn_cop (.cv y) (.cv x)) (syn_cres A B))) (syn_wex y (syn_wa (.classMem (.cv y) B) (.classMem (syn_cop (.cv y) (.cv x)) A))) (.classMem (.cv x) (syn_crn (syn_cres A B))) (.classMem (.cv x) (syn_cima A B)) p0003 p0004 p0005
  have p0007 :=
    @g_eqriv x (syn_cima A B) (syn_crn (syn_cres A B)) dv_cache_0005 dv_cache_0006 p0006
  exact p0007

noncomputable def g_dfima4
    (x : Var) (y : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classEq (syn_cima A B) (.cab y (syn_wex x (syn_wa (.classMem (.cv x) B) (.classMem (syn_cop (.cv x) (.cv y)) A))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv
  have dv_cache_0001 : y ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show y ≠ x from (by exact Ne.symm dv_x_y))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ima y x A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) A (.cv y))))
  have p0002 :=
    @g_rexbii (syn_wbr (.cv x) A (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) A) x B p0001
  have p0003 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex x B (.classMem (syn_cop (.cv x) (.cv y)) A))))
  have p0004 :=
    @g_bitri (syn_wrex x B (syn_wbr (.cv x) A (.cv y))) (syn_wrex x B (.classMem (syn_cop (.cv x) (.cv y)) A)) (syn_wex x (syn_wa (.classMem (.cv x) B) (.classMem (syn_cop (.cv x) (.cv y)) A))) p0002 p0003
  have p0005 :=
    @g_abbii (syn_wrex x B (syn_wbr (.cv x) A (.cv y))) (syn_wex x (syn_wa (.classMem (.cv x) B) (.classMem (syn_cop (.cv x) (.cv y)) A))) y p0004
  have p0006 :=
    @g_eqtri (syn_cima A B) (.cab y (syn_wrex x B (syn_wbr (.cv x) A (.cv y)))) (.cab y (syn_wex x (syn_wa (.classMem (.cv x) B) (.classMem (syn_cop (.cv x) (.cv y)) A)))) p0000 p0005
  exact p0006

noncomputable def g_rneq
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_crn A) (syn_crn B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_imaeq1 A B (syn_cvv)
  have p0001 :=
    (by simpa [syn_crn] using (Nominal.classEqRefl (syn_crn A)))
  have p0002 :=
    (by simpa [syn_crn] using (Nominal.classEqRefl (syn_crn B)))
  have p0003 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cima A (syn_cvv)) (syn_cima B (syn_cvv)) (syn_crn A) (syn_crn B) p0000 p0001 p0002
  exact p0003

noncomputable def g_rneqi
    (A : Class) (B : Class) (hyp_rneqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_crn A) (syn_crn B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_rneq A B
  have p0001 :=
    Nominal.mp hyp_rneqi_1 p0000
  exact p0001

noncomputable def g_rneqd
    (ph : Wff) (A : Class) (B : Class) (hyp_rneqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_crn A) (syn_crn B))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_rneq A B
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_crn A) (syn_crn B)) hyp_rneqd_1 p0000
  exact p0001

noncomputable def g_rnss
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wss A B) (syn_wss (syn_crn A) (syn_crn B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_cnvss A B
  have p0001 :=
    @g_dmss (syn_ccnv A) (syn_ccnv B)
  have p0002 :=
    @g_syl (syn_wss A B) (syn_wss (syn_ccnv A) (syn_ccnv B)) (syn_wss (syn_cdm (syn_ccnv A)) (syn_cdm (syn_ccnv B))) p0000 p0001
  have p0003 :=
    @g_dfrn4 A
  have p0004 :=
    @g_dfrn4 B
  have p0005 :=
    @g_n_3sstr4g (syn_wss A B) (syn_cdm (syn_ccnv A)) (syn_cdm (syn_ccnv B)) (syn_crn A) (syn_crn B) p0002 p0003 p0004
  exact p0005

noncomputable def g_brelrn
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wbr A C B) (.classMem B (syn_crn C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_breldm B A (syn_ccnv C)
  have p0001 :=
    @g_brcnv B A C
  have p0002 :=
    @g_bicomi (syn_wbr B (syn_ccnv C) A) (syn_wbr A C B) p0001
  have p0003 :=
    @g_dfrn4 C
  have p0004 :=
    @g_eleq2i (syn_crn C) (syn_cdm (syn_ccnv C)) B p0003
  have p0005 :=
    @g_n_3imtr4i (syn_wbr B (syn_ccnv C) A) (.classMem B (syn_cdm (syn_ccnv C))) (syn_wbr A C B) (.classMem B (syn_crn C)) p0000 p0002 p0004
  exact p0005

noncomputable def g_opelrn
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classMem (syn_cop A B) C) (.classMem B (syn_crn C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr A C B)))
  have p0001 :=
    @g_brelrn A B C
  have p0002 :=
    @g_sylbir (.classMem (syn_cop A B) C) (syn_wbr A C B) (.classMem B (syn_crn C)) p0000 p0001
  exact p0002

noncomputable def g_dfrnf
    (x : Var) (y : Var) (A : Class) (dv_x_y : x ≠ y) (hyp_dfrnf_1 : Nominal.NPrf (syn_wnfc x A)) (hyp_dfrnf_2 : Nominal.NPrf (syn_wnfc y A)) :
    Nominal.NPrf (.classEq (syn_crn A) (.cab y (syn_wex x (syn_wbr (.cv x) A (.cv y))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv
  let v : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  have fresh_v : v ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
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
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
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
  have fresh_v_ne_w : v ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_w_ne_v : w ≠ v :=
    Ne.symm fresh_v_ne_w
  have dv_cache_0001 : v ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : w ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : v ≠ w := by
    clear dv_cache_0001 dv_cache_0002
    exact (show v ≠ w from (by exact fresh_v_ne_w))
  have dv_cache_0004 : x ∉ ((Class.cv v)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Class.cv w)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : v ∉ ((syn_wbr (.cv x) A (.cv w))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_x, fresh_v_ne_w, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_y), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((Class.cv w)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : w ∉ ((syn_wex x (syn_wbr (.cv x) A (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, fresh_w_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ ((Wff.classEq (.cv w) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_w, dv_x_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_dfrn2 v w A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_nfcv x (.cv v) dv_cache_0004
  have p0002 :=
    @g_nfcv x (.cv w) dv_cache_0005
  have p0003 :=
    @g_nfbr x (.cv v) (.cv w) A p0001 hyp_dfrnf_1 p0002
  have p0004 :=
    @g_nfv (syn_wbr (.cv x) A (.cv w)) v dv_cache_0006
  have p0005 :=
    @g_breq1 (.cv v) (.cv x) (.cv w) A
  have p0006_e02_recanon : Nominal.NPrf (.imp (.objEq v x) (syn_wb (syn_wbr (.cv v) A (.cv w)) (syn_wbr (.cv x) A (.cv w)))) :=
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
    @g_cbvex (syn_wbr (.cv v) A (.cv w)) (syn_wbr (.cv x) A (.cv w)) v x p0003 p0004 p0006_e02_recanon
  have p0007 :=
    @g_abbii (syn_wex v (syn_wbr (.cv v) A (.cv w))) (syn_wex x (syn_wbr (.cv x) A (.cv w))) w p0006
  have p0008 :=
    @g_nfcv y (.cv x) dv_cache_0007
  have p0009 :=
    @g_nfcv y (.cv w) dv_cache_0008
  have p0010 :=
    @g_nfbr y (.cv x) (.cv w) A p0008 hyp_dfrnf_2 p0009
  have p0011 :=
    @g_nfex (syn_wbr (.cv x) A (.cv w)) y x p0010
  have p0012 :=
    @g_nfv (syn_wex x (syn_wbr (.cv x) A (.cv y))) w dv_cache_0009
  have p0013 :=
    @g_breq2 (.cv w) (.cv y) (.cv x) A
  have p0014 :=
    @g_exbidv (.classEq (.cv w) (.cv y)) (syn_wbr (.cv x) A (.cv w)) (syn_wbr (.cv x) A (.cv y)) x dv_cache_0010 p0013
  have p0015_e02_recanon : Nominal.NPrf (.imp (.objEq w y) (syn_wb (syn_wex x (syn_wbr (.cv x) A (.cv w))) (syn_wex x (syn_wbr (.cv x) A (.cv y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0014
  have p0015 :=
    @g_cbvab (syn_wex x (syn_wbr (.cv x) A (.cv w))) (syn_wex x (syn_wbr (.cv x) A (.cv y))) w y p0011 p0012 p0015_e02_recanon
  have p0016 :=
    @g_n_3eqtri (syn_crn A) (.cab w (syn_wex v (syn_wbr (.cv v) A (.cv w)))) (.cab w (syn_wex x (syn_wbr (.cv x) A (.cv w)))) (.cab y (syn_wex x (syn_wbr (.cv x) A (.cv y)))) p0000 p0007 p0015
  exact p0016

noncomputable def g_rnopab
    (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classEq (syn_crn (syn_copab x y ph)) (.cab y (syn_wex x ph))) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var)
  have dv_cache_0001 : x ≠ y := by
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @g_nfopab1 ph x y
  have p0001 :=
    @g_nfopab2 ph x y
  have p0002 :=
    @g_dfrnf x y (syn_copab x y ph) dv_cache_0001 p0000 p0001
  have p0003 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) (syn_copab x y ph) (.cv y))))
  have p0004 :=
    @g_opabid ph x y
  have p0005 :=
    @g_bitri (syn_wbr (.cv x) (syn_copab x y ph) (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) (syn_copab x y ph)) ph p0003 p0004
  have p0006 :=
    @g_exbii (syn_wbr (.cv x) (syn_copab x y ph) (.cv y)) ph x p0005
  have p0007 :=
    @g_abbii (syn_wex x (syn_wbr (.cv x) (syn_copab x y ph) (.cv y))) (syn_wex x ph) y p0006
  have p0008 :=
    @g_eqtri (syn_crn (syn_copab x y ph)) (.cab y (syn_wex x (syn_wbr (.cv x) (syn_copab x y ph) (.cv y)))) (.cab y (syn_wex x ph)) p0002 p0007
  exact p0008

noncomputable def g_rnopab2
    (x : Var) (y : Var) (A : Class) (B : Class) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classEq (syn_crn (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B)))) (.cab y (syn_wrex x A (.classEq (.cv y) B)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv
  have dv_cache_0001 : x ≠ y := by
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @g_rnopab (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B)) x y dv_cache_0001
  have p0001 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex x A (.classEq (.cv y) B))))
  have p0002 :=
    @g_abbii (syn_wrex x A (.classEq (.cv y) B)) (syn_wex x (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) y p0001
  have p0003 :=
    @g_eqtr4i (syn_crn (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B)))) (.cab y (syn_wex x (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B)))) (.cab y (syn_wrex x A (.classEq (.cv y) B))) p0000 p0002
  exact p0003

noncomputable def g_rn0
     :
    Nominal.NPrf (.classEq (syn_crn (syn_c0)) (syn_c0)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_dm0
  have p0001 :=
    @g_dm0rn0 (syn_c0)
  have p0002 :=
    @g_mpbi (.classEq (syn_cdm (syn_c0)) (syn_c0)) (.classEq (syn_crn (syn_c0)) (syn_c0)) p0000 p0001
  exact p0002

#print axioms g_rn0

end NFChoice.DirectNominalPrf.WPPReplay
