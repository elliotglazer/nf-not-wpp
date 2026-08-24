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
import NominalWPPReplayChunk010Compact001Part011

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

noncomputable def g_srelkex
     :
    Nominal.NPrf (.classMem (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_nncex
  have p0001 :=
    @g_nncex
  have p0002 :=
    @g_xpkex (syn_cnnc) (syn_cnnc) p0000 p0001
  have p0003 :=
    @g_n_1cex
  have p0004 :=
    @g_pwex (syn_c1c) p0003
  have p0005 :=
    @g_vvex
  have p0006 :=
    @g_xpkex (syn_cpw (syn_c1c)) (syn_cvv) p0004 p0005
  have p0007 :=
    @g_ssetkex
  have p0008 :=
    @g_ins3kex (syn_cssetk) p0007
  have p0009 :=
    @g_ssetkex
  have p0010 :=
    @g_sikex (syn_cssetk) p0009
  have p0011 :=
    @g_ins2kex (syn_csik (syn_cssetk)) p0010
  have p0012 :=
    @g_symdifex (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))) p0008 p0011
  have p0013 :=
    @g_n_1cex
  have p0014 :=
    @g_pw1ex (syn_c1c) p0013
  have p0015 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0014
  have p0016 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0015
  have p0017 :=
    @g_imakex (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0012 p0016
  have p0018 :=
    @g_difex (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0006 p0017
  have p0019 :=
    @g_sikex (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0018
  have p0020 :=
    @g_ins3kex (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) p0019
  have p0021 :=
    @g_ssetkex
  have p0022 :=
    @g_ins2kex (syn_cssetk) p0021
  have p0023 :=
    @g_inex (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)) p0020 p0022
  have p0024 :=
    @g_imakex (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))) p0023 p0015
  have p0025 :=
    @g_ins3kex (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0024
  have p0026 :=
    @g_imakex (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))) p0012 p0015
  have p0027 :=
    @g_complex (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0026
  have p0028 :=
    @g_sikex (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0027
  have p0029 :=
    @g_ins3kex (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0028
  have p0030 :=
    @g_inex (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)) p0029 p0022
  have p0031 :=
    @g_imakex (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))) p0030 p0015
  have p0032 :=
    @g_ins2kex (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0031
  have p0033 :=
    @g_inex (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0025 p0032
  have p0034 :=
    @g_imakex (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0033 p0016
  have p0035 :=
    @g_inex (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0002 p0034
  exact p0035

noncomputable def g_sfineq1
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wsfin A C) (syn_wsfin B C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ ((Wff.classEq A B)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eleq1 A B (syn_cnnc)
  have p0001 :=
    @g_eleq2 A B (syn_cpw1 (.cv y))
  have p0002 :=
    @g_anbi1d (.classEq A B) (.classMem (syn_cpw1 (.cv y)) A) (.classMem (syn_cpw1 (.cv y)) B) (.classMem (syn_cpw (.cv y)) C) p0001
  have p0003 :=
    @g_exbidv (.classEq A B) (syn_wa (.classMem (syn_cpw1 (.cv y)) A) (.classMem (syn_cpw (.cv y)) C)) (syn_wa (.classMem (syn_cpw1 (.cv y)) B) (.classMem (syn_cpw (.cv y)) C)) y dv_cache_0001 p0002
  have p0004 :=
    @g_n_3anbi13d (.classEq A B) (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (syn_wex y (syn_wa (.classMem (syn_cpw1 (.cv y)) A) (.classMem (syn_cpw (.cv y)) C))) (syn_wex y (syn_wa (.classMem (syn_cpw1 (.cv y)) B) (.classMem (syn_cpw (.cv y)) C))) (.classMem C (syn_cnnc)) p0000 p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin A C y dv_cache_0002 dv_cache_0003
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin B C y dv_cache_0004 dv_cache_0003
  have p0007 :=
    @g_n_3bitr4g (.classEq A B) (syn_w3a (.classMem A (syn_cnnc)) (.classMem C (syn_cnnc)) (syn_wex y (syn_wa (.classMem (syn_cpw1 (.cv y)) A) (.classMem (syn_cpw (.cv y)) C)))) (syn_w3a (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc)) (syn_wex y (syn_wa (.classMem (syn_cpw1 (.cv y)) B) (.classMem (syn_cpw (.cv y)) C)))) (syn_wsfin A C) (syn_wsfin B C) p0004 p0005 p0006
  exact p0007

noncomputable def g_sfineq2
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wsfin C A) (syn_wsfin C B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ ((Wff.classEq A B)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (C).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
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
  have p0000 :=
    @g_eleq1 A B (syn_cnnc)
  have p0001 :=
    @g_eleq2 A B (syn_cpw (.cv y))
  have p0002 :=
    @g_anbi2d (.classEq A B) (.classMem (syn_cpw (.cv y)) A) (.classMem (syn_cpw (.cv y)) B) (.classMem (syn_cpw1 (.cv y)) C) p0001
  have p0003 :=
    @g_exbidv (.classEq A B) (syn_wa (.classMem (syn_cpw1 (.cv y)) C) (.classMem (syn_cpw (.cv y)) A)) (syn_wa (.classMem (syn_cpw1 (.cv y)) C) (.classMem (syn_cpw (.cv y)) B)) y dv_cache_0001 p0002
  have p0004 :=
    @g_n_3anbi23d (.classEq A B) (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (syn_wex y (syn_wa (.classMem (syn_cpw1 (.cv y)) C) (.classMem (syn_cpw (.cv y)) A))) (syn_wex y (syn_wa (.classMem (syn_cpw1 (.cv y)) C) (.classMem (syn_cpw (.cv y)) B))) (.classMem C (syn_cnnc)) p0000 p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin C A y dv_cache_0002 dv_cache_0003
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin C B y dv_cache_0002 dv_cache_0004
  have p0007 :=
    @g_n_3bitr4g (.classEq A B) (syn_w3a (.classMem C (syn_cnnc)) (.classMem A (syn_cnnc)) (syn_wex y (syn_wa (.classMem (syn_cpw1 (.cv y)) C) (.classMem (syn_cpw (.cv y)) A)))) (syn_w3a (.classMem C (syn_cnnc)) (.classMem B (syn_cnnc)) (syn_wex y (syn_wa (.classMem (syn_cpw1 (.cv y)) C) (.classMem (syn_cpw (.cv y)) B)))) (syn_wsfin C A) (syn_wsfin C B) p0004 p0005 p0006
  exact p0007

noncomputable def g_sfin01
     :
    Nominal.NPrf (syn_wsfin (syn_c0c) (syn_c1c)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let a : Var := freshVar proofSupport 0
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have dv_cache_0001 : a ∉ ((syn_c0)).fv := by
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : a ∉ ((syn_wa (.classEq (syn_cpw1 (syn_c0)) (syn_c0)) (.classMem (syn_csn (syn_c0)) (syn_c1c)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : a ∉ ((syn_c0c)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : a ∉ ((syn_c1c)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_peano1
  have p0001 :=
    @g_n_1cnnc
  have p0002 :=
    @g_pw10
  have p0003 :=
    @g_n_0ex
  have p0004 :=
    @g_snel1c (syn_c0) p0003
  have p0005 :=
    @g_n_0ex
  have p0006 :=
    @g_el0c (syn_cpw1 (.cv a))
  have p0007 :=
    @g_pw1eq (.cv a) (syn_c0)
  have p0008 :=
    @g_eqeq1d (.classEq (.cv a) (syn_c0)) (syn_cpw1 (.cv a)) (syn_cpw1 (syn_c0)) (syn_c0) p0007
  have p0009 :=
    @g_syl5bb (.classMem (syn_cpw1 (.cv a)) (syn_c0c)) (.classEq (syn_cpw1 (.cv a)) (syn_c0)) (.classEq (.cv a) (syn_c0)) (.classEq (syn_cpw1 (syn_c0)) (syn_c0)) p0006 p0008
  have p0010 :=
    @g_pweq (.cv a) (syn_c0)
  have p0011 :=
    @g_pw0
  have p0012 :=
    @g_syl6eq (.classEq (.cv a) (syn_c0)) (syn_cpw (.cv a)) (syn_cpw (syn_c0)) (syn_csn (syn_c0)) p0010 p0011
  have p0013 :=
    @g_eleq1d (.classEq (.cv a) (syn_c0)) (syn_cpw (.cv a)) (syn_csn (syn_c0)) (syn_c1c) p0012
  have p0014 :=
    @g_anbi12d (.classEq (.cv a) (syn_c0)) (.classMem (syn_cpw1 (.cv a)) (syn_c0c)) (.classEq (syn_cpw1 (syn_c0)) (syn_c0)) (.classMem (syn_cpw (.cv a)) (syn_c1c)) (.classMem (syn_csn (syn_c0)) (syn_c1c)) p0009 p0013
  have p0015 :=
    @g_spcev (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_c0c)) (.classMem (syn_cpw (.cv a)) (syn_c1c))) (syn_wa (.classEq (syn_cpw1 (syn_c0)) (syn_c0)) (.classMem (syn_csn (syn_c0)) (syn_c1c))) a (syn_c0) dv_cache_0001 dv_cache_0002 p0005 p0014
  have p0016 :=
    @g_mp2an (.classEq (syn_cpw1 (syn_c0)) (syn_c0)) (.classMem (syn_csn (syn_c0)) (syn_c1c)) (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_c0c)) (.classMem (syn_cpw (.cv a)) (syn_c1c)))) p0002 p0004 p0015
  have p0017 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin (syn_c0c) (syn_c1c) a dv_cache_0003 dv_cache_0004
  have p0018 :=
    @g_mpbir3an (syn_wsfin (syn_c0c) (syn_c1c)) (.classMem (syn_c0c) (syn_cnnc)) (.classMem (syn_c1c) (syn_cnnc)) (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_c0c)) (.classMem (syn_cpw (.cv a)) (syn_c1c)))) p0000 p0001 p0016 p0017
  exact p0018

noncomputable def g_sfin112
    (P : Class) (M : Class) (N : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wsfin M N) (syn_wsfin M P)) (.classEq N P)) := by
  let proofSupport : Finset Var := P.fv ∪ M.fv ∪ N.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let n : Var := freshVar proofSupport 2
  let k : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_P : x ∉ P.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_M : x ∉ M.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_N : x ∉ N.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_P : y ∉ P.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_M : y ∉ M.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_N : y ∉ N.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_n_not_P : n ∉ P.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_n_not_M : n ∉ M.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_not_N : n ∉ N.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have fresh_k : k ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_k_not_P : k ∉ P.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_k_not_M : k ∉ M.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_k_not_N : k ∉ N.fv := by
    intro h
    exact fresh_k (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_n : x ≠ n := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_n_ne_x : n ≠ x :=
    Ne.symm fresh_x_ne_n
  have fresh_x_ne_k : x ≠ k := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_k_ne_x : k ≠ x :=
    Ne.symm fresh_x_ne_k
  have fresh_y_ne_n : y ≠ n := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_n_ne_y : n ≠ y :=
    Ne.symm fresh_y_ne_n
  have fresh_y_ne_k : y ≠ k := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_k_ne_y : k ≠ y :=
    Ne.symm fresh_y_ne_k
  have fresh_n_ne_k : n ≠ k := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_k_ne_n : k ≠ n :=
    Ne.symm fresh_n_ne_k
  have dv_cache_0001 : y ∉ ((syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N))).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_M, fresh_y_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, fresh_x_not_M, fresh_x_not_P, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (M).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (N).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ (M).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ (P).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_P, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : n ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : n ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : k ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : k ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : k ∉ ((Class.cv n)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : k ∉ ((Wff.classEq N P)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_N, fresh_k_not_P, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : k ∉ ((syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc))) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))) (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_M, fresh_k_not_N, fresh_k_not_P, fresh_k_ne_x, fresh_k_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : n ∉ ((Wff.classEq N P)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_N, fresh_n_not_P, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : n ∉ ((syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc))) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))) (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_M, fresh_n_not_N, fresh_n_not_P, fresh_n_ne_x, fresh_n_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : x ∉ ((Wff.classEq N P)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_N, fresh_x_not_P, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : y ∉ ((Wff.classEq N P)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_N, fresh_y_not_P, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : x ∉ ((syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc))) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_M, fresh_x_not_N, fresh_x_not_P, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : y ∉ ((syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc))) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_M, fresh_y_not_N, fresh_y_not_P, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_n_3an6 (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)) (syn_wex x (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N))) (syn_wex y (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)))
  have p0001 :=
    @g_eeanv (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)) x y dv_cache_0001 dv_cache_0002
  have p0002 :=
    @g_n_3anbi3i (syn_wex x (syn_wex y (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P))))) (syn_wa (syn_wex x (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N))) (syn_wex y (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)))) (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc))) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))) p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin M N x dv_cache_0003 dv_cache_0004
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin M P y dv_cache_0005 dv_cache_0006
  have p0005 :=
    @g_anbi12i (syn_wsfin M N) (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wex x (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N)))) (syn_wsfin M P) (syn_w3a (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)) (syn_wex y (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)))) p0003 p0004
  have p0006 :=
    @g_n_3bitr4ri (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc))) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))) (syn_wa (syn_wex x (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N))) (syn_wex y (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P))))) (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wex x (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N)))) (syn_w3a (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)) (syn_wex y (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P))))) (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc))) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))) (syn_wex x (syn_wex y (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)))))) (syn_wa (syn_wsfin M N) (syn_wsfin M P)) p0000 p0002 p0005
  have p0007 :=
    @g_simpllr (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc)) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))) (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)))
  have p0008 :=
    @g_simprll (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc))) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))) (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P))
  have p0009 :=
    @g_simprrl (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc))) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))) (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N)) (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)
  have p0010 :=
    @g_ncfinlower (.cv x) (.cv y) n M dv_cache_0007 dv_cache_0008
  have p0011_e03_recanon : Nominal.NPrf (.imp (syn_w3a (.classMem M (syn_cnnc)) (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw1 (.cv y)) M)) (syn_wrex n (syn_cnnc) (syn_wa (.objMem x n) (.objMem y n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_cnnc syn_cint syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_cpw syn_wss syn_c1c syn_wex syn_csn syn_wrex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
      )
      p0010
  have p0011 :=
    @g_syl3anc (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc))) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))) (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)))) (.classMem M (syn_cnnc)) (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw1 (.cv y)) M) (syn_wrex n (syn_cnnc) (syn_wa (.objMem x n) (.objMem y n))) p0007 p0008 p0009 p0011_e03_recanon
  have p0012 :=
    @g_nnpweq (.cv x) (.cv y) k (.cv n) dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0013_e00_recanon : Nominal.NPrf (.imp (syn_w3a (.classMem (.cv n) (syn_cnnc)) (.objMem x n) (.objMem y n)) (syn_wrex k (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv x)) (.cv k)) (.classMem (syn_cpw (.cv y)) (.cv k))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_cnnc syn_cint syn_wrex syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0012
  have p0013 :=
    @g_n_3expb (.classMem (.cv n) (syn_cnnc)) (.objMem x n) (.objMem y n) (syn_wrex k (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv x)) (.cv k)) (.classMem (syn_cpw (.cv y)) (.cv k)))) p0013_e00_recanon
  have p0014 :=
    @g_simp1rl (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)) (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc))) (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv x)) (.cv k)) (.classMem (syn_cpw (.cv y)) (.cv k))))
  have p0015 :=
    @g_simp3l (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc))) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))) (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P))) (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv x)) (.cv k)) (.classMem (syn_cpw (.cv y)) (.cv k)))
  have p0016 :=
    @g_simp2lr (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)) (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc))) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv x)) (.cv k)) (.classMem (syn_cpw (.cv y)) (.cv k))))
  have p0017 :=
    @g_simp3rl (.classMem (syn_cpw (.cv x)) (.cv k)) (.classMem (syn_cpw (.cv y)) (.cv k)) (.classMem (.cv k) (syn_cnnc)) (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc))) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))) (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)))
  have p0018 :=
    @g_nnceleq (syn_cpw (.cv x)) N (.cv k)
  have p0019 :=
    @g_syl22anc (syn_w3a (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc))) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))) (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv x)) (.cv k)) (.classMem (syn_cpw (.cv y)) (.cv k))))) (.classMem N (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)) (.classMem (syn_cpw (.cv x)) N) (.classMem (syn_cpw (.cv x)) (.cv k)) (.classEq N (.cv k)) p0014 p0015 p0016 p0017 p0018
  have p0020 :=
    @g_simp1rr (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)) (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc))) (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv x)) (.cv k)) (.classMem (syn_cpw (.cv y)) (.cv k))))
  have p0021 :=
    @g_simp2rr (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P) (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N)) (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc))) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv x)) (.cv k)) (.classMem (syn_cpw (.cv y)) (.cv k))))
  have p0022 :=
    @g_simp3rr (.classMem (syn_cpw (.cv x)) (.cv k)) (.classMem (syn_cpw (.cv y)) (.cv k)) (.classMem (.cv k) (syn_cnnc)) (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc))) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))) (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)))
  have p0023 :=
    @g_nnceleq (syn_cpw (.cv y)) P (.cv k)
  have p0024 :=
    @g_syl22anc (syn_w3a (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc))) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))) (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv x)) (.cv k)) (.classMem (syn_cpw (.cv y)) (.cv k))))) (.classMem P (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)) (.classMem (syn_cpw (.cv y)) P) (.classMem (syn_cpw (.cv y)) (.cv k)) (.classEq P (.cv k)) p0020 p0015 p0021 p0022 p0023
  have p0025 :=
    @g_eqtr4d (syn_w3a (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc))) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))) (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv x)) (.cv k)) (.classMem (syn_cpw (.cv y)) (.cv k))))) N (.cv k) P p0019 p0024
  have p0026 :=
    @g_n_3expa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc))) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))) (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv x)) (.cv k)) (.classMem (syn_cpw (.cv y)) (.cv k)))) (.classEq N P) p0025
  have p0027 :=
    @g_expr (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc))) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))) (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)))) (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv x)) (.cv k)) (.classMem (syn_cpw (.cv y)) (.cv k))) (.classEq N P) p0026
  have p0028 :=
    @g_rexlimdva (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc))) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))) (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)))) (syn_wa (.classMem (syn_cpw (.cv x)) (.cv k)) (.classMem (syn_cpw (.cv y)) (.cv k))) (.classEq N P) k (syn_cnnc) dv_cache_0012 dv_cache_0013 p0027
  have p0029 :=
    @g_syl5 (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.objMem x n) (.objMem y n))) (syn_wrex k (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv x)) (.cv k)) (.classMem (syn_cpw (.cv y)) (.cv k)))) (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc))) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))) (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)))) (.classEq N P) p0013 p0028
  have p0030 :=
    @g_exp3a (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc))) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))) (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)))) (.classMem (.cv n) (syn_cnnc)) (syn_wa (.objMem x n) (.objMem y n)) (.classEq N P) p0029
  have p0031 :=
    @g_rexlimdv (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc))) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))) (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)))) (syn_wa (.objMem x n) (.objMem y n)) (.classEq N P) n (syn_cnnc) dv_cache_0014 dv_cache_0015 p0030
  have p0032 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc))) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))) (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)))) (syn_wrex n (syn_cnnc) (syn_wa (.objMem x n) (.objMem y n))) (.classEq N P) p0011 p0031
  have p0033 :=
    @g_ex (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc))) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))) (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P))) (.classEq N P) p0032
  have p0034 :=
    @g_exlimdvv (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc))) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))) (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P))) (.classEq N P) x y dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 p0033
  have p0035 :=
    @g_n_3impia (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc))) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))) (syn_wex x (syn_wex y (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P))))) (.classEq N P) p0034
  have p0036 :=
    @g_sylbi (syn_wa (syn_wsfin M N) (syn_wsfin M P)) (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc))) (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))) (syn_wex x (syn_wex y (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N)) (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)))))) (.classEq N P) p0006 p0035
  exact p0036

#print axioms g_sfin112

end NFChoice.DirectNominalPrf.WPPReplay
