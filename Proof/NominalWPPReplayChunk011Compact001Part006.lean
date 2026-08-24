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
import NominalWPPReplayChunk011Compact001Part005

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

noncomputable def g_imadmrn
    (A : Class) :
    Nominal.NPrf (.classEq (syn_cima A (syn_cdm A)) (syn_crn A)) := by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : y ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_cdm A)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_cdm A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have dv_cache_0006 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex x (syn_cdm A) (syn_wbr (.cv x) A (.cv y)))))
  have p0001 :=
    @g_breldm (.cv x) (.cv y) A
  have p0002 :=
    @g_pm4_71ri (syn_wbr (.cv x) A (.cv y)) (.classMem (.cv x) (syn_cdm A)) p0001
  have p0003 :=
    @g_exbii (syn_wbr (.cv x) A (.cv y)) (syn_wa (.classMem (.cv x) (syn_cdm A)) (syn_wbr (.cv x) A (.cv y))) x p0002
  have p0004 :=
    @g_bitr4i (syn_wrex x (syn_cdm A) (syn_wbr (.cv x) A (.cv y))) (syn_wex x (syn_wa (.classMem (.cv x) (syn_cdm A)) (syn_wbr (.cv x) A (.cv y)))) (syn_wex x (syn_wbr (.cv x) A (.cv y))) p0000 p0003
  have p0005 :=
    @g_abbii (syn_wrex x (syn_cdm A) (syn_wbr (.cv x) A (.cv y))) (syn_wex x (syn_wbr (.cv x) A (.cv y))) y p0004
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ima y x A (syn_cdm A) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0007 :=
    @g_dfrn2 x y A dv_cache_0002 dv_cache_0001 dv_cache_0006
  have p0008 :=
    @g_n_3eqtr4i (.cab y (syn_wrex x (syn_cdm A) (syn_wbr (.cv x) A (.cv y)))) (.cab y (syn_wex x (syn_wbr (.cv x) A (.cv y)))) (syn_cima A (syn_cdm A)) (syn_crn A) p0005 p0006 p0007
  exact p0008

noncomputable def g_imassrn
    (A : Class) (B : Class) :
    Nominal.NPrf (syn_wss (syn_cima A B) (syn_crn A)) := by
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
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_simpr (.classMem (.cv x) B) (.classMem (syn_cop (.cv x) (.cv y)) A)
  have p0001 :=
    @g_eximi (syn_wa (.classMem (.cv x) B) (.classMem (syn_cop (.cv x) (.cv y)) A)) (.classMem (syn_cop (.cv x) (.cv y)) A) x p0000
  have p0002 :=
    @g_ss2abi (syn_wex x (syn_wa (.classMem (.cv x) B) (.classMem (syn_cop (.cv x) (.cv y)) A))) (syn_wex x (.classMem (syn_cop (.cv x) (.cv y)) A)) y p0001
  have p0003 :=
    @g_dfima4 x y A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0004 :=
    @g_dfrn3 x y A dv_cache_0001 dv_cache_0002 dv_cache_0005
  have p0005 :=
    @g_n_3sstr4i (.cab y (syn_wex x (syn_wa (.classMem (.cv x) B) (.classMem (syn_cop (.cv x) (.cv y)) A)))) (.cab y (syn_wex x (.classMem (syn_cop (.cv x) (.cv y)) A))) (syn_cima A B) (syn_crn A) p0002 p0003 p0004
  exact p0005

noncomputable def g_imai
    (A : Class) :
    Nominal.NPrf (.classEq (syn_cima (syn_cid) A) A) := by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ ((syn_cid)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cid)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0006 : x ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Wff.classMem (.cv y) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_dfima4 x y (syn_cid) A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) (syn_cid) (.cv y))))
  have p0002 :=
    @g_vex y
  have p0003 :=
    @g_ideq (.cv x) (.cv y) p0002
  have p0004 :=
    @g_bitr3i (.classMem (syn_cop (.cv x) (.cv y)) (syn_cid)) (syn_wbr (.cv x) (syn_cid) (.cv y)) (.classEq (.cv x) (.cv y)) p0001 p0003
  have p0005 :=
    @g_anbi2i (.classMem (syn_cop (.cv x) (.cv y)) (syn_cid)) (.classEq (.cv x) (.cv y)) (.classMem (.cv x) A) p0004
  have p0006 :=
    @g_ancom (.classMem (.cv x) A) (.classEq (.cv x) (.cv y))
  have p0007 :=
    @g_bitri (syn_wa (.classMem (.cv x) A) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cid))) (syn_wa (.classMem (.cv x) A) (.classEq (.cv x) (.cv y))) (syn_wa (.classEq (.cv x) (.cv y)) (.classMem (.cv x) A)) p0005 p0006
  have p0008 :=
    @g_exbii (syn_wa (.classMem (.cv x) A) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cid))) (syn_wa (.classEq (.cv x) (.cv y)) (.classMem (.cv x) A)) x p0007
  have p0009 :=
    @g_eleq1 (.cv x) (.cv y) A
  have p0010 :=
    @g_ceqsexv (.classMem (.cv x) A) (.classMem (.cv y) A) x (.cv y) dv_cache_0006 dv_cache_0007 p0002 p0009
  have p0011 :=
    @g_bitri (syn_wex x (syn_wa (.classMem (.cv x) A) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cid)))) (syn_wex x (syn_wa (.classEq (.cv x) (.cv y)) (.classMem (.cv x) A))) (.classMem (.cv y) A) p0008 p0010
  have p0012 :=
    @g_abbii (syn_wex x (syn_wa (.classMem (.cv x) A) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cid)))) (.classMem (.cv y) A) y p0011
  have p0013 :=
    @g_abid2 y A dv_cache_0004
  have p0014 :=
    @g_n_3eqtri (syn_cima (syn_cid) A) (.cab y (syn_wex x (syn_wa (.classMem (.cv x) A) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cid))))) (.cab y (.classMem (.cv y) A)) A p0000 p0012 p0013
  exact p0014

noncomputable def g_ima0
    (A : Class) :
    Nominal.NPrf (.classEq (syn_cima A (syn_c0)) (syn_c0)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_dfima3 A (syn_c0)
  have p0001 :=
    @g_res0 A
  have p0002 :=
    @g_rneqi (syn_cres A (syn_c0)) (syn_c0) p0001
  have p0003 :=
    @g_rn0
  have p0004 :=
    @g_n_3eqtri (syn_cima A (syn_c0)) (syn_crn (syn_cres A (syn_c0))) (syn_crn (syn_c0)) (syn_c0) p0000 p0002 p0003
  exact p0004

noncomputable def g_cnvimass
    (A : Class) (B : Class) :
    Nominal.NPrf (syn_wss (syn_cima (syn_ccnv A) B) (syn_cdm A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_imassrn (syn_ccnv A) B
  have p0001 :=
    (by simpa [syn_cdm] using (Nominal.classEqRefl (syn_cdm A)))
  have p0002 :=
    @g_sseqtr4i (syn_cima (syn_ccnv A) B) (syn_crn (syn_ccnv A)) (syn_cdm A) p0000 p0001
  exact p0002

noncomputable def g_imasn
    (y : Var) (A : Class) (R : Class) (dv_A_y : y ∉ A.fv) (dv_R_y : y ∉ R.fv) :
    Nominal.NPrf (.classEq (syn_cima R (syn_csn A)) (.cab y (syn_wbr A R (.cv y)))) := by
  let proofSupport : Finset Var := ({y} : Finset Var) ∪ A.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_y : x ≠ y := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ (R).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (R).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_csn A)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_csn A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have dv_cache_0006 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_wbr A R (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_y, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((Wff.classMem A (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ima y x R (syn_csn A) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @g_breq1 (.cv x) A (.cv y) R
  have p0002 :=
    @g_rexsng (syn_wbr (.cv x) R (.cv y)) (syn_wbr A R (.cv y)) x A (syn_cvv) dv_cache_0006 dv_cache_0007 p0001
  have p0003 :=
    @g_abbidv (.classMem A (syn_cvv)) (syn_wrex x (syn_csn A) (syn_wbr (.cv x) R (.cv y))) (syn_wbr A R (.cv y)) y dv_cache_0008 p0002
  have p0004 :=
    @g_syl5eq (.classMem A (syn_cvv)) (syn_cima R (syn_csn A)) (.cab y (syn_wrex x (syn_csn A) (syn_wbr (.cv x) R (.cv y)))) (.cab y (syn_wbr A R (.cv y))) p0000 p0003
  have p0005 :=
    @g_ima0 R
  have p0006 :=
    @g_snprc A
  have p0007 :=
    @g_biimpi (.neg (.classMem A (syn_cvv))) (.classEq (syn_csn A) (syn_c0)) p0006
  have p0008 :=
    @g_imaeq2d (.neg (.classMem A (syn_cvv))) (syn_csn A) (syn_c0) R p0007
  have p0009 :=
    @g_brex A (.cv y) R
  have p0010 :=
    @g_simpld (syn_wbr A R (.cv y)) (.classMem A (syn_cvv)) (.classMem (.cv y) (syn_cvv)) p0009
  have p0011 :=
    @g_exlimiv (syn_wbr A R (.cv y)) (.classMem A (syn_cvv)) y dv_cache_0008 p0010
  have p0012 :=
    @g_con3i (syn_wex y (syn_wbr A R (.cv y))) (.classMem A (syn_cvv)) p0011
  have p0013 :=
    @g_abn0 (syn_wbr A R (.cv y)) y
  have p0014 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (.cab y (syn_wbr A R (.cv y))) (syn_c0))))
  have p0015 :=
    @g_bitr3i (syn_wex y (syn_wbr A R (.cv y))) (syn_wne (.cab y (syn_wbr A R (.cv y))) (syn_c0)) (.neg (.classEq (.cab y (syn_wbr A R (.cv y))) (syn_c0))) p0013 p0014
  have p0016 :=
    @g_con2bii (syn_wex y (syn_wbr A R (.cv y))) (.classEq (.cab y (syn_wbr A R (.cv y))) (syn_c0)) p0015
  have p0017 :=
    @g_sylibr (.neg (.classMem A (syn_cvv))) (.neg (syn_wex y (syn_wbr A R (.cv y)))) (.classEq (.cab y (syn_wbr A R (.cv y))) (syn_c0)) p0012 p0016
  have p0018 :=
    @g_n_3eqtr4a (.neg (.classMem A (syn_cvv))) (syn_cima R (syn_c0)) (syn_c0) (syn_cima R (syn_csn A)) (.cab y (syn_wbr A R (.cv y))) p0005 p0008 p0017
  have p0019 :=
    @g_pm2_61i (.classMem A (syn_cvv)) (.classEq (syn_cima R (syn_csn A)) (.cab y (syn_wbr A R (.cv y)))) p0004 p0018
  exact p0019

noncomputable def g_elimasn
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (syn_wb (.classMem C (syn_cima A (syn_csn B))) (.classMem (syn_cop B C) A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (C).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_wbr B A C)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, fresh_x_not_C, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elex C (syn_cima A (syn_csn B))
  have p0001 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr B A C)))
  have p0002 :=
    @g_brex B C A
  have p0003 :=
    @g_simprd (syn_wbr B A C) (.classMem B (syn_cvv)) (.classMem C (syn_cvv)) p0002
  have p0004 :=
    @g_sylbir (.classMem (syn_cop B C) A) (syn_wbr B A C) (.classMem C (syn_cvv)) p0001 p0003
  have p0005 :=
    @g_breq2 (.cv x) C B A
  have p0006 :=
    @g_elabg (syn_wbr B A (.cv x)) (syn_wbr B A C) x C (syn_cvv) dv_cache_0001 dv_cache_0002 p0005
  have p0007 :=
    @g_imasn x B A dv_cache_0003 dv_cache_0004
  have p0008 :=
    @g_eleq2i (syn_cima A (syn_csn B)) (.cab x (syn_wbr B A (.cv x))) C p0007
  have p0009 :=
    @g_bicomi (syn_wbr B A C) (.classMem (syn_cop B C) A) p0001
  have p0010 :=
    @g_n_3bitr4g (.classMem C (syn_cvv)) (.classMem C (.cab x (syn_wbr B A (.cv x)))) (syn_wbr B A C) (.classMem C (syn_cima A (syn_csn B))) (.classMem (syn_cop B C) A) p0006 p0008 p0009
  have p0011 :=
    @g_pm5_21nii (.classMem C (syn_cima A (syn_csn B))) (.classMem C (syn_cvv)) (.classMem (syn_cop B C) A) p0000 p0004 p0010
  exact p0011

noncomputable def g_eliniseg
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (syn_wb (.classMem C (syn_cima (syn_ccnv A) (syn_csn B))) (syn_wbr C A B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_elimasn (syn_ccnv A) B C
  have p0001 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr B (syn_ccnv A) C)))
  have p0002 :=
    @g_brcnv B C A
  have p0003 :=
    @g_n_3bitr2i (.classMem C (syn_cima (syn_ccnv A) (syn_csn B))) (.classMem (syn_cop B C) (syn_ccnv A)) (syn_wbr B (syn_ccnv A) C) (syn_wbr C A B) p0000 p0001 p0002
  exact p0003

noncomputable def g_iniseg
    (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (.classEq (syn_cima (syn_ccnv A) (syn_csn B)) (.cab x (syn_wbr (.cv x) A B))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv
  have dv_cache_0001 : x ∉ (B).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_ccnv A)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_imasn x B (syn_ccnv A) dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_brcnv B (.cv x) A
  have p0002 :=
    @g_abbii (syn_wbr B (syn_ccnv A) (.cv x)) (syn_wbr (.cv x) A B) x p0001
  have p0003 :=
    @g_eqtri (syn_cima (syn_ccnv A) (syn_csn B)) (.cab x (syn_wbr B (syn_ccnv A) (.cv x))) (.cab x (syn_wbr (.cv x) A B)) p0000 p0002
  exact p0003

noncomputable def g_imass2
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wss A B) (syn_wss (syn_cima C A) (syn_cima C B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_ssres2 A B C
  have p0001 :=
    @g_rnss (syn_cres C A) (syn_cres C B)
  have p0002 :=
    @g_syl (syn_wss A B) (syn_wss (syn_cres C A) (syn_cres C B)) (syn_wss (syn_crn (syn_cres C A)) (syn_crn (syn_cres C B))) p0000 p0001
  have p0003 :=
    @g_dfima3 C A
  have p0004 :=
    @g_dfima3 C B
  have p0005 :=
    @g_n_3sstr4g (syn_wss A B) (syn_crn (syn_cres C A)) (syn_crn (syn_cres C B)) (syn_cima C A) (syn_cima C B) p0002 p0003 p0004
  exact p0005

noncomputable def g_ndmima
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.neg (.classMem A (syn_cdm B))) (.classEq (syn_cima B (syn_csn A)) (syn_c0))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_dfima3 B (syn_csn A)
  have p0001 :=
    @g_dmres B (syn_csn A)
  have p0002 :=
    @g_incom (syn_csn A) (syn_cdm B)
  have p0003 :=
    @g_eqtri (syn_cdm (syn_cres B (syn_csn A))) (syn_cin (syn_csn A) (syn_cdm B)) (syn_cin (syn_cdm B) (syn_csn A)) p0001 p0002
  have p0004 :=
    @g_disjsn (syn_cdm B) A
  have p0005 :=
    @g_biimpri (.classEq (syn_cin (syn_cdm B) (syn_csn A)) (syn_c0)) (.neg (.classMem A (syn_cdm B))) p0004
  have p0006 :=
    @g_syl5eq (.neg (.classMem A (syn_cdm B))) (syn_cdm (syn_cres B (syn_csn A))) (syn_cin (syn_cdm B) (syn_csn A)) (syn_c0) p0003 p0005
  have p0007 :=
    @g_dm0rn0 (syn_cres B (syn_csn A))
  have p0008 :=
    @g_sylib (.neg (.classMem A (syn_cdm B))) (.classEq (syn_cdm (syn_cres B (syn_csn A))) (syn_c0)) (.classEq (syn_crn (syn_cres B (syn_csn A))) (syn_c0)) p0006 p0007
  have p0009 :=
    @g_syl5eq (.neg (.classMem A (syn_cdm B))) (syn_cima B (syn_csn A)) (syn_crn (syn_cres B (syn_csn A))) (syn_c0) p0000 p0008
  exact p0009

noncomputable def g_cnvopab
    (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classEq (syn_ccnv (syn_copab x y ph)) (syn_copab y x ph)) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var)
  let z : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_y_ne_w : y ≠ w :=
    Ne.symm fresh_w_ne_y
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have dv_cache_0001 : x ∉ ((Class.cv z)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ≠ y := by
    clear dv_cache_0001
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0003 : y ∉ ((Class.cv w)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show y ≠ x from (by exact Ne.symm dv_x_y))
  have dv_cache_0005 : z ∉ ((syn_ccnv (syn_copab x y ph))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_ph, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : w ∉ ((syn_ccnv (syn_copab x y ph))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_ph, fresh_w_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((syn_copab y x ph)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_ph, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : w ∉ ((syn_copab y x ph)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_ph, fresh_w_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have p0000 :=
    @g_opelopabsb ph x y (.cv w) (.cv z) dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_sbccom ph x y (.cv w) (.cv z) dv_cache_0003 dv_cache_0001 dv_cache_0002
  have p0002 :=
    @g_bitri (.classMem (syn_cop (.cv w) (.cv z)) (syn_copab x y ph)) (syn_wsbc (.cv w) x (syn_wsbc (.cv z) y ph)) (syn_wsbc (.cv z) y (syn_wsbc (.cv w) x ph)) p0000 p0001
  have p0003 :=
    @g_opelcnv (.cv z) (.cv w) (syn_copab x y ph)
  have p0004 :=
    @g_opelopabsb ph y x (.cv z) (.cv w) dv_cache_0003 dv_cache_0004
  have p0005 :=
    @g_n_3bitr4i (.classMem (syn_cop (.cv w) (.cv z)) (syn_copab x y ph)) (syn_wsbc (.cv z) y (syn_wsbc (.cv w) x ph)) (.classMem (syn_cop (.cv z) (.cv w)) (syn_ccnv (syn_copab x y ph))) (.classMem (syn_cop (.cv z) (.cv w)) (syn_copab y x ph)) p0002 p0003 p0004
  have p0006 :=
    @g_eqrelriv z w (syn_ccnv (syn_copab x y ph)) (syn_copab y x ph) dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 p0005
  exact p0006

noncomputable def g_cnv0
     :
    Nominal.NPrf (.classEq (syn_ccnv (syn_c0)) (syn_c0)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ ((syn_ccnv (syn_c0))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_ccnv (syn_c0))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_c0)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_c0)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_noel (syn_cop (.cv y) (.cv x))
  have p0001 :=
    @g_opelcnv (.cv x) (.cv y) (syn_c0)
  have p0002 :=
    @g_mtbir (.classMem (syn_cop (.cv x) (.cv y)) (syn_ccnv (syn_c0))) (.classMem (syn_cop (.cv y) (.cv x)) (syn_c0)) p0000 p0001
  have p0003 :=
    @g_noel (syn_cop (.cv x) (.cv y))
  have p0004 :=
    @g_n_2false (.classMem (syn_cop (.cv x) (.cv y)) (syn_ccnv (syn_c0))) (.classMem (syn_cop (.cv x) (.cv y)) (syn_c0)) p0002 p0003
  have p0005 :=
    @g_eqrelriv x y (syn_ccnv (syn_c0)) (syn_c0) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 p0004
  exact p0005

noncomputable def g_cnvi
     :
    Nominal.NPrf (.classEq (syn_ccnv (syn_cid)) (syn_cid)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have dv_cache_0001 : x ∉ ((syn_cid)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cid)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_vex x
  have p0001 :=
    @g_ideq (.cv y) (.cv x) p0000
  have p0002 :=
    @g_equcom y x
  have p0003_e01_recanon : Nominal.NPrf (syn_wb (.classEq (.cv y) (.cv x)) (.classEq (.cv x) (.cv y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
      )
      p0002
  have p0003 :=
    @g_bitri (syn_wbr (.cv y) (syn_cid) (.cv x)) (.classEq (.cv y) (.cv x)) (.classEq (.cv x) (.cv y)) p0001 p0003_e01_recanon
  have p0004 :=
    @g_opabbii (syn_wbr (.cv y) (syn_cid) (.cv x)) (.classEq (.cv x) (.cv y)) x y p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_cnv x y (syn_cid) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_id x y dv_cache_0003
  have p0007_e02_recanon : Nominal.NPrf (.classEq (syn_cid) (syn_copab x y (.classEq (.cv x) (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cid syn_copab syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.classEq
        ·
          exact Nominal.RecanonTransportDev.TRecanonClass.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonClass.cab
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
      )
      p0006
  have p0007 :=
    @g_n_3eqtr4i (syn_copab x y (syn_wbr (.cv y) (syn_cid) (.cv x))) (syn_copab x y (.classEq (.cv x) (.cv y))) (syn_ccnv (syn_cid)) (syn_cid) p0004 p0005 p0007_e02_recanon
  exact p0007

noncomputable def g_cnvun
    (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_ccnv (syn_cun A B)) (syn_cun (syn_ccnv A) (syn_ccnv B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0004 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_cun A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((syn_cun A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_unopab (syn_wbr (.cv y) A (.cv x)) (syn_wbr (.cv y) B (.cv x)) x y
  have p0001 :=
    @g_brun (.cv y) (.cv x) A B
  have p0002 :=
    @g_opabbii (syn_wbr (.cv y) (syn_cun A B) (.cv x)) (syn_wo (syn_wbr (.cv y) A (.cv x)) (syn_wbr (.cv y) B (.cv x))) x y p0001
  have p0003 :=
    @g_eqtr4i (syn_cun (syn_copab x y (syn_wbr (.cv y) A (.cv x))) (syn_copab x y (syn_wbr (.cv y) B (.cv x)))) (syn_copab x y (syn_wo (syn_wbr (.cv y) A (.cv x)) (syn_wbr (.cv y) B (.cv x)))) (syn_copab x y (syn_wbr (.cv y) (syn_cun A B) (.cv x))) p0000 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_cnv x y A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_cnv x y B dv_cache_0004 dv_cache_0005 dv_cache_0003
  have p0006 :=
    @g_uneq12i (syn_ccnv A) (syn_copab x y (syn_wbr (.cv y) A (.cv x))) (syn_ccnv B) (syn_copab x y (syn_wbr (.cv y) B (.cv x))) p0004 p0005
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_cnv x y (syn_cun A B) dv_cache_0006 dv_cache_0007 dv_cache_0003
  have p0008 :=
    @g_n_3eqtr4ri (syn_cun (syn_copab x y (syn_wbr (.cv y) A (.cv x))) (syn_copab x y (syn_wbr (.cv y) B (.cv x)))) (syn_copab x y (syn_wbr (.cv y) (syn_cun A B) (.cv x))) (syn_cun (syn_ccnv A) (syn_ccnv B)) (syn_ccnv (syn_cun A B)) p0003 p0006 p0007
  exact p0008

noncomputable def g_cnvdif
    (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_ccnv (syn_cdif A B)) (syn_cdif (syn_ccnv A) (syn_ccnv B))) := by
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
  have dv_cache_0001 : x ∉ ((syn_ccnv (syn_cdif A B))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_ccnv (syn_cdif A B))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cdif (syn_ccnv A) (syn_ccnv B))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_cdif (syn_ccnv A) (syn_ccnv B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_eldif (syn_cop (.cv y) (.cv x)) A B
  have p0001 :=
    @g_opelcnv (.cv x) (.cv y) A
  have p0002 :=
    @g_opelcnv (.cv x) (.cv y) B
  have p0003 :=
    @g_notbii (.classMem (syn_cop (.cv x) (.cv y)) (syn_ccnv B)) (.classMem (syn_cop (.cv y) (.cv x)) B) p0002
  have p0004 :=
    @g_anbi12i (.classMem (syn_cop (.cv x) (.cv y)) (syn_ccnv A)) (.classMem (syn_cop (.cv y) (.cv x)) A) (.neg (.classMem (syn_cop (.cv x) (.cv y)) (syn_ccnv B))) (.neg (.classMem (syn_cop (.cv y) (.cv x)) B)) p0001 p0003
  have p0005 :=
    @g_bitr4i (.classMem (syn_cop (.cv y) (.cv x)) (syn_cdif A B)) (syn_wa (.classMem (syn_cop (.cv y) (.cv x)) A) (.neg (.classMem (syn_cop (.cv y) (.cv x)) B))) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_ccnv A)) (.neg (.classMem (syn_cop (.cv x) (.cv y)) (syn_ccnv B)))) p0000 p0004
  have p0006 :=
    @g_opelcnv (.cv x) (.cv y) (syn_cdif A B)
  have p0007 :=
    @g_eldif (syn_cop (.cv x) (.cv y)) (syn_ccnv A) (syn_ccnv B)
  have p0008 :=
    @g_n_3bitr4i (.classMem (syn_cop (.cv y) (.cv x)) (syn_cdif A B)) (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_ccnv A)) (.neg (.classMem (syn_cop (.cv x) (.cv y)) (syn_ccnv B)))) (.classMem (syn_cop (.cv x) (.cv y)) (syn_ccnv (syn_cdif A B))) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cdif (syn_ccnv A) (syn_ccnv B))) p0005 p0006 p0007
  have p0009 :=
    @g_eqrelriv x y (syn_ccnv (syn_cdif A B)) (syn_cdif (syn_ccnv A) (syn_ccnv B)) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 p0008
  exact p0009

noncomputable def g_cnvin
    (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_ccnv (syn_cin A B)) (syn_cin (syn_ccnv A) (syn_ccnv B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_cnvdif A (syn_cdif A B)
  have p0001 :=
    @g_cnvdif A B
  have p0002 :=
    @g_difeq2i (syn_ccnv (syn_cdif A B)) (syn_cdif (syn_ccnv A) (syn_ccnv B)) (syn_ccnv A) p0001
  have p0003 :=
    @g_eqtri (syn_ccnv (syn_cdif A (syn_cdif A B))) (syn_cdif (syn_ccnv A) (syn_ccnv (syn_cdif A B))) (syn_cdif (syn_ccnv A) (syn_cdif (syn_ccnv A) (syn_ccnv B))) p0000 p0002
  have p0004 :=
    @g_dfin4 A B
  have p0005 :=
    @g_cnveqi (syn_cin A B) (syn_cdif A (syn_cdif A B)) p0004
  have p0006 :=
    @g_dfin4 (syn_ccnv A) (syn_ccnv B)
  have p0007 :=
    @g_n_3eqtr4i (syn_ccnv (syn_cdif A (syn_cdif A B))) (syn_cdif (syn_ccnv A) (syn_cdif (syn_ccnv A) (syn_ccnv B))) (syn_ccnv (syn_cin A B)) (syn_cin (syn_ccnv A) (syn_ccnv B)) p0003 p0005 p0006
  exact p0007

noncomputable def g_rnun
    (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_crn (syn_cun A B)) (syn_cun (syn_crn A) (syn_crn B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_cnvun A B
  have p0001 :=
    @g_dmeqi (syn_ccnv (syn_cun A B)) (syn_cun (syn_ccnv A) (syn_ccnv B)) p0000
  have p0002 :=
    @g_dmun (syn_ccnv A) (syn_ccnv B)
  have p0003 :=
    @g_eqtri (syn_cdm (syn_ccnv (syn_cun A B))) (syn_cdm (syn_cun (syn_ccnv A) (syn_ccnv B))) (syn_cun (syn_cdm (syn_ccnv A)) (syn_cdm (syn_ccnv B))) p0001 p0002
  have p0004 :=
    @g_dfrn4 (syn_cun A B)
  have p0005 :=
    @g_dfrn4 A
  have p0006 :=
    @g_dfrn4 B
  have p0007 :=
    @g_uneq12i (syn_crn A) (syn_cdm (syn_ccnv A)) (syn_crn B) (syn_cdm (syn_ccnv B)) p0005 p0006
  have p0008 :=
    @g_n_3eqtr4i (syn_cdm (syn_ccnv (syn_cun A B))) (syn_cun (syn_cdm (syn_ccnv A)) (syn_cdm (syn_ccnv B))) (syn_crn (syn_cun A B)) (syn_cun (syn_crn A) (syn_crn B)) p0003 p0004 p0007
  exact p0008

#print axioms g_rnun

end NFChoice.DirectNominalPrf.WPPReplay
