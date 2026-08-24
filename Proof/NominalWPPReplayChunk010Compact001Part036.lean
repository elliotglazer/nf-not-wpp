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
import NominalWPPReplayChunk010Compact001Part035

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

noncomputable def g_phiun
    (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cphi (syn_cun A B)) (syn_cun (syn_cphi A) (syn_cphi B))) := by
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
  have dv_cache_0001 : y ∉ ((syn_cun A B)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cun A B)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ≠ x := by
    clear dv_cache_0001 dv_cache_0002
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have dv_cache_0004 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_rexun (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) y A B
  have p0001 :=
    @g_abbii (syn_wrex y (syn_cun A B) (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) (syn_wo (syn_wrex y A (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) (syn_wrex y B (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))))) x p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_phi y x (syn_cun A B) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_phi y x A dv_cache_0004 dv_cache_0005 dv_cache_0003
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_phi y x B dv_cache_0006 dv_cache_0007 dv_cache_0003
  have p0005 :=
    @g_uneq12i (syn_cphi A) (.cab x (syn_wrex y A (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))))) (syn_cphi B) (.cab x (syn_wrex y B (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))))) p0003 p0004
  have p0006 :=
    @g_unab (syn_wrex y A (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) (syn_wrex y B (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) x
  have p0007 :=
    @g_eqtri (syn_cun (syn_cphi A) (syn_cphi B)) (syn_cun (.cab x (syn_wrex y A (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))))) (.cab x (syn_wrex y B (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))))) (.cab x (syn_wo (syn_wrex y A (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) (syn_wrex y B (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))))) p0005 p0006
  have p0008 :=
    @g_n_3eqtr4i (.cab x (syn_wrex y (syn_cun A B) (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))))) (.cab x (syn_wo (syn_wrex y A (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) (syn_wrex y B (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))))) (syn_cphi (syn_cun A B)) (syn_cun (syn_cphi A) (syn_cphi B)) p0001 p0002 p0007
  exact p0008

noncomputable def g_phidisjnn
    (A : Class) :
    Nominal.NPrf (.imp (.classEq (syn_cin A (syn_cnnc)) (syn_c0)) (.classEq (syn_cphi A) A)) := by
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
  have dv_cache_0002 : y ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Wff.classEq (syn_cin A (syn_cnnc)) (syn_c0))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classEq (syn_cin A (syn_cnnc)) (syn_c0))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have p0000 :=
    @g_disj y A (syn_cnnc) dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_biimpi (.classEq (syn_cin A (syn_cnnc)) (syn_c0)) (syn_wral y A (.neg (.classMem (.cv y) (syn_cnnc)))) p0000
  have p0002 :=
    @g_r19_21bi (.classEq (syn_cin A (syn_cnnc)) (syn_c0)) (.neg (.classMem (.cv y) (syn_cnnc))) y A p0001
  have p0003 :=
    @g_iffalse (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)
  have p0004 :=
    @g_syl (syn_wa (.classEq (syn_cin A (syn_cnnc)) (syn_c0)) (.classMem (.cv y) A)) (.neg (.classMem (.cv y) (syn_cnnc))) (.classEq (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)) (.cv y)) p0002 p0003
  have p0005 :=
    @g_eqeq2d (syn_wa (.classEq (syn_cin A (syn_cnnc)) (syn_c0)) (.classMem (.cv y) A)) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)) (.cv y) (.cv x) p0004
  have p0006 :=
    @g_equcom y x
  have p0007_e00_recanon : Nominal.NPrf (.imp (syn_wa (.classEq (syn_cin A (syn_cnnc)) (syn_c0)) (.classMem (.cv y) A)) (syn_wb (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.objEq x y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cin syn_ccompl syn_cnin syn_wnan syn_cnnc syn_cint syn_c0 syn_cdif syn_cvv syn_wb syn_cif syn_wo syn_cplc syn_wrex syn_wex syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0005
  have p0007 :=
    @g_syl6bbr (syn_wa (.classEq (syn_cin A (syn_cnnc)) (syn_c0)) (.classMem (.cv y) A)) (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.objEq x y) (.objEq y x) p0007_e00_recanon p0006
  have p0008 :=
    @g_rexbidva (.classEq (syn_cin A (syn_cnnc)) (syn_c0)) (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (.objEq y x) y A dv_cache_0003 p0007
  have p0009 :=
    @g_risset y (.cv x) A dv_cache_0004 dv_cache_0001
  have p0010_e01_recanon : Nominal.NPrf (syn_wb (.classMem (.cv x) A) (syn_wrex y A (.objEq y x))) :=
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
      p0009
  have p0010 :=
    @g_syl6bbr (.classEq (syn_cin A (syn_cnnc)) (syn_c0)) (syn_wrex y A (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) (syn_wrex y A (.objEq y x)) (.classMem (.cv x) A) p0008 p0010_e01_recanon
  have p0011 :=
    @g_alrimiv (.classEq (syn_cin A (syn_cnnc)) (syn_c0)) (syn_wb (syn_wrex y A (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) (.classMem (.cv x) A)) x dv_cache_0005 p0010
  have p0012 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_phi y x A dv_cache_0001 dv_cache_0006 dv_cache_0007
  have p0013 :=
    @g_eqeq1i (syn_cphi A) (.cab x (syn_wrex y A (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))))) A p0012
  have p0014 :=
    @g_eqabcb (syn_wrex y A (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) x A dv_cache_0006
  have p0015 :=
    @g_bitri (.classEq (syn_cphi A) A) (.classEq (.cab x (syn_wrex y A (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))))) A) (.all x (syn_wb (syn_wrex y A (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) (.classMem (.cv x) A))) p0013 p0014
  have p0016 :=
    @g_sylibr (.classEq (syn_cin A (syn_cnnc)) (syn_c0)) (.all x (syn_wb (syn_wrex y A (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))) (.classMem (.cv x) A))) (.classEq (syn_cphi A) A) p0011 p0015
  exact p0016

#print axioms g_phidisjnn

end NFChoice.DirectNominalPrf.WPPReplay
