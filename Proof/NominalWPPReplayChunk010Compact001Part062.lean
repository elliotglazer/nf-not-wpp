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
import NominalWPPReplayChunk010Compact001Part061

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

noncomputable def g_opeliunxp
    (x : Var) (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (syn_wb (.classMem (syn_cop (.cv x) C) (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B))) (syn_wa (.classMem (.cv x) A) (.classMem C B))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  let z : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z_ne_y : z ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have dv_cache_0001 : z ∉ ((syn_wa (.classMem (.cv x) A) (.classMem (.cv y) (syn_cxp (syn_csn (.cv x)) B)))).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_A, fresh_z_ne_y, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ≠ z := by
    clear dv_cache_0001
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0003 : x ∉ ((syn_csn (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0006 : z ∉ ((Wff.classEq (.cv y) (syn_cop (.cv x) C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_x, fresh_z_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_cxp (syn_csn (.cv x)) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((syn_cop (.cv x) C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((syn_wex z (syn_wa (syn_wsb z x (.classMem (.cv x) A)) (.classMem (syn_cop (.cv x) C) (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csb, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_A, fresh_y_ne_z, fresh_y_not_C, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : z ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : z ∉ ((syn_wa (.classMem (.cv x) A) (.classMem C B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_A, fresh_z_not_C, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elex (syn_cop (.cv x) C) (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B))
  have p0001 :=
    @g_opexb (.cv x) C
  have p0002 :=
    @g_simprbi (.classMem (syn_cop (.cv x) C) (syn_cvv)) (.classMem (.cv x) (syn_cvv)) (.classMem C (syn_cvv)) p0001
  have p0003 :=
    @g_syl (.classMem (syn_cop (.cv x) C) (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B))) (.classMem (syn_cop (.cv x) C) (syn_cvv)) (.classMem C (syn_cvv)) p0000 p0002
  have p0004 :=
    @g_elex C B
  have p0005 :=
    @g_adantl (.classMem C B) (.classMem C (syn_cvv)) (.classMem (.cv x) A) p0004
  have p0006 :=
    @g_vex x
  have p0007 :=
    @g_opexg (.cv x) C (syn_cvv) (syn_cvv)
  have p0008 :=
    @g_mpan (.classMem (.cv x) (syn_cvv)) (.classMem C (syn_cvv)) (.classMem (syn_cop (.cv x) C) (syn_cvv)) p0006 p0007
  have p0009 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex x A (.classMem (.cv y) (syn_cxp (syn_csn (.cv x)) B)))))
  have p0010 :=
    @g_nfv (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) (syn_cxp (syn_csn (.cv x)) B))) z dv_cache_0001
  have p0011 :=
    @g_nfs1v (.classMem (.cv x) A) x z dv_cache_0002
  have p0012 :=
    @g_nfcv x (syn_csn (.cv z)) dv_cache_0003
  have p0013 :=
    @g_nfcsb1v x (.cv z) B dv_cache_0004
  have p0014 :=
    @g_nfxp x (syn_csn (.cv z)) (syn_csb (.cv z) x B) p0012 p0013
  have p0015 :=
    @g_nfcri x y (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B)) dv_cache_0005 p0014
  have p0016 :=
    @g_nfan (syn_wsb z x (.classMem (.cv x) A)) (.classMem (.cv y) (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B))) x p0011 p0015
  have p0017 :=
    @g_sbequ12 (.classMem (.cv x) A) x z
  have p0018 :=
    @g_sneq (.cv x) (.cv z)
  have p0019 :=
    @g_csbeq1a x (.cv z) B
  have p0020_e00_recanon : Nominal.NPrf (.imp (.objEq x z) (.classEq (syn_csn (.cv x)) (syn_csn (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0018
  have p0020_e01_recanon : Nominal.NPrf (.imp (.objEq x z) (.classEq B (syn_csb (.cv z) x B))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_csb syn_wsbc
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csb, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0019
  have p0020 :=
    @g_xpeq12d (.objEq x z) (syn_csn (.cv x)) (syn_csn (.cv z)) B (syn_csb (.cv z) x B) p0020_e00_recanon p0020_e01_recanon
  have p0021 :=
    @g_eleq2d (.objEq x z) (syn_cxp (syn_csn (.cv x)) B) (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B)) (.cv y) p0020
  have p0022 :=
    @g_anbi12d (.objEq x z) (.classMem (.cv x) A) (syn_wsb z x (.classMem (.cv x) A)) (.classMem (.cv y) (syn_cxp (syn_csn (.cv x)) B)) (.classMem (.cv y) (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B))) p0017 p0021
  have p0023 :=
    @g_cbvex (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) (syn_cxp (syn_csn (.cv x)) B))) (syn_wa (syn_wsb z x (.classMem (.cv x) A)) (.classMem (.cv y) (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B)))) x z p0010 p0016 p0022
  have p0024 :=
    @g_bitri (syn_wrex x A (.classMem (.cv y) (syn_cxp (syn_csn (.cv x)) B))) (syn_wex x (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) (syn_cxp (syn_csn (.cv x)) B)))) (syn_wex z (syn_wa (syn_wsb z x (.classMem (.cv x) A)) (.classMem (.cv y) (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B))))) p0009 p0023
  have p0025 :=
    @g_eleq1 (.cv y) (syn_cop (.cv x) C) (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B))
  have p0026 :=
    @g_anbi2d (.classEq (.cv y) (syn_cop (.cv x) C)) (.classMem (.cv y) (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B))) (.classMem (syn_cop (.cv x) C) (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B))) (syn_wsb z x (.classMem (.cv x) A)) p0025
  have p0027 :=
    @g_exbidv (.classEq (.cv y) (syn_cop (.cv x) C)) (syn_wa (syn_wsb z x (.classMem (.cv x) A)) (.classMem (.cv y) (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B)))) (syn_wa (syn_wsb z x (.classMem (.cv x) A)) (.classMem (syn_cop (.cv x) C) (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B)))) z dv_cache_0006 p0026
  have p0028 :=
    @g_syl5bb (syn_wrex x A (.classMem (.cv y) (syn_cxp (syn_csn (.cv x)) B))) (syn_wex z (syn_wa (syn_wsb z x (.classMem (.cv x) A)) (.classMem (.cv y) (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B))))) (.classEq (.cv y) (syn_cop (.cv x) C)) (syn_wex z (syn_wa (syn_wsb z x (.classMem (.cv x) A)) (.classMem (syn_cop (.cv x) C) (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B))))) p0024 p0027
  have p0029 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iun x y A (syn_cxp (syn_csn (.cv x)) B) dv_cache_0007 dv_cache_0008 dv_cache_0005
  have p0030 :=
    @g_elab2g (syn_wrex x A (.classMem (.cv y) (syn_cxp (syn_csn (.cv x)) B))) (syn_wex z (syn_wa (syn_wsb z x (.classMem (.cv x) A)) (.classMem (syn_cop (.cv x) C) (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B))))) y (syn_cop (.cv x) C) (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)) (syn_cvv) dv_cache_0009 dv_cache_0010 p0028 p0029
  have p0031 :=
    @g_syl (.classMem C (syn_cvv)) (.classMem (syn_cop (.cv x) C) (syn_cvv)) (syn_wb (.classMem (syn_cop (.cv x) C) (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B))) (syn_wex z (syn_wa (syn_wsb z x (.classMem (.cv x) A)) (.classMem (syn_cop (.cv x) C) (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B)))))) p0008 p0030
  have p0032 :=
    @g_opelxp (.cv x) C (syn_csn (.cv z)) (syn_csb (.cv z) x B)
  have p0033 :=
    @g_anbi2i (.classMem (syn_cop (.cv x) C) (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B))) (syn_wa (.classMem (.cv x) (syn_csn (.cv z))) (.classMem C (syn_csb (.cv z) x B))) (syn_wsb z x (.classMem (.cv x) A)) p0032
  have p0034 :=
    @g_an12 (syn_wsb z x (.classMem (.cv x) A)) (.classMem (.cv x) (syn_csn (.cv z))) (.classMem C (syn_csb (.cv z) x B))
  have p0035 :=
    @g_elsn x (.cv z) dv_cache_0004
  have p0036 :=
    @g_equcom x z
  have p0037_e00_recanon : Nominal.NPrf (syn_wb (.classMem (.cv x) (syn_csn (.cv z))) (.objEq x z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
      p0035
  have p0037 :=
    @g_bitri (.classMem (.cv x) (syn_csn (.cv z))) (.objEq x z) (.objEq z x) p0037_e00_recanon p0036
  have p0038 :=
    @g_anbi1i (.classMem (.cv x) (syn_csn (.cv z))) (.objEq z x) (syn_wa (syn_wsb z x (.classMem (.cv x) A)) (.classMem C (syn_csb (.cv z) x B))) p0037
  have p0039 :=
    @g_n_3bitri (syn_wa (syn_wsb z x (.classMem (.cv x) A)) (.classMem (syn_cop (.cv x) C) (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B)))) (syn_wa (syn_wsb z x (.classMem (.cv x) A)) (syn_wa (.classMem (.cv x) (syn_csn (.cv z))) (.classMem C (syn_csb (.cv z) x B)))) (syn_wa (.classMem (.cv x) (syn_csn (.cv z))) (syn_wa (syn_wsb z x (.classMem (.cv x) A)) (.classMem C (syn_csb (.cv z) x B)))) (syn_wa (.objEq z x) (syn_wa (syn_wsb z x (.classMem (.cv x) A)) (.classMem C (syn_csb (.cv z) x B)))) p0033 p0034 p0038
  have p0040 :=
    @g_exbii (syn_wa (syn_wsb z x (.classMem (.cv x) A)) (.classMem (syn_cop (.cv x) C) (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B)))) (syn_wa (.objEq z x) (syn_wa (syn_wsb z x (.classMem (.cv x) A)) (.classMem C (syn_csb (.cv z) x B)))) z p0039
  have p0041 :=
    @g_sbequ12r (.classMem (.cv x) A) z x
  have p0042_e00_recanon : Nominal.NPrf (.imp (.objEq x z) (.classEq B (syn_csb (.cv z) x B))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_csb syn_wsbc
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csb, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0019
  have p0042 :=
    @g_equcoms (.classEq B (syn_csb (.cv z) x B)) x z p0042_e00_recanon
  have p0043 :=
    @g_eqcomd (.objEq z x) B (syn_csb (.cv z) x B) p0042
  have p0044 :=
    @g_eleq2d (.objEq z x) (syn_csb (.cv z) x B) B C p0043
  have p0045 :=
    @g_anbi12d (.objEq z x) (syn_wsb z x (.classMem (.cv x) A)) (.classMem (.cv x) A) (.classMem C (syn_csb (.cv z) x B)) (.classMem C B) p0041 p0044
  have p0046_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv z) (.cv x)) (syn_wb (syn_wa (syn_wsb z x (.classMem (.cv x) A)) (.classMem C (syn_csb (.cv z) x B))) (syn_wa (.classMem (.cv x) A) (.classMem C B)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wa syn_wsb syn_csb syn_wsbc
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0045
  have p0046 :=
    @g_ceqsexv (syn_wa (syn_wsb z x (.classMem (.cv x) A)) (.classMem C (syn_csb (.cv z) x B))) (syn_wa (.classMem (.cv x) A) (.classMem C B)) z (.cv x) dv_cache_0011 dv_cache_0012 p0006 p0046_e01_recanon
  have p0047_e01_recanon : Nominal.NPrf (syn_wb (syn_wex z (syn_wa (.objEq z x) (syn_wa (syn_wsb z x (.classMem (.cv x) A)) (.classMem C (syn_csb (.cv z) x B))))) (syn_wa (.classMem (.cv x) A) (.classMem C B))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csb, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
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
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0046
  have p0047 :=
    @g_bitri (syn_wex z (syn_wa (syn_wsb z x (.classMem (.cv x) A)) (.classMem (syn_cop (.cv x) C) (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B))))) (syn_wex z (syn_wa (.objEq z x) (syn_wa (syn_wsb z x (.classMem (.cv x) A)) (.classMem C (syn_csb (.cv z) x B))))) (syn_wa (.classMem (.cv x) A) (.classMem C B)) p0040 p0047_e01_recanon
  have p0048 :=
    @g_syl6bb (.classMem C (syn_cvv)) (.classMem (syn_cop (.cv x) C) (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B))) (syn_wex z (syn_wa (syn_wsb z x (.classMem (.cv x) A)) (.classMem (syn_cop (.cv x) C) (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B))))) (syn_wa (.classMem (.cv x) A) (.classMem C B)) p0031 p0047
  have p0049 :=
    @g_pm5_21nii (.classMem (syn_cop (.cv x) C) (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B))) (.classMem C (syn_cvv)) (syn_wa (.classMem (.cv x) A) (.classMem C B)) p0003 p0005 p0048
  exact p0049

noncomputable def g_eliunxp
    (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (syn_wb (.classMem C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B))) (syn_wex x (syn_wex y (syn_wa (.classEq C (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  have dv_cache_0001 : x ∉ (C).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (C).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0004 : y ∉ ((Wff.classMem C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ciun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_y, dv_A_y, (Ne.symm dv_x_y), dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elex C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B))
  have p0001 :=
    @g_pm4_71ri (.classMem C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B))) (.classMem C (syn_cvv)) p0000
  have p0002 :=
    @g_opeqexb x y C dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0003 :=
    @g_anbi1i (.classMem C (syn_cvv)) (syn_wex x (syn_wex y (.classEq C (syn_cop (.cv x) (.cv y))))) (.classMem C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B))) p0002
  have p0004 :=
    @g_bitri (.classMem C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B))) (syn_wa (.classMem C (syn_cvv)) (.classMem C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)))) (syn_wa (syn_wex x (syn_wex y (.classEq C (syn_cop (.cv x) (.cv y))))) (.classMem C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)))) p0001 p0003
  have p0005 :=
    @g_nfiu1 x A (syn_cxp (syn_csn (.cv x)) B)
  have p0006 :=
    @g_nfel2 x C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)) dv_cache_0001 p0005
  have p0007 :=
    @g_n_19_41 (syn_wex y (.classEq C (syn_cop (.cv x) (.cv y)))) (.classMem C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B))) x p0006
  have p0008 :=
    @g_n_19_41v (.classEq C (syn_cop (.cv x) (.cv y))) (.classMem C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B))) y dv_cache_0004
  have p0009 :=
    @g_eleq1 C (syn_cop (.cv x) (.cv y)) (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B))
  have p0010 :=
    @g_opeliunxp x A B (.cv y)
  have p0011 :=
    @g_syl6bb (.classEq C (syn_cop (.cv x) (.cv y))) (.classMem C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B))) (.classMem (syn_cop (.cv x) (.cv y)) (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B))) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) p0009 p0010
  have p0012 :=
    @g_pm5_32i (.classEq C (syn_cop (.cv x) (.cv y))) (.classMem C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B))) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) p0011
  have p0013 :=
    @g_exbii (syn_wa (.classEq C (syn_cop (.cv x) (.cv y))) (.classMem C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)))) (syn_wa (.classEq C (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))) y p0012
  have p0014 :=
    @g_bitr3i (syn_wa (syn_wex y (.classEq C (syn_cop (.cv x) (.cv y)))) (.classMem C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)))) (syn_wex y (syn_wa (.classEq C (syn_cop (.cv x) (.cv y))) (.classMem C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B))))) (syn_wex y (syn_wa (.classEq C (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)))) p0008 p0013
  have p0015 :=
    @g_exbii (syn_wa (syn_wex y (.classEq C (syn_cop (.cv x) (.cv y)))) (.classMem C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)))) (syn_wex y (syn_wa (.classEq C (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)))) x p0014
  have p0016 :=
    @g_n_3bitr2i (.classMem C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B))) (syn_wa (syn_wex x (syn_wex y (.classEq C (syn_cop (.cv x) (.cv y))))) (.classMem C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)))) (syn_wex x (syn_wa (syn_wex y (.classEq C (syn_cop (.cv x) (.cv y)))) (.classMem C (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B))))) (syn_wex x (syn_wex y (syn_wa (.classEq C (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))))) p0004 p0007 p0015
  exact p0016

noncomputable def g_raliunxp
    (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_ph_y : y ∉ ph.fv) (dv_ph_z : z ∉ ph.fv) (dv_ps_x : x ∉ ps.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) (hyp_raliunxp_1 : Nominal.NPrf (.imp (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (syn_wral x (syn_ciun y A (syn_cxp (syn_csn (.cv y)) B)) ph) (syn_wral y A (syn_wral z B ps))) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ A.fv ∪ B.fv
  have dv_cache_0001 : z ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_y), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_z), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show y ≠ z from (by exact dv_y_z))
  have dv_cache_0006 : y ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ph_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ph_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_cop (.cv y) (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_x_y, dv_x_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((Wff.imp (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B)) ps)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_x_y, dv_A_x, dv_x_z, dv_B_x, dv_ps_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eliunxp y z A B (.cv x) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @g_imbi1i (.classMem (.cv x) (syn_ciun y A (syn_cxp (syn_csn (.cv y)) B))) (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B))))) ph p0000
  have p0002 :=
    @g_n_19_23vv (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B))) ph y z dv_cache_0006 dv_cache_0007
  have p0003 :=
    @g_bitr4i (.imp (.classMem (.cv x) (syn_ciun y A (syn_cxp (syn_csn (.cv y)) B))) ph) (.imp (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B))))) ph) (.all y (.all z (.imp (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B))) ph))) p0001 p0002
  have p0004 :=
    @g_albii (.imp (.classMem (.cv x) (syn_ciun y A (syn_cxp (syn_csn (.cv y)) B))) ph) (.all y (.all z (.imp (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B))) ph))) x p0003
  have p0005 :=
    @g_alrot3 (.imp (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B))) ph) x y z
  have p0006 :=
    @g_impexp (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B)) ph
  have p0007 :=
    @g_albii (.imp (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B))) ph) (.imp (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) (.imp (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B)) ph)) x p0006
  have p0008 :=
    @g_vex y
  have p0009 :=
    @g_vex z
  have p0010 :=
    @g_opex (.cv y) (.cv z) p0008 p0009
  have p0011 :=
    @g_imbi2d (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) ph ps (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B)) hyp_raliunxp_1
  have p0012 :=
    @g_ceqsalv (.imp (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B)) ph) (.imp (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B)) ps) x (syn_cop (.cv y) (.cv z)) dv_cache_0008 dv_cache_0009 p0010 p0011
  have p0013 :=
    @g_bitri (.all x (.imp (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B))) ph)) (.all x (.imp (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) (.imp (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B)) ph))) (.imp (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B)) ps) p0007 p0012
  have p0014 :=
    @g_n_2albii (.all x (.imp (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B))) ph)) (.imp (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B)) ps) y z p0013
  have p0015 :=
    @g_bitri (.all x (.all y (.all z (.imp (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B))) ph)))) (.all y (.all z (.all x (.imp (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B))) ph)))) (.all y (.all z (.imp (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B)) ps))) p0005 p0014
  have p0016 :=
    @g_bitri (.all x (.imp (.classMem (.cv x) (syn_ciun y A (syn_cxp (syn_csn (.cv y)) B))) ph)) (.all x (.all y (.all z (.imp (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B))) ph)))) (.all y (.all z (.imp (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B)) ps))) p0004 p0015
  have p0017 :=
    (by simpa [syn_wb, syn_wral] using (Nominal.biimpRefl (syn_wral x (syn_ciun y A (syn_cxp (syn_csn (.cv y)) B)) ph)))
  have p0018 :=
    @g_r2al ps y z A B dv_cache_0001 dv_cache_0005
  have p0019 :=
    @g_n_3bitr4i (.all x (.imp (.classMem (.cv x) (syn_ciun y A (syn_cxp (syn_csn (.cv y)) B))) ph)) (.all y (.all z (.imp (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B)) ps))) (syn_wral x (syn_ciun y A (syn_cxp (syn_csn (.cv y)) B)) ph) (syn_wral y A (syn_wral z B ps)) p0016 p0017 p0018
  exact p0019

noncomputable def g_rexiunxp
    (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_ph_y : y ∉ ph.fv) (dv_ph_z : z ∉ ph.fv) (dv_ps_x : x ∉ ps.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) (hyp_raliunxp_1 : Nominal.NPrf (.imp (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (syn_wrex x (syn_ciun y A (syn_cxp (syn_csn (.cv y)) B)) ph) (syn_wrex y A (syn_wrex z B ps))) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ A.fv ∪ B.fv
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((Wff.neg ph)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ph_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((Wff.neg ph)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ph_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((Wff.neg ps)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ps_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0010 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0011 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show y ≠ z from (by exact dv_y_z))
  have p0000 :=
    @g_notbid (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) ph ps hyp_raliunxp_1
  have p0001 :=
    @g_raliunxp (.neg ph) (.neg ps) x y z A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 p0000
  have p0002 :=
    @g_ralnex ps z B
  have p0003 :=
    @g_ralbii (syn_wral z B (.neg ps)) (.neg (syn_wrex z B ps)) y A p0002
  have p0004 :=
    @g_bitri (syn_wral x (syn_ciun y A (syn_cxp (syn_csn (.cv y)) B)) (.neg ph)) (syn_wral y A (syn_wral z B (.neg ps))) (syn_wral y A (.neg (syn_wrex z B ps))) p0001 p0003
  have p0005 :=
    @g_notbii (syn_wral x (syn_ciun y A (syn_cxp (syn_csn (.cv y)) B)) (.neg ph)) (syn_wral y A (.neg (syn_wrex z B ps))) p0004
  have p0006 :=
    @g_dfrex2 ph x (syn_ciun y A (syn_cxp (syn_csn (.cv y)) B))
  have p0007 :=
    @g_dfrex2 (syn_wrex z B ps) y A
  have p0008 :=
    @g_n_3bitr4i (.neg (syn_wral x (syn_ciun y A (syn_cxp (syn_csn (.cv y)) B)) (.neg ph))) (.neg (syn_wral y A (.neg (syn_wrex z B ps)))) (syn_wrex x (syn_ciun y A (syn_cxp (syn_csn (.cv y)) B)) ph) (syn_wrex y A (syn_wrex z B ps)) p0005 p0006 p0007
  exact p0008

noncomputable def g_rexxp
    (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_ph_y : y ∉ ph.fv) (dv_ph_z : z ∉ ph.fv) (dv_ps_x : x ∉ ps.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) (hyp_raliunxp_1 : Nominal.NPrf (.imp (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (syn_wrex x (syn_cxp A B) ph) (syn_wrex y A (syn_wrex z B ps))) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ A.fv ∪ B.fv
  have dv_cache_0001 : y ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_ciun y A (syn_cxp (syn_csn (.cv y)) B))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ciun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, dv_x_y, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_cxp A B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : z ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ph_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : z ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ph_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : x ∉ (ps).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ps_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0013 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0014 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show y ≠ z from (by exact dv_y_z))
  have p0000 :=
    @g_iunxpconst y A B dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_rexeqi ph x (syn_ciun y A (syn_cxp (syn_csn (.cv y)) B)) (syn_cxp A B) dv_cache_0003 dv_cache_0004 p0000
  have p0002 :=
    @g_rexiunxp ph ps x y z A B dv_cache_0005 dv_cache_0001 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 hyp_raliunxp_1
  have p0003 :=
    @g_bitr3i (syn_wrex x (syn_cxp A B) ph) (syn_wrex x (syn_ciun y A (syn_cxp (syn_csn (.cv y)) B)) ph) (syn_wrex y A (syn_wrex z B ps)) p0001 p0002
  exact p0003

noncomputable def g_brel
    (A : Class) (B : Class) (C : Class) (D : Class) (R : Class) (hyp_brelg_1 : Nominal.NPrf (syn_wss R (syn_cxp C D))) :
    Nominal.NPrf (.imp (syn_wbr A R B) (syn_wa (.classMem A C) (.classMem B D))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv
  have p0000 :=
    @g_ssbri R (syn_cxp C D) A B hyp_brelg_1
  have p0001 :=
    @g_brxp A B C D
  have p0002 :=
    @g_sylib (syn_wbr A R B) (syn_wbr A (syn_cxp C D) B) (syn_wa (.classMem A C) (.classMem B D)) p0000 p0001
  exact p0002

#print axioms g_brel

end NFChoice.DirectNominalPrf.WPPReplay
