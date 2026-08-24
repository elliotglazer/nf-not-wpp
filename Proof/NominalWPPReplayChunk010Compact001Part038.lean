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
import NominalWPPReplayChunk010Compact001Part037

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

noncomputable def g_opeq
    (A : Class) :
    Nominal.NPrf (.classEq A (syn_cop (syn_cproj1 A) (syn_cproj2 A))) := by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
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
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
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
  have dv_cache_0001 : x ∉ ((syn_cproj1 A)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cproj1 A)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cproj2 A)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj2, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_cproj2 A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj2, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0006 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Class.cab z (.classMem (syn_cphi (.cv z)) A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : z ∉ ((Wff.classMem (syn_cphi (.cv y)) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0010 : y ∉ ((Wff.classMem (.cv x) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((Class.cab z (.classMem (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : z ∉ ((Wff.classMem (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_op x y (syn_cproj1 A) (syn_cproj2 A) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_proj1 z A dv_cache_0006
  have p0002 :=
    @g_rexeqi (.classEq (.cv x) (syn_cphi (.cv y))) y (syn_cproj1 A) (.cab z (.classMem (syn_cphi (.cv z)) A)) dv_cache_0002 dv_cache_0007 p0001
  have p0003 :=
    @g_phieq (.cv z) (.cv y)
  have p0004_e00_recanon : Nominal.NPrf (.imp (.objEq z y) (.classEq (syn_cphi (.cv z)) (syn_cphi (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cphi syn_wrex syn_wex syn_wa syn_cif syn_wo syn_cnnc syn_cint syn_cplc syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0003
  have p0004 :=
    @g_eleq1d (.objEq z y) (syn_cphi (.cv z)) (syn_cphi (.cv y)) A p0004_e00_recanon
  have p0005 :=
    @g_rexab (.classMem (syn_cphi (.cv z)) A) (.classMem (syn_cphi (.cv y)) A) (.classEq (.cv x) (syn_cphi (.cv y))) y z dv_cache_0008 dv_cache_0009 p0004
  have p0006 :=
    @g_ancom (.classMem (syn_cphi (.cv y)) A) (.classEq (.cv x) (syn_cphi (.cv y)))
  have p0007 :=
    @g_eleq1 (.cv x) (syn_cphi (.cv y)) A
  have p0008 :=
    @g_pm5_32i (.classEq (.cv x) (syn_cphi (.cv y))) (.classMem (.cv x) A) (.classMem (syn_cphi (.cv y)) A) p0007
  have p0009 :=
    @g_bitr4i (syn_wa (.classMem (syn_cphi (.cv y)) A) (.classEq (.cv x) (syn_cphi (.cv y)))) (syn_wa (.classEq (.cv x) (syn_cphi (.cv y))) (.classMem (syn_cphi (.cv y)) A)) (syn_wa (.classEq (.cv x) (syn_cphi (.cv y))) (.classMem (.cv x) A)) p0006 p0008
  have p0010 :=
    @g_exbii (syn_wa (.classMem (syn_cphi (.cv y)) A) (.classEq (.cv x) (syn_cphi (.cv y)))) (syn_wa (.classEq (.cv x) (syn_cphi (.cv y))) (.classMem (.cv x) A)) y p0009
  have p0011 :=
    @g_n_19_41v (.classEq (.cv x) (syn_cphi (.cv y))) (.classMem (.cv x) A) y dv_cache_0010
  have p0012 :=
    @g_ancom (syn_wex y (.classEq (.cv x) (syn_cphi (.cv y)))) (.classMem (.cv x) A)
  have p0013 :=
    @g_n_3bitri (syn_wex y (syn_wa (.classMem (syn_cphi (.cv y)) A) (.classEq (.cv x) (syn_cphi (.cv y))))) (syn_wex y (syn_wa (.classEq (.cv x) (syn_cphi (.cv y))) (.classMem (.cv x) A))) (syn_wa (syn_wex y (.classEq (.cv x) (syn_cphi (.cv y)))) (.classMem (.cv x) A)) (syn_wa (.classMem (.cv x) A) (syn_wex y (.classEq (.cv x) (syn_cphi (.cv y))))) p0010 p0011 p0012
  have p0014 :=
    @g_n_3bitri (syn_wrex y (syn_cproj1 A) (.classEq (.cv x) (syn_cphi (.cv y)))) (syn_wrex y (.cab z (.classMem (syn_cphi (.cv z)) A)) (.classEq (.cv x) (syn_cphi (.cv y)))) (syn_wex y (syn_wa (.classMem (syn_cphi (.cv y)) A) (.classEq (.cv x) (syn_cphi (.cv y))))) (syn_wa (.classMem (.cv x) A) (syn_wex y (.classEq (.cv x) (syn_cphi (.cv y))))) p0002 p0005 p0013
  have p0015 :=
    @g_abbii (syn_wrex y (syn_cproj1 A) (.classEq (.cv x) (syn_cphi (.cv y)))) (syn_wa (.classMem (.cv x) A) (syn_wex y (.classEq (.cv x) (syn_cphi (.cv y))))) x p0014
  have p0016 :=
    (by simpa [syn_crab] using (Nominal.classEqRefl (syn_crab x A (syn_wex y (.classEq (.cv x) (syn_cphi (.cv y)))))))
  have p0017 :=
    @g_eqtr4i (.cab x (syn_wrex y (syn_cproj1 A) (.classEq (.cv x) (syn_cphi (.cv y))))) (.cab x (syn_wa (.classMem (.cv x) A) (syn_wex y (.classEq (.cv x) (syn_cphi (.cv y)))))) (syn_crab x A (syn_wex y (.classEq (.cv x) (syn_cphi (.cv y))))) p0015 p0016
  have p0018 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_proj2 z A dv_cache_0006
  have p0019 :=
    @g_rexeqi (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))) y (syn_cproj2 A) (.cab z (.classMem (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) A)) dv_cache_0004 dv_cache_0011 p0018
  have p0020_e00_recanon : Nominal.NPrf (.imp (.objEq z y) (.classEq (syn_cphi (.cv z)) (syn_cphi (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cphi syn_wrex syn_wex syn_wa syn_cif syn_wo syn_cnnc syn_cint syn_cplc syn_c1c
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0003
  have p0020 :=
    @g_uneq1d (.objEq z y) (syn_cphi (.cv z)) (syn_cphi (.cv y)) (syn_csn (syn_c0c)) p0020_e00_recanon
  have p0021 :=
    @g_eleq1d (.objEq z y) (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))) A p0020
  have p0022 :=
    @g_rexab (.classMem (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) A) (.classMem (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))) A) (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))) y z dv_cache_0012 dv_cache_0009 p0021
  have p0023 :=
    @g_ancom (.classMem (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))) A) (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))
  have p0024 :=
    @g_eleq1 (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))) A
  have p0025 :=
    @g_pm5_32i (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))) (.classMem (.cv x) A) (.classMem (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))) A) p0024
  have p0026 :=
    @g_bitr4i (syn_wa (.classMem (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))) A) (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))) (syn_wa (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))) (.classMem (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))) A)) (syn_wa (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))) (.classMem (.cv x) A)) p0023 p0025
  have p0027 :=
    @g_exbii (syn_wa (.classMem (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))) A) (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))) (syn_wa (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))) (.classMem (.cv x) A)) y p0026
  have p0028 :=
    @g_n_19_41v (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))) (.classMem (.cv x) A) y dv_cache_0010
  have p0029 :=
    @g_ancom (syn_wex y (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))) (.classMem (.cv x) A)
  have p0030 :=
    @g_n_3bitri (syn_wex y (syn_wa (.classMem (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))) A) (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))) (syn_wex y (syn_wa (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))) (.classMem (.cv x) A))) (syn_wa (syn_wex y (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))) (.classMem (.cv x) A)) (syn_wa (.classMem (.cv x) A) (syn_wex y (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))) p0027 p0028 p0029
  have p0031 :=
    @g_n_3bitri (syn_wrex y (syn_cproj2 A) (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))) (syn_wrex y (.cab z (.classMem (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) A)) (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))) (syn_wex y (syn_wa (.classMem (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))) A) (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))) (syn_wa (.classMem (.cv x) A) (syn_wex y (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))) p0019 p0022 p0030
  have p0032 :=
    @g_abbii (syn_wrex y (syn_cproj2 A) (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))) (syn_wa (.classMem (.cv x) A) (syn_wex y (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))) x p0031
  have p0033 :=
    (by simpa [syn_crab] using (Nominal.classEqRefl (syn_crab x A (syn_wex y (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))))
  have p0034 :=
    @g_eqtr4i (.cab x (syn_wrex y (syn_cproj2 A) (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))) (.cab x (syn_wa (.classMem (.cv x) A) (syn_wex y (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))) (syn_crab x A (syn_wex y (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))) p0032 p0033
  have p0035 :=
    @g_uneq12i (.cab x (syn_wrex y (syn_cproj1 A) (.classEq (.cv x) (syn_cphi (.cv y))))) (syn_crab x A (syn_wex y (.classEq (.cv x) (syn_cphi (.cv y))))) (.cab x (syn_wrex y (syn_cproj2 A) (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))) (syn_crab x A (syn_wex y (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))) p0017 p0034
  have p0036 :=
    @g_unrab (syn_wex y (.classEq (.cv x) (syn_cphi (.cv y)))) (syn_wex y (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))) x A
  have p0037 :=
    @g_rabid2 (syn_wo (syn_wex y (.classEq (.cv x) (syn_cphi (.cv y)))) (syn_wex y (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))) x A dv_cache_0013
  have p0038 :=
    @g_vex x
  have p0039 :=
    @g_phiall y (.cv x) dv_cache_0014 p0038
  have p0040 :=
    @g_n_19_43 (.classEq (.cv x) (syn_cphi (.cv y))) (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))) y
  have p0041 :=
    @g_mpbi (syn_wex y (syn_wo (.classEq (.cv x) (syn_cphi (.cv y))) (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))) (syn_wo (syn_wex y (.classEq (.cv x) (syn_cphi (.cv y)))) (syn_wex y (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))) p0039 p0040
  have p0042 :=
    @g_a1i (syn_wo (syn_wex y (.classEq (.cv x) (syn_cphi (.cv y)))) (syn_wex y (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))) (.classMem (.cv x) A) p0041
  have p0043 :=
    @g_mprgbir (.classEq A (syn_crab x A (syn_wo (syn_wex y (.classEq (.cv x) (syn_cphi (.cv y)))) (syn_wex y (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))))) (syn_wo (syn_wex y (.classEq (.cv x) (syn_cphi (.cv y)))) (syn_wex y (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))) x A p0037 p0042
  have p0044 :=
    @g_eqtr4i (syn_cun (syn_crab x A (syn_wex y (.classEq (.cv x) (syn_cphi (.cv y))))) (syn_crab x A (syn_wex y (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))) (syn_crab x A (syn_wo (syn_wex y (.classEq (.cv x) (syn_cphi (.cv y)))) (syn_wex y (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))) A p0036 p0043
  have p0045 :=
    @g_n_3eqtrri (syn_cop (syn_cproj1 A) (syn_cproj2 A)) (syn_cun (.cab x (syn_wrex y (syn_cproj1 A) (.classEq (.cv x) (syn_cphi (.cv y))))) (.cab x (syn_wrex y (syn_cproj2 A) (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))) (syn_cun (syn_crab x A (syn_wex y (.classEq (.cv x) (syn_cphi (.cv y))))) (syn_crab x A (syn_wex y (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))) A p0000 p0035 p0044
  exact p0045

noncomputable def g_opeqexb
    (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cvv)) (syn_wex x (syn_wex y (.classEq A (syn_cop (.cv x) (.cv y)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv
  have dv_cache_0001 : y ∉ ((Wff.classEq (.cv x) (syn_cproj1 A))).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_y), dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classEq (.cv y) (syn_cproj2 A))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj2, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_x_y, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cproj1 A)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_cproj2 A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj2, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_opexb (syn_cproj1 A) (syn_cproj2 A)
  have p0001 :=
    @g_opeq A
  have p0002 :=
    @g_eleq1i A (syn_cop (syn_cproj1 A) (syn_cproj2 A)) (syn_cvv) p0001
  have p0003 :=
    @g_eeanv (.classEq (.cv x) (syn_cproj1 A)) (.classEq (.cv y) (syn_cproj2 A)) x y dv_cache_0001 dv_cache_0002
  have p0004 :=
    @g_eqeq1i A (syn_cop (syn_cproj1 A) (syn_cproj2 A)) (syn_cop (.cv x) (.cv y)) p0001
  have p0005 :=
    @g_eqcom (syn_cop (syn_cproj1 A) (syn_cproj2 A)) (syn_cop (.cv x) (.cv y))
  have p0006 :=
    @g_opth (.cv x) (.cv y) (syn_cproj1 A) (syn_cproj2 A)
  have p0007 :=
    @g_n_3bitri (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq (syn_cop (syn_cproj1 A) (syn_cproj2 A)) (syn_cop (.cv x) (.cv y))) (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop (syn_cproj1 A) (syn_cproj2 A))) (syn_wa (.classEq (.cv x) (syn_cproj1 A)) (.classEq (.cv y) (syn_cproj2 A))) p0004 p0005 p0006
  have p0008 :=
    @g_n_2exbii (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wa (.classEq (.cv x) (syn_cproj1 A)) (.classEq (.cv y) (syn_cproj2 A))) x y p0007
  have p0009 :=
    @g_isset x (syn_cproj1 A) dv_cache_0003
  have p0010 :=
    @g_isset y (syn_cproj2 A) dv_cache_0004
  have p0011 :=
    @g_anbi12i (.classMem (syn_cproj1 A) (syn_cvv)) (syn_wex x (.classEq (.cv x) (syn_cproj1 A))) (.classMem (syn_cproj2 A) (syn_cvv)) (syn_wex y (.classEq (.cv y) (syn_cproj2 A))) p0009 p0010
  have p0012 :=
    @g_n_3bitr4i (syn_wex x (syn_wex y (syn_wa (.classEq (.cv x) (syn_cproj1 A)) (.classEq (.cv y) (syn_cproj2 A))))) (syn_wa (syn_wex x (.classEq (.cv x) (syn_cproj1 A))) (syn_wex y (.classEq (.cv y) (syn_cproj2 A)))) (syn_wex x (syn_wex y (.classEq A (syn_cop (.cv x) (.cv y))))) (syn_wa (.classMem (syn_cproj1 A) (syn_cvv)) (.classMem (syn_cproj2 A) (syn_cvv))) p0003 p0008 p0011
  have p0013 :=
    @g_n_3bitr4i (.classMem (syn_cop (syn_cproj1 A) (syn_cproj2 A)) (syn_cvv)) (syn_wa (.classMem (syn_cproj1 A) (syn_cvv)) (.classMem (syn_cproj2 A) (syn_cvv))) (.classMem A (syn_cvv)) (syn_wex x (syn_wex y (.classEq A (syn_cop (.cv x) (.cv y))))) p0000 p0002 p0012
  exact p0013

noncomputable def g_opeqex
    (x : Var) (y : Var) (A : Class) (V : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (.classMem A V) (syn_wex x (syn_wex y (.classEq A (syn_cop (.cv x) (.cv y)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ V.fv
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
  have dv_cache_0003 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @g_elex A V
  have p0001 :=
    @g_opeqexb x y A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0002 :=
    @g_sylib (.classMem A V) (.classMem A (syn_cvv)) (syn_wex x (syn_wex y (.classEq A (syn_cop (.cv x) (.cv y))))) p0000 p0001
  exact p0002

noncomputable def g_opabbid
    (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var) (hyp_opabbid_1 : Nominal.NPrf (syn_wnf x ph)) (hyp_opabbid_2 : Nominal.NPrf (syn_wnf y ph)) (hyp_opabbid_3 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (.classEq (syn_copab x y ps) (syn_copab x y ch))) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_z_not_ps : z ∉ ps.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_ch : z ∉ ch.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
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
  have dv_cache_0001 : z ∉ (ph).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ (ps).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_ps, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0004 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0005 : z ∉ (ch).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_ch, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_anbi2d ph ps ch (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) hyp_opabbid_3
  have p0001 :=
    @g_exbid ph (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ps) (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ch) y hyp_opabbid_2 p0000
  have p0002 :=
    @g_exbid ph (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ps)) (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ch)) x hyp_opabbid_1 p0001
  have p0003 :=
    @g_abbidv ph (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ps))) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ch))) z dv_cache_0001 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_opab ps x y z dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_opab ch x y z dv_cache_0005 dv_cache_0003 dv_cache_0004
  have p0006 :=
    @g_n_3eqtr4g ph (.cab z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ps)))) (.cab z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ch)))) (syn_copab x y ps) (syn_copab x y ch) p0003 p0004 p0005
  exact p0006

noncomputable def g_opabbidv
    (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var) (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv) (hyp_opabbidv_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (.classEq (syn_copab x y ps) (syn_copab x y ch))) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var)
  have dv_cache_0001 : x ∉ (ph).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ph_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (ph).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ph_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_nfv ph x dv_cache_0001
  have p0001 :=
    @g_nfv ph y dv_cache_0002
  have p0002 :=
    @g_opabbid ph ps ch x y p0000 p0001 hyp_opabbidv_1
  exact p0002

noncomputable def g_opabbii
    (ph : Wff) (ps : Wff) (x : Var) (y : Var) (hyp_opabbii_1 : Nominal.NPrf (syn_wb ph ps)) :
    Nominal.NPrf (.classEq (syn_copab x y ph) (syn_copab x y ps)) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_not_ps : z ∉ ps.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
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
  have dv_cache_0001 : x ∉ ((Wff.classEq (.cv z) (.cv z))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Wff.classEq (.cv z) (.cv z))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eqid (.cv z)
  have p0001 :=
    @g_a1i (syn_wb ph ps) (.classEq (.cv z) (.cv z)) hyp_opabbii_1
  have p0002 :=
    @g_opabbidv (.classEq (.cv z) (.cv z)) ph ps x y dv_cache_0001 dv_cache_0002 p0001
  have p0003 :=
    Nominal.mp p0000 p0002
  exact p0003

noncomputable def g_nfopab
    (ph : Wff) (x : Var) (y : Var) (z : Var) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) (hyp_nfopab_1 : Nominal.NPrf (syn_wnf z ph)) :
    Nominal.NPrf (syn_wnfc z (syn_copab x y ph)) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var)
  let w : Var := freshVar proofSupport 0
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_w : y ≠ w :=
    Ne.symm fresh_w_ne_y
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_z_ne_w : z ≠ w :=
    Ne.symm fresh_w_ne_z
  have dv_cache_0001 : w ∉ (ph).fv := by
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ≠ w := by
    clear dv_cache_0001
    exact (show x ≠ w from (by exact fresh_x_ne_w))
  have dv_cache_0003 : y ≠ w := by
    clear dv_cache_0001 dv_cache_0002
    exact (show y ≠ w from (by exact fresh_y_ne_w))
  have dv_cache_0004 : z ∉ ((Wff.classEq (.cv w) (syn_cop (.cv x) (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_w, (Ne.symm dv_x_z), (Ne.symm dv_y_z), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_opab ph x y w dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_nfv (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) z dv_cache_0004
  have p0002 :=
    @g_nfan (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph z p0001 hyp_nfopab_1
  have p0003 :=
    @g_nfex (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph) z y p0002
  have p0004 :=
    @g_nfex (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)) z x p0003
  have p0005 :=
    @g_nfab (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))) z w p0004
  have p0006 :=
    @g_nfcxfr z (syn_copab x y ph) (.cab w (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)))) p0000 p0005
  exact p0006

noncomputable def g_nfopab1
    (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (syn_wnfc x (syn_copab x y ph)) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var)
  let z : Var := freshVar proofSupport 0
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
  have dv_cache_0001 : z ∉ (ph).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ≠ z := by
    clear dv_cache_0001
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0003 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_opab ph x y z dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_nfe1 (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph)) x
  have p0002 :=
    @g_nfab (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph))) x z p0001
  have p0003 :=
    @g_nfcxfr x (syn_copab x y ph) (.cab z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph)))) p0000 p0002
  exact p0003

noncomputable def g_nfopab2
    (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (syn_wnfc y (syn_copab x y ph)) := by
  let proofSupport : Finset Var := ph.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var)
  let z : Var := freshVar proofSupport 0
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
  have dv_cache_0001 : z ∉ (ph).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ≠ z := by
    clear dv_cache_0001
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0003 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_opab ph x y z dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_nfe1 (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph) y
  have p0002 :=
    @g_nfex (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph)) y x p0001
  have p0003 :=
    @g_nfab (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph))) y z p0002
  have p0004 :=
    @g_nfcxfr y (syn_copab x y ph) (.cab z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph)))) p0000 p0003
  exact p0004

noncomputable def g_cbvopab1
    (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var) (dv_x_y : x ≠ y) (dv_y_z : y ≠ z) (hyp_cbvopab1_1 : Nominal.NPrf (syn_wnf z ph)) (hyp_cbvopab1_2 : Nominal.NPrf (syn_wnf x ps)) (hyp_cbvopab1_3 : Nominal.NPrf (.imp (.objEq x z) (syn_wb ph ps))) :
    Nominal.NPrf (.classEq (syn_copab x y ph) (syn_copab z y ps)) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var)
  let w : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_w_not_ps : w ∉ ps.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_w : y ≠ w :=
    Ne.symm fresh_w_ne_y
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_z_ne_w : z ≠ w :=
    Ne.symm fresh_w_ne_z
  have fresh_v : v ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_v_not_ph : v ∉ ph.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_v_not_ps : v ∉ ps.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_v_ne_x : v ≠ x := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_v : x ≠ v :=
    Ne.symm fresh_v_ne_x
  have fresh_v_ne_y : v ≠ y := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_v : y ≠ v :=
    Ne.symm fresh_v_ne_y
  have fresh_v_ne_z : v ≠ z := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_z_ne_v : z ≠ v :=
    Ne.symm fresh_v_ne_z
  have fresh_w_ne_v : w ≠ v := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_v_ne_w : v ≠ w :=
    Ne.symm fresh_w_ne_v
  have dv_cache_0001 : v ∉ ((syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))).fv := by
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_w, fresh_v_ne_x, fresh_v_ne_y, fresh_v_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classEq (.cv w) (syn_cop (.cv v) (.cv y)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_w, fresh_x_ne_v, dv_x_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ≠ v := by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ v from (by exact fresh_x_ne_v))
  have dv_cache_0004 : y ∉ ((Wff.classEq (.cv x) (.cv v))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_y), fresh_y_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((Wff.classEq (.cv w) (syn_cop (.cv v) (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_w, fresh_z_ne_v, (Ne.symm dv_y_z), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : v ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show v ≠ z from (by exact fresh_v_ne_z))
  have dv_cache_0007 : v ∉ ((syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv z) (.cv y))) ps))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_w, fresh_v_ne_z, fresh_v_ne_y, fresh_v_not_ps, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((Wff.classEq (.cv v) (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_v, dv_y_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : w ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ w from (by exact fresh_x_ne_w))
  have dv_cache_0011 : y ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show y ≠ w from (by exact fresh_y_ne_w))
  have dv_cache_0012 : w ∉ (ps).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_ps, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : z ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have p0000 :=
    @g_nfv (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)) v dv_cache_0001
  have p0001 :=
    @g_nfv (.classEq (.cv w) (syn_cop (.cv v) (.cv y))) x dv_cache_0002
  have p0002 :=
    @g_nfs1v ph x v dv_cache_0003
  have p0003 :=
    @g_nfan (.classEq (.cv w) (syn_cop (.cv v) (.cv y))) (syn_wsb v x ph) x p0001 p0002
  have p0004 :=
    @g_nfex (syn_wa (.classEq (.cv w) (syn_cop (.cv v) (.cv y))) (syn_wsb v x ph)) x y p0003
  have p0005 :=
    @g_opeq1 (.cv x) (.cv v) (.cv y)
  have p0006 :=
    @g_eqeq2d (.classEq (.cv x) (.cv v)) (syn_cop (.cv x) (.cv y)) (syn_cop (.cv v) (.cv y)) (.cv w) p0005
  have p0007 :=
    @g_sbequ12 ph x v
  have p0008_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv x) (.cv v)) (syn_wb ph (syn_wsb v x ph))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wsb syn_wa syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0007
  have p0008 :=
    @g_anbi12d (.classEq (.cv x) (.cv v)) (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) (.classEq (.cv w) (syn_cop (.cv v) (.cv y))) ph (syn_wsb v x ph) p0006 p0008_e01_recanon
  have p0009 :=
    @g_exbidv (.classEq (.cv x) (.cv v)) (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph) (syn_wa (.classEq (.cv w) (syn_cop (.cv v) (.cv y))) (syn_wsb v x ph)) y dv_cache_0004 p0008
  have p0010_e02_recanon : Nominal.NPrf (.imp (.objEq x v) (syn_wb (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)) (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv v) (.cv y))) (syn_wsb v x ph))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_wa syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsb, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0009
  have p0010 :=
    @g_cbvex (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)) (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv v) (.cv y))) (syn_wsb v x ph))) x v p0000 p0004 p0010_e02_recanon
  have p0011 :=
    @g_nfv (.classEq (.cv w) (syn_cop (.cv v) (.cv y))) z dv_cache_0005
  have p0012 :=
    @g_nfsb ph x v z dv_cache_0006 hyp_cbvopab1_1
  have p0013 :=
    @g_nfan (.classEq (.cv w) (syn_cop (.cv v) (.cv y))) (syn_wsb v x ph) z p0011 p0012
  have p0014 :=
    @g_nfex (syn_wa (.classEq (.cv w) (syn_cop (.cv v) (.cv y))) (syn_wsb v x ph)) z y p0013
  have p0015 :=
    @g_nfv (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv z) (.cv y))) ps)) v dv_cache_0007
  have p0016 :=
    @g_opeq1 (.cv v) (.cv z) (.cv y)
  have p0017 :=
    @g_eqeq2d (.classEq (.cv v) (.cv z)) (syn_cop (.cv v) (.cv y)) (syn_cop (.cv z) (.cv y)) (.cv w) p0016
  have p0018 :=
    @g_sbequ ph v z x
  have p0019 :=
    @g_sbie ph ps x z hyp_cbvopab1_2 hyp_cbvopab1_3
  have p0020_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv v) (.cv z)) (syn_wb (syn_wsb v x ph) (syn_wsb z x ph))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wsb syn_wa syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0018
  have p0020 :=
    @g_syl6bb (.classEq (.cv v) (.cv z)) (syn_wsb v x ph) (syn_wsb z x ph) ps p0020_e00_recanon p0019
  have p0021 :=
    @g_anbi12d (.classEq (.cv v) (.cv z)) (.classEq (.cv w) (syn_cop (.cv v) (.cv y))) (.classEq (.cv w) (syn_cop (.cv z) (.cv y))) (syn_wsb v x ph) ps p0017 p0020
  have p0022 :=
    @g_exbidv (.classEq (.cv v) (.cv z)) (syn_wa (.classEq (.cv w) (syn_cop (.cv v) (.cv y))) (syn_wsb v x ph)) (syn_wa (.classEq (.cv w) (syn_cop (.cv z) (.cv y))) ps) y dv_cache_0008 p0021
  have p0023_e02_recanon : Nominal.NPrf (.imp (.objEq v z) (syn_wb (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv v) (.cv y))) (syn_wsb v x ph))) (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv z) (.cv y))) ps)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_wa syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex syn_cphi syn_wsb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsb, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0022
  have p0023 :=
    @g_cbvex (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv v) (.cv y))) (syn_wsb v x ph))) (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv z) (.cv y))) ps)) v z p0014 p0015 p0023_e02_recanon
  have p0024 :=
    @g_bitri (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))) (syn_wex v (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv v) (.cv y))) (syn_wsb v x ph)))) (syn_wex z (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv z) (.cv y))) ps))) p0010 p0023
  have p0025 :=
    @g_abbii (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))) (syn_wex z (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv z) (.cv y))) ps))) w p0024
  have p0026 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_opab ph x y w dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0027 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_opab ps z y w dv_cache_0012 dv_cache_0013 dv_cache_0011
  have p0028 :=
    @g_n_3eqtr4i (.cab w (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)))) (.cab w (syn_wex z (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv z) (.cv y))) ps)))) (syn_copab x y ph) (syn_copab z y ps) p0025 p0026 p0027
  exact p0028

#print axioms g_cbvopab1

end NFChoice.DirectNominalPrf.WPPReplay
