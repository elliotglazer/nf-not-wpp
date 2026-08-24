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
import NominalAlphaRepairedBase001049OprabReflected001
import NominalNFLiteralBaseFour
import NominalNFLiteralXpViaCompletenessDev003
import NominalNFLiteralRemainingViaCompletenessDev001
import NominalDefinitionLeafHandlersCanonical001
import NominalDefinitionLeafHandlersObjExtCompat001
import NominalRecanonTransportCompat001
import NominalWPPReplayChunk012ACompact002Part001

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

noncomputable def g_fv3
    (x : Var) (y : Var) (A : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_F_x : x ∉ F.fv) (dv_F_y : y ∉ F.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classEq (syn_cfv F A) (.cab x (syn_wa (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (syn_wbr A F (.cv y)))) (syn_weu y (syn_wbr A F (.cv y)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ F.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 : z ∉ ((Class.cv x)).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show z ≠ y from (by exact fresh_z_ne_y))
  have dv_cache_0007 : y ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_wbr A F (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, fresh_y_ne_z, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((syn_wa (.classMem (.cv x) (.cv z)) (syn_wbr A F (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_y), fresh_y_ne_z, dv_A_y, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : z ∉ ((syn_wa (.classMem (.cv x) (.cv y)) (syn_wbr A F (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_A, fresh_z_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0012 : z ∉ ((syn_wbr A F (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_y, fresh_z_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : y ∉ ((Wff.classMem (.cv x) (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_y), fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : x ∉ ((syn_cfv F A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, dv_F_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elfv z y (.cv x) A F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_bi2 (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))
  have p0002 :=
    @g_alimi (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))) (.imp (.classEq (.cv y) (.cv z)) (syn_wbr A F (.cv y))) y p0001
  have p0003 :=
    @g_vex z
  have p0004 :=
    @g_breq2 (.cv y) (.cv z) A F
  have p0005 :=
    @g_ceqsalv (syn_wbr A F (.cv y)) (syn_wbr A F (.cv z)) y (.cv z) dv_cache_0007 dv_cache_0008 p0003 p0004
  have p0006 :=
    @g_sylib (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z)))) (.all y (.imp (.classEq (.cv y) (.cv z)) (syn_wbr A F (.cv y)))) (syn_wbr A F (.cv z)) p0002 p0005
  have p0007 :=
    @g_anim2i (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z)))) (syn_wbr A F (.cv z)) (.classMem (.cv x) (.cv z)) p0006
  have p0008 :=
    @g_eximi (syn_wa (.classMem (.cv x) (.cv z)) (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))))) (syn_wa (.classMem (.cv x) (.cv z)) (syn_wbr A F (.cv z))) z p0007
  have p0009 :=
    @g_elequ2 z y x
  have p0010 :=
    @g_breq2 (.cv z) (.cv y) A F
  have p0011_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv z) (.cv y)) (syn_wb (.classMem (.cv x) (.cv z)) (.classMem (.cv x) (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
      )
      p0009
  have p0011 :=
    @g_anbi12d (.classEq (.cv z) (.cv y)) (.classMem (.cv x) (.cv z)) (.classMem (.cv x) (.cv y)) (syn_wbr A F (.cv z)) (syn_wbr A F (.cv y)) p0011_e00_recanon p0010
  have p0012_e00_recanon : Nominal.NPrf (.imp (.objEq z y) (syn_wb (syn_wa (.classMem (.cv x) (.cv z)) (syn_wbr A F (.cv z))) (syn_wa (.classMem (.cv x) (.cv y)) (syn_wbr A F (.cv y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0011
  have p0012 :=
    @g_cbvexv (syn_wa (.classMem (.cv x) (.cv z)) (syn_wbr A F (.cv z))) (syn_wa (.classMem (.cv x) (.cv y)) (syn_wbr A F (.cv y))) z y dv_cache_0009 dv_cache_0010 p0012_e00_recanon
  have p0013 :=
    @g_sylib (syn_wex z (syn_wa (.classMem (.cv x) (.cv z)) (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z)))))) (syn_wex z (syn_wa (.classMem (.cv x) (.cv z)) (syn_wbr A F (.cv z)))) (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (syn_wbr A F (.cv y)))) p0008 p0012
  have p0014 :=
    @g_n_19_40 (.classMem (.cv x) (.cv z)) (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z)))) z
  have p0015 :=
    @g_simprd (syn_wex z (syn_wa (.classMem (.cv x) (.cv z)) (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z)))))) (syn_wex z (.classMem (.cv x) (.cv z))) (syn_wex z (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))))) p0014
  have p0016 :=
    Nominal.dfEu y z (syn_wbr A F (.cv y)) dv_cache_0011 dv_cache_0012
  have p0017_e01_recanon : Nominal.NPrf (syn_wb (syn_weu y (syn_wbr A F (.cv y))) (syn_wex z (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_weu syn_wex syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_weu, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
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
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0016
  have p0017 :=
    @g_sylibr (syn_wex z (syn_wa (.classMem (.cv x) (.cv z)) (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z)))))) (syn_wex z (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))))) (syn_weu y (syn_wbr A F (.cv y))) p0015 p0017_e01_recanon
  have p0018 :=
    @g_jca (syn_wex z (syn_wa (.classMem (.cv x) (.cv z)) (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z)))))) (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (syn_wbr A F (.cv y)))) (syn_weu y (syn_wbr A F (.cv y))) p0013 p0017
  have p0019 :=
    @g_nfeu1 (syn_wbr A F (.cv y)) y
  have p0020 :=
    @g_nfv (.classMem (.cv x) (.cv z)) y dv_cache_0013
  have p0021 :=
    @g_nfa1 (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))) y
  have p0022 :=
    @g_nfan (.classMem (.cv x) (.cv z)) (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z)))) y p0020 p0021
  have p0023 :=
    @g_nfex (syn_wa (.classMem (.cv x) (.cv z)) (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))))) y z p0022
  have p0024 :=
    @g_nfim (syn_weu y (syn_wbr A F (.cv y))) (syn_wex z (syn_wa (.classMem (.cv x) (.cv z)) (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z)))))) y p0019 p0023
  have p0025 :=
    @g_bi1 (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))
  have p0026 :=
    Nominal.ax14 y z x
  have p0027_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv y) (.cv z)) (.imp (.classMem (.cv x) (.cv y)) (.classMem (.cv x) (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
      )
      p0026
  have p0027 :=
    @g_syl6 (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))) (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z)) (.imp (.classMem (.cv x) (.cv y)) (.classMem (.cv x) (.cv z))) p0025 p0027_e01_recanon
  have p0028 :=
    @g_com23 (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))) (syn_wbr A F (.cv y)) (.classMem (.cv x) (.cv y)) (.classMem (.cv x) (.cv z)) p0027
  have p0029 :=
    @g_imp3a (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))) (.classMem (.cv x) (.cv y)) (syn_wbr A F (.cv y)) (.classMem (.cv x) (.cv z)) p0028
  have p0030 :=
    @g_sps (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))) (.imp (syn_wa (.classMem (.cv x) (.cv y)) (syn_wbr A F (.cv y))) (.classMem (.cv x) (.cv z))) y p0029
  have p0031 :=
    @g_anc2ri (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z)))) (syn_wa (.classMem (.cv x) (.cv y)) (syn_wbr A F (.cv y))) (.classMem (.cv x) (.cv z)) p0030
  have p0032 :=
    @g_com12 (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z)))) (syn_wa (.classMem (.cv x) (.cv y)) (syn_wbr A F (.cv y))) (syn_wa (.classMem (.cv x) (.cv z)) (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))))) p0031
  have p0033 :=
    @g_eximdv (syn_wa (.classMem (.cv x) (.cv y)) (syn_wbr A F (.cv y))) (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z)))) (syn_wa (.classMem (.cv x) (.cv z)) (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))))) z dv_cache_0010 p0032
  have p0034_e00_recanon : Nominal.NPrf (syn_wb (syn_weu y (syn_wbr A F (.cv y))) (syn_wex z (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_weu syn_wex syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_weu, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
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
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0016
  have p0034 :=
    @g_syl5bi (syn_weu y (syn_wbr A F (.cv y))) (syn_wex z (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))))) (syn_wa (.classMem (.cv x) (.cv y)) (syn_wbr A F (.cv y))) (syn_wex z (syn_wa (.classMem (.cv x) (.cv z)) (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z)))))) p0034_e00_recanon p0033
  have p0035 :=
    @g_exlimi (syn_wa (.classMem (.cv x) (.cv y)) (syn_wbr A F (.cv y))) (.imp (syn_weu y (syn_wbr A F (.cv y))) (syn_wex z (syn_wa (.classMem (.cv x) (.cv z)) (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))))))) y p0024 p0034
  have p0036 :=
    @g_imp (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (syn_wbr A F (.cv y)))) (syn_weu y (syn_wbr A F (.cv y))) (syn_wex z (syn_wa (.classMem (.cv x) (.cv z)) (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z)))))) p0035
  have p0037 :=
    @g_impbii (syn_wex z (syn_wa (.classMem (.cv x) (.cv z)) (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z)))))) (syn_wa (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (syn_wbr A F (.cv y)))) (syn_weu y (syn_wbr A F (.cv y)))) p0018 p0036
  have p0038_e00_recanon : Nominal.NPrf (syn_wb (.classMem (.cv x) (syn_cfv F A)) (syn_wex z (syn_wa (.classMem (.cv x) (.cv z)) (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cfv syn_cio syn_cuni syn_wex syn_wa syn_csn syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
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
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                ·
                  exact Nominal.RecanonTransportDev.TRecanonWff.same _
                ·
                  exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              ·
                apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                ·
                  exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
                ·
                  exact Nominal.RecanonTransportDev.TRecanonWff.same _
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
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                ·
                  exact Nominal.RecanonTransportDev.TRecanonWff.same _
                ·
                  exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              ·
                apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                ·
                  exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
                ·
                  exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0000
  have p0038 :=
    @g_bitri (.classMem (.cv x) (syn_cfv F A)) (syn_wex z (syn_wa (.classMem (.cv x) (.cv z)) (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z)))))) (syn_wa (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (syn_wbr A F (.cv y)))) (syn_weu y (syn_wbr A F (.cv y)))) p0038_e00_recanon p0037
  have p0039 :=
    @g_eqabi (syn_wa (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (syn_wbr A F (.cv y)))) (syn_weu y (syn_wbr A F (.cv y)))) x (syn_cfv F A) dv_cache_0014 p0038
  exact p0039

noncomputable def g_fvres
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (.classMem A B) (.classEq (syn_cfv (syn_cres F B) A) (syn_cfv F A))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
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
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((Wff.classMem A B)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cres F B)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_iba (.classMem A B) (syn_wbr A F (.cv x))
  have p0001 :=
    @g_brres A (.cv x) F B
  have p0002 :=
    @g_syl6rbbr (.classMem A B) (syn_wbr A F (.cv x)) (syn_wa (syn_wbr A F (.cv x)) (.classMem A B)) (syn_wbr A (syn_cres F B) (.cv x)) p0000 p0001
  have p0003 :=
    @g_iotabidv (.classMem A B) (syn_wbr A (syn_cres F B) (.cv x)) (syn_wbr A F (.cv x)) x dv_cache_0001 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fv x A (syn_cres F B) dv_cache_0002 dv_cache_0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fv x A F dv_cache_0002 dv_cache_0004
  have p0006 :=
    @g_n_3eqtr4g (.classMem A B) (syn_cio x (syn_wbr A (syn_cres F B) (.cv x))) (syn_cio x (syn_wbr A F (.cv x))) (syn_cfv (syn_cres F B) A) (syn_cfv F A) p0003 p0004 p0005
  exact p0006

noncomputable def g_funssfv
    (A : Class) (F : Class) (G : Class) :
    Nominal.NPrf (.imp (syn_w3a (syn_wfun F) (syn_wss G F) (.classMem A (syn_cdm G))) (.classEq (syn_cfv F A) (syn_cfv G A))) := by
  let proofSupport : Finset Var := A.fv ∪ F.fv ∪ G.fv
  have p0000 :=
    @g_fvres A (syn_cdm G) F
  have p0001 :=
    @g_eqcomd (.classMem A (syn_cdm G)) (syn_cfv (syn_cres F (syn_cdm G)) A) (syn_cfv F A) p0000
  have p0002 :=
    @g_funssres F G
  have p0003 :=
    @g_fveq1d (syn_wa (syn_wfun F) (syn_wss G F)) A (syn_cres F (syn_cdm G)) G p0002
  have p0004 :=
    @g_sylan9eqr (.classMem A (syn_cdm G)) (syn_wa (syn_wfun F) (syn_wss G F)) (syn_cfv F A) (syn_cfv (syn_cres F (syn_cdm G)) A) (syn_cfv G A) p0001 p0003
  have p0005 :=
    @g_n_3impa (syn_wfun F) (syn_wss G F) (.classMem A (syn_cdm G)) (.classEq (syn_cfv F A) (syn_cfv G A)) p0004
  exact p0005

noncomputable def g_tz6_12_1
    (y : Var) (A : Class) (B : Class) (F : Class) (dv_A_y : y ∉ A.fv) (dv_F_y : y ∉ F.fv) :
    Nominal.NPrf (.imp (syn_wa (syn_wbr A F B) (syn_weu y (syn_wbr A F (.cv y)))) (.classEq (syn_cfv F A) B)) := by
  let proofSupport : Finset Var := ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ F.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_y : x ≠ y := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((syn_wbr A F (.cv y))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_y, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_wbr A F (.cv x))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, fresh_y_ne_x, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_wbr A F B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_nfv (syn_wbr A F (.cv y)) x dv_cache_0001
  have p0001 :=
    @g_nfv (syn_wbr A F (.cv x)) y dv_cache_0002
  have p0002 :=
    @g_breq2 (.cv y) (.cv x) A F
  have p0003_e02_recanon : Nominal.NPrf (.imp (.objEq y x) (syn_wb (syn_wbr A F (.cv y)) (syn_wbr A F (.cv x)))) :=
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
      p0002
  have p0003 :=
    @g_cbveu (syn_wbr A F (.cv y)) (syn_wbr A F (.cv x)) y x p0000 p0001 p0003_e02_recanon
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fv x A F dv_cache_0003 dv_cache_0004
  have p0005 :=
    @g_brrelrnex A B F
  have p0006 :=
    @g_adantr (syn_wbr A F B) (.classMem B (syn_cvv)) (syn_weu x (syn_wbr A F (.cv x))) p0005
  have p0007 :=
    @g_breq2 (.cv x) B A F
  have p0008 :=
    @g_iota2 (syn_wbr A F (.cv x)) (syn_wbr A F B) x B (syn_cvv) dv_cache_0005 dv_cache_0006 p0007
  have p0009 :=
    @g_biimpd (syn_wa (.classMem B (syn_cvv)) (syn_weu x (syn_wbr A F (.cv x)))) (syn_wbr A F B) (.classEq (syn_cio x (syn_wbr A F (.cv x))) B) p0008
  have p0010 :=
    @g_ex (.classMem B (syn_cvv)) (syn_weu x (syn_wbr A F (.cv x))) (.imp (syn_wbr A F B) (.classEq (syn_cio x (syn_wbr A F (.cv x))) B)) p0009
  have p0011 :=
    @g_com23 (.classMem B (syn_cvv)) (syn_weu x (syn_wbr A F (.cv x))) (syn_wbr A F B) (.classEq (syn_cio x (syn_wbr A F (.cv x))) B) p0010
  have p0012 :=
    @g_imp3a (.classMem B (syn_cvv)) (syn_wbr A F B) (syn_weu x (syn_wbr A F (.cv x))) (.classEq (syn_cio x (syn_wbr A F (.cv x))) B) p0011
  have p0013 :=
    @g_mpcom (.classMem B (syn_cvv)) (syn_wa (syn_wbr A F B) (syn_weu x (syn_wbr A F (.cv x)))) (.classEq (syn_cio x (syn_wbr A F (.cv x))) B) p0006 p0012
  have p0014 :=
    @g_syl5eq (syn_wa (syn_wbr A F B) (syn_weu x (syn_wbr A F (.cv x)))) (syn_cfv F A) (syn_cio x (syn_wbr A F (.cv x))) B p0004 p0013
  have p0015 :=
    @g_sylan2b (syn_weu y (syn_wbr A F (.cv y))) (syn_wbr A F B) (syn_weu x (syn_wbr A F (.cv x))) (.classEq (syn_cfv F A) B) p0003 p0014
  exact p0015

noncomputable def g_tz6_12_2
    (y : Var) (A : Class) (F : Class) (dv_A_y : y ∉ A.fv) (dv_F_y : y ∉ F.fv) :
    Nominal.NPrf (.imp (.neg (syn_weu y (syn_wbr A F (.cv y)))) (.classEq (syn_cfv F A) (syn_c0))) := by
  let proofSupport : Finset Var := ({y} : Finset Var) ∪ A.fv ∪ F.fv
  let x : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
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
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
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
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0006 : y ∉ ((Wff.objEq x z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_wa (syn_wex y (syn_wa (.objMem z y) (syn_wbr A F (.cv y)))) (syn_weu y (syn_wbr A F (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_weu, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, fresh_x_ne_y, fresh_x_not_A, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((Class.cab x (syn_wa (syn_wex y (syn_wa (.objMem x y) (syn_wbr A F (.cv y)))) (syn_weu y (syn_wbr A F (.cv y)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_weu, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_A, fresh_z_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : z ∉ ((Wff.neg (syn_weu y (syn_wbr A F (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_weu, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_y, fresh_z_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_fv3 x y A F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @g_vex z
  have p0002 :=
    @g_elequ1 x z y
  have p0003 :=
    @g_anbi1d (.objEq x z) (.objMem x y) (.objMem z y) (syn_wbr A F (.cv y)) p0002
  have p0004 :=
    @g_exbidv (.objEq x z) (syn_wa (.objMem x y) (syn_wbr A F (.cv y))) (syn_wa (.objMem z y) (syn_wbr A F (.cv y))) y dv_cache_0006 p0003
  have p0005 :=
    @g_anbi1d (.objEq x z) (syn_wex y (syn_wa (.objMem x y) (syn_wbr A F (.cv y)))) (syn_wex y (syn_wa (.objMem z y) (syn_wbr A F (.cv y)))) (syn_weu y (syn_wbr A F (.cv y))) p0004
  have p0006_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv x) (.cv z)) (syn_wb (syn_wa (syn_wex y (syn_wa (.objMem x y) (syn_wbr A F (.cv y)))) (syn_weu y (syn_wbr A F (.cv y)))) (syn_wa (syn_wex y (syn_wa (.objMem z y) (syn_wbr A F (.cv y)))) (syn_weu y (syn_wbr A F (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wa syn_wex syn_weu syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_weu, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0005
  have p0006 :=
    @g_elab (syn_wa (syn_wex y (syn_wa (.objMem x y) (syn_wbr A F (.cv y)))) (syn_weu y (syn_wbr A F (.cv y)))) (syn_wa (syn_wex y (syn_wa (.objMem z y) (syn_wbr A F (.cv y)))) (syn_weu y (syn_wbr A F (.cv y)))) x (.cv z) dv_cache_0007 dv_cache_0008 p0001 p0006_e01_recanon
  have p0007 :=
    @g_simprbi (.classMem (.cv z) (.cab x (syn_wa (syn_wex y (syn_wa (.objMem x y) (syn_wbr A F (.cv y)))) (syn_weu y (syn_wbr A F (.cv y)))))) (syn_wex y (syn_wa (.objMem z y) (syn_wbr A F (.cv y)))) (syn_weu y (syn_wbr A F (.cv y))) p0006
  have p0008 :=
    @g_con3i (.classMem (.cv z) (.cab x (syn_wa (syn_wex y (syn_wa (.objMem x y) (syn_wbr A F (.cv y)))) (syn_weu y (syn_wbr A F (.cv y)))))) (syn_weu y (syn_wbr A F (.cv y))) p0007
  have p0009 :=
    @g_eq0rdv (.neg (syn_weu y (syn_wbr A F (.cv y)))) z (.cab x (syn_wa (syn_wex y (syn_wa (.objMem x y) (syn_wbr A F (.cv y)))) (syn_weu y (syn_wbr A F (.cv y))))) dv_cache_0009 dv_cache_0010 p0008
  have p0010_e00_recanon : Nominal.NPrf (.classEq (syn_cfv F A) (.cab x (syn_wa (syn_wex y (syn_wa (.objMem x y) (syn_wbr A F (.cv y)))) (syn_weu y (syn_wbr A F (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cfv syn_cio syn_cuni syn_wex syn_wa syn_csn syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_weu, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.classEq
        ·
          exact Nominal.RecanonTransportDev.TRecanonClass.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonClass.cab
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0000
  have p0010 :=
    @g_syl5eq (.neg (syn_weu y (syn_wbr A F (.cv y)))) (syn_cfv F A) (.cab x (syn_wa (syn_wex y (syn_wa (.objMem x y) (syn_wbr A F (.cv y)))) (syn_weu y (syn_wbr A F (.cv y))))) (syn_c0) p0010_e00_recanon p0009
  exact p0010

noncomputable def g_tz6_12c
    (y : Var) (A : Class) (B : Class) (F : Class) (dv_A_y : y ∉ A.fv) (dv_F_y : y ∉ F.fv) :
    Nominal.NPrf (.imp (syn_weu y (syn_wbr A F (.cv y))) (syn_wb (.classEq (syn_cfv F A) B) (syn_wbr A F B))) := by
  let proofSupport : Finset Var := ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ F.fv
  have dv_cache_0001 : y ∉ ((syn_wbr A F (syn_cfv F A))).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_euex (syn_wbr A F (.cv y)) y
  have p0001 :=
    @g_nfeu1 (syn_wbr A F (.cv y)) y
  have p0002 :=
    @g_nfv (syn_wbr A F (syn_cfv F A)) y dv_cache_0001
  have p0003 :=
    @g_nfim (syn_weu y (syn_wbr A F (.cv y))) (syn_wbr A F (syn_cfv F A)) y p0001 p0002
  have p0004 :=
    @g_tz6_12_1 y A (.cv y) F dv_cache_0002 dv_cache_0003
  have p0005 :=
    @g_expcom (syn_wbr A F (.cv y)) (syn_weu y (syn_wbr A F (.cv y))) (.classEq (syn_cfv F A) (.cv y)) p0004
  have p0006 :=
    @g_breq2 (syn_cfv F A) (.cv y) A F
  have p0007 :=
    @g_biimprd (.classEq (syn_cfv F A) (.cv y)) (syn_wbr A F (syn_cfv F A)) (syn_wbr A F (.cv y)) p0006
  have p0008 :=
    @g_syli (syn_wbr A F (.cv y)) (syn_weu y (syn_wbr A F (.cv y))) (.classEq (syn_cfv F A) (.cv y)) (syn_wbr A F (syn_cfv F A)) p0005 p0007
  have p0009 :=
    @g_com12 (syn_weu y (syn_wbr A F (.cv y))) (syn_wbr A F (.cv y)) (syn_wbr A F (syn_cfv F A)) p0008
  have p0010 :=
    @g_exlimi (syn_wbr A F (.cv y)) (.imp (syn_weu y (syn_wbr A F (.cv y))) (syn_wbr A F (syn_cfv F A))) y p0003 p0009
  have p0011 :=
    @g_mpcom (syn_wex y (syn_wbr A F (.cv y))) (syn_weu y (syn_wbr A F (.cv y))) (syn_wbr A F (syn_cfv F A)) p0000 p0010
  have p0012 :=
    @g_breq2 (syn_cfv F A) B A F
  have p0013 :=
    @g_syl5ibcom (syn_weu y (syn_wbr A F (.cv y))) (syn_wbr A F (syn_cfv F A)) (.classEq (syn_cfv F A) B) (syn_wbr A F B) p0011 p0012
  have p0014 :=
    @g_tz6_12_1 y A B F dv_cache_0002 dv_cache_0003
  have p0015 :=
    @g_expcom (syn_wbr A F B) (syn_weu y (syn_wbr A F (.cv y))) (.classEq (syn_cfv F A) B) p0014
  have p0016 :=
    @g_impbid (syn_weu y (syn_wbr A F (.cv y))) (.classEq (syn_cfv F A) B) (syn_wbr A F B) p0013 p0015
  exact p0016

noncomputable def g_ndmfv
    (A : Class) (F : Class) :
    Nominal.NPrf (.imp (.neg (.classMem A (syn_cdm F))) (.classEq (syn_cfv F A) (syn_c0))) := by
  let proofSupport : Finset Var := A.fv ∪ F.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (F).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eldm x A F dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_euex (syn_wbr A F (.cv x)) x
  have p0002 :=
    @g_con3i (syn_weu x (syn_wbr A F (.cv x))) (syn_wex x (syn_wbr A F (.cv x))) p0001
  have p0003 :=
    @g_tz6_12_2 x A F dv_cache_0001 dv_cache_0002
  have p0004 :=
    @g_syl (.neg (syn_wex x (syn_wbr A F (.cv x)))) (.neg (syn_weu x (syn_wbr A F (.cv x)))) (.classEq (syn_cfv F A) (syn_c0)) p0002 p0003
  have p0005 :=
    @g_sylnbi (.classMem A (syn_cdm F)) (syn_wex x (syn_wbr A F (.cv x))) (.classEq (syn_cfv F A) (syn_c0)) p0000 p0004
  exact p0005

noncomputable def g_elfvdm
    (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cfv F B)) (.classMem B (syn_cdm F))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  have p0000 :=
    @g_ne0i (syn_cfv F B) A
  have p0001 :=
    @g_ndmfv B F
  have p0002 :=
    @g_necon1ai (.classMem B (syn_cdm F)) (syn_cfv F B) (syn_c0) p0001
  have p0003 :=
    @g_syl (.classMem A (syn_cfv F B)) (syn_wne (syn_cfv F B) (syn_c0)) (.classMem B (syn_cdm F)) p0000 p0002
  exact p0003

#print axioms g_elfvdm

end NFChoice.DirectNominalPrf.WPPReplay
