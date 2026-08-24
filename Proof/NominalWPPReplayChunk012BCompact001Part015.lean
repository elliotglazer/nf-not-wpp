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
import NominalAlphaPrefix050WppNotmem014Data
import NominalAlphaGlobal051ProofData001
import NominalAlphaRelease004Coarse052
import NominalAlphaRelease004Coarse053
import NominalAlphaRelease004Coarse054
import NominalAlphaRelease004Coarse055
import NominalAlphaRelease004Coarse056
import NominalAlphaRelease004Coarse057
import NominalAlphaRelease004Coarse058
import NominalAlphaRelease004Coarse059
import NominalAlphaRelease004Coarse060
import NominalAlphaRelease004Coarse061
import NominalAlphaRelease004Coarse062
import NominalAlphaRelease004Coarse063
import NominalAlphaRelease004Coarse064
import NominalAlphaRelease004Coarse065
import NominalAlphaRelease004Coarse066
import NominalAlphaRelease004Coarse067
import NominalAlphaRelease004Coarse068
import NominalAlphaRelease004Coarse069
import NominalAlphaRelease004Coarse070
import NominalAlphaRelease004Coarse071
import NominalAlphaRelease004Coarse072
import NominalAlphaRelease004Coarse073
import NominalAlphaRelease004Coarse074
import NominalAlphaRelease004Coarse075
import NominalAlphaRelease004Coarse076
import NominalAlphaRelease004Coarse077
import NominalAlphaRelease004Coarse078
import NominalAlphaRelease004Coarse079
import NominalAlphaRelease004Coarse080
import NominalAlphaRelease004Coarse081
import NominalAlphaRelease004Coarse082
import NominalAlphaRelease004Coarse083
import NominalAlphaRelease004Coarse084
import NominalAlphaRelease004Coarse085
import NominalAlphaRelease004Coarse086
import NominalAlphaRelease004Coarse087
import NominalAlphaHygieneV5Probe088
import NominalAlphaRelease004Coarse089
import NominalAlphaRelease004Coarse090
import NominalAlphaHygieneV5Coalesced091B
import NominalAlphaHygieneV5Coalesced092
import NominalAlphaHygieneV5Coalesced093
import NominalAlphaHygieneV5Coalesced094
import NominalAlphaHygieneV5Coalesced095
import NominalAlphaHygieneV5Coalesced096
import NominalAlphaHygieneV5Coalesced097
import NominalNFLiteralBaseFour
import NominalNFLiteralXpViaCompletenessDev003
import NominalNFLiteralRemainingViaCompletenessDev001
import NominalDefinitionLeafHandlersCanonical001
import NominalDefinitionLeafHandlersObjExtCompat001
import NominalRecanonTransportCompat001
import NominalWPPReplayChunk012BCompact001Part014

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

noncomputable def g_cbvmpt
    (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (hyp_cbvmpt_1 : Nominal.NPrf (syn_wnfc y B)) (hyp_cbvmpt_2 : Nominal.NPrf (syn_wnfc x C)) (hyp_cbvmpt_3 : Nominal.NPrf (.imp (.objEq x y) (.classEq B C))) :
    Nominal.NPrf (.classEq (syn_cmpt x A B) (syn_cmpt y A C)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  let z : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_w : y ≠ w :=
    Ne.symm fresh_w_ne_y
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_C : w ∉ C.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have dv_cache_0001 : w ∉ ((syn_wa (.classMem (.cv x) A) (.classEq (.cv z) B))).fv := by
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, fresh_w_not_A, fresh_w_ne_z, fresh_w_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classMem (.cv w) A)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_w, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ≠ w := by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ w from (by exact fresh_x_ne_w))
  have dv_cache_0004 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0005 : z ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have dv_cache_0006 : y ∉ ((Wff.classMem (.cv w) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_w, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : w ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show w ≠ y from (by exact fresh_w_ne_y))
  have dv_cache_0009 : w ∉ ((syn_wa (.classMem (.cv y) A) (.classEq (.cv z) C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_y, fresh_w_not_A, fresh_w_ne_z, fresh_w_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : w ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show w ≠ z from (by exact fresh_w_ne_z))
  have dv_cache_0012 : z ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show z ≠ y from (by exact fresh_z_ne_y))
  have dv_cache_0013 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : z ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : z ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    @g_nfv (syn_wa (.classMem (.cv x) A) (.classEq (.cv z) B)) w dv_cache_0001
  have p0001 :=
    @g_nfv (.classMem (.cv w) A) x dv_cache_0002
  have p0002 :=
    @g_nfs1v (.classEq (.cv z) B) x w dv_cache_0003
  have p0003 :=
    @g_nfan (.classMem (.cv w) A) (syn_wsb w x (.classEq (.cv z) B)) x p0001 p0002
  have p0004 :=
    @g_eleq1 (.cv x) (.cv w) A
  have p0005 :=
    @g_sbequ12 (.classEq (.cv z) B) x w
  have p0006_e01_recanon : Nominal.NPrf (.imp (.classEq (.cv x) (.cv w)) (syn_wb (.classEq (.cv z) B) (syn_wsb w x (.classEq (.cv z) B)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wsb syn_wa syn_wex
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsb]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0005
  have p0006 :=
    @g_anbi12d (.classEq (.cv x) (.cv w)) (.classMem (.cv x) A) (.classMem (.cv w) A) (.classEq (.cv z) B) (syn_wsb w x (.classEq (.cv z) B)) p0004 p0006_e01_recanon
  have p0007_e02_recanon : Nominal.NPrf (.imp (.objEq x w) (syn_wb (syn_wa (.classMem (.cv x) A) (.classEq (.cv z) B)) (syn_wa (.classMem (.cv w) A) (syn_wsb w x (.classEq (.cv z) B))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsb, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0006
  have p0007 :=
    @g_cbvopab1 (syn_wa (.classMem (.cv x) A) (.classEq (.cv z) B)) (syn_wa (.classMem (.cv w) A) (syn_wsb w x (.classEq (.cv z) B))) x z w dv_cache_0004 dv_cache_0005 p0000 p0003 p0007_e02_recanon
  have p0008 :=
    @g_nfv (.classMem (.cv w) A) y dv_cache_0006
  have p0009 :=
    @g_nfeq2 y (.cv z) B dv_cache_0007 hyp_cbvmpt_1
  have p0010 :=
    @g_nfsb (.classEq (.cv z) B) x w y dv_cache_0008 p0009
  have p0011 :=
    @g_nfan (.classMem (.cv w) A) (syn_wsb w x (.classEq (.cv z) B)) y p0008 p0010
  have p0012 :=
    @g_nfv (syn_wa (.classMem (.cv y) A) (.classEq (.cv z) C)) w dv_cache_0009
  have p0013 :=
    @g_eleq1 (.cv w) (.cv y) A
  have p0014 :=
    @g_sbequ (.classEq (.cv z) B) w y x
  have p0015 :=
    @g_nfeq2 x (.cv z) C dv_cache_0010 hyp_cbvmpt_2
  have p0016_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv x) (.cv y)) (.classEq B C)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      hyp_cbvmpt_3
  have p0016 :=
    @g_eqeq2d (.classEq (.cv x) (.cv y)) B C (.cv z) p0016_e00_recanon
  have p0017_e01_recanon : Nominal.NPrf (.imp (.objEq x y) (syn_wb (.classEq (.cv z) B) (.classEq (.cv z) C))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0016
  have p0017 :=
    @g_sbie (.classEq (.cv z) B) (.classEq (.cv z) C) x y p0015 p0017_e01_recanon
  have p0018_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv w) (.cv y)) (syn_wb (syn_wsb w x (.classEq (.cv z) B)) (syn_wsb y x (.classEq (.cv z) B)))) :=
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
      p0014
  have p0018 :=
    @g_syl6bb (.classEq (.cv w) (.cv y)) (syn_wsb w x (.classEq (.cv z) B)) (syn_wsb y x (.classEq (.cv z) B)) (.classEq (.cv z) C) p0018_e00_recanon p0017
  have p0019 :=
    @g_anbi12d (.classEq (.cv w) (.cv y)) (.classMem (.cv w) A) (.classMem (.cv y) A) (syn_wsb w x (.classEq (.cv z) B)) (.classEq (.cv z) C) p0013 p0018
  have p0020_e02_recanon : Nominal.NPrf (.imp (.objEq w y) (syn_wb (syn_wa (.classMem (.cv w) A) (syn_wsb w x (.classEq (.cv z) B))) (syn_wa (.classMem (.cv y) A) (.classEq (.cv z) C)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wa syn_wsb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsb, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0019
  have p0020 :=
    @g_cbvopab1 (syn_wa (.classMem (.cv w) A) (syn_wsb w x (.classEq (.cv z) B))) (syn_wa (.classMem (.cv y) A) (.classEq (.cv z) C)) w z y dv_cache_0011 dv_cache_0012 p0011 p0012 p0020_e02_recanon
  have p0021 :=
    @g_eqtri (syn_copab x z (syn_wa (.classMem (.cv x) A) (.classEq (.cv z) B))) (syn_copab w z (syn_wa (.classMem (.cv w) A) (syn_wsb w x (.classEq (.cv z) B)))) (syn_copab y z (syn_wa (.classMem (.cv y) A) (.classEq (.cv z) C))) p0007 p0020
  have p0022 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_mpt x z A B dv_cache_0013 dv_cache_0014 dv_cache_0004
  have p0023 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_mpt y z A C dv_cache_0013 dv_cache_0015 dv_cache_0016
  have p0024 :=
    @g_n_3eqtr4i (syn_copab x z (syn_wa (.classMem (.cv x) A) (.classEq (.cv z) B))) (syn_copab y z (syn_wa (.classMem (.cv y) A) (.classEq (.cv z) C))) (syn_cmpt x A B) (syn_cmpt y A C) p0021 p0022 p0023
  exact p0024

noncomputable def g_cbvmptv
    (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_C_x : x ∉ C.fv) (hyp_cbvmptv_1 : Nominal.NPrf (.imp (.objEq x y) (.classEq B C))) :
    Nominal.NPrf (.classEq (syn_cmpt x A B) (syn_cmpt y A C)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  have dv_cache_0001 : y ∉ (B).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (C).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_nfcv y B dv_cache_0001
  have p0001 :=
    @g_nfcv x C dv_cache_0002
  have p0002 :=
    @g_cbvmpt x y A B C dv_cache_0003 dv_cache_0004 p0000 p0001 hyp_cbvmptv_1
  exact p0002

noncomputable def g_mptpreima
    (x : Var) (A : Class) (B : Class) (C : Class) (F : Class) (dv_C_x : x ∉ C.fv) (hyp_dmmpt2_1 : Nominal.NPrf (.classEq F (syn_cmpt x A B))) :
    Nominal.NPrf (.classEq (syn_cima (syn_ccnv F) C) (syn_crab x A (.classMem B C))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0004 : y ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have dv_cache_0007 : y ∉ ((Wff.classMem (.cv x) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_mpt x y A B dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_eqtri F (syn_cmpt x A B) (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) hyp_dmmpt2_1 p0000
  have p0002 :=
    @g_cnveqi F (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) p0001
  have p0003 :=
    @g_cnvopab (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B)) x y dv_cache_0003
  have p0004 :=
    @g_eqtri (syn_ccnv F) (syn_ccnv (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B)))) (syn_copab y x (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) p0002 p0003
  have p0005 :=
    @g_imaeq1i (syn_ccnv F) (syn_copab y x (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) C p0004
  have p0006 :=
    @g_dfima3 (syn_copab y x (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) C
  have p0007 :=
    @g_resopab (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B)) y x C dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0008 :=
    @g_rneqi (syn_cres (syn_copab y x (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) C) (syn_copab y x (syn_wa (.classMem (.cv y) C) (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B)))) p0007
  have p0009 :=
    @g_ancom (.classMem (.cv y) C) (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))
  have p0010 :=
    @g_anass (.classMem (.cv x) A) (.classEq (.cv y) B) (.classMem (.cv y) C)
  have p0011 :=
    @g_bitri (syn_wa (.classMem (.cv y) C) (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) (syn_wa (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B)) (.classMem (.cv y) C)) (syn_wa (.classMem (.cv x) A) (syn_wa (.classEq (.cv y) B) (.classMem (.cv y) C))) p0009 p0010
  have p0012 :=
    @g_exbii (syn_wa (.classMem (.cv y) C) (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) (syn_wa (.classMem (.cv x) A) (syn_wa (.classEq (.cv y) B) (.classMem (.cv y) C))) y p0011
  have p0013 :=
    @g_n_19_42v (.classMem (.cv x) A) (syn_wa (.classEq (.cv y) B) (.classMem (.cv y) C)) y dv_cache_0007
  have p0014 :=
    (by simpa [NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfClelGoal, syn_wb, syn_wex, syn_wa, Wff.biimp, Wff.ex, Wff.conj, Wff.neg] using (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV y B C dv_cache_0002 dv_cache_0004))
  have p0015 :=
    @g_bicomi (.classMem B C) (syn_wex y (syn_wa (.classEq (.cv y) B) (.classMem (.cv y) C))) p0014
  have p0016 :=
    @g_anbi2i (syn_wex y (syn_wa (.classEq (.cv y) B) (.classMem (.cv y) C))) (.classMem B C) (.classMem (.cv x) A) p0015
  have p0017 :=
    @g_bitri (syn_wex y (syn_wa (.classMem (.cv x) A) (syn_wa (.classEq (.cv y) B) (.classMem (.cv y) C)))) (syn_wa (.classMem (.cv x) A) (syn_wex y (syn_wa (.classEq (.cv y) B) (.classMem (.cv y) C)))) (syn_wa (.classMem (.cv x) A) (.classMem B C)) p0013 p0016
  have p0018 :=
    @g_bitri (syn_wex y (syn_wa (.classMem (.cv y) C) (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B)))) (syn_wex y (syn_wa (.classMem (.cv x) A) (syn_wa (.classEq (.cv y) B) (.classMem (.cv y) C)))) (syn_wa (.classMem (.cv x) A) (.classMem B C)) p0012 p0017
  have p0019 :=
    @g_abbii (syn_wex y (syn_wa (.classMem (.cv y) C) (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B)))) (syn_wa (.classMem (.cv x) A) (.classMem B C)) x p0018
  have p0020 :=
    @g_rnopab (syn_wa (.classMem (.cv y) C) (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) y x dv_cache_0006
  have p0021 :=
    (by simpa [syn_crab] using (Nominal.classEqRefl (syn_crab x A (.classMem B C))))
  have p0022 :=
    @g_n_3eqtr4i (.cab x (syn_wex y (syn_wa (.classMem (.cv y) C) (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))))) (.cab x (syn_wa (.classMem (.cv x) A) (.classMem B C))) (syn_crn (syn_copab y x (syn_wa (.classMem (.cv y) C) (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))))) (syn_crab x A (.classMem B C)) p0019 p0020 p0021
  have p0023 :=
    @g_eqtri (syn_crn (syn_cres (syn_copab y x (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) C)) (syn_crn (syn_copab y x (syn_wa (.classMem (.cv y) C) (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))))) (syn_crab x A (.classMem B C)) p0008 p0022
  have p0024 :=
    @g_eqtri (syn_cima (syn_copab y x (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) C) (syn_crn (syn_cres (syn_copab y x (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) C)) (syn_crab x A (.classMem B C)) p0006 p0023
  have p0025 :=
    @g_eqtri (syn_cima (syn_ccnv F) C) (syn_cima (syn_copab y x (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) C) (syn_crab x A (.classMem B C)) p0005 p0024
  exact p0025

noncomputable def g_dmmpt
    (x : Var) (A : Class) (B : Class) (F : Class) (hyp_dmmpt2_1 : Nominal.NPrf (.classEq F (syn_cmpt x A B))) :
    Nominal.NPrf (.classEq (syn_cdm F) (syn_crab x A (.classMem B (syn_cvv)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ F.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
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
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0004 : y ∉ ((Wff.classMem (.cv x) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_mpt x y A B dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_eqtri F (syn_cmpt x A B) (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) hyp_dmmpt2_1 p0000
  have p0002 :=
    @g_dmeqi F (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) p0001
  have p0003 :=
    @g_dmopab (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B)) x y dv_cache_0003
  have p0004 :=
    @g_n_19_42v (.classMem (.cv x) A) (.classEq (.cv y) B) y dv_cache_0004
  have p0005 :=
    @g_isset y B dv_cache_0002
  have p0006 :=
    @g_anbi2i (.classMem B (syn_cvv)) (syn_wex y (.classEq (.cv y) B)) (.classMem (.cv x) A) p0005
  have p0007 :=
    @g_bitr4i (syn_wex y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) (syn_wa (.classMem (.cv x) A) (syn_wex y (.classEq (.cv y) B))) (syn_wa (.classMem (.cv x) A) (.classMem B (syn_cvv))) p0004 p0006
  have p0008 :=
    @g_abbii (syn_wex y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) (syn_wa (.classMem (.cv x) A) (.classMem B (syn_cvv))) x p0007
  have p0009 :=
    (by simpa [syn_crab] using (Nominal.classEqRefl (syn_crab x A (.classMem B (syn_cvv)))))
  have p0010 :=
    @g_eqtr4i (.cab x (syn_wex y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B)))) (.cab x (syn_wa (.classMem (.cv x) A) (.classMem B (syn_cvv)))) (syn_crab x A (.classMem B (syn_cvv))) p0008 p0009
  have p0011 :=
    @g_n_3eqtri (syn_cdm F) (syn_cdm (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B)))) (.cab x (syn_wex y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B)))) (syn_crab x A (.classMem B (syn_cvv))) p0002 p0003 p0010
  exact p0011

noncomputable def g_rnmpt
    (x : Var) (y : Var) (A : Class) (B : Class) (F : Class) (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) (hyp_rnmpt_1 : Nominal.NPrf (.classEq F (syn_cmpt x A B))) :
    Nominal.NPrf (.classEq (syn_crn F) (.cab y (syn_wrex x A (.classEq (.cv y) B)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ F.fv
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
  have dv_cache_0003 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_mpt x y A B dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_eqtri F (syn_cmpt x A B) (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) hyp_rnmpt_1 p0000
  have p0002 :=
    @g_rneqi F (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) p0001
  have p0003 :=
    @g_rnopab2 x y A B dv_cache_0003
  have p0004 :=
    @g_eqtri (syn_crn F) (syn_crn (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B)))) (.cab y (syn_wrex x A (.classEq (.cv y) B))) p0002 p0003
  exact p0004

noncomputable def g_mptfng
    (x : Var) (A : Class) (B : Class) (F : Class) (dv_A_x : x ∉ A.fv) (hyp_mptfng_1 : Nominal.NPrf (.classEq F (syn_cmpt x A B))) :
    Nominal.NPrf (syn_wb (syn_wral x A (.classMem B (syn_cvv))) (syn_wfn F A)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ F.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
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
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0004 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_mpt x y A B dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_eqtri F (syn_cmpt x A B) (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) hyp_mptfng_1 p0000
  have p0002 :=
    @g_fnopab2g x y A B F dv_cache_0004 dv_cache_0001 dv_cache_0002 dv_cache_0003 p0001
  exact p0002

noncomputable def g_fnmpt
    (x : Var) (A : Class) (B : Class) (F : Class) (V : Class) (dv_A_x : x ∉ A.fv) (hyp_mptfng_1 : Nominal.NPrf (.classEq F (syn_cmpt x A B))) :
    Nominal.NPrf (.imp (syn_wral x A (.classMem B V)) (syn_wfn F A)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ F.fv ∪ V.fv
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elex B V
  have p0001 :=
    @g_ralimi (.classMem B V) (.classMem B (syn_cvv)) x A p0000
  have p0002 :=
    @g_mptfng x A B F dv_cache_0001 hyp_mptfng_1
  have p0003 :=
    @g_sylib (syn_wral x A (.classMem B V)) (syn_wral x A (.classMem B (syn_cvv))) (syn_wfn F A) p0001 p0002
  exact p0003

noncomputable def g_fnmpti
    (x : Var) (A : Class) (B : Class) (F : Class) (dv_A_x : x ∉ A.fv) (hyp_fnmpti_1 : Nominal.NPrf (.classMem B (syn_cvv))) (hyp_fnmpti_2 : Nominal.NPrf (.classEq F (syn_cmpt x A B))) :
    Nominal.NPrf (syn_wfn F A) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ F.fv
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_rgenw (.classMem B (syn_cvv)) x A hyp_fnmpti_1
  have p0001 :=
    @g_mptfng x A B F dv_cache_0001 hyp_fnmpti_2
  have p0002 :=
    @g_mpbi (syn_wral x A (.classMem B (syn_cvv))) (syn_wfn F A) p0000 p0001
  exact p0002

noncomputable def g_fmpt
    (x : Var) (A : Class) (B : Class) (C : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (hyp_fmpt_1 : Nominal.NPrf (.classEq F (syn_cmpt x A C))) :
    Nominal.NPrf (syn_wb (syn_wral x A (.classMem C B)) (syn_wf F A B)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
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
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0005 : x ∉ ((Wff.classMem (.cv y) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((syn_wral x A (.classMem C B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_C, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_fnmpt x A C F B dv_cache_0001 hyp_fmpt_1
  have p0001 :=
    @g_rnmpt x y A C F dv_cache_0002 dv_cache_0003 dv_cache_0004 hyp_fmpt_1
  have p0002 :=
    @g_r19_29 (.classMem C B) (.classEq (.cv y) C) x A
  have p0003 :=
    @g_eleq1 (.cv y) C B
  have p0004 :=
    @g_biimparc (.classEq (.cv y) C) (.classMem (.cv y) B) (.classMem C B) p0003
  have p0005 :=
    @g_rexlimivw (syn_wa (.classMem C B) (.classEq (.cv y) C)) (.classMem (.cv y) B) x A dv_cache_0005 p0004
  have p0006 :=
    @g_syl (syn_wa (syn_wral x A (.classMem C B)) (syn_wrex x A (.classEq (.cv y) C))) (syn_wrex x A (syn_wa (.classMem C B) (.classEq (.cv y) C))) (.classMem (.cv y) B) p0002 p0005
  have p0007 :=
    @g_ex (syn_wral x A (.classMem C B)) (syn_wrex x A (.classEq (.cv y) C)) (.classMem (.cv y) B) p0006
  have p0008 :=
    @g_abssdv (syn_wral x A (.classMem C B)) (syn_wrex x A (.classEq (.cv y) C)) y B dv_cache_0006 dv_cache_0007 p0007
  have p0009 :=
    @g_syl5eqss (syn_wral x A (.classMem C B)) (syn_crn F) (.cab y (syn_wrex x A (.classEq (.cv y) C))) B p0001 p0008
  have p0010 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf F A B)))
  have p0011 :=
    @g_sylanbrc (syn_wral x A (.classMem C B)) (syn_wfn F A) (syn_wss (syn_crn F) B) (syn_wf F A B) p0000 p0009 p0010
  have p0012 :=
    @g_mptpreima x A C B F dv_cache_0008 hyp_fmpt_1
  have p0013 :=
    @g_fimacnv A B F
  have p0014 :=
    @g_syl5reqr (syn_wf F A B) (syn_crab x A (.classMem C B)) (syn_cima (syn_ccnv F) B) A p0012 p0013
  have p0015 :=
    @g_rabid2 (.classMem C B) x A dv_cache_0001
  have p0016 :=
    @g_sylib (syn_wf F A B) (.classEq A (syn_crab x A (.classMem C B))) (syn_wral x A (.classMem C B)) p0014 p0015
  have p0017 :=
    @g_impbii (syn_wral x A (.classMem C B)) (syn_wf F A B) p0011 p0016
  exact p0017

noncomputable def g_fmpti
    (x : Var) (A : Class) (B : Class) (C : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (hyp_fmpt_1 : Nominal.NPrf (.classEq F (syn_cmpt x A C))) (hyp_fmpti_2 : Nominal.NPrf (.imp (.classMem (.cv x) A) (.classMem C B))) :
    Nominal.NPrf (syn_wf F A B) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ F.fv
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
  have p0000 :=
    @g_rgen (.classMem C B) x A hyp_fmpti_2
  have p0001 :=
    @g_fmpt x A B C F dv_cache_0001 dv_cache_0002 hyp_fmpt_1
  have p0002 :=
    @g_mpbi (syn_wral x A (.classMem C B)) (syn_wf F A B) p0000 p0001
  exact p0002

noncomputable def g_resmpt
    (x : Var) (A : Class) (B : Class) (C : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (.imp (syn_wss B A) (.classEq (syn_cres (syn_cmpt x A C) B) (syn_cmpt x B C))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
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
  have dv_cache_0001 : x ∉ (B).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
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
  have dv_cache_0006 : y ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_resopab2 (.classEq (.cv y) C) x y B A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_mpt x y A C dv_cache_0004 dv_cache_0006 dv_cache_0005
  have p0002 :=
    @g_reseq1i (syn_cmpt x A C) (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) C))) B p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_mpt x y B C dv_cache_0002 dv_cache_0006 dv_cache_0005
  have p0004 :=
    @g_n_3eqtr4g (syn_wss B A) (syn_cres (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) C))) B) (syn_copab x y (syn_wa (.classMem (.cv x) B) (.classEq (.cv y) C))) (syn_cres (syn_cmpt x A C) B) (syn_cmpt x B C) p0000 p0002 p0003
  exact p0004

noncomputable def g_fvmptg
    (x : Var) (A : Class) (B : Class) (C : Class) (D : Class) (R : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_C_x : x ∉ C.fv) (dv_D_x : x ∉ D.fv) (hyp_fvmptg_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (.classEq B C))) (hyp_fvmptg_2 : Nominal.NPrf (.classEq F (syn_cmpt x D B))) :
    Nominal.NPrf (.imp (syn_wa (.classMem A D) (.classMem C R)) (.classEq (syn_cfv F A) C)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv ∪ F.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0004 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_mpt x y D B dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_eqtri F (syn_cmpt x D B) (syn_copab x y (syn_wa (.classMem (.cv x) D) (.classEq (.cv y) B))) hyp_fvmptg_2 p0000
  have p0002 :=
    @g_fvopab4g x y A B C D R F dv_cache_0004 dv_cache_0005 dv_cache_0002 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0001 dv_cache_0003 hyp_fvmptg_1 p0001
  exact p0002

#print axioms g_fvmptg

end NFChoice.DirectNominalPrf.WPPReplay
