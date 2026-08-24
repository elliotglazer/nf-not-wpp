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
import NominalWPPReplayChunk013Compact001Part031

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

noncomputable def g_ener
     :
    Nominal.NPrf (syn_wbr (syn_cen) (syn_cer) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
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
  have dv_cache_0001 : x ∉ ((syn_cvv)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_cen)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_cen)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((syn_cen)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ (syn_wtru).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ (syn_wtru).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ (syn_wtru).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0011 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0012 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    @g_enex
  have p0001 :=
    @g_a1i (.classMem (syn_cen) (syn_cvv)) syn_wtru p0000
  have p0002 :=
    @g_vvex
  have p0003 :=
    @g_a1i (.classMem (syn_cvv) (syn_cvv)) syn_wtru p0002
  have p0004 :=
    @g_ensymi (.cv x) (.cv y)
  have p0005 :=
    @g_n_3ad2ant3 (syn_wbr (.cv x) (syn_cen) (.cv y)) syn_wtru (syn_wbr (.cv y) (syn_cen) (.cv x)) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))) p0004
  have p0006 :=
    @g_entr (.cv x) (.cv y) (.cv z)
  have p0007 :=
    @g_n_3ad2ant3 (syn_wa (syn_wbr (.cv x) (syn_cen) (.cv y)) (syn_wbr (.cv y) (syn_cen) (.cv z))) syn_wtru (syn_wbr (.cv x) (syn_cen) (.cv z)) (syn_w3a (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)) (.classMem (.cv z) (syn_cvv))) p0006
  have p0008 :=
    @g_iserd syn_wtru x y z (syn_cvv) (syn_cen) (syn_cvv) (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 p0001 p0003 p0005 p0007
  have p0009 :=
    @g_trud (syn_wbr (syn_cen) (syn_cer) (syn_cvv)) p0008
  exact p0009

noncomputable def g_idssen
     :
    Nominal.NPrf (syn_wss (syn_cid) (syn_cen)) := by
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
  have dv_cache_0003 : x ∉ ((syn_cen)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_cen)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_vex y
  have p0001 :=
    @g_ideq (.cv x) (.cv y) p0000
  have p0002 :=
    @g_vex x
  have p0003 :=
    @g_enrflx (.cv x) p0002
  have p0004 :=
    @g_breq2 (.cv x) (.cv y) (.cv x) (syn_cen)
  have p0005_e01_recanon : Nominal.NPrf (.imp (.objEq x y) (syn_wb (syn_wbr (.cv x) (syn_cen) (.cv x)) (syn_wbr (.cv x) (syn_cen) (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_cen syn_copab
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0004
  have p0005 :=
    @g_mpbii (.objEq x y) (syn_wbr (.cv x) (syn_cen) (.cv x)) (syn_wbr (.cv x) (syn_cen) (.cv y)) p0003 p0005_e01_recanon
  have p0006_e00_recanon : Nominal.NPrf (syn_wb (syn_wbr (.cv x) (syn_cid) (.cv y)) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_cid syn_copab
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
      p0001
  have p0006 :=
    @g_sylbi (syn_wbr (.cv x) (syn_cid) (.cv y)) (.objEq x y) (syn_wbr (.cv x) (syn_cen) (.cv y)) p0006_e00_recanon p0005
  have p0007 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) (syn_cid) (.cv y))))
  have p0008 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) (syn_cen) (.cv y))))
  have p0009 :=
    @g_n_3imtr3i (syn_wbr (.cv x) (syn_cid) (.cv y)) (syn_wbr (.cv x) (syn_cen) (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cid)) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cen)) p0006 p0007 p0008
  have p0010 :=
    @g_relssi x y (syn_cid) (syn_cen) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 p0009
  exact p0010

noncomputable def g_dmen
     :
    Nominal.NPrf (.classEq (syn_cdm (syn_cen)) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_idssen
  have p0001 :=
    @g_dmi
  have p0002 :=
    @g_dmss (syn_cid) (syn_cen)
  have p0003 :=
    @g_syl5eqssr (syn_wss (syn_cid) (syn_cen)) (syn_cvv) (syn_cdm (syn_cid)) (syn_cdm (syn_cen)) p0001 p0002
  have p0004 :=
    Nominal.mp p0000 p0003
  have p0005 :=
    @g_vss (syn_cdm (syn_cen))
  have p0006 :=
    @g_mpbi (syn_wss (syn_cvv) (syn_cdm (syn_cen))) (.classEq (syn_cdm (syn_cen)) (syn_cvv)) p0004 p0005
  exact p0006

noncomputable def g_en0
    (A : Class) :
    Nominal.NPrf (syn_wb (syn_wbr A (syn_cen) (syn_c0)) (.classEq A (syn_c0))) := by
  let proofSupport : Finset Var := A.fv
  let f : Var := freshVar proofSupport 0
  have fresh_f : f ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_A : f ∉ A.fv := by
    intro h
    exact fresh_f (h)
  have dv_cache_0001 : f ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : f ∉ ((syn_c0)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : f ∉ ((Wff.classEq A (syn_c0))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_bren A (syn_c0) f dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_f1ocnv A (syn_c0) (.cv f)
  have p0002 :=
    @g_f1o00 A (syn_ccnv (.cv f))
  have p0003 :=
    @g_simprbi (syn_wf1o (syn_ccnv (.cv f)) (syn_c0) A) (.classEq (syn_ccnv (.cv f)) (syn_c0)) (.classEq A (syn_c0)) p0002
  have p0004 :=
    @g_syl (syn_wf1o (.cv f) A (syn_c0)) (syn_wf1o (syn_ccnv (.cv f)) (syn_c0) A) (.classEq A (syn_c0)) p0001 p0003
  have p0005 :=
    @g_exlimiv (syn_wf1o (.cv f) A (syn_c0)) (.classEq A (syn_c0)) f dv_cache_0003 p0004
  have p0006 :=
    @g_sylbi (syn_wbr A (syn_cen) (syn_c0)) (syn_wex f (syn_wf1o (.cv f) A (syn_c0))) (.classEq A (syn_c0)) p0000 p0005
  have p0007 :=
    @g_n_0ex
  have p0008 :=
    @g_enrflx (syn_c0) p0007
  have p0009 :=
    @g_breq1 A (syn_c0) (syn_c0) (syn_cen)
  have p0010 :=
    @g_mpbiri (.classEq A (syn_c0)) (syn_wbr A (syn_cen) (syn_c0)) (syn_wbr (syn_c0) (syn_cen) (syn_c0)) p0008 p0009
  have p0011 :=
    @g_impbii (syn_wbr A (syn_cen) (syn_c0)) (.classEq A (syn_c0)) p0006 p0010
  exact p0011

noncomputable def g_fundmen
    (F : Class) (hyp_fundmen_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wfun F) (syn_wbr (syn_cdm F) (syn_cen) F)) := by
  let proofSupport : Finset Var := F.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let a : Var := freshVar proofSupport 3
  let b : Var := freshVar proofSupport 4
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (h)
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (h)
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_a_not_F : a ∉ F.fv := by
    intro h
    exact fresh_a (h)
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_b_not_F : b ∉ F.fv := by
    intro h
    exact fresh_b (h)
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
  have fresh_x_ne_a : x ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_a_ne_x : a ≠ x :=
    Ne.symm fresh_x_ne_a
  have fresh_x_ne_b : x ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_b_ne_x : b ≠ x :=
    Ne.symm fresh_x_ne_b
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_y_ne_a : y ≠ a := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_a_ne_y : a ≠ y :=
    Ne.symm fresh_y_ne_a
  have fresh_y_ne_b : y ≠ b := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_b_ne_y : b ≠ y :=
    Ne.symm fresh_y_ne_b
  have fresh_z_ne_a : z ≠ a := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_a_ne_z : a ≠ z :=
    Ne.symm fresh_z_ne_a
  have fresh_z_ne_b : z ≠ b := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_b_ne_z : b ≠ z :=
    Ne.symm fresh_z_ne_b
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have dv_cache_0001 : a ∉ ((Class.cv y)).fv := by
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : a ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : a ∉ ((Wff.classMem (.cv y) F)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_y, fresh_a_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : b ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : b ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : b ∉ ((Wff.classMem (.cv z) F)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_z, fresh_b_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : b ∉ ((syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv a))) (.classMem (.cv y) F))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_y, fresh_b_ne_x, fresh_b_ne_a, fresh_b_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : a ∉ ((syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv b))) (.classMem (.cv z) F))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_z, fresh_a_ne_x, fresh_a_ne_b, fresh_a_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : a ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : b ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : x ≠ a := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show x ≠ a from (by exact fresh_x_ne_a))
  have dv_cache_0013 : x ≠ b := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show x ≠ b from (by exact fresh_x_ne_b))
  have dv_cache_0014 : a ≠ b := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0015 : a ∉ ((Wff.objEq y z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_y, fresh_a_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : b ∉ ((Wff.objEq y z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_y, fresh_b_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : a ∉ ((syn_wfun F)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : b ∉ ((syn_wfun F)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : z ∉ ((syn_wfun F)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : x ∉ ((syn_wfun F)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : y ∉ ((syn_wfun F)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : x ∉ ((syn_ccnv (syn_cres (syn_c1st) F))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : y ∉ ((syn_ccnv (syn_cres (syn_c1st) F))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : z ∉ ((syn_ccnv (syn_cres (syn_c1st) F))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0026 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0027 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    @g_ssv F
  have p0001 :=
    @g_n_1stfo
  have p0002 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0003 :=
    @g_fnssresb (syn_cvv) F (syn_c1st)
  have p0004 :=
    @g_mp2b (syn_wfo (syn_c1st) (syn_cvv) (syn_cvv)) (syn_wfn (syn_c1st) (syn_cvv)) (syn_wb (syn_wfn (syn_cres (syn_c1st) F) F) (syn_wss F (syn_cvv))) p0001 p0002 p0003
  have p0005 :=
    @g_mpbir (syn_wfn (syn_cres (syn_c1st) F) F) (syn_wss F (syn_cvv)) p0000 p0004
  have p0006 :=
    @g_a1i (syn_wfn (syn_cres (syn_c1st) F) F) (syn_wfun F) p0005
  have p0007 :=
    @g_brcnv (.cv x) (.cv y) (syn_cres (syn_c1st) F)
  have p0008 :=
    @g_brres (.cv y) (.cv x) (syn_c1st) F
  have p0009 :=
    @g_vex x
  have p0010 :=
    @g_br1st a (.cv y) (.cv x) dv_cache_0001 dv_cache_0002 p0009
  have p0011 :=
    @g_anbi1i (syn_wbr (.cv y) (syn_c1st) (.cv x)) (syn_wex a (.classEq (.cv y) (syn_cop (.cv x) (.cv a)))) (.classMem (.cv y) F) p0010
  have p0012 :=
    @g_n_19_41v (.classEq (.cv y) (syn_cop (.cv x) (.cv a))) (.classMem (.cv y) F) a dv_cache_0003
  have p0013 :=
    @g_bitr4i (syn_wa (syn_wbr (.cv y) (syn_c1st) (.cv x)) (.classMem (.cv y) F)) (syn_wa (syn_wex a (.classEq (.cv y) (syn_cop (.cv x) (.cv a)))) (.classMem (.cv y) F)) (syn_wex a (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv a))) (.classMem (.cv y) F))) p0011 p0012
  have p0014 :=
    @g_n_3bitri (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_c1st) F)) (.cv y)) (syn_wbr (.cv y) (syn_cres (syn_c1st) F) (.cv x)) (syn_wa (syn_wbr (.cv y) (syn_c1st) (.cv x)) (.classMem (.cv y) F)) (syn_wex a (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv a))) (.classMem (.cv y) F))) p0007 p0008 p0013
  have p0015 :=
    @g_brcnv (.cv x) (.cv z) (syn_cres (syn_c1st) F)
  have p0016 :=
    @g_brres (.cv z) (.cv x) (syn_c1st) F
  have p0017 :=
    @g_br1st b (.cv z) (.cv x) dv_cache_0004 dv_cache_0005 p0009
  have p0018 :=
    @g_anbi1i (syn_wbr (.cv z) (syn_c1st) (.cv x)) (syn_wex b (.classEq (.cv z) (syn_cop (.cv x) (.cv b)))) (.classMem (.cv z) F) p0017
  have p0019 :=
    @g_n_3bitri (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_c1st) F)) (.cv z)) (syn_wbr (.cv z) (syn_cres (syn_c1st) F) (.cv x)) (syn_wa (syn_wbr (.cv z) (syn_c1st) (.cv x)) (.classMem (.cv z) F)) (syn_wa (syn_wex b (.classEq (.cv z) (syn_cop (.cv x) (.cv b)))) (.classMem (.cv z) F)) p0015 p0016 p0018
  have p0020 :=
    @g_n_19_41v (.classEq (.cv z) (syn_cop (.cv x) (.cv b))) (.classMem (.cv z) F) b dv_cache_0006
  have p0021 :=
    @g_bitr4i (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_c1st) F)) (.cv z)) (syn_wa (syn_wex b (.classEq (.cv z) (syn_cop (.cv x) (.cv b)))) (.classMem (.cv z) F)) (syn_wex b (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv b))) (.classMem (.cv z) F))) p0019 p0020
  have p0022 :=
    @g_anbi12i (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_c1st) F)) (.cv y)) (syn_wex a (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv a))) (.classMem (.cv y) F))) (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_c1st) F)) (.cv z)) (syn_wex b (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv b))) (.classMem (.cv z) F))) p0014 p0021
  have p0023 :=
    @g_eeanv (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv a))) (.classMem (.cv y) F)) (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv b))) (.classMem (.cv z) F)) a b dv_cache_0007 dv_cache_0008
  have p0024 :=
    @g_bitr4i (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_c1st) F)) (.cv y)) (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_c1st) F)) (.cv z))) (syn_wa (syn_wex a (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv a))) (.classMem (.cv y) F))) (syn_wex b (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv b))) (.classMem (.cv z) F)))) (syn_wex a (syn_wex b (syn_wa (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv a))) (.classMem (.cv y) F)) (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv b))) (.classMem (.cv z) F))))) p0022 p0023
  have p0025 :=
    @g_an4 (.classEq (.cv y) (syn_cop (.cv x) (.cv a))) (.classMem (.cv y) F) (.classEq (.cv z) (syn_cop (.cv x) (.cv b))) (.classMem (.cv z) F)
  have p0026 :=
    @g_dffun4 x a b F dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
  have p0027 :=
    @g_sp (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv a)) F) (.classMem (syn_cop (.cv x) (.cv b)) F)) (.objEq a b)) b
  have p0028 :=
    @g_sps (.all b (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv a)) F) (.classMem (syn_cop (.cv x) (.cv b)) F)) (.objEq a b))) (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv a)) F) (.classMem (syn_cop (.cv x) (.cv b)) F)) (.objEq a b)) a p0027
  have p0029 :=
    @g_sps (.all a (.all b (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv a)) F) (.classMem (syn_cop (.cv x) (.cv b)) F)) (.objEq a b)))) (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv a)) F) (.classMem (syn_cop (.cv x) (.cv b)) F)) (.objEq a b)) x p0028
  have p0030 :=
    @g_sylbi (syn_wfun F) (.all x (.all a (.all b (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv a)) F) (.classMem (syn_cop (.cv x) (.cv b)) F)) (.objEq a b))))) (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv a)) F) (.classMem (syn_cop (.cv x) (.cv b)) F)) (.objEq a b)) p0026 p0029
  have p0031 :=
    @g_opeq2 (.cv a) (.cv b) (.cv x)
  have p0032_e01_recanon : Nominal.NPrf (.imp (.objEq a b) (.classEq (syn_cop (.cv x) (.cv a)) (syn_cop (.cv x) (.cv b)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0031
  have p0032 :=
    @g_syl6 (syn_wfun F) (syn_wa (.classMem (syn_cop (.cv x) (.cv a)) F) (.classMem (syn_cop (.cv x) (.cv b)) F)) (.objEq a b) (.classEq (syn_cop (.cv x) (.cv a)) (syn_cop (.cv x) (.cv b))) p0030 p0032_e01_recanon
  have p0033 :=
    @g_eleq1 (.cv y) (syn_cop (.cv x) (.cv a)) F
  have p0034 :=
    @g_eleq1 (.cv z) (syn_cop (.cv x) (.cv b)) F
  have p0035 :=
    @g_bi2anan9 (.classEq (.cv y) (syn_cop (.cv x) (.cv a))) (.classMem (.cv y) F) (.classMem (syn_cop (.cv x) (.cv a)) F) (.classEq (.cv z) (syn_cop (.cv x) (.cv b))) (.classMem (.cv z) F) (.classMem (syn_cop (.cv x) (.cv b)) F) p0033 p0034
  have p0036 :=
    @g_eqeq12 (.cv y) (syn_cop (.cv x) (.cv a)) (.cv z) (syn_cop (.cv x) (.cv b))
  have p0037_e01_recanon : Nominal.NPrf (.imp (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv a))) (.classEq (.cv z) (syn_cop (.cv x) (.cv b)))) (syn_wb (.objEq y z) (.classEq (syn_cop (.cv x) (.cv a)) (syn_cop (.cv x) (.cv b))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex syn_wex syn_cphi syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0036
  have p0037 :=
    @g_imbi12d (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv a))) (.classEq (.cv z) (syn_cop (.cv x) (.cv b)))) (syn_wa (.classMem (.cv y) F) (.classMem (.cv z) F)) (syn_wa (.classMem (syn_cop (.cv x) (.cv a)) F) (.classMem (syn_cop (.cv x) (.cv b)) F)) (.objEq y z) (.classEq (syn_cop (.cv x) (.cv a)) (syn_cop (.cv x) (.cv b))) p0035 p0037_e01_recanon
  have p0038 :=
    @g_biimprcd (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv a))) (.classEq (.cv z) (syn_cop (.cv x) (.cv b)))) (.imp (syn_wa (.classMem (.cv y) F) (.classMem (.cv z) F)) (.objEq y z)) (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv a)) F) (.classMem (syn_cop (.cv x) (.cv b)) F)) (.classEq (syn_cop (.cv x) (.cv a)) (syn_cop (.cv x) (.cv b)))) p0037
  have p0039 :=
    @g_imp3a (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv a)) F) (.classMem (syn_cop (.cv x) (.cv b)) F)) (.classEq (syn_cop (.cv x) (.cv a)) (syn_cop (.cv x) (.cv b)))) (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv a))) (.classEq (.cv z) (syn_cop (.cv x) (.cv b)))) (syn_wa (.classMem (.cv y) F) (.classMem (.cv z) F)) (.objEq y z) p0038
  have p0040 :=
    @g_syl (syn_wfun F) (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv a)) F) (.classMem (syn_cop (.cv x) (.cv b)) F)) (.classEq (syn_cop (.cv x) (.cv a)) (syn_cop (.cv x) (.cv b)))) (.imp (syn_wa (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv a))) (.classEq (.cv z) (syn_cop (.cv x) (.cv b)))) (syn_wa (.classMem (.cv y) F) (.classMem (.cv z) F))) (.objEq y z)) p0032 p0039
  have p0041 :=
    @g_syl5bi (syn_wa (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv a))) (.classMem (.cv y) F)) (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv b))) (.classMem (.cv z) F))) (syn_wa (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv a))) (.classEq (.cv z) (syn_cop (.cv x) (.cv b)))) (syn_wa (.classMem (.cv y) F) (.classMem (.cv z) F))) (syn_wfun F) (.objEq y z) p0025 p0040
  have p0042 :=
    @g_exlimdvv (syn_wfun F) (syn_wa (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv a))) (.classMem (.cv y) F)) (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv b))) (.classMem (.cv z) F))) (.objEq y z) a b dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 p0041
  have p0043 :=
    @g_syl5bi (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_c1st) F)) (.cv y)) (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_c1st) F)) (.cv z))) (syn_wex a (syn_wex b (syn_wa (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv a))) (.classMem (.cv y) F)) (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv b))) (.classMem (.cv z) F))))) (syn_wfun F) (.objEq y z) p0024 p0042
  have p0044 :=
    @g_alrimiv (syn_wfun F) (.imp (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_c1st) F)) (.cv y)) (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_c1st) F)) (.cv z))) (.objEq y z)) z dv_cache_0019 p0043
  have p0045 :=
    @g_alrimivv (syn_wfun F) (.all z (.imp (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_c1st) F)) (.cv y)) (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_c1st) F)) (.cv z))) (.objEq y z))) x y dv_cache_0020 dv_cache_0021 p0044
  have p0046 :=
    @g_dffun2 x y z (syn_ccnv (syn_cres (syn_c1st) F)) dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
  have p0047 :=
    @g_sylibr (syn_wfun F) (.all x (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_c1st) F)) (.cv y)) (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_c1st) F)) (.cv z))) (.objEq y z))))) (syn_wfun (syn_ccnv (syn_cres (syn_c1st) F))) p0045 p0046
  have p0048 :=
    @g_dfdm4 F
  have p0049 :=
    @g_dfima3 (syn_c1st) F
  have p0050 :=
    @g_eqtr2i (syn_cdm F) (syn_cima (syn_c1st) F) (syn_crn (syn_cres (syn_c1st) F)) p0048 p0049
  have p0051 :=
    @g_a1i (.classEq (syn_crn (syn_cres (syn_c1st) F)) (syn_cdm F)) (syn_wfun F) p0050
  have p0052 :=
    @g_dff1o2 F (syn_cdm F) (syn_cres (syn_c1st) F)
  have p0053 :=
    @g_syl3anbrc (syn_wfun F) (syn_wfn (syn_cres (syn_c1st) F) F) (syn_wfun (syn_ccnv (syn_cres (syn_c1st) F))) (.classEq (syn_crn (syn_cres (syn_c1st) F)) (syn_cdm F)) (syn_wf1o (syn_cres (syn_c1st) F) F (syn_cdm F)) p0006 p0047 p0051 p0052
  have p0054 :=
    @g_n_1stex
  have p0055 :=
    @g_resex (syn_c1st) F p0054 hyp_fundmen_1
  have p0056 :=
    @g_f1oen F (syn_cdm F) (syn_cres (syn_c1st) F) p0055
  have p0057 :=
    @g_syl (syn_wfun F) (syn_wf1o (syn_cres (syn_c1st) F) F (syn_cdm F)) (syn_wbr F (syn_cen) (syn_cdm F)) p0053 p0056
  have p0058 :=
    @g_ensym F (syn_cdm F)
  have p0059 :=
    @g_sylib (syn_wfun F) (syn_wbr F (syn_cen) (syn_cdm F)) (syn_wbr (syn_cdm F) (syn_cen) F) p0057 p0058
  exact p0059

noncomputable def g_en2sn
    (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A C) (.classMem B D)) (syn_wbr (syn_csn A) (syn_cen) (syn_csn B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  have p0000 :=
    @g_f1osng A B C D
  have p0001 :=
    @g_snex (syn_cop A B)
  have p0002 :=
    @g_f1oen (syn_csn A) (syn_csn B) (syn_csn (syn_cop A B)) p0001
  have p0003 :=
    @g_syl (syn_wa (.classMem A C) (.classMem B D)) (syn_wf1o (syn_csn (syn_cop A B)) (syn_csn A) (syn_csn B)) (syn_wbr (syn_csn A) (syn_cen) (syn_csn B)) p0000 p0002
  exact p0003

#print axioms g_en2sn

end NFChoice.DirectNominalPrf.WPPReplay
