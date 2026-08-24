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
import NominalWPPReplayChunk013Compact001Part011

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

noncomputable def g_fnfullfunlem1
    (x : Var) (A : Class) (B : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf (syn_wb (syn_wbr A (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) B) (syn_wa (syn_wbr A F B) (.all x (.imp (syn_wbr A F (.cv x)) (.classEq (.cv x) B))))) := by
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
  have dv_cache_0001 : x ∉ ((Wff.classEq (.cv y) B)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_ccompl (syn_cid))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((syn_wb (syn_wbr A (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) B) (syn_wa (syn_wbr A F B) (.all x (.imp (syn_wbr A F (.cv x)) (.classEq (.cv x) B)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, fresh_y_not_F, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_brex A B (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
  have p0001 :=
    @g_simprd (syn_wbr A (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) B) (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) p0000
  have p0002 :=
    @g_brex A B F
  have p0003 :=
    @g_simprd (syn_wbr A F B) (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) p0002
  have p0004 :=
    @g_adantr (syn_wbr A F B) (.classMem B (syn_cvv)) (.all x (.imp (syn_wbr A F (.cv x)) (.classEq (.cv x) B))) p0003
  have p0005 :=
    @g_breq2 (.cv y) B A (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
  have p0006 :=
    @g_breq2 (.cv y) B A F
  have p0007 :=
    @g_eqeq2 (.cv y) B (.cv x)
  have p0008_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv y) B) (syn_wb (.objEq x y) (.classEq (.cv x) B))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
      p0007
  have p0008 :=
    @g_imbi2d (.classEq (.cv y) B) (.objEq x y) (.classEq (.cv x) B) (syn_wbr A F (.cv x)) p0008_e00_recanon
  have p0009 :=
    @g_albidv (.classEq (.cv y) B) (.imp (syn_wbr A F (.cv x)) (.objEq x y)) (.imp (syn_wbr A F (.cv x)) (.classEq (.cv x) B)) x dv_cache_0001 p0008
  have p0010 :=
    @g_anbi12d (.classEq (.cv y) B) (syn_wbr A F (.cv y)) (syn_wbr A F B) (.all x (.imp (syn_wbr A F (.cv x)) (.objEq x y))) (.all x (.imp (syn_wbr A F (.cv x)) (.classEq (.cv x) B))) p0006 p0009
  have p0011 :=
    @g_bibi12d (.classEq (.cv y) B) (syn_wbr A (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv y)) (syn_wbr A (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) B) (syn_wa (syn_wbr A F (.cv y)) (.all x (.imp (syn_wbr A F (.cv x)) (.objEq x y)))) (syn_wa (syn_wbr A F B) (.all x (.imp (syn_wbr A F (.cv x)) (.classEq (.cv x) B)))) p0005 p0010
  have p0012 :=
    @g_brdif A (.cv y) (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)
  have p0013 :=
    @g_coi2 F
  have p0014 :=
    @g_breqi A (.cv y) (syn_ccom (syn_cid) F) F p0013
  have p0015 :=
    @g_brco x A (.cv y) (syn_ccompl (syn_cid)) F dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0016 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) (syn_ccompl (syn_cid)) (.cv y))))
  have p0017 :=
    @g_vex x
  have p0018 :=
    @g_vex y
  have p0019 :=
    @g_opex (.cv x) (.cv y) p0017 p0018
  have p0020 :=
    @g_elcompl (syn_cop (.cv x) (.cv y)) (syn_cid) p0019
  have p0021 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) (syn_cid) (.cv y))))
  have p0022 :=
    @g_ideq (.cv x) (.cv y) p0018
  have p0023_e01_recanon : Nominal.NPrf (syn_wb (syn_wbr (.cv x) (syn_cid) (.cv y)) (.objEq x y)) :=
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
      p0022
  have p0023 :=
    @g_bitr3i (.classMem (syn_cop (.cv x) (.cv y)) (syn_cid)) (syn_wbr (.cv x) (syn_cid) (.cv y)) (.objEq x y) p0021 p0023_e01_recanon
  have p0024 :=
    @g_xchbinx (.classMem (syn_cop (.cv x) (.cv y)) (syn_ccompl (syn_cid))) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cid)) (.objEq x y) p0020 p0023
  have p0025 :=
    @g_bitri (syn_wbr (.cv x) (syn_ccompl (syn_cid)) (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) (syn_ccompl (syn_cid))) (.neg (.objEq x y)) p0016 p0024
  have p0026 :=
    @g_anbi2i (syn_wbr (.cv x) (syn_ccompl (syn_cid)) (.cv y)) (.neg (.objEq x y)) (syn_wbr A F (.cv x)) p0025
  have p0027 :=
    @g_exbii (syn_wa (syn_wbr A F (.cv x)) (syn_wbr (.cv x) (syn_ccompl (syn_cid)) (.cv y))) (syn_wa (syn_wbr A F (.cv x)) (.neg (.objEq x y))) x p0026
  have p0028 :=
    @g_exanali (syn_wbr A F (.cv x)) (.objEq x y) x
  have p0029 :=
    @g_n_3bitrri (syn_wbr A (syn_ccom (syn_ccompl (syn_cid)) F) (.cv y)) (syn_wex x (syn_wa (syn_wbr A F (.cv x)) (syn_wbr (.cv x) (syn_ccompl (syn_cid)) (.cv y)))) (syn_wex x (syn_wa (syn_wbr A F (.cv x)) (.neg (.objEq x y)))) (.neg (.all x (.imp (syn_wbr A F (.cv x)) (.objEq x y)))) p0015 p0027 p0028
  have p0030 :=
    @g_con1bii (.all x (.imp (syn_wbr A F (.cv x)) (.objEq x y))) (syn_wbr A (syn_ccom (syn_ccompl (syn_cid)) F) (.cv y)) p0029
  have p0031 :=
    @g_anbi12i (syn_wbr A (syn_ccom (syn_cid) F) (.cv y)) (syn_wbr A F (.cv y)) (.neg (syn_wbr A (syn_ccom (syn_ccompl (syn_cid)) F) (.cv y))) (.all x (.imp (syn_wbr A F (.cv x)) (.objEq x y))) p0014 p0030
  have p0032 :=
    @g_bitri (syn_wbr A (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv y)) (syn_wa (syn_wbr A (syn_ccom (syn_cid) F) (.cv y)) (.neg (syn_wbr A (syn_ccom (syn_ccompl (syn_cid)) F) (.cv y)))) (syn_wa (syn_wbr A F (.cv y)) (.all x (.imp (syn_wbr A F (.cv x)) (.objEq x y)))) p0012 p0031
  have p0033 :=
    @g_vtoclg (syn_wb (syn_wbr A (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv y)) (syn_wa (syn_wbr A F (.cv y)) (.all x (.imp (syn_wbr A F (.cv x)) (.objEq x y))))) (syn_wb (syn_wbr A (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) B) (syn_wa (syn_wbr A F B) (.all x (.imp (syn_wbr A F (.cv x)) (.classEq (.cv x) B))))) y B (syn_cvv) dv_cache_0006 dv_cache_0007 p0011 p0032
  have p0034 :=
    @g_pm5_21nii (syn_wbr A (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) B) (.classMem B (syn_cvv)) (syn_wa (syn_wbr A F B) (.all x (.imp (syn_wbr A F (.cv x)) (.classEq (.cv x) B)))) p0001 p0004 p0033
  exact p0034

noncomputable def g_fnfullfunlem2
    (F : Class) :
    Nominal.NPrf (syn_wfun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) := by
  let proofSupport : Finset Var := F.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
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
  have dv_cache_0001 : x ∉ ((syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0005 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0006 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0007 : z ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : z ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_dffun2 x y z (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_fnfullfunlem1 z (.cv x) (.cv y) F dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0002 :=
    @g_fnfullfunlem1 y (.cv x) (.cv z) F dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0003 :=
    @g_sp (.imp (syn_wbr (.cv x) F (.cv y)) (.objEq y z)) y
  have p0004 :=
    @g_impcom (.all y (.imp (syn_wbr (.cv x) F (.cv y)) (.objEq y z))) (syn_wbr (.cv x) F (.cv y)) (.objEq y z) p0003
  have p0005 :=
    @g_ad2ant2rl (syn_wbr (.cv x) F (.cv y)) (.all y (.imp (syn_wbr (.cv x) F (.cv y)) (.objEq y z))) (.objEq y z) (.all z (.imp (syn_wbr (.cv x) F (.cv z)) (.objEq z y))) (syn_wbr (.cv x) F (.cv z)) p0004
  have p0006_e00_recanon : Nominal.NPrf (syn_wb (syn_wbr (.cv x) (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv y)) (syn_wa (syn_wbr (.cv x) F (.cv y)) (.all z (.imp (syn_wbr (.cv x) F (.cv z)) (.objEq z y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_cdif syn_cin syn_ccom syn_copab syn_cid
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
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
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
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
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0001
  have p0006_e01_recanon : Nominal.NPrf (syn_wb (syn_wbr (.cv x) (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv z)) (syn_wa (syn_wbr (.cv x) F (.cv z)) (.all y (.imp (syn_wbr (.cv x) F (.cv y)) (.objEq y z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_cdif syn_cin syn_ccom syn_copab syn_cid
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
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
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
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
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0002
  have p0006 :=
    @g_syl2anb (syn_wbr (.cv x) (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv y)) (syn_wa (syn_wbr (.cv x) F (.cv y)) (.all z (.imp (syn_wbr (.cv x) F (.cv z)) (.objEq z y)))) (syn_wa (syn_wbr (.cv x) F (.cv z)) (.all y (.imp (syn_wbr (.cv x) F (.cv y)) (.objEq y z)))) (.objEq y z) (syn_wbr (.cv x) (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv z)) p0006_e00_recanon p0006_e01_recanon p0005
  have p0007 :=
    @g_gen2 (.imp (syn_wa (syn_wbr (.cv x) (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv y)) (syn_wbr (.cv x) (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv z))) (.objEq y z)) y z p0006
  have p0008 :=
    @g_mpgbir (syn_wfun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv y)) (syn_wbr (.cv x) (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv z))) (.objEq y z)))) x p0000 p0007
  exact p0008

noncomputable def g_fnfullfun
    (F : Class) :
    Nominal.NPrf (syn_wfn (syn_cfullfun F) (syn_cvv)) := by
  let proofSupport : Finset Var := F.fv
  have p0000 :=
    @g_fnfullfunlem2 F
  have p0001 :=
    @g_funfn (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
  have p0002 :=
    @g_mpbi (syn_wfun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) (syn_wfn (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) p0000 p0001
  have p0003 :=
    @g_n_0ex
  have p0004 :=
    @g_fnconstg (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_c0) (syn_cvv)
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_pm3_2i (syn_wfn (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_wfn (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0))) (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))) p0002 p0005
  have p0007 :=
    @g_incompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
  have p0008 :=
    @g_fnun (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0)))
  have p0009 :=
    @g_mp2an (syn_wa (syn_wfn (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_wfn (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0))) (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))))) (.classEq (syn_cin (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))) (syn_c0)) (syn_wfn (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0)))) (syn_cun (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))))) p0006 p0007 p0008
  have p0010 :=
    (by simpa [syn_cfullfun] using (Nominal.classEqRefl (syn_cfullfun F)))
  have p0011 :=
    @g_uncompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
  have p0012 :=
    @g_eqcomi (syn_cun (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))) (syn_cvv) p0011
  have p0013 :=
    @g_fneq1 (syn_cvv) (syn_cfullfun F) (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0))))
  have p0014 :=
    @g_fneq2 (syn_cvv) (syn_cun (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))) (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0))))
  have p0015 :=
    @g_sylan9bb (.classEq (syn_cfullfun F) (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0))))) (syn_wfn (syn_cfullfun F) (syn_cvv)) (syn_wfn (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0)))) (syn_cvv)) (.classEq (syn_cvv) (syn_cun (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))))) (syn_wfn (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0)))) (syn_cun (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))))) p0013 p0014
  have p0016 :=
    @g_mp2an (.classEq (syn_cfullfun F) (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0))))) (.classEq (syn_cvv) (syn_cun (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))))) (syn_wb (syn_wfn (syn_cfullfun F) (syn_cvv)) (syn_wfn (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0)))) (syn_cun (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))))) p0010 p0012 p0015
  have p0017 :=
    @g_mpbir (syn_wfn (syn_cfullfun F) (syn_cvv)) (syn_wfn (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0)))) (syn_cun (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))))) p0009 p0016
  exact p0017

noncomputable def g_fullfunexg
    (F : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem F V) (.classMem (syn_cfullfun F) (syn_cvv))) := by
  let proofSupport : Finset Var := F.fv ∪ V.fv
  have p0000 :=
    (by simpa [syn_cfullfun] using (Nominal.classEqRefl (syn_cfullfun F)))
  have p0001 :=
    @g_idex
  have p0002 :=
    @g_coexg (syn_cid) F (syn_cvv) V
  have p0003 :=
    @g_mpan (.classMem (syn_cid) (syn_cvv)) (.classMem F V) (.classMem (syn_ccom (syn_cid) F) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_idex
  have p0005 :=
    @g_complex (syn_cid) p0004
  have p0006 :=
    @g_coexg (syn_ccompl (syn_cid)) F (syn_cvv) V
  have p0007 :=
    @g_mpan (.classMem (syn_ccompl (syn_cid)) (syn_cvv)) (.classMem F V) (.classMem (syn_ccom (syn_ccompl (syn_cid)) F) (syn_cvv)) p0005 p0006
  have p0008 :=
    @g_difexg (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F) (syn_cvv) (syn_cvv)
  have p0009 :=
    @g_syl2anc (.classMem F V) (.classMem (syn_ccom (syn_cid) F) (syn_cvv)) (.classMem (syn_ccom (syn_ccompl (syn_cid)) F) (syn_cvv)) (.classMem (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cvv)) p0003 p0007 p0008
  have p0010 :=
    @g_dmexg (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cvv)
  have p0011 :=
    @g_complexg (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) (syn_cvv)
  have p0012 :=
    @g_n_3syl (.classMem F V) (.classMem (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cvv)) (.classMem (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) (syn_cvv)) (.classMem (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_cvv)) p0009 p0010 p0011
  have p0013 :=
    @g_snex (syn_c0)
  have p0014 :=
    @g_xpexg (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0)) (syn_cvv) (syn_cvv)
  have p0015 :=
    @g_sylancl (.classMem F V) (.classMem (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_cvv)) (.classMem (syn_csn (syn_c0)) (syn_cvv)) (.classMem (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0))) (syn_cvv)) p0012 p0013 p0014
  have p0016 :=
    @g_unexg (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0))) (syn_cvv) (syn_cvv)
  have p0017 :=
    @g_syl2anc (.classMem F V) (.classMem (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cvv)) (.classMem (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0))) (syn_cvv)) (.classMem (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0)))) (syn_cvv)) p0009 p0015 p0016
  have p0018 :=
    @g_syl5eqel (.classMem F V) (syn_cfullfun F) (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0)))) (syn_cvv) p0000 p0017
  exact p0018

noncomputable def g_fullfunex
    (F : Class) (hyp_fullfunex_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cfullfun F) (syn_cvv)) := by
  let proofSupport : Finset Var := F.fv
  have p0000 :=
    @g_fullfunexg F (syn_cvv)
  have p0001 :=
    Nominal.mp hyp_fullfunex_1 p0000
  exact p0001

noncomputable def g_fvfullfunlem1
    (x : Var) (y : Var) (F : Class) (dv_F_x : x ∉ F.fv) (dv_F_y : y ∉ F.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classEq (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) (.cab x (syn_weu y (syn_wbr (.cv x) F (.cv y))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ F.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ ((Class.cv x)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_y), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((syn_wbr (.cv x) F (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0008 : y ∉ ((syn_wbr (.cv x) F (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_y), fresh_y_ne_z, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eldm y (.cv x) (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_fnfullfunlem1 z (.cv x) (.cv y) F dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0002_e00_recanon : Nominal.NPrf (syn_wb (syn_wbr (.cv x) (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv y)) (syn_wa (syn_wbr (.cv x) F (.cv y)) (.all z (.imp (syn_wbr (.cv x) F (.cv z)) (.objEq z y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_cdif syn_cin syn_ccom syn_copab syn_cid
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
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
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
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
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0001
  have p0002 :=
    @g_exbii (syn_wbr (.cv x) (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv y)) (syn_wa (syn_wbr (.cv x) F (.cv y)) (.all z (.imp (syn_wbr (.cv x) F (.cv z)) (.objEq z y)))) y p0002_e00_recanon
  have p0003 :=
    @g_nfv (syn_wbr (.cv x) F (.cv y)) z dv_cache_0006
  have p0004 :=
    @g_eu1 (syn_wbr (.cv x) F (.cv y)) y z dv_cache_0007 p0003
  have p0005 :=
    @g_nfv (syn_wbr (.cv x) F (.cv z)) y dv_cache_0008
  have p0006 :=
    @g_breq2 (.cv y) (.cv z) (.cv x) F
  have p0007_e01_recanon : Nominal.NPrf (.imp (.objEq y z) (syn_wb (syn_wbr (.cv x) F (.cv y)) (syn_wbr (.cv x) F (.cv z)))) :=
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
      p0006
  have p0007 :=
    @g_sbie (syn_wbr (.cv x) F (.cv y)) (syn_wbr (.cv x) F (.cv z)) y z p0005 p0007_e01_recanon
  have p0008 :=
    @g_equcom y z
  have p0009 :=
    @g_imbi12i (syn_wsb z y (syn_wbr (.cv x) F (.cv y))) (syn_wbr (.cv x) F (.cv z)) (.objEq y z) (.objEq z y) p0007 p0008
  have p0010 :=
    @g_albii (.imp (syn_wsb z y (syn_wbr (.cv x) F (.cv y))) (.objEq y z)) (.imp (syn_wbr (.cv x) F (.cv z)) (.objEq z y)) z p0009
  have p0011 :=
    @g_anbi2i (.all z (.imp (syn_wsb z y (syn_wbr (.cv x) F (.cv y))) (.objEq y z))) (.all z (.imp (syn_wbr (.cv x) F (.cv z)) (.objEq z y))) (syn_wbr (.cv x) F (.cv y)) p0010
  have p0012 :=
    @g_exbii (syn_wa (syn_wbr (.cv x) F (.cv y)) (.all z (.imp (syn_wsb z y (syn_wbr (.cv x) F (.cv y))) (.objEq y z)))) (syn_wa (syn_wbr (.cv x) F (.cv y)) (.all z (.imp (syn_wbr (.cv x) F (.cv z)) (.objEq z y)))) y p0011
  have p0013_e00_recanon : Nominal.NPrf (syn_wb (syn_weu y (syn_wbr (.cv x) F (.cv y))) (syn_wex y (syn_wa (syn_wbr (.cv x) F (.cv y)) (.all z (.imp (syn_wsb z y (syn_wbr (.cv x) F (.cv y))) (.objEq y z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_weu syn_wex syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_weu, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
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
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0004
  have p0013 :=
    @g_bitr2i (syn_weu y (syn_wbr (.cv x) F (.cv y))) (syn_wex y (syn_wa (syn_wbr (.cv x) F (.cv y)) (.all z (.imp (syn_wsb z y (syn_wbr (.cv x) F (.cv y))) (.objEq y z))))) (syn_wex y (syn_wa (syn_wbr (.cv x) F (.cv y)) (.all z (.imp (syn_wbr (.cv x) F (.cv z)) (.objEq z y))))) p0013_e00_recanon p0012
  have p0014 :=
    @g_n_3bitri (.classMem (.cv x) (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_wex y (syn_wbr (.cv x) (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv y))) (syn_wex y (syn_wa (syn_wbr (.cv x) F (.cv y)) (.all z (.imp (syn_wbr (.cv x) F (.cv z)) (.objEq z y))))) (syn_weu y (syn_wbr (.cv x) F (.cv y))) p0000 p0002 p0013
  have p0015 :=
    @g_eqabi (syn_weu y (syn_wbr (.cv x) F (.cv y))) x (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) dv_cache_0009 p0014
  exact p0015

#print axioms g_fvfullfunlem1

end NFChoice.DirectNominalPrf.WPPReplay
