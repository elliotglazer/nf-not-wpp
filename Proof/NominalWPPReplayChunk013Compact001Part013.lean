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
import NominalWPPReplayChunk013Compact001Part012

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

noncomputable def g_fvfullfunlem2
    (F : Class) :
    Nominal.NPrf (syn_wss (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) F) := by
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
  have dv_cache_0001 : z ∉ ((Class.cv x)).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_simpl (syn_wbr (.cv x) F (.cv y)) (.all z (.imp (syn_wbr (.cv x) F (.cv z)) (.objEq z y)))
  have p0001 :=
    @g_fnfullfunlem1 z (.cv x) (.cv y) F dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0002 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv y))))
  have p0003_e00_recanon : Nominal.NPrf (syn_wb (syn_wbr (.cv x) (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv y)) (syn_wa (syn_wbr (.cv x) F (.cv y)) (.all z (.imp (syn_wbr (.cv x) F (.cv z)) (.objEq z y))))) :=
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
  have p0003 :=
    @g_bitr3i (syn_wa (syn_wbr (.cv x) F (.cv y)) (.all z (.imp (syn_wbr (.cv x) F (.cv z)) (.objEq z y)))) (syn_wbr (.cv x) (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) p0003_e00_recanon p0002
  have p0004 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) F (.cv y))))
  have p0005 :=
    @g_n_3imtr3i (syn_wa (syn_wbr (.cv x) F (.cv y)) (.all z (.imp (syn_wbr (.cv x) F (.cv z)) (.objEq z y)))) (syn_wbr (.cv x) F (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) (.classMem (syn_cop (.cv x) (.cv y)) F) p0000 p0003 p0004
  have p0006 :=
    @g_gen2 (.imp (.classMem (syn_cop (.cv x) (.cv y)) (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) (.classMem (syn_cop (.cv x) (.cv y)) F)) x y p0005
  have p0007 :=
    @g_ssrel x y (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) F dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0008 :=
    @g_mpbir (syn_wss (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) F) (.all x (.all y (.imp (.classMem (syn_cop (.cv x) (.cv y)) (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) (.classMem (syn_cop (.cv x) (.cv y)) F)))) p0006 p0007
  exact p0008

noncomputable def g_fvfullfunlem3
    (A : Class) (F : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (.classEq (syn_cfv (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) A) (syn_cfv F A))) := by
  let proofSupport : Finset Var := A.fv ∪ F.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
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
  have dv_cache_0001 : x ∉ ((syn_cres F (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cres F (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_cres F (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0005 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0006 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0007 : x ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : z ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_dffun2 x y z (syn_cres F (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_brres (.cv x) (.cv y) F (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
  have p0002 :=
    @g_fvfullfunlem1 x z F dv_cache_0007 dv_cache_0008 dv_cache_0005
  have p0003 :=
    @g_eqabri (syn_weu z (syn_wbr (.cv x) F (.cv z))) x (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) p0002
  have p0004 :=
    @g_anbi2i (.classMem (.cv x) (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_weu z (syn_wbr (.cv x) F (.cv z))) (syn_wbr (.cv x) F (.cv y)) p0003
  have p0005 :=
    @g_bitri (syn_wbr (.cv x) (syn_cres F (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (.cv y)) (syn_wa (syn_wbr (.cv x) F (.cv y)) (.classMem (.cv x) (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))) (syn_wa (syn_wbr (.cv x) F (.cv y)) (syn_weu z (syn_wbr (.cv x) F (.cv z)))) p0001 p0004
  have p0006 :=
    @g_brres (.cv x) (.cv z) F (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
  have p0007 :=
    @g_fvfullfunlem1 x y F dv_cache_0007 dv_cache_0009 dv_cache_0004
  have p0008 :=
    @g_eqabri (syn_weu y (syn_wbr (.cv x) F (.cv y))) x (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) p0007
  have p0009 :=
    @g_anbi2i (.classMem (.cv x) (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_weu y (syn_wbr (.cv x) F (.cv y))) (syn_wbr (.cv x) F (.cv z)) p0008
  have p0010 :=
    @g_bitri (syn_wbr (.cv x) (syn_cres F (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (.cv z)) (syn_wa (syn_wbr (.cv x) F (.cv z)) (.classMem (.cv x) (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))) (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_weu y (syn_wbr (.cv x) F (.cv y)))) p0006 p0009
  have p0011 :=
    @g_tz6_12_1 y (.cv x) (.cv y) F dv_cache_0010 dv_cache_0009
  have p0012 :=
    @g_adantrl (syn_wbr (.cv x) F (.cv y)) (syn_weu y (syn_wbr (.cv x) F (.cv y))) (.classEq (syn_cfv F (.cv x)) (.cv y)) (syn_wbr (.cv x) F (.cv z)) p0011
  have p0013 :=
    @g_tz6_12_1 y (.cv x) (.cv z) F dv_cache_0010 dv_cache_0009
  have p0014 :=
    @g_adantl (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_weu y (syn_wbr (.cv x) F (.cv y)))) (.classEq (syn_cfv F (.cv x)) (.cv z)) (syn_wbr (.cv x) F (.cv y)) p0013
  have p0015 :=
    @g_eqtr3d (syn_wa (syn_wbr (.cv x) F (.cv y)) (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_weu y (syn_wbr (.cv x) F (.cv y))))) (syn_cfv F (.cv x)) (.cv y) (.cv z) p0012 p0014
  have p0016_e00_recanon : Nominal.NPrf (.imp (syn_wa (syn_wbr (.cv x) F (.cv y)) (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_weu y (syn_wbr (.cv x) F (.cv y))))) (.objEq y z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_weu, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0015
  have p0016 :=
    @g_adantlr (syn_wbr (.cv x) F (.cv y)) (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_weu y (syn_wbr (.cv x) F (.cv y)))) (.objEq y z) (syn_weu z (syn_wbr (.cv x) F (.cv z))) p0016_e00_recanon
  have p0017 :=
    @g_syl2anb (syn_wbr (.cv x) (syn_cres F (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (.cv y)) (syn_wa (syn_wbr (.cv x) F (.cv y)) (syn_weu z (syn_wbr (.cv x) F (.cv z)))) (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_weu y (syn_wbr (.cv x) F (.cv y)))) (.objEq y z) (syn_wbr (.cv x) (syn_cres F (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (.cv z)) p0005 p0010 p0016
  have p0018 :=
    @g_gen2 (.imp (syn_wa (syn_wbr (.cv x) (syn_cres F (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (.cv y)) (syn_wbr (.cv x) (syn_cres F (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (.cv z))) (.objEq y z)) y z p0017
  have p0019 :=
    @g_mpgbir (syn_wfun (syn_cres F (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))) (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) (syn_cres F (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (.cv y)) (syn_wbr (.cv x) (syn_cres F (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (.cv z))) (.objEq y z)))) x p0000 p0018
  have p0020 :=
    @g_fvfullfunlem2 F
  have p0021 :=
    @g_ssdmrn (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
  have p0022 :=
    @g_ssv (syn_crn (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
  have p0023 :=
    @g_xpss2 (syn_crn (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) (syn_cvv) (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
  have p0024 :=
    Nominal.mp p0022 p0023
  have p0025 :=
    @g_sstri (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cxp (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) (syn_crn (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_cxp (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) (syn_cvv)) p0021 p0024
  have p0026 :=
    @g_ssini (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) F (syn_cxp (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) (syn_cvv)) p0020 p0025
  have p0027 :=
    (by simpa [syn_cres] using (Nominal.classEqRefl (syn_cres F (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))))
  have p0028 :=
    @g_sseqtr4i (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cin F (syn_cxp (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) (syn_cvv))) (syn_cres F (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) p0026 p0027
  have p0029 :=
    @g_funssfv A (syn_cres F (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
  have p0030 :=
    @g_mp3an12 (syn_wfun (syn_cres F (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))) (syn_wss (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cres F (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))) (.classMem A (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (.classEq (syn_cfv (syn_cres F (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) A) (syn_cfv (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) A)) p0019 p0028 p0029
  have p0031 :=
    @g_fvres A (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) F
  have p0032 :=
    @g_eqtr3d (.classMem A (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_cfv (syn_cres F (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) A) (syn_cfv (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) A) (syn_cfv F A) p0030 p0031
  exact p0032

noncomputable def g_fvfullfun
    (A : Class) (F : Class) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cfullfun F) A) (syn_cfv F A)) := by
  let proofSupport : Finset Var := A.fv ∪ F.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ (F).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (F).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0004 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((Wff.classEq (syn_cfv (syn_cfullfun F) A) (syn_cfv F A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfullfun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_fveq2 (.cv x) A (syn_cfullfun F)
  have p0001 :=
    @g_fveq2 (.cv x) A F
  have p0002 :=
    @g_eqeq12d (.classEq (.cv x) A) (syn_cfv (syn_cfullfun F) (.cv x)) (syn_cfv (syn_cfullfun F) A) (syn_cfv F (.cv x)) (syn_cfv F A) p0000 p0001
  have p0003 :=
    (by simpa [syn_cfullfun] using (Nominal.classEqRefl (syn_cfullfun F)))
  have p0004 :=
    @g_fveq1i (.cv x) (syn_cfullfun F) (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0)))) p0003
  have p0005 :=
    @g_incompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
  have p0006 :=
    @g_fnfullfunlem2 F
  have p0007 :=
    @g_funfn (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
  have p0008 :=
    @g_mpbi (syn_wfun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) (syn_wfn (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) p0006 p0007
  have p0009 :=
    @g_n_0ex
  have p0010 :=
    @g_fnconstg (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_c0) (syn_cvv)
  have p0011 :=
    Nominal.mp p0009 p0010
  have p0012 :=
    @g_fvun1 (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0))) (.cv x)
  have p0013 :=
    @g_mp3an12 (syn_wfn (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_wfn (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0))) (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))) (syn_wa (.classEq (syn_cin (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))) (syn_c0)) (.classMem (.cv x) (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))) (.classEq (syn_cfv (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0)))) (.cv x)) (syn_cfv (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv x))) p0008 p0011 p0012
  have p0014 :=
    @g_mpan (.classEq (syn_cin (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))) (syn_c0)) (.classMem (.cv x) (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (.classEq (syn_cfv (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0)))) (.cv x)) (syn_cfv (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv x))) p0005 p0013
  have p0015 :=
    @g_fvfullfunlem3 (.cv x) F
  have p0016 :=
    @g_eqtrd (.classMem (.cv x) (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_cfv (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0)))) (.cv x)) (syn_cfv (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv x)) (syn_cfv F (.cv x)) p0014 p0015
  have p0017 :=
    @g_vex x
  have p0018 :=
    @g_elcompl (.cv x) (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) p0017
  have p0019 :=
    @g_fvun2 (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0))) (.cv x)
  have p0020 :=
    @g_mp3an12 (syn_wfn (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_wfn (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0))) (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))) (syn_wa (.classEq (syn_cin (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))) (syn_c0)) (.classMem (.cv x) (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))))) (.classEq (syn_cfv (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0)))) (.cv x)) (syn_cfv (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0))) (.cv x))) p0008 p0011 p0019
  have p0021 :=
    @g_mpan (.classEq (syn_cin (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))) (syn_c0)) (.classMem (.cv x) (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))) (.classEq (syn_cfv (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0)))) (.cv x)) (syn_cfv (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0))) (.cv x))) p0005 p0020
  have p0022 :=
    @g_sylbir (.neg (.classMem (.cv x) (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))) (.classMem (.cv x) (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))) (.classEq (syn_cfv (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0)))) (.cv x)) (syn_cfv (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0))) (.cv x))) p0018 p0021
  have p0023 :=
    @g_fvfullfunlem1 x y F dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0024 :=
    @g_eqabri (syn_weu y (syn_wbr (.cv x) F (.cv y))) x (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) p0023
  have p0025 :=
    @g_tz6_12_2 y (.cv x) F dv_cache_0004 dv_cache_0002
  have p0026 :=
    @g_sylnbi (.classMem (.cv x) (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_weu y (syn_wbr (.cv x) F (.cv y))) (.classEq (syn_cfv F (.cv x)) (syn_c0)) p0024 p0025
  have p0027 :=
    @g_n_0ex
  have p0028 :=
    @g_fvconst2 (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_c0) (.cv x) p0027
  have p0029 :=
    @g_sylbir (.neg (.classMem (.cv x) (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))) (.classMem (.cv x) (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))) (.classEq (syn_cfv (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0))) (.cv x)) (syn_c0)) p0018 p0028
  have p0030 :=
    @g_eqtr4d (.neg (.classMem (.cv x) (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))) (syn_cfv F (.cv x)) (syn_c0) (syn_cfv (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0))) (.cv x)) p0026 p0029
  have p0031 :=
    @g_eqtr4d (.neg (.classMem (.cv x) (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))) (syn_cfv (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0)))) (.cv x)) (syn_cfv (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0))) (.cv x)) (syn_cfv F (.cv x)) p0022 p0030
  have p0032 :=
    @g_pm2_61i (.classMem (.cv x) (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (.classEq (syn_cfv (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0)))) (.cv x)) (syn_cfv F (.cv x))) p0016 p0031
  have p0033 :=
    @g_eqtri (syn_cfv (syn_cfullfun F) (.cv x)) (syn_cfv (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cxp (syn_ccompl (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (syn_csn (syn_c0)))) (.cv x)) (syn_cfv F (.cv x)) p0004 p0032
  have p0034 :=
    @g_vtoclg (.classEq (syn_cfv (syn_cfullfun F) (.cv x)) (syn_cfv F (.cv x))) (.classEq (syn_cfv (syn_cfullfun F) A) (syn_cfv F A)) x A (syn_cvv) dv_cache_0005 dv_cache_0006 p0002 p0033
  have p0035 :=
    @g_fvprc A (syn_cfullfun F)
  have p0036 :=
    @g_fvprc A F
  have p0037 :=
    @g_eqtr4d (.neg (.classMem A (syn_cvv))) (syn_cfv (syn_cfullfun F) A) (syn_c0) (syn_cfv F A) p0035 p0036
  have p0038 :=
    @g_pm2_61i (.classMem A (syn_cvv)) (.classEq (syn_cfv (syn_cfullfun F) A) (syn_cfv F A)) p0034 p0037
  exact p0038

noncomputable def g_fvdomfn
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classEq (syn_cfv (syn_cdomfn) A) (syn_cdm A))) := by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cdm A)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elex A V
  have p0001 :=
    @g_dmexg A (syn_cvv)
  have p0002 :=
    @g_dmeq (.cv x) A
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_domfn x
  have p0004 :=
    @g_fvmptg x A (syn_cdm (.cv x)) (syn_cdm A) (syn_cvv) (syn_cvv) (syn_cdomfn) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0002 p0003
  have p0005 :=
    @g_mpdan (.classMem A (syn_cvv)) (.classMem (syn_cdm A) (syn_cvv)) (.classEq (syn_cfv (syn_cdomfn) A) (syn_cdm A)) p0001 p0004
  have p0006 :=
    @g_syl (.classMem A V) (.classMem A (syn_cvv)) (.classEq (syn_cfv (syn_cdomfn) A) (syn_cdm A)) p0000 p0005
  exact p0006

noncomputable def g_fvranfn
    (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classEq (syn_cfv (syn_cranfn) A) (syn_crn A))) := by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_crn A)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elex A V
  have p0001 :=
    @g_rnexg A (syn_cvv)
  have p0002 :=
    @g_rneq (.cv x) A
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ranfn x
  have p0004 :=
    @g_fvmptg x A (syn_crn (.cv x)) (syn_crn A) (syn_cvv) (syn_cvv) (syn_cranfn) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0002 p0003
  have p0005 :=
    @g_mpdan (.classMem A (syn_cvv)) (.classMem (syn_crn A) (syn_cvv)) (.classEq (syn_cfv (syn_cranfn) A) (syn_crn A)) p0001 p0004
  have p0006 :=
    @g_syl (.classMem A V) (.classMem A (syn_cvv)) (.classEq (syn_cfv (syn_cranfn) A) (syn_crn A)) p0000 p0005
  exact p0006

#print axioms g_fvranfn

end NFChoice.DirectNominalPrf.WPPReplay
