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
import NominalWPPReplayChunk015Compact001Part022

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

noncomputable def g_lndifopex
     :
    Nominal.NPrf (.classMem (syn_clndifop) (syn_cvv)) := by
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
  have dv_cache_0001 : x ≠ y := by
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0002 : x ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_cdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_csset)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_cdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_csset)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((syn_cdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_csset)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((syn_cdif (.cv x) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0009 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_lndifop x y dv_cache_0001
  have p0001 :=
    @g_vex y
  have p0002 :=
    @g_otelins3 (syn_csn (.cv z)) (.cv x) (.cv y) (syn_csset) p0001
  have p0003 :=
    @g_vex z
  have p0004 :=
    @g_vex x
  have p0005 :=
    @g_opelssetsn (.cv z) (.cv x) p0003 p0004
  have p0006_e01_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv z)) (.cv x)) (syn_csset)) (.objMem z x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0005
  have p0006 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_cins3 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv z)) (.cv x)) (syn_csset)) (.objMem z x) p0002 p0006_e01_recanon
  have p0007 :=
    @g_otelins2 (syn_csn (.cv z)) (.cv x) (.cv y) (syn_csset) p0004
  have p0008 :=
    @g_opelssetsn (.cv z) (.cv y) p0003 p0001
  have p0009_e01_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv z)) (.cv y)) (syn_csset)) (.objMem z y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0008
  have p0009 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_cins2 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv z)) (.cv y)) (syn_csset)) (.objMem z y) p0007 p0009_e01_recanon
  have p0010 :=
    @g_lnanbi12ni (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_cins3 (syn_csset))) (.objMem z x) (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_cins2 (syn_csset))) (.objMem z y) p0006 p0009
  have p0011 :=
    @g_eldif (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_cins3 (syn_csset)) (syn_cins2 (syn_csset))
  have p0012 :=
    @g_eldif (.cv z) (.cv x) (.cv y)
  have p0013_e02_recanon : Nominal.NPrf (syn_wb (.classMem (.cv z) (syn_cdif (.cv x) (.cv y))) (syn_wa (.objMem z x) (.neg (.objMem z y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0012
  have p0013 :=
    @g_n_3bitr4i (syn_wa (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_cins3 (syn_csset))) (.neg (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_cins2 (syn_csset))))) (syn_wa (.objMem z x) (.neg (.objMem z y))) (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_cdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_csset)))) (.classMem (.cv z) (syn_cdif (.cv x) (.cv y))) p0010 p0011 p0013_e02_recanon
  have p0014 :=
    @g_releqmpt2 x y z (syn_cvv) (syn_cvv) (syn_cdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_csset))) (syn_cdif (.cv x) (.cv y)) dv_cache_0002 dv_cache_0003 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0001 dv_cache_0008 dv_cache_0009 p0013
  have p0015 :=
    @g_eqtr4i (syn_clndifop) (syn_cmpt2 x (syn_cvv) y (syn_cvv) (syn_cdif (.cv x) (.cv y))) (syn_cdif (syn_cxp (syn_cxp (syn_cvv) (syn_cvv)) (syn_cvv)) (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_cdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_csset))))) (syn_c1c))) p0000 p0014
  have p0016 :=
    @g_vvex
  have p0017 :=
    @g_vvex
  have p0018 :=
    @g_ssetex
  have p0019 :=
    @g_ins3ex (syn_csset) p0018
  have p0020 :=
    @g_ssetex
  have p0021 :=
    @g_ins2ex (syn_csset) p0020
  have p0022 :=
    @g_difex (syn_cins3 (syn_csset)) (syn_cins2 (syn_csset)) p0019 p0021
  have p0023 :=
    @g_mpt2exlem (syn_cvv) (syn_cvv) (syn_cdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_csset))) p0016 p0017 p0022
  have p0024 :=
    @g_eqeltri (syn_clndifop) (syn_cdif (syn_cxp (syn_cxp (syn_cvv) (syn_cvv)) (syn_cvv)) (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_cdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_csset))))) (syn_c1c))) (syn_cvv) p0015 p0023
  exact p0024

noncomputable def g_ln1stfn
     :
    Nominal.NPrf (syn_wfn (syn_c1st) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_n_1stfo
  have p0001 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0002 :=
    Nominal.mp p0000 p0001
  exact p0002

noncomputable def g_ln2ndfn
     :
    Nominal.NPrf (syn_wfn (syn_c2nd) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_n_2ndfo
  have p0001 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0002 :=
    Nominal.mp p0000 p0001
  exact p0002

noncomputable def g_lnpwasymfnfn
     :
    Nominal.NPrf (syn_wfn (syn_clnpwasymfn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_fnlndifop
  have p0001 :=
    @g_n_1stfo
  have p0002 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    @g_imageswapfn
  have p0005 :=
    @g_n_1stfo
  have p0006 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_c1st) p0004 p0007
  have p0009 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cvv)) p0003 p0008
  have p0010 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))
  have p0011 :=
    Nominal.mp p0009 p0010
  have p0012 :=
    @g_inidm (syn_cvv)
  have p0013 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) p0012
  have p0014 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) (syn_cvv)) p0011 p0013
  have p0015 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) p0000 p0014
  have p0016 :=
    (by simpa [syn_clnpwasymfn] using (Nominal.classEqRefl (syn_clnpwasymfn)))
  have p0017 :=
    @g_fneq1i (syn_cvv) (syn_clnpwasymfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))) p0016
  have p0018 :=
    @g_mpbir (syn_wfn (syn_clnpwasymfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))) (syn_cvv)) p0015 p0017
  exact p0018

noncomputable def g_lnpwasymfnex
     :
    Nominal.NPrf (.classMem (syn_clnpwasymfn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_clnpwasymfn] using (Nominal.classEqRefl (syn_clnpwasymfn)))
  have p0001 :=
    @g_lndifopex
  have p0002 :=
    @g_n_1stex
  have p0003 :=
    @g_swapex
  have p0004 :=
    @g_imageex (syn_cswap) p0003
  have p0005 :=
    @g_n_1stex
  have p0006 :=
    @g_coex (syn_cimage (syn_cswap)) (syn_c1st) p0004 p0005
  have p0007 :=
    @g_txpex (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) p0002 p0006
  have p0008 :=
    @g_coex (syn_clndifop) (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) p0001 p0007
  have p0009 :=
    @g_eqeltri (syn_clnpwasymfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))) (syn_cvv) p0000 p0008
  exact p0009

noncomputable def g_lnpwasymfnval
    (D : Class) (R : Class) (hyp_lnpwasymfnval_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_lnpwasymfnval_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_clnpwasymfn) (syn_cop R D)) (syn_cdif R (syn_ccnv R))) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_clnpwasymfn] using (Nominal.classEqRefl (syn_clnpwasymfn)))
  have p0001 :=
    @g_fveq1i (syn_cop R D) (syn_clnpwasymfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))) p0000
  have p0002 :=
    @g_n_1stfo
  have p0003 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0004 :=
    Nominal.mp p0002 p0003
  have p0005 :=
    @g_imageswapfn
  have p0006 :=
    @g_n_1stfo
  have p0007 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_c1st) p0005 p0008
  have p0010 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cvv)) p0004 p0009
  have p0011 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))
  have p0012 :=
    Nominal.mp p0010 p0011
  have p0013 :=
    @g_inidm (syn_cvv)
  have p0014 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) p0013
  have p0015 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) (syn_cvv)) p0012 p0014
  have p0016 :=
    @g_opex R D hyp_lnpwasymfnval_1 hyp_lnpwasymfnval_2
  have p0017 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) (syn_cvv)) (.classMem (syn_cop R D) (syn_cvv)) p0015 p0016
  have p0018 :=
    @g_fvco2 (syn_cvv) (syn_cop R D) (syn_clndifop) (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))
  have p0019 :=
    Nominal.mp p0017 p0018
  have p0020 :=
    @g_n_1stfo
  have p0021 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0022 :=
    Nominal.mp p0020 p0021
  have p0023 :=
    @g_imageswapfn
  have p0024 :=
    @g_n_1stfo
  have p0025 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0026 :=
    Nominal.mp p0024 p0025
  have p0027 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_c1st) p0023 p0026
  have p0028 :=
    @g_opex R D hyp_lnpwasymfnval_1 hyp_lnpwasymfnval_2
  have p0029 :=
    @g_fvtxpvv (syn_cop R D) (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) p0022 p0027 p0028
  have p0030 :=
    @g_opfv1st R D hyp_lnpwasymfnval_1 hyp_lnpwasymfnval_2
  have p0031 :=
    @g_n_1stfo
  have p0032 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0033 :=
    Nominal.mp p0031 p0032
  have p0034 :=
    @g_opex R D hyp_lnpwasymfnval_1 hyp_lnpwasymfnval_2
  have p0035 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (.classMem (syn_cop R D) (syn_cvv)) p0033 p0034
  have p0036 :=
    @g_fvco2 (syn_cvv) (syn_cop R D) (syn_cimage (syn_cswap)) (syn_c1st)
  have p0037 :=
    Nominal.mp p0035 p0036
  have p0038 :=
    @g_opfv1st R D hyp_lnpwasymfnval_1 hyp_lnpwasymfnval_2
  have p0039 :=
    @g_fveq2i (syn_cfv (syn_c1st) (syn_cop R D)) R (syn_cimage (syn_cswap)) p0038
  have p0040 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cop R D)) (syn_cfv (syn_cimage (syn_cswap)) (syn_cfv (syn_c1st) (syn_cop R D))) (syn_cfv (syn_cimage (syn_cswap)) R) p0037 p0039
  have p0041 :=
    @g_eqid (syn_cima (syn_cswap) R)
  have p0042 :=
    @g_swapex
  have p0043 :=
    @g_imaex (syn_cswap) R p0042 hyp_lnpwasymfnval_1
  have p0044 :=
    @g_brimage R (syn_cima (syn_cswap) R) (syn_cswap) hyp_lnpwasymfnval_1 p0043
  have p0045 :=
    @g_mpbir (syn_wbr R (syn_cimage (syn_cswap)) (syn_cima (syn_cswap) R)) (.classEq (syn_cima (syn_cswap) R) (syn_cima (syn_cswap) R)) p0041 p0044
  have p0046 :=
    @g_imageswapfn
  have p0047 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_cswap)) (syn_cvv)) (.classMem R (syn_cvv)) p0046 hyp_lnpwasymfnval_1
  have p0048 :=
    @g_fnbrfvb (syn_cvv) R (syn_cima (syn_cswap) R) (syn_cimage (syn_cswap))
  have p0049 :=
    Nominal.mp p0047 p0048
  have p0050 :=
    @g_mpbir (.classEq (syn_cfv (syn_cimage (syn_cswap)) R) (syn_cima (syn_cswap) R)) (syn_wbr R (syn_cimage (syn_cswap)) (syn_cima (syn_cswap) R)) p0045 p0049
  have p0051 :=
    @g_dfcnv2 R
  have p0052 :=
    @g_eqtr4i (syn_cfv (syn_cimage (syn_cswap)) R) (syn_cima (syn_cswap) R) (syn_ccnv R) p0050 p0051
  have p0053 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cop R D)) (syn_cfv (syn_cimage (syn_cswap)) R) (syn_ccnv R) p0040 p0052
  have p0054 :=
    @g_opeq12i (syn_cfv (syn_c1st) (syn_cop R D)) R (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cop R D)) (syn_ccnv R) p0030 p0053
  have p0055 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) (syn_cop R D)) (syn_cop (syn_cfv (syn_c1st) (syn_cop R D)) (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cop R D))) (syn_cop R (syn_ccnv R)) p0029 p0054
  have p0056 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) (syn_cop R D)) (syn_cop R (syn_ccnv R)) (syn_clndifop) p0055
  have p0057 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))) (syn_cop R D)) (syn_cfv (syn_clndifop) (syn_cfv (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) (syn_cop R D))) (syn_cfv (syn_clndifop) (syn_cop R (syn_ccnv R))) p0019 p0056
  have p0058 :=
    (by simpa [syn_co] using (Nominal.classEqRefl (syn_co R (syn_clndifop) (syn_ccnv R))))
  have p0059 :=
    @g_eqcomi (syn_co R (syn_clndifop) (syn_ccnv R)) (syn_cfv (syn_clndifop) (syn_cop R (syn_ccnv R))) p0058
  have p0060 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))) (syn_cop R D)) (syn_cfv (syn_clndifop) (syn_cop R (syn_ccnv R))) (syn_co R (syn_clndifop) (syn_ccnv R)) p0057 p0059
  have p0061 :=
    @g_cnvex R hyp_lnpwasymfnval_1
  have p0062 :=
    @g_pm3_2i (.classMem R (syn_cvv)) (.classMem (syn_ccnv R) (syn_cvv)) hyp_lnpwasymfnval_1 p0061
  have p0063 :=
    @g_lndifopvalg R (syn_ccnv R) (syn_cvv) (syn_cvv)
  have p0064 :=
    Nominal.mp p0062 p0063
  have p0065 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))) (syn_cop R D)) (syn_co R (syn_clndifop) (syn_ccnv R)) (syn_cdif R (syn_ccnv R)) p0060 p0064
  have p0066 :=
    @g_eqtri (syn_cfv (syn_clnpwasymfn) (syn_cop R D)) (syn_cfv (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))) (syn_cop R D)) (syn_cdif R (syn_ccnv R)) p0001 p0065
  exact p0066

noncomputable def g_tc3lecan
    (M : Class) (N : Class) (hyp_tc3lecb_1 : Nominal.NPrf (.classMem M (syn_cncs))) (hyp_tc3lecb_2 : Nominal.NPrf (.classMem N (syn_cncs))) :
    Nominal.NPrf (.imp (syn_wbr (syn_ctc (syn_ctc (syn_ctc M))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))) (syn_wbr M (syn_clec) N)) := by
  let proofSupport : Finset Var := M.fv ∪ N.fv
  have p0000 :=
    @g_pm3_2i (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) hyp_tc3lecb_1 hyp_tc3lecb_2
  have p0001 :=
    @g_tlecg M N
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_tccl M
  have p0004 :=
    Nominal.mp hyp_tc3lecb_1 p0003
  have p0005 :=
    @g_tccl N
  have p0006 :=
    Nominal.mp hyp_tc3lecb_2 p0005
  have p0007 :=
    @g_pm3_2i (.classMem (syn_ctc M) (syn_cncs)) (.classMem (syn_ctc N) (syn_cncs)) p0004 p0006
  have p0008 :=
    @g_tlecg (syn_ctc M) (syn_ctc N)
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_bitri (syn_wbr M (syn_clec) N) (syn_wbr (syn_ctc M) (syn_clec) (syn_ctc N)) (syn_wbr (syn_ctc (syn_ctc M)) (syn_clec) (syn_ctc (syn_ctc N))) p0002 p0009
  have p0011 :=
    @g_tccl M
  have p0012 :=
    Nominal.mp hyp_tc3lecb_1 p0011
  have p0013 :=
    @g_tccl (syn_ctc M)
  have p0014 :=
    Nominal.mp p0012 p0013
  have p0015 :=
    @g_tccl N
  have p0016 :=
    Nominal.mp hyp_tc3lecb_2 p0015
  have p0017 :=
    @g_tccl (syn_ctc N)
  have p0018 :=
    Nominal.mp p0016 p0017
  have p0019 :=
    @g_pm3_2i (.classMem (syn_ctc (syn_ctc M)) (syn_cncs)) (.classMem (syn_ctc (syn_ctc N)) (syn_cncs)) p0014 p0018
  have p0020 :=
    @g_tlecg (syn_ctc (syn_ctc M)) (syn_ctc (syn_ctc N))
  have p0021 :=
    Nominal.mp p0019 p0020
  have p0022 :=
    @g_bitri (syn_wbr M (syn_clec) N) (syn_wbr (syn_ctc (syn_ctc M)) (syn_clec) (syn_ctc (syn_ctc N))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc M))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))) p0010 p0021
  have p0023 :=
    @g_biimpri (syn_wbr M (syn_clec) N) (syn_wbr (syn_ctc (syn_ctc (syn_ctc M))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))) p0022
  exact p0023

noncomputable def g_fdifssa
    (A : Class) (B : Class) (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_B_R : Disjoint B.fv R.fv) :
    Nominal.NPrf (syn_wss (syn_cfdif R A B) A) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  let d : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  have fresh_d : d ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_not_R : d ∉ R.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_d_ne_x : d ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_d : x ≠ d :=
    Ne.symm fresh_d_ne_x
  have fresh_d_ne_y : d ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_d : y ≠ d :=
    Ne.symm fresh_d_ne_y
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0003 : d ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0007 : d ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : d ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : d ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show d ≠ x from (by exact fresh_d_ne_x))
  have dv_cache_0014 : d ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show d ≠ y from (by exact fresh_d_ne_y))
  have dv_cache_0015 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fdif x y A B R d dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0001 :=
    @g_ssrab2 (syn_wrex x B (syn_wrex y B (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y))))) d A dv_cache_0003
  have p0002 :=
    @g_eqsstri (syn_cfdif R A B) (syn_crab d A (syn_wrex x B (syn_wrex y B (.classMem (.cv d) (syn_cfpiv R A (.cv x) (.cv y)))))) A p0000 p0001
  exact p0002

noncomputable def g_fdordwe2
    (A : Class) (B : Class) (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_B_R : Disjoint B.fv R.fv) (hyp_fdordwe2_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_fdordwe2_2 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_fdordwe2_3 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wbr R (syn_cwe) A) (syn_wbr (syn_cfdord R A B) (syn_cwe) (syn_cfdif R A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0003 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have p0000 :=
    @g_id (syn_wbr R (syn_cwe) A)
  have p0001 :=
    @g_fdifssa A B R dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0002 :=
    @g_a1i (syn_wss (syn_cfdif R A B) A) (syn_wbr R (syn_cwe) A) p0001
  have p0003 :=
    @g_fdifex2 A B R dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fdordwe2_1 hyp_fdordwe2_2 hyp_fdordwe2_3
  have p0004 :=
    @g_werestrndv (syn_wbr R (syn_cwe) A) (syn_cfdif R A B) A R p0000 p0002 p0003
  have p0005 :=
    (by simpa [syn_cfdord] using (Nominal.classEqRefl (syn_cfdord R A B)))
  have p0006 :=
    @g_breq1i (syn_cfdord R A B) (syn_cin R (syn_cxp (syn_cfdif R A B) (syn_cfdif R A B))) (syn_cfdif R A B) (syn_cwe) p0005
  have p0007 :=
    @g_sylibr (syn_wbr R (syn_cwe) A) (syn_wbr (syn_cin R (syn_cxp (syn_cfdif R A B) (syn_cfdif R A B))) (syn_cwe) (syn_cfdif R A B)) (syn_wbr (syn_cfdord R A B) (syn_cwe) (syn_cfdif R A B)) p0004 p0006
  exact p0007

noncomputable def g_ncpw1pw2
    (A : Class) (hyp_ncpw1pw2_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cnc (syn_cpw1 (syn_cpw (syn_cpw A)))) (syn_cnc (syn_cpw (syn_cpw (syn_cpw1 A))))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_pwex A hyp_ncpw1pw2_1
  have p0001 :=
    @g_enpw1pw (syn_cpw A) p0000
  have p0002 :=
    @g_enpw1pw A hyp_ncpw1pw2_1
  have p0003 :=
    @g_enpw (syn_cpw1 (syn_cpw A)) (syn_cpw (syn_cpw1 A))
  have p0004 :=
    Nominal.mp p0002 p0003
  have p0005 :=
    @g_pm3_2i (syn_wbr (syn_cpw1 (syn_cpw (syn_cpw A))) (syn_cen) (syn_cpw (syn_cpw1 (syn_cpw A)))) (syn_wbr (syn_cpw (syn_cpw1 (syn_cpw A))) (syn_cen) (syn_cpw (syn_cpw (syn_cpw1 A)))) p0001 p0004
  have p0006 :=
    @g_entr (syn_cpw1 (syn_cpw (syn_cpw A))) (syn_cpw (syn_cpw1 (syn_cpw A))) (syn_cpw (syn_cpw (syn_cpw1 A)))
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_pwex A hyp_ncpw1pw2_1
  have p0009 :=
    @g_pwex (syn_cpw A) p0008
  have p0010 :=
    @g_pw1ex (syn_cpw (syn_cpw A)) p0009
  have p0011 :=
    @g_eqnc (syn_cpw1 (syn_cpw (syn_cpw A))) (syn_cpw (syn_cpw (syn_cpw1 A))) p0010
  have p0012 :=
    @g_mpbir (.classEq (syn_cnc (syn_cpw1 (syn_cpw (syn_cpw A)))) (syn_cnc (syn_cpw (syn_cpw (syn_cpw1 A))))) (syn_wbr (syn_cpw1 (syn_cpw (syn_cpw A))) (syn_cen) (syn_cpw (syn_cpw (syn_cpw1 A)))) p0007 p0011
  exact p0012

noncomputable def g_tc3nc
    (A : Class) (hyp_tc3nc_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_cnc A)))) (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 A))))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_tc2nc A hyp_tc3nc_1
  have p0001 :=
    @g_tceq (syn_ctc (syn_ctc (syn_cnc A))) (syn_cnc (syn_cpw1 (syn_cpw1 A)))
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_pw1ex A hyp_tc3nc_1
  have p0004 :=
    @g_pw1ex (syn_cpw1 A) p0003
  have p0005 :=
    @g_tcnc (syn_cpw1 (syn_cpw1 A)) p0004
  have p0006 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_ctc (syn_cnc A)))) (syn_ctc (syn_cnc (syn_cpw1 (syn_cpw1 A)))) (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 A)))) p0002 p0005
  exact p0006

noncomputable def g_kqlefintcb
    (M : Class) (N : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wb (syn_wbr M (syn_ckqrel (syn_clefin)) N) (syn_wbr (syn_ctc M) (syn_ckqrel (syn_clefin)) (syn_ctc N)))) := by
  let proofSupport : Finset Var := M.fv ∪ N.fv
  have p0000 :=
    @g_kqlefinbr M N (syn_cnnc) (syn_cnnc)
  have p0001 :=
    @g_tfinlefin M N
  have p0002 :=
    @g_bitrd (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wbr M (syn_ckqrel (syn_clefin)) N) (.classMem (syn_copk M N) (syn_clefin)) (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_clefin)) p0000 p0001
  have p0003 :=
    @g_simpl (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
  have p0004 :=
    @g_nntctfin M
  have p0005 :=
    @g_syl (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classMem M (syn_cnnc)) (.classEq (syn_ctc M) (syn_ctfin M)) p0003 p0004
  have p0006 :=
    @g_simpr (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
  have p0007 :=
    @g_nntctfin N
  have p0008 :=
    @g_syl (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classMem N (syn_cnnc)) (.classEq (syn_ctc N) (syn_ctfin N)) p0006 p0007
  have p0009 :=
    @g_opkeq12d (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_ctc M) (syn_ctfin M) (syn_ctc N) (syn_ctfin N) p0005 p0008
  have p0010 :=
    @g_eleq1d (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_copk (syn_ctc M) (syn_ctc N)) (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_clefin) p0009
  have p0011 :=
    @g_bicomd (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classMem (syn_copk (syn_ctc M) (syn_ctc N)) (syn_clefin)) (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_clefin)) p0010
  have p0012 :=
    @g_bitrd (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wbr M (syn_ckqrel (syn_clefin)) N) (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_clefin)) (.classMem (syn_copk (syn_ctc M) (syn_ctc N)) (syn_clefin)) p0002 p0011
  have p0013 :=
    @g_simpl (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
  have p0014 :=
    @g_nntccl M
  have p0015 :=
    @g_syl (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classMem M (syn_cnnc)) (.classMem (syn_ctc M) (syn_cnnc)) p0013 p0014
  have p0016 :=
    @g_simpr (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
  have p0017 :=
    @g_nntccl N
  have p0018 :=
    @g_syl (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classMem N (syn_cnnc)) (.classMem (syn_ctc N) (syn_cnnc)) p0016 p0017
  have p0019 :=
    @g_jca (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (.classMem (syn_ctc M) (syn_cnnc)) (.classMem (syn_ctc N) (syn_cnnc)) p0015 p0018
  have p0020 :=
    @g_kqlefinbr (syn_ctc M) (syn_ctc N) (syn_cnnc) (syn_cnnc)
  have p0021 :=
    @g_syl (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wa (.classMem (syn_ctc M) (syn_cnnc)) (.classMem (syn_ctc N) (syn_cnnc))) (syn_wb (syn_wbr (syn_ctc M) (syn_ckqrel (syn_clefin)) (syn_ctc N)) (.classMem (syn_copk (syn_ctc M) (syn_ctc N)) (syn_clefin))) p0019 p0020
  have p0022 :=
    @g_bicomd (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wbr (syn_ctc M) (syn_ckqrel (syn_clefin)) (syn_ctc N)) (.classMem (syn_copk (syn_ctc M) (syn_ctc N)) (syn_clefin)) p0021
  have p0023 :=
    @g_bitrd (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wbr M (syn_ckqrel (syn_clefin)) N) (.classMem (syn_copk (syn_ctc M) (syn_ctc N)) (syn_clefin)) (syn_wbr (syn_ctc M) (syn_ckqrel (syn_clefin)) (syn_ctc N)) p0012 p0022
  exact p0023

noncomputable def g_tcnnresfn
     :
    Nominal.NPrf (syn_wfn (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_fntcfn
  have p0001 :=
    @g_pw1ss1c (syn_cnnc)
  have p0002 :=
    @g_pm3_2i (syn_wfn (syn_ctcfn) (syn_c1c)) (syn_wss (syn_cpw1 (syn_cnnc)) (syn_c1c)) p0000 p0001
  have p0003 :=
    @g_fnssres (syn_c1c) (syn_cpw1 (syn_cnnc)) (syn_ctcfn)
  have p0004 :=
    Nominal.mp p0002 p0003
  exact p0004

noncomputable def g_tcnnex
     :
    Nominal.NPrf (.classMem (syn_ctcnn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_tcfnex
  have p0001 :=
    @g_nncex
  have p0002 :=
    @g_pw1ex (syn_cnnc) p0001
  have p0003 :=
    @g_resex (syn_ctcfn) (syn_cpw1 (syn_cnnc)) p0000 p0002
  have p0004 :=
    @g_rnex (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) p0003
  have p0005 :=
    (by simpa [syn_ctcnn] using (Nominal.classEqRefl (syn_ctcnn)))
  have p0006 :=
    @g_eleq1i (syn_ctcnn) (syn_crn (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc)))) (syn_cvv) p0005
  have p0007 :=
    @g_mpbir (.classMem (syn_ctcnn) (syn_cvv)) (.classMem (syn_crn (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc)))) (syn_cvv)) p0004 p0006
  exact p0007

noncomputable def g_eltcnn
    (A : Class) (q : Var) (dv_A_q : q ∉ A.fv) :
    Nominal.NPrf (syn_wb (.classMem A (syn_ctcnn)) (syn_wrex q (syn_cpw1 (syn_cnnc)) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A))) := by
  let proofSupport : Finset Var := A.fv ∪ ({q} : Finset Var)
  have dv_cache_0001 : q ∉ ((syn_cpw1 (syn_cnnc))).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctcfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    (by simpa [syn_ctcnn] using (Nominal.classEqRefl (syn_ctcnn)))
  have p0001 :=
    @g_eleq2i (syn_ctcnn) (syn_crn (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc)))) A p0000
  have p0002 :=
    @g_fntcfn
  have p0003 :=
    @g_pw1ss1c (syn_cnnc)
  have p0004 :=
    @g_pm3_2i (syn_wfn (syn_ctcfn) (syn_c1c)) (syn_wss (syn_cpw1 (syn_cnnc)) (syn_c1c)) p0002 p0003
  have p0005 :=
    @g_fnssres (syn_c1c) (syn_cpw1 (syn_cnnc)) (syn_ctcfn)
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_fvelrnb q (syn_cpw1 (syn_cnnc)) A (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_bitri (.classMem A (syn_ctcnn)) (.classMem A (syn_crn (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))))) (syn_wrex q (syn_cpw1 (syn_cnnc)) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) A)) p0001 p0008
  exact p0009

noncomputable def g_tcfnfvcl
    (B : Class) :
    Nominal.NPrf (.imp (.classMem B (syn_cvv)) (.classEq (syn_cfv (syn_ctcfn) (syn_csn B)) (syn_ctc B))) := by
  let proofSupport : Finset Var := B.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (h)
  have dv_cache_0001 : x ∉ (B).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classEq (syn_cfv (syn_ctcfn) (syn_csn B)) (syn_ctc B))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctcfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_sneq (.cv x) B
  have p0001 :=
    @g_fveq2d (.classEq (.cv x) B) (syn_csn (.cv x)) (syn_csn B) (syn_ctcfn) p0000
  have p0002 :=
    @g_tceq (.cv x) B
  have p0003 :=
    @g_eqeq12d (.classEq (.cv x) B) (syn_cfv (syn_ctcfn) (syn_csn (.cv x))) (syn_cfv (syn_ctcfn) (syn_csn B)) (syn_ctc (.cv x)) (syn_ctc B) p0001 p0002
  have p0004 :=
    @g_vex x
  have p0005 :=
    @g_tcfnfv (.cv x) p0004
  have p0006 :=
    @g_vtoclg (.classEq (syn_cfv (syn_ctcfn) (syn_csn (.cv x))) (syn_ctc (.cv x))) (.classEq (syn_cfv (syn_ctcfn) (syn_csn B)) (syn_ctc B)) x B (syn_cvv) dv_cache_0001 dv_cache_0002 p0003 p0005
  exact p0006

noncomputable def g_tcnnssnn
     :
    Nominal.NPrf (syn_wss (syn_ctcnn) (syn_cnnc)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let q : Var := freshVar proofSupport 0
  let p : Var := freshVar proofSupport 1
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_q_ne_p : q ≠ p := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_p_ne_q : p ≠ q :=
    Ne.symm fresh_q_ne_p
  have dv_cache_0001 : p ∉ ((Class.cv q)).fv := by
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((Wff.classMem (.cv q) (syn_cnnc))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((syn_ctcnn)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ctcnn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eltcnn (.cv q) p dv_cache_0001
  have p0001 :=
    @g_biimpi (.classMem (.cv q) (syn_ctcnn)) (syn_wrex p (syn_cpw1 (syn_cnnc)) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (.cv q))) p0000
  have p0002 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (.cv q))
  have p0003 :=
    @g_hnwpw1argcl (syn_cnnc) p
  have p0004 :=
    @g_simpl (.classMem (syn_cuni (.cv p)) (syn_cnnc)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))
  have p0005 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (syn_wa (.classMem (syn_cuni (.cv p)) (syn_cnnc)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))) (.classMem (syn_cuni (.cv p)) (syn_cnnc)) p0003 p0004
  have p0006 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (.cv q))) (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (syn_cuni (.cv p)) (syn_cnnc)) p0002 p0005
  have p0007 :=
    @g_nntccl (syn_cuni (.cv p))
  have p0008 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (.cv q))) (.classMem (syn_cuni (.cv p)) (syn_cnnc)) (.classMem (syn_ctc (syn_cuni (.cv p))) (syn_cnnc)) p0006 p0007
  have p0009 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (.cv q))
  have p0010 :=
    @g_fvres (.cv p) (syn_cpw1 (syn_cnnc)) (syn_ctcfn)
  have p0011 :=
    @g_hnwpw1argcl (syn_cnnc) p
  have p0012 :=
    @g_simpr (.classMem (syn_cuni (.cv p)) (syn_cnnc)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))
  have p0013 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (syn_wa (.classMem (syn_cuni (.cv p)) (syn_cnnc)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0011 p0012
  have p0014 :=
    @g_fveq2d (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.cv p) (syn_csn (syn_cuni (.cv p))) (syn_ctcfn) p0013
  have p0015 :=
    @g_eqtrd (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_ctcfn) (.cv p)) (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv p)))) p0010 p0014
  have p0016 :=
    @g_hnwpw1argcl (syn_cnnc) p
  have p0017 :=
    @g_simpl (.classMem (syn_cuni (.cv p)) (syn_cnnc)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))
  have p0018 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (syn_wa (.classMem (syn_cuni (.cv p)) (syn_cnnc)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))) (.classMem (syn_cuni (.cv p)) (syn_cnnc)) p0016 p0017
  have p0019 :=
    @g_elex (syn_cuni (.cv p)) (syn_cnnc)
  have p0020 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (syn_cuni (.cv p)) (syn_cnnc)) (.classMem (syn_cuni (.cv p)) (syn_cvv)) p0018 p0019
  have p0021 :=
    @g_tcfnfvcl (syn_cuni (.cv p))
  have p0022 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (syn_cuni (.cv p)) (syn_cvv)) (.classEq (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv p)))) (syn_ctc (syn_cuni (.cv p)))) p0020 p0021
  have p0023 :=
    @g_eqtrd (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv p)))) (syn_ctc (syn_cuni (.cv p))) p0015 p0022
  have p0024 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (.cv q))) (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_ctc (syn_cuni (.cv p)))) p0009 p0023
  have p0025 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (.cv q))
  have p0026 :=
    @g_eqtr3d (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (.cv q))) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_ctc (syn_cuni (.cv p))) (.cv q) p0024 p0025
  have p0027 :=
    @g_eleq1d (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (.cv q))) (syn_ctc (syn_cuni (.cv p))) (.cv q) (syn_cnnc) p0026
  have p0028 :=
    @g_mpbid (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (.cv q))) (.classMem (syn_ctc (syn_cuni (.cv p))) (syn_cnnc)) (.classMem (.cv q) (syn_cnnc)) p0008 p0027
  have p0029 :=
    @g_rexlimiva (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (.cv q)) (.classMem (.cv q) (syn_cnnc)) p (syn_cpw1 (syn_cnnc)) dv_cache_0002 p0028
  have p0030 :=
    @g_syl (.classMem (.cv q) (syn_ctcnn)) (syn_wrex p (syn_cpw1 (syn_cnnc)) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (.cv q))) (.classMem (.cv q) (syn_cnnc)) p0001 p0029
  have p0031 :=
    @g_ssriv q (syn_ctcnn) (syn_cnnc) dv_cache_0003 dv_cache_0004 p0030
  exact p0031

noncomputable def g_nntcsuc
    (N : Class) :
    Nominal.NPrf (.imp (.classMem N (syn_cnnc)) (.classEq (syn_ctc (syn_cplc N (syn_c1c))) (syn_cplc (syn_ctc N) (syn_c1c)))) := by
  let proofSupport : Finset Var := N.fv
  have p0000 :=
    @g_nnnc N
  have p0001 :=
    @g_n_1cnc
  have p0002 :=
    @g_a1i (.classMem (syn_c1c) (syn_cncs)) (.classMem N (syn_cnnc)) p0001
  have p0003 :=
    @g_jca (.classMem N (syn_cnnc)) (.classMem N (syn_cncs)) (.classMem (syn_c1c) (syn_cncs)) p0000 p0002
  have p0004 :=
    @g_tcdi N (syn_c1c)
  have p0005 :=
    @g_syl (.classMem N (syn_cnnc)) (syn_wa (.classMem N (syn_cncs)) (.classMem (syn_c1c) (syn_cncs))) (.classEq (syn_ctc (syn_cplc N (syn_c1c))) (syn_cplc (syn_ctc N) (syn_ctc (syn_c1c)))) p0003 p0004
  have p0006 :=
    @g_tc1c
  have p0007 :=
    @g_a1i (.classEq (syn_ctc (syn_c1c)) (syn_c1c)) (.classMem N (syn_cnnc)) p0006
  have p0008 :=
    @g_addceq2d (.classMem N (syn_cnnc)) (syn_ctc (syn_c1c)) (syn_c1c) (syn_ctc N) p0007
  have p0009 :=
    @g_eqtrd (.classMem N (syn_cnnc)) (syn_ctc (syn_cplc N (syn_c1c))) (syn_cplc (syn_ctc N) (syn_ctc (syn_c1c))) (syn_cplc (syn_ctc N) (syn_c1c)) p0005 p0008
  exact p0009

#print axioms g_nntcsuc

end NFChoice.DirectNominalPrf.WPPReplay
