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
import NominalWPPReplayChunk012BCompact001

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

noncomputable def g_brdisj
    (A : Class) (B : Class) (hyp_brdisj_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_brdisj_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wb (syn_wbr A (syn_cdisj) B) (.classEq (syn_cin A B) (syn_c0))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_brdisjg A B (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (syn_wb (syn_wbr A (syn_cdisj) B) (.classEq (syn_cin A B) (syn_c0))) hyp_brdisj_1 hyp_brdisj_2 p0000
  exact p0001

noncomputable def g_disjex
     :
    Nominal.NPrf (.classMem (syn_cdisj) (syn_cvv)) := by
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
  have dv_cache_0002 : z ∉ ((syn_cop (.cv x) (.cv y))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_ctxp (syn_csset) (syn_csset))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_ccompl (syn_cima (syn_ctxp (syn_csset) (syn_csset)) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((syn_ccompl (syn_cima (syn_ctxp (syn_csset) (syn_csset)) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_disj x y dv_cache_0001
  have p0001 :=
    @g_oteltxp (syn_csn (.cv z)) (.cv x) (.cv y) (syn_csset) (syn_csset)
  have p0002 :=
    @g_vex z
  have p0003 :=
    @g_vex x
  have p0004 :=
    @g_opelssetsn (.cv z) (.cv x) p0002 p0003
  have p0005 :=
    @g_vex y
  have p0006 :=
    @g_opelssetsn (.cv z) (.cv y) p0002 p0005
  have p0007_e00_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv z)) (.cv x)) (syn_csset)) (.objMem z x)) :=
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
      p0004
  have p0007_e01_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv z)) (.cv y)) (syn_csset)) (.objMem z y)) :=
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
      p0006
  have p0007 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv z)) (.cv x)) (syn_csset)) (.objMem z x) (.classMem (syn_cop (syn_csn (.cv z)) (.cv y)) (syn_csset)) (.objMem z y) p0007_e00_recanon p0007_e01_recanon
  have p0008 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_ctxp (syn_csset) (syn_csset))) (syn_wa (.classMem (syn_cop (syn_csn (.cv z)) (.cv x)) (syn_csset)) (.classMem (syn_cop (syn_csn (.cv z)) (.cv y)) (syn_csset))) (syn_wa (.objMem z x) (.objMem z y)) p0001 p0007
  have p0009 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_ctxp (syn_csset) (syn_csset))) (syn_wa (.objMem z x) (.objMem z y)) z p0008
  have p0010 :=
    @g_elima1c z (syn_cop (.cv x) (.cv y)) (syn_ctxp (syn_csset) (syn_csset)) dv_cache_0002 dv_cache_0003
  have p0011 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex z (.cv x) (.objMem z y))))
  have p0012_e02_recanon : Nominal.NPrf (syn_wb (syn_wrex z (.cv x) (.objMem z y)) (syn_wex z (syn_wa (.objMem z x) (.objMem z y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wrex syn_wex syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]
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
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
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
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0011
  have p0012 :=
    @g_n_3bitr4i (syn_wex z (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_ctxp (syn_csset) (syn_csset)))) (syn_wex z (syn_wa (.objMem z x) (.objMem z y))) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cima (syn_ctxp (syn_csset) (syn_csset)) (syn_c1c))) (syn_wrex z (.cv x) (.objMem z y)) p0009 p0010 p0012_e02_recanon
  have p0013 :=
    @g_dfrex2 (.objMem z y) z (.cv x)
  have p0014 :=
    @g_bitri (.classMem (syn_cop (.cv x) (.cv y)) (syn_cima (syn_ctxp (syn_csset) (syn_csset)) (syn_c1c))) (syn_wrex z (.cv x) (.objMem z y)) (.neg (syn_wral z (.cv x) (.neg (.objMem z y)))) p0012 p0013
  have p0015 :=
    @g_con2bii (.classMem (syn_cop (.cv x) (.cv y)) (syn_cima (syn_ctxp (syn_csset) (syn_csset)) (syn_c1c))) (syn_wral z (.cv x) (.neg (.objMem z y))) p0014
  have p0016 :=
    @g_disj z (.cv x) (.cv y) dv_cache_0004 dv_cache_0005
  have p0017 :=
    @g_opex (.cv x) (.cv y) p0003 p0005
  have p0018 :=
    @g_elcompl (syn_cop (.cv x) (.cv y)) (syn_cima (syn_ctxp (syn_csset) (syn_csset)) (syn_c1c)) p0017
  have p0019_e01_recanon : Nominal.NPrf (syn_wb (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0)) (syn_wral z (.cv x) (.neg (.objMem z y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_c0 syn_cdif syn_cvv syn_wral
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0016
  have p0019 :=
    @g_n_3bitr4ri (syn_wral z (.cv x) (.neg (.objMem z y))) (.neg (.classMem (syn_cop (.cv x) (.cv y)) (syn_cima (syn_ctxp (syn_csset) (syn_csset)) (syn_c1c)))) (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0)) (.classMem (syn_cop (.cv x) (.cv y)) (syn_ccompl (syn_cima (syn_ctxp (syn_csset) (syn_csset)) (syn_c1c)))) p0015 p0019_e01_recanon p0018
  have p0020 :=
    @g_opabbi2i (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0)) x y (syn_ccompl (syn_cima (syn_ctxp (syn_csset) (syn_csset)) (syn_c1c))) dv_cache_0006 dv_cache_0007 dv_cache_0001 p0019
  have p0021 :=
    @g_eqtr4i (syn_cdisj) (syn_copab x y (.classEq (syn_cin (.cv x) (.cv y)) (syn_c0))) (syn_ccompl (syn_cima (syn_ctxp (syn_csset) (syn_csset)) (syn_c1c))) p0000 p0020
  have p0022 :=
    @g_ssetex
  have p0023 :=
    @g_ssetex
  have p0024 :=
    @g_txpex (syn_csset) (syn_csset) p0022 p0023
  have p0025 :=
    @g_n_1cex
  have p0026 :=
    @g_imaex (syn_ctxp (syn_csset) (syn_csset)) (syn_c1c) p0024 p0025
  have p0027 :=
    @g_complex (syn_cima (syn_ctxp (syn_csset) (syn_csset)) (syn_c1c)) p0026
  have p0028 :=
    @g_eqeltri (syn_cdisj) (syn_ccompl (syn_cima (syn_ctxp (syn_csset) (syn_csset)) (syn_c1c))) (syn_cvv) p0021 p0027
  exact p0028

#print axioms g_disjex

end NFChoice.DirectNominalPrf.WPPReplay
