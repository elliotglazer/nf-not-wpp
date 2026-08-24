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
import NominalWPPReplayChunk013Compact001Part029

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

noncomputable def g_qsexg
    (A : Class) (R : Class) (V : Class) (W : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem R V) (.classMem A W)) (.classMem (syn_cqs A R) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ R.fv ∪ V.fv ∪ W.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_W : x ∉ W.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_V : y ∉ V.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_W : y ∉ W.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_V : z ∉ V.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_W : z ∉ W.fv := by
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
  have dv_cache_0001 : y ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have dv_cache_0006 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((syn_ccompl (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R)))) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : z ∉ ((syn_cop (syn_csn (.cv y)) (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : z ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : z ∉ ((syn_cec (.cv y) R)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, fresh_z_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((syn_cima (syn_ccompl (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R)))) (syn_c1c))) (syn_cpw1 A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_qs y x A R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @g_elimapw1 y (.cv x) (syn_ccompl (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R)))) (syn_c1c))) A dv_cache_0006 dv_cache_0007 dv_cache_0001
  have p0002 :=
    @g_elima1c z (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R)))) dv_cache_0008 dv_cache_0009
  have p0003 :=
    @g_elsymdif (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))) (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R)))
  have p0004 :=
    @g_snex (.cv y)
  have p0005 :=
    @g_otelins2 (syn_csn (.cv z)) (syn_csn (.cv y)) (.cv x) (syn_csset) p0004
  have p0006 :=
    @g_vex z
  have p0007 :=
    @g_vex x
  have p0008 :=
    @g_opelssetsn (.cv z) (.cv x) p0006 p0007
  have p0009_e01_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv z)) (.cv x)) (syn_csset)) (.objMem z x)) :=
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
    @g_bitri (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))) (syn_cins2 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv z)) (.cv x)) (syn_csset)) (.objMem z x) p0005 p0009_e01_recanon
  have p0010 :=
    @g_otelins3 (syn_csn (.cv z)) (syn_csn (.cv y)) (.cv x) (syn_csi (syn_ccnv R)) p0007
  have p0011 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv z) (syn_ccnv R) (.cv y))))
  have p0012 :=
    @g_brcnv (.cv z) (.cv y) R
  have p0013 :=
    @g_bitr3i (.classMem (syn_cop (.cv z) (.cv y)) (syn_ccnv R)) (syn_wbr (.cv z) (syn_ccnv R) (.cv y)) (syn_wbr (.cv y) R (.cv z)) p0011 p0012
  have p0014 :=
    @g_vex y
  have p0015 :=
    @g_opsnelsi (.cv z) (.cv y) (syn_ccnv R) p0006 p0014
  have p0016 :=
    @g_elec (.cv z) (.cv y) R
  have p0017 :=
    @g_n_3bitr4i (.classMem (syn_cop (.cv z) (.cv y)) (syn_ccnv R)) (syn_wbr (.cv y) R (.cv z)) (.classMem (syn_cop (syn_csn (.cv z)) (syn_csn (.cv y))) (syn_csi (syn_ccnv R))) (.classMem (.cv z) (syn_cec (.cv y) R)) p0013 p0015 p0016
  have p0018 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))) (syn_cins3 (syn_csi (syn_ccnv R)))) (.classMem (syn_cop (syn_csn (.cv z)) (syn_csn (.cv y))) (syn_csi (syn_ccnv R))) (.classMem (.cv z) (syn_cec (.cv y) R)) p0010 p0017
  have p0019 :=
    @g_bibi12i (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))) (syn_cins2 (syn_csset))) (.objMem z x) (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))) (syn_cins3 (syn_csi (syn_ccnv R)))) (.classMem (.cv z) (syn_cec (.cv y) R)) p0009 p0018
  have p0020 :=
    @g_notbii (syn_wb (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))) (syn_cins2 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))) (syn_cins3 (syn_csi (syn_ccnv R))))) (syn_wb (.objMem z x) (.classMem (.cv z) (syn_cec (.cv y) R))) p0019
  have p0021 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))) (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R))))) (.neg (syn_wb (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))) (syn_cins2 (syn_csset))) (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))) (syn_cins3 (syn_csi (syn_ccnv R)))))) (.neg (syn_wb (.objMem z x) (.classMem (.cv z) (syn_cec (.cv y) R)))) p0003 p0020
  have p0022 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))) (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R))))) (.neg (syn_wb (.objMem z x) (.classMem (.cv z) (syn_cec (.cv y) R)))) z p0021
  have p0023 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R)))) (syn_c1c))) (syn_wex z (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))) (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R)))))) (syn_wex z (.neg (syn_wb (.objMem z x) (.classMem (.cv z) (syn_cec (.cv y) R))))) p0002 p0022
  have p0024 :=
    @g_notbii (.classMem (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R)))) (syn_c1c))) (syn_wex z (.neg (syn_wb (.objMem z x) (.classMem (.cv z) (syn_cec (.cv y) R))))) p0023
  have p0025 :=
    @g_opex (syn_csn (.cv y)) (.cv x) p0004 p0007
  have p0026 :=
    @g_elcompl (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R)))) (syn_c1c)) p0025
  have p0027 :=
    @g_alex (syn_wb (.objMem z x) (.classMem (.cv z) (syn_cec (.cv y) R))) z
  have p0028 :=
    @g_n_3bitr4i (.neg (.classMem (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R)))) (syn_c1c)))) (.neg (syn_wex z (.neg (syn_wb (.objMem z x) (.classMem (.cv z) (syn_cec (.cv y) R)))))) (.classMem (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_ccompl (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R)))) (syn_c1c)))) (.all z (syn_wb (.objMem z x) (.classMem (.cv z) (syn_cec (.cv y) R)))) p0024 p0026 p0027
  have p0029 :=
    @g_dfcleq z (.cv x) (syn_cec (.cv y) R) dv_cache_0010 dv_cache_0011
  have p0030_e01_recanon : Nominal.NPrf (syn_wb (.classEq (.cv x) (syn_cec (.cv y) R)) (.all z (syn_wb (.objMem z x) (.classMem (.cv z) (syn_cec (.cv y) R))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cec syn_cima syn_wrex syn_wex syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.same _
              ·
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0029
  have p0030 :=
    @g_bitr4i (.classMem (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_ccompl (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R)))) (syn_c1c)))) (.all z (syn_wb (.objMem z x) (.classMem (.cv z) (syn_cec (.cv y) R)))) (.classEq (.cv x) (syn_cec (.cv y) R)) p0028 p0030_e01_recanon
  have p0031 :=
    @g_rexbii (.classMem (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_ccompl (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R)))) (syn_c1c)))) (.classEq (.cv x) (syn_cec (.cv y) R)) y A p0030
  have p0032 :=
    @g_bitri (.classMem (.cv x) (syn_cima (syn_ccompl (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R)))) (syn_c1c))) (syn_cpw1 A))) (syn_wrex y A (.classMem (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_ccompl (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R)))) (syn_c1c))))) (syn_wrex y A (.classEq (.cv x) (syn_cec (.cv y) R))) p0001 p0031
  have p0033 :=
    @g_eqabi (syn_wrex y A (.classEq (.cv x) (syn_cec (.cv y) R))) x (syn_cima (syn_ccompl (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R)))) (syn_c1c))) (syn_cpw1 A)) dv_cache_0012 p0032
  have p0034 :=
    @g_eqtr4i (syn_cqs A R) (.cab x (syn_wrex y A (.classEq (.cv x) (syn_cec (.cv y) R)))) (syn_cima (syn_ccompl (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R)))) (syn_c1c))) (syn_cpw1 A)) p0000 p0033
  have p0035 :=
    @g_ssetex
  have p0036 :=
    @g_ins2ex (syn_csset) p0035
  have p0037 :=
    @g_cnvexg R V
  have p0038 :=
    @g_siexg (syn_ccnv R) (syn_cvv)
  have p0039 :=
    @g_ins3exg (syn_csi (syn_ccnv R)) (syn_cvv)
  have p0040 :=
    @g_n_3syl (.classMem R V) (.classMem (syn_ccnv R) (syn_cvv)) (.classMem (syn_csi (syn_ccnv R)) (syn_cvv)) (.classMem (syn_cins3 (syn_csi (syn_ccnv R))) (syn_cvv)) p0037 p0038 p0039
  have p0041 :=
    @g_symdifexg (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R))) (syn_cvv) (syn_cvv)
  have p0042 :=
    @g_sylancr (.classMem R V) (.classMem (syn_cins2 (syn_csset)) (syn_cvv)) (.classMem (syn_cins3 (syn_csi (syn_ccnv R))) (syn_cvv)) (.classMem (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R)))) (syn_cvv)) p0036 p0040 p0041
  have p0043 :=
    @g_n_1cex
  have p0044 :=
    @g_imaexg (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R)))) (syn_c1c) (syn_cvv) (syn_cvv)
  have p0045 :=
    @g_sylancl (.classMem R V) (.classMem (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R)))) (syn_cvv)) (.classMem (syn_c1c) (syn_cvv)) (.classMem (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R)))) (syn_c1c)) (syn_cvv)) p0042 p0043 p0044
  have p0046 :=
    @g_complexg (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R)))) (syn_c1c)) (syn_cvv)
  have p0047 :=
    @g_syl (.classMem R V) (.classMem (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R)))) (syn_c1c)) (syn_cvv)) (.classMem (syn_ccompl (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R)))) (syn_c1c))) (syn_cvv)) p0045 p0046
  have p0048 :=
    @g_pw1exg A W
  have p0049 :=
    @g_imaexg (syn_ccompl (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R)))) (syn_c1c))) (syn_cpw1 A) (syn_cvv) (syn_cvv)
  have p0050 :=
    @g_syl2an (.classMem R V) (.classMem (syn_ccompl (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R)))) (syn_c1c))) (syn_cvv)) (.classMem (syn_cpw1 A) (syn_cvv)) (.classMem (syn_cima (syn_ccompl (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R)))) (syn_c1c))) (syn_cpw1 A)) (syn_cvv)) (.classMem A W) p0047 p0048 p0049
  have p0051 :=
    @g_syl5eqel (syn_wa (.classMem R V) (.classMem A W)) (syn_cqs A R) (syn_cima (syn_ccompl (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R)))) (syn_c1c))) (syn_cpw1 A)) (syn_cvv) p0034 p0050
  exact p0051

noncomputable def g_qsex
    (A : Class) (R : Class) (hyp_qsex_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_qsex_2 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cqs A R) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv ∪ R.fv
  have p0000 :=
    @g_qsexg A R (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem R (syn_cvv)) (.classMem A (syn_cvv)) (.classMem (syn_cqs A R) (syn_cvv)) hyp_qsex_1 hyp_qsex_2 p0000
  exact p0001

noncomputable def g_ectocld
    (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class) (B : Class) (R : Class) (S : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_R_x : x ∉ R.fv) (dv_ch_x : x ∉ ch.fv) (dv_ps_x : x ∉ ps.fv) (hyp_ectocl_1 : Nominal.NPrf (.classEq S (syn_cqs B R))) (hyp_ectocl_2 : Nominal.NPrf (.imp (.classEq (syn_cec (.cv x) R) A) (syn_wb ph ps))) (hyp_ectocld_3 : Nominal.NPrf (.imp (syn_wa ch (.classMem (.cv x) B)) ph)) :
    Nominal.NPrf (.imp (syn_wa ch (.classMem A S)) ps) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ R.fv ∪ S.fv
  have dv_cache_0001 : x ∉ (B).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (ps).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ps_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (ch).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ch_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elqsi x B A R dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_eleq2s (syn_wrex x B (.classEq A (syn_cec (.cv x) R))) A (syn_cqs B R) S p0000 hyp_ectocl_1
  have p0002 :=
    @g_eqcoms (syn_wb ph ps) (syn_cec (.cv x) R) A hyp_ectocl_2
  have p0003 :=
    @g_syl5ibcom (syn_wa ch (.classMem (.cv x) B)) ph (.classEq A (syn_cec (.cv x) R)) ps hyp_ectocld_3 p0002
  have p0004 :=
    @g_rexlimdva ch (.classEq A (syn_cec (.cv x) R)) ps x B dv_cache_0004 dv_cache_0005 p0003
  have p0005 :=
    @g_syl5 (.classMem A S) (syn_wrex x B (.classEq A (syn_cec (.cv x) R))) ch ps p0001 p0004
  have p0006 :=
    @g_imp ch (.classMem A S) ps p0005
  exact p0006

noncomputable def g_ectocl
    (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class) (R : Class) (S : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_R_x : x ∉ R.fv) (dv_ps_x : x ∉ ps.fv) (hyp_ectocl_1 : Nominal.NPrf (.classEq S (syn_cqs B R))) (hyp_ectocl_2 : Nominal.NPrf (.imp (.classEq (syn_cec (.cv x) R) A) (syn_wb ph ps))) (hyp_ectocl_3 : Nominal.NPrf (.imp (.classMem (.cv x) B) ph)) :
    Nominal.NPrf (.imp (.classMem A S) ps) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ R.fv ∪ S.fv
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
  have dv_cache_0003 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (syn_wtru).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (ps).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_ps_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_tru
  have p0001 :=
    @g_adantl (.classMem (.cv x) B) ph syn_wtru hyp_ectocl_3
  have p0002 :=
    @g_ectocld ph ps syn_wtru x A B R S dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 hyp_ectocl_1 hyp_ectocl_2 p0001
  have p0003 :=
    @g_mpan syn_wtru (.classMem A S) ps p0000 p0002
  exact p0003

noncomputable def g_elqsn0
    (A : Class) (B : Class) (R : Class) :
    Nominal.NPrf (.imp (syn_wa (.classEq (syn_cdm R) A) (.classMem B (syn_cqs A R))) (syn_wne B (syn_c0))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
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
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (B).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classEq (syn_cdm R) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_wne B (syn_c0))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eqid (syn_cqs A R)
  have p0001 :=
    @g_neeq1 (syn_cec (.cv x) R) B (syn_c0)
  have p0002 :=
    @g_eleq2 (syn_cdm R) A (.cv x)
  have p0003 :=
    @g_biimpar (.classEq (syn_cdm R) A) (.classMem (.cv x) (syn_cdm R)) (.classMem (.cv x) A) p0002
  have p0004 :=
    @g_ecdmn0 (.cv x) R
  have p0005 :=
    @g_sylib (syn_wa (.classEq (syn_cdm R) A) (.classMem (.cv x) A)) (.classMem (.cv x) (syn_cdm R)) (syn_wne (syn_cec (.cv x) R) (syn_c0)) p0003 p0004
  have p0006 :=
    @g_ectocld (syn_wne (syn_cec (.cv x) R) (syn_c0)) (syn_wne B (syn_c0)) (.classEq (syn_cdm R) A) x B A R (syn_cqs A R) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 p0000 p0001 p0005
  exact p0006

noncomputable def g_mapexi
    (A : Class) (B : Class) (f : Var) (dv_A_f : f ∉ A.fv) (dv_B_f : f ∉ B.fv) (hyp_mapexi_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_mapexi_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (.cab f (syn_wf (.cv f) A B)) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ ({f} : Finset Var)
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
  have fresh_x_ne_f : x ≠ f := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_f_ne_x : f ≠ x :=
    Ne.symm fresh_x_ne_f
  have dv_cache_0001 : x ∉ ((Class.cv f)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_ccnv (syn_cimage (syn_c2nd)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cpw B)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_crn (.cv f))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : f ∉ ((syn_cin (syn_cin (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_c1st))) (syn_csn A))) (syn_cima (syn_ccnv (syn_cimage (syn_c2nd))) (syn_cpw B)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfuns, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_f, dv_B_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elin (.cv f) (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_c1st))) (syn_csn A))
  have p0001 :=
    @g_vex f
  have p0002 :=
    @g_elfuns (.cv f) p0001
  have p0003 :=
    @g_elimasn (syn_ccnv (syn_cimage (syn_c1st))) A (.cv f)
  have p0004 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr A (syn_ccnv (syn_cimage (syn_c1st))) (.cv f))))
  have p0005 :=
    @g_brcnv A (.cv f) (syn_cimage (syn_c1st))
  have p0006 :=
    @g_brimage (.cv f) A (syn_c1st) p0001 hyp_mapexi_1
  have p0007 :=
    @g_dfdm4 (.cv f)
  have p0008 :=
    @g_eqeq2i (syn_cdm (.cv f)) (syn_cima (syn_c1st) (.cv f)) A p0007
  have p0009 :=
    @g_eqcom A (syn_cdm (.cv f))
  have p0010 :=
    @g_n_3bitr2i (syn_wbr (.cv f) (syn_cimage (syn_c1st)) A) (.classEq A (syn_cima (syn_c1st) (.cv f))) (.classEq A (syn_cdm (.cv f))) (.classEq (syn_cdm (.cv f)) A) p0006 p0008 p0009
  have p0011 :=
    @g_bitri (syn_wbr A (syn_ccnv (syn_cimage (syn_c1st))) (.cv f)) (syn_wbr (.cv f) (syn_cimage (syn_c1st)) A) (.classEq (syn_cdm (.cv f)) A) p0005 p0010
  have p0012 :=
    @g_n_3bitr2i (.classMem (.cv f) (syn_cima (syn_ccnv (syn_cimage (syn_c1st))) (syn_csn A))) (.classMem (syn_cop A (.cv f)) (syn_ccnv (syn_cimage (syn_c1st)))) (syn_wbr A (syn_ccnv (syn_cimage (syn_c1st))) (.cv f)) (.classEq (syn_cdm (.cv f)) A) p0003 p0004 p0011
  have p0013 :=
    @g_anbi12i (.classMem (.cv f) (syn_cfuns)) (syn_wfun (.cv f)) (.classMem (.cv f) (syn_cima (syn_ccnv (syn_cimage (syn_c1st))) (syn_csn A))) (.classEq (syn_cdm (.cv f)) A) p0002 p0012
  have p0014 :=
    @g_bitri (.classMem (.cv f) (syn_cin (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_c1st))) (syn_csn A)))) (syn_wa (.classMem (.cv f) (syn_cfuns)) (.classMem (.cv f) (syn_cima (syn_ccnv (syn_cimage (syn_c1st))) (syn_csn A)))) (syn_wa (syn_wfun (.cv f)) (.classEq (syn_cdm (.cv f)) A)) p0000 p0013
  have p0015 :=
    @g_vex x
  have p0016 :=
    @g_brimage (.cv f) (.cv x) (syn_c2nd) p0001 p0015
  have p0017 :=
    @g_brcnv (.cv x) (.cv f) (syn_cimage (syn_c2nd))
  have p0018 :=
    @g_dfrn5 (.cv f)
  have p0019 :=
    @g_eqeq2i (syn_crn (.cv f)) (syn_cima (syn_c2nd) (.cv f)) (.cv x) p0018
  have p0020 :=
    @g_n_3bitr4i (syn_wbr (.cv f) (syn_cimage (syn_c2nd)) (.cv x)) (.classEq (.cv x) (syn_cima (syn_c2nd) (.cv f))) (syn_wbr (.cv x) (syn_ccnv (syn_cimage (syn_c2nd))) (.cv f)) (.classEq (.cv x) (syn_crn (.cv f))) p0016 p0017 p0019
  have p0021 :=
    @g_rexbii (syn_wbr (.cv x) (syn_ccnv (syn_cimage (syn_c2nd))) (.cv f)) (.classEq (.cv x) (syn_crn (.cv f))) x (syn_cpw B) p0020
  have p0022 :=
    @g_elima x (.cv f) (syn_ccnv (syn_cimage (syn_c2nd))) (syn_cpw B) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0023 :=
    @g_risset x (syn_crn (.cv f)) (syn_cpw B) dv_cache_0004 dv_cache_0003
  have p0024 :=
    @g_n_3bitr4i (syn_wrex x (syn_cpw B) (syn_wbr (.cv x) (syn_ccnv (syn_cimage (syn_c2nd))) (.cv f))) (syn_wrex x (syn_cpw B) (.classEq (.cv x) (syn_crn (.cv f)))) (.classMem (.cv f) (syn_cima (syn_ccnv (syn_cimage (syn_c2nd))) (syn_cpw B))) (.classMem (syn_crn (.cv f)) (syn_cpw B)) p0021 p0022 p0023
  have p0025 :=
    @g_rnex (.cv f) p0001
  have p0026 :=
    @g_elpw (syn_crn (.cv f)) B p0025
  have p0027 :=
    @g_bitri (.classMem (.cv f) (syn_cima (syn_ccnv (syn_cimage (syn_c2nd))) (syn_cpw B))) (.classMem (syn_crn (.cv f)) (syn_cpw B)) (syn_wss (syn_crn (.cv f)) B) p0024 p0026
  have p0028 :=
    @g_anbi12i (.classMem (.cv f) (syn_cin (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_c1st))) (syn_csn A)))) (syn_wa (syn_wfun (.cv f)) (.classEq (syn_cdm (.cv f)) A)) (.classMem (.cv f) (syn_cima (syn_ccnv (syn_cimage (syn_c2nd))) (syn_cpw B))) (syn_wss (syn_crn (.cv f)) B) p0014 p0027
  have p0029 :=
    @g_elin (.cv f) (syn_cin (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_c1st))) (syn_csn A))) (syn_cima (syn_ccnv (syn_cimage (syn_c2nd))) (syn_cpw B))
  have p0030 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf (.cv f) A B)))
  have p0031 :=
    (by simpa [syn_wb, syn_wfn] using (Nominal.biimpRefl (syn_wfn (.cv f) A)))
  have p0032 :=
    @g_anbi1i (syn_wfn (.cv f) A) (syn_wa (syn_wfun (.cv f)) (.classEq (syn_cdm (.cv f)) A)) (syn_wss (syn_crn (.cv f)) B) p0031
  have p0033 :=
    @g_bitri (syn_wf (.cv f) A B) (syn_wa (syn_wfn (.cv f) A) (syn_wss (syn_crn (.cv f)) B)) (syn_wa (syn_wa (syn_wfun (.cv f)) (.classEq (syn_cdm (.cv f)) A)) (syn_wss (syn_crn (.cv f)) B)) p0030 p0032
  have p0034 :=
    @g_n_3bitr4i (syn_wa (.classMem (.cv f) (syn_cin (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_c1st))) (syn_csn A)))) (.classMem (.cv f) (syn_cima (syn_ccnv (syn_cimage (syn_c2nd))) (syn_cpw B)))) (syn_wa (syn_wa (syn_wfun (.cv f)) (.classEq (syn_cdm (.cv f)) A)) (syn_wss (syn_crn (.cv f)) B)) (.classMem (.cv f) (syn_cin (syn_cin (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_c1st))) (syn_csn A))) (syn_cima (syn_ccnv (syn_cimage (syn_c2nd))) (syn_cpw B)))) (syn_wf (.cv f) A B) p0028 p0029 p0033
  have p0035 :=
    @g_eqabi (syn_wf (.cv f) A B) f (syn_cin (syn_cin (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_c1st))) (syn_csn A))) (syn_cima (syn_ccnv (syn_cimage (syn_c2nd))) (syn_cpw B))) dv_cache_0005 p0034
  have p0036 :=
    @g_funsex
  have p0037 :=
    @g_n_1stex
  have p0038 :=
    @g_imageex (syn_c1st) p0037
  have p0039 :=
    @g_cnvex (syn_cimage (syn_c1st)) p0038
  have p0040 :=
    @g_snex A
  have p0041 :=
    @g_imaex (syn_ccnv (syn_cimage (syn_c1st))) (syn_csn A) p0039 p0040
  have p0042 :=
    @g_inex (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_c1st))) (syn_csn A)) p0036 p0041
  have p0043 :=
    @g_n_2ndex
  have p0044 :=
    @g_imageex (syn_c2nd) p0043
  have p0045 :=
    @g_cnvex (syn_cimage (syn_c2nd)) p0044
  have p0046 :=
    @g_pwex B hyp_mapexi_2
  have p0047 :=
    @g_imaex (syn_ccnv (syn_cimage (syn_c2nd))) (syn_cpw B) p0045 p0046
  have p0048 :=
    @g_inex (syn_cin (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_c1st))) (syn_csn A))) (syn_cima (syn_ccnv (syn_cimage (syn_c2nd))) (syn_cpw B)) p0042 p0047
  have p0049 :=
    @g_eqeltrri (syn_cin (syn_cin (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_c1st))) (syn_csn A))) (syn_cima (syn_ccnv (syn_cimage (syn_c2nd))) (syn_cpw B))) (.cab f (syn_wf (.cv f) A B)) (syn_cvv) p0035 p0048
  exact p0049

noncomputable def g_mapex
    (A : Class) (B : Class) (C : Class) (D : Class) (f : Var) (dv_A_f : f ∉ A.fv) (dv_B_f : f ∉ B.fv) :
    Nominal.NPrf (.imp (syn_wa (.classMem A C) (.classMem B D)) (.classMem (.cab f (syn_wf (.cv f) A B)) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ ({f} : Finset Var)
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_a_not_C : a ∉ C.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a_not_D : a ∉ D.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_ne_f : a ≠ f := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_f_ne_a : f ≠ a :=
    Ne.symm fresh_a_ne_f
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_b_not_C : b ∉ C.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_b_not_D : b ∉ D.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_ne_f : b ≠ f := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_f_ne_b : f ≠ b :=
    Ne.symm fresh_b_ne_f
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have dv_cache_0001 : f ∉ ((Wff.classEq (.cv a) A)).fv := by
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_a, dv_A_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : f ∉ ((Wff.classEq (.cv b) B)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_b, dv_B_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : f ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : f ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : a ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : b ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : b ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : b ∉ ((Wff.classMem (.cab f (syn_wf (.cv f) A B)) (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_A, fresh_b_not_B, fresh_b_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : a ∉ ((Wff.classMem (.cab f (syn_wf (.cv f) A (.cv b))) (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, fresh_a_ne_b, fresh_a_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_feq2 (.cv a) A (.cv b) (.cv f)
  have p0001 :=
    @g_abbidv (.classEq (.cv a) A) (syn_wf (.cv f) (.cv a) (.cv b)) (syn_wf (.cv f) A (.cv b)) f dv_cache_0001 p0000
  have p0002 :=
    @g_eleq1d (.classEq (.cv a) A) (.cab f (syn_wf (.cv f) (.cv a) (.cv b))) (.cab f (syn_wf (.cv f) A (.cv b))) (syn_cvv) p0001
  have p0003 :=
    @g_feq3 (.cv b) B A (.cv f)
  have p0004 :=
    @g_abbidv (.classEq (.cv b) B) (syn_wf (.cv f) A (.cv b)) (syn_wf (.cv f) A B) f dv_cache_0002 p0003
  have p0005 :=
    @g_eleq1d (.classEq (.cv b) B) (.cab f (syn_wf (.cv f) A (.cv b))) (.cab f (syn_wf (.cv f) A B)) (syn_cvv) p0004
  have p0006 :=
    @g_vex a
  have p0007 :=
    @g_vex b
  have p0008 :=
    @g_mapexi (.cv a) (.cv b) f dv_cache_0003 dv_cache_0004 p0006 p0007
  have p0009 :=
    @g_vtocl2g (.classMem (.cab f (syn_wf (.cv f) (.cv a) (.cv b))) (syn_cvv)) (.classMem (.cab f (syn_wf (.cv f) A (.cv b))) (syn_cvv)) (.classMem (.cab f (syn_wf (.cv f) A B)) (syn_cvv)) a b A B C D dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 p0002 p0005 p0008
  exact p0009

#print axioms g_mapex

end NFChoice.DirectNominalPrf.WPPReplay
