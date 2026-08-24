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
import NominalWPPReplayChunk013Compact001Part010

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

noncomputable def g_pw1fnex
     :
    Nominal.NPrf (.classMem (syn_cpw1fn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let t : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_t : x ≠ t := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_t_ne_x : t ≠ x :=
    Ne.symm fresh_x_ne_t
  have fresh_y_ne_t : y ≠ t := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_t_ne_y : t ≠ y :=
    Ne.symm fresh_y_ne_t
  have dv_cache_0001 : y ∉ ((syn_cop (syn_csn (syn_csn (.cv t))) (.cv x))).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_t, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Class.cv t)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_t, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : t ∉ ((syn_cop (syn_csn (.cv y)) (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : t ∉ ((syn_ctxp (syn_cid) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : t ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : t ∉ ((syn_cuni (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((syn_c1c)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ ((syn_cima (syn_ctxp (syn_cid) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((syn_cima (syn_ctxp (syn_cid) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ ((syn_cpw1 (syn_cuni (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_pw1fn x
  have p0001 :=
    @g_oteltxp (syn_csn (syn_csn (.cv t))) (syn_csn (.cv y)) (.cv x) (syn_cid) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))
  have p0002 :=
    @g_snex (.cv y)
  have p0003 :=
    @g_ideq (syn_csn (syn_csn (.cv t))) (syn_csn (.cv y)) p0002
  have p0004 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (syn_csn (syn_csn (.cv t))) (syn_cid) (syn_csn (.cv y)))))
  have p0005 :=
    @g_eqcom (syn_csn (syn_csn (.cv t))) (syn_csn (.cv y))
  have p0006 :=
    @g_vex y
  have p0007 :=
    @g_sneqb (.cv y) (syn_csn (.cv t)) p0006
  have p0008 :=
    @g_bitri (.classEq (syn_csn (syn_csn (.cv t))) (syn_csn (.cv y))) (.classEq (syn_csn (.cv y)) (syn_csn (syn_csn (.cv t)))) (.classEq (.cv y) (syn_csn (.cv t))) p0005 p0007
  have p0009 :=
    @g_n_3bitr3i (syn_wbr (syn_csn (syn_csn (.cv t))) (syn_cid) (syn_csn (.cv y))) (.classEq (syn_csn (syn_csn (.cv t))) (syn_csn (.cv y))) (.classMem (syn_cop (syn_csn (syn_csn (.cv t))) (syn_csn (.cv y))) (syn_cid)) (.classEq (.cv y) (syn_csn (.cv t))) p0003 p0004 p0008
  have p0010 :=
    @g_oteltxp (syn_csn (.cv y)) (syn_csn (syn_csn (.cv t))) (.cv x) (syn_csi (syn_ccnv (syn_csset))) (syn_csset)
  have p0011 :=
    @g_snex (.cv t)
  have p0012 :=
    @g_brsnsi (.cv y) (syn_csn (.cv t)) (syn_ccnv (syn_csset)) p0006 p0011
  have p0013 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (syn_csn (.cv y)) (syn_csi (syn_ccnv (syn_csset))) (syn_csn (syn_csn (.cv t))))))
  have p0014 :=
    @g_brcnv (.cv y) (syn_csn (.cv t)) (syn_csset)
  have p0015 :=
    @g_vex t
  have p0016 :=
    @g_brssetsn (.cv t) (.cv y) p0015 p0006
  have p0017_e01_recanon : Nominal.NPrf (syn_wb (syn_wbr (syn_csn (.cv t)) (syn_csset) (.cv y)) (.objMem t y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
      p0016
  have p0017 :=
    @g_bitri (syn_wbr (.cv y) (syn_ccnv (syn_csset)) (syn_csn (.cv t))) (syn_wbr (syn_csn (.cv t)) (syn_csset) (.cv y)) (.objMem t y) p0014 p0017_e01_recanon
  have p0018 :=
    @g_n_3bitr3i (syn_wbr (syn_csn (.cv y)) (syn_csi (syn_ccnv (syn_csset))) (syn_csn (syn_csn (.cv t)))) (syn_wbr (.cv y) (syn_ccnv (syn_csset)) (syn_csn (.cv t))) (.classMem (syn_cop (syn_csn (.cv y)) (syn_csn (syn_csn (.cv t)))) (syn_csi (syn_ccnv (syn_csset)))) (.objMem t y) p0012 p0013 p0017
  have p0019 :=
    @g_vex x
  have p0020 :=
    @g_opelssetsn (.cv y) (.cv x) p0006 p0019
  have p0021_e01_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_csset)) (.objMem y x)) :=
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
      p0020
  have p0021 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv y)) (syn_csn (syn_csn (.cv t)))) (syn_csi (syn_ccnv (syn_csset)))) (.objMem t y) (.classMem (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_csset)) (.objMem y x) p0018 p0021_e01_recanon
  have p0022 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (syn_csn (.cv t))) (.cv x))) (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset))) (syn_wa (.classMem (syn_cop (syn_csn (.cv y)) (syn_csn (syn_csn (.cv t)))) (syn_csi (syn_ccnv (syn_csset)))) (.classMem (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_csset))) (syn_wa (.objMem t y) (.objMem y x)) p0010 p0021
  have p0023 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (syn_csn (.cv t))) (.cv x))) (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset))) (syn_wa (.objMem t y) (.objMem y x)) y p0022
  have p0024 :=
    @g_elima1c y (syn_cop (syn_csn (syn_csn (.cv t))) (.cv x)) (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) dv_cache_0001 dv_cache_0002
  have p0025 :=
    @g_eluni y (.cv t) (.cv x) dv_cache_0003 dv_cache_0004
  have p0026_e02_recanon : Nominal.NPrf (syn_wb (.classMem (.cv t) (syn_cuni (.cv x))) (syn_wex y (syn_wa (.objMem t y) (.objMem y x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cuni syn_wex syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
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
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0025
  have p0026 :=
    @g_n_3bitr4i (syn_wex y (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (syn_csn (.cv t))) (.cv x))) (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)))) (syn_wex y (syn_wa (.objMem t y) (.objMem y x))) (.classMem (syn_cop (syn_csn (syn_csn (.cv t))) (.cv x)) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (.classMem (.cv t) (syn_cuni (.cv x))) p0023 p0024 p0026_e02_recanon
  have p0027 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (syn_csn (.cv t))) (syn_csn (.cv y))) (syn_cid)) (.classEq (.cv y) (syn_csn (.cv t))) (.classMem (syn_cop (syn_csn (syn_csn (.cv t))) (.cv x)) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (.classMem (.cv t) (syn_cuni (.cv x))) p0009 p0026
  have p0028 :=
    @g_bitri (.classMem (syn_cop (syn_csn (syn_csn (.cv t))) (syn_cop (syn_csn (.cv y)) (.cv x))) (syn_ctxp (syn_cid) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))) (syn_wa (.classMem (syn_cop (syn_csn (syn_csn (.cv t))) (syn_csn (.cv y))) (syn_cid)) (.classMem (syn_cop (syn_csn (syn_csn (.cv t))) (.cv x)) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))) (syn_wa (.classEq (.cv y) (syn_csn (.cv t))) (.classMem (.cv t) (syn_cuni (.cv x)))) p0001 p0027
  have p0029 :=
    @g_ancom (.classEq (.cv y) (syn_csn (.cv t))) (.classMem (.cv t) (syn_cuni (.cv x)))
  have p0030 :=
    @g_bitri (.classMem (syn_cop (syn_csn (syn_csn (.cv t))) (syn_cop (syn_csn (.cv y)) (.cv x))) (syn_ctxp (syn_cid) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))) (syn_wa (.classEq (.cv y) (syn_csn (.cv t))) (.classMem (.cv t) (syn_cuni (.cv x)))) (syn_wa (.classMem (.cv t) (syn_cuni (.cv x))) (.classEq (.cv y) (syn_csn (.cv t)))) p0028 p0029
  have p0031 :=
    @g_exbii (.classMem (syn_cop (syn_csn (syn_csn (.cv t))) (syn_cop (syn_csn (.cv y)) (.cv x))) (syn_ctxp (syn_cid) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))) (syn_wa (.classMem (.cv t) (syn_cuni (.cv x))) (.classEq (.cv y) (syn_csn (.cv t)))) t p0030
  have p0032 :=
    @g_elimapw11c t (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_ctxp (syn_cid) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) dv_cache_0005 dv_cache_0006
  have p0033 :=
    @g_elpw1 t (.cv y) (syn_cuni (.cv x)) dv_cache_0007 dv_cache_0008
  have p0034 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex t (syn_cuni (.cv x)) (.classEq (.cv y) (syn_csn (.cv t))))))
  have p0035 :=
    @g_bitri (.classMem (.cv y) (syn_cpw1 (syn_cuni (.cv x)))) (syn_wrex t (syn_cuni (.cv x)) (.classEq (.cv y) (syn_csn (.cv t)))) (syn_wex t (syn_wa (.classMem (.cv t) (syn_cuni (.cv x))) (.classEq (.cv y) (syn_csn (.cv t))))) p0033 p0034
  have p0036 :=
    @g_n_3bitr4i (syn_wex t (.classMem (syn_cop (syn_csn (syn_csn (.cv t))) (syn_cop (syn_csn (.cv y)) (.cv x))) (syn_ctxp (syn_cid) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))))) (syn_wex t (syn_wa (.classMem (.cv t) (syn_cuni (.cv x))) (.classEq (.cv y) (syn_csn (.cv t))))) (.classMem (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_cima (syn_ctxp (syn_cid) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c)))) (.classMem (.cv y) (syn_cpw1 (syn_cuni (.cv x)))) p0031 p0032 p0035
  have p0037 :=
    @g_releqmpt x y (syn_c1c) (syn_cima (syn_ctxp (syn_cid) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))) (syn_cpw1 (syn_cuni (.cv x))) dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 p0036
  have p0038 :=
    @g_eqtr4i (syn_cpw1fn) (syn_cmpt x (syn_c1c) (syn_cpw1 (syn_cuni (.cv x)))) (syn_cin (syn_cxp (syn_c1c) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cima (syn_ctxp (syn_cid) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_c1c))))) p0000 p0037
  have p0039 :=
    @g_n_1cex
  have p0040 :=
    @g_idex
  have p0041 :=
    @g_ssetex
  have p0042 :=
    @g_cnvex (syn_csset) p0041
  have p0043 :=
    @g_siex (syn_ccnv (syn_csset)) p0042
  have p0044 :=
    @g_ssetex
  have p0045 :=
    @g_txpex (syn_csi (syn_ccnv (syn_csset))) (syn_csset) p0043 p0044
  have p0046 :=
    @g_n_1cex
  have p0047 :=
    @g_imaex (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c) p0045 p0046
  have p0048 :=
    @g_txpex (syn_cid) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)) p0040 p0047
  have p0049 :=
    @g_n_1cex
  have p0050 :=
    @g_pw1ex (syn_c1c) p0049
  have p0051 :=
    @g_imaex (syn_ctxp (syn_cid) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c)) p0048 p0050
  have p0052 :=
    @g_mptexlem (syn_c1c) (syn_cima (syn_ctxp (syn_cid) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))) p0039 p0051
  have p0053 :=
    @g_eqeltri (syn_cpw1fn) (syn_cin (syn_cxp (syn_c1c) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cima (syn_ctxp (syn_cid) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_c1c))))) (syn_cvv) p0038 p0052
  exact p0053

noncomputable def g_fnpw1fn
     :
    Nominal.NPrf (syn_wfn (syn_cpw1fn) (syn_c1c)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have dv_cache_0001 : x ∉ ((syn_c1c)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_pw1fn x
  have p0001 :=
    @g_fnmpt x (syn_c1c) (syn_cpw1 (syn_cuni (.cv x))) (syn_cpw1fn) (syn_cvv) dv_cache_0001 p0000
  have p0002 :=
    @g_vex x
  have p0003 :=
    @g_uniex (.cv x) p0002
  have p0004 :=
    @g_pw1ex (syn_cuni (.cv x)) p0003
  have p0005 :=
    @g_a1i (.classMem (syn_cpw1 (syn_cuni (.cv x))) (syn_cvv)) (.classMem (.cv x) (syn_c1c)) p0004
  have p0006 :=
    @g_mprg (.classMem (syn_cpw1 (syn_cuni (.cv x))) (syn_cvv)) (syn_wfn (syn_cpw1fn) (syn_c1c)) x (syn_c1c) p0001 p0005
  exact p0006

noncomputable def g_brpw1fn
    (A : Class) (B : Class) (hyp_brpw1fn_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wb (syn_wbr (syn_csn A) (syn_cpw1fn) B) (.classEq B (syn_cpw1 A))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_pw1fnval A hyp_brpw1fn_1
  have p0001 :=
    @g_eqeq1i (syn_cfv (syn_cpw1fn) (syn_csn A)) (syn_cpw1 A) B p0000
  have p0002 :=
    @g_fnpw1fn
  have p0003 :=
    @g_snel1c A hyp_brpw1fn_1
  have p0004 :=
    @g_fnbrfvb (syn_c1c) (syn_csn A) B (syn_cpw1fn)
  have p0005 :=
    @g_mp2an (syn_wfn (syn_cpw1fn) (syn_c1c)) (.classMem (syn_csn A) (syn_c1c)) (syn_wb (.classEq (syn_cfv (syn_cpw1fn) (syn_csn A)) B) (syn_wbr (syn_csn A) (syn_cpw1fn) B)) p0002 p0003 p0004
  have p0006 :=
    @g_eqcom (syn_cpw1 A) B
  have p0007 :=
    @g_n_3bitr3i (.classEq (syn_cfv (syn_cpw1fn) (syn_csn A)) B) (.classEq (syn_cpw1 A) B) (syn_wbr (syn_csn A) (syn_cpw1fn) B) (.classEq B (syn_cpw1 A)) p0001 p0005 p0006
  exact p0007

noncomputable def g_pw1fnf1o
     :
    Nominal.NPrf (syn_wf1o (syn_cpw1fn) (syn_c1c) (syn_cpw (syn_c1c))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let a : Var := freshVar proofSupport 3
  let b : Var := freshVar proofSupport 4
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
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
  have dv_cache_0001 : y ∉ ((syn_c1c)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cpw1 (syn_cuni (.cv x)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0004 : z ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((Wff.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_csn (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((Wff.classEq (.cv y) (syn_cpw1 (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((syn_cpw (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : a ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : b ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : b ∉ ((Wff.classEq (.cv x) (syn_csn (.cv a)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_x, fresh_b_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : a ∉ ((Wff.classEq (.cv y) (syn_csn (.cv b)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_y, fresh_a_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : a ∉ ((Wff.imp (.classEq (syn_cfv (syn_cpw1fn) (.cv x)) (syn_cfv (syn_cpw1fn) (.cv y))) (.objEq x y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_x, fresh_a_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : b ∉ ((Wff.imp (.classEq (syn_cfv (syn_cpw1fn) (.cv x)) (syn_cfv (syn_cpw1fn) (.cv y))) (.objEq x y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_x, fresh_b_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : x ∉ ((syn_c1c)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : x ∉ ((syn_cpw1fn)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : y ∉ ((syn_cpw1fn)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_fnpw1fn
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_pw1fn x
  have p0002 :=
    @g_rnmpt x y (syn_c1c) (syn_cpw1 (syn_cuni (.cv x))) (syn_cpw1fn) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0001
  have p0003 :=
    @g_vex y
  have p0004 :=
    @g_sspw1 z (.cv y) (syn_cvv) dv_cache_0004 dv_cache_0005 p0003
  have p0005 :=
    @g_df1c2
  have p0006 :=
    @g_sseq2i (syn_c1c) (syn_cpw1 (syn_cvv)) (.cv y) p0005
  have p0007 :=
    @g_ssv (.cv z)
  have p0008 :=
    @g_biantrur (syn_wss (.cv z) (syn_cvv)) (.classEq (.cv y) (syn_cpw1 (.cv z))) p0007
  have p0009 :=
    @g_exbii (.classEq (.cv y) (syn_cpw1 (.cv z))) (syn_wa (syn_wss (.cv z) (syn_cvv)) (.classEq (.cv y) (syn_cpw1 (.cv z)))) z p0008
  have p0010 :=
    @g_n_3bitr4i (syn_wss (.cv y) (syn_cpw1 (syn_cvv))) (syn_wex z (syn_wa (syn_wss (.cv z) (syn_cvv)) (.classEq (.cv y) (syn_cpw1 (.cv z))))) (syn_wss (.cv y) (syn_c1c)) (syn_wex z (.classEq (.cv y) (syn_cpw1 (.cv z)))) p0004 p0006 p0009
  have p0011 :=
    @g_elpw (.cv y) (syn_c1c) p0003
  have p0012 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex x (syn_c1c) (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x)))))))
  have p0013 :=
    @g_el1c z (.cv x) dv_cache_0006
  have p0014 :=
    @g_anbi1i (.classMem (.cv x) (syn_c1c)) (syn_wex z (.classEq (.cv x) (syn_csn (.cv z)))) (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x)))) p0013
  have p0015 :=
    @g_n_19_41v (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x)))) z dv_cache_0007
  have p0016 :=
    @g_bitr4i (syn_wa (.classMem (.cv x) (syn_c1c)) (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x))))) (syn_wa (syn_wex z (.classEq (.cv x) (syn_csn (.cv z)))) (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x))))) (syn_wex z (syn_wa (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x)))))) p0014 p0015
  have p0017 :=
    @g_exbii (syn_wa (.classMem (.cv x) (syn_c1c)) (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x))))) (syn_wex z (syn_wa (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x)))))) x p0016
  have p0018 :=
    @g_excom (syn_wa (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x))))) x z
  have p0019 :=
    @g_snex (.cv z)
  have p0020 :=
    @g_unieq (.cv x) (syn_csn (.cv z))
  have p0021 :=
    @g_vex z
  have p0022 :=
    @g_unisn (.cv z) p0021
  have p0023 :=
    @g_syl6eq (.classEq (.cv x) (syn_csn (.cv z))) (syn_cuni (.cv x)) (syn_cuni (syn_csn (.cv z))) (.cv z) p0020 p0022
  have p0024 :=
    @g_pw1eq (syn_cuni (.cv x)) (.cv z)
  have p0025 :=
    @g_syl (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (syn_cuni (.cv x)) (.cv z)) (.classEq (syn_cpw1 (syn_cuni (.cv x))) (syn_cpw1 (.cv z))) p0023 p0024
  have p0026 :=
    @g_eqeq2d (.classEq (.cv x) (syn_csn (.cv z))) (syn_cpw1 (syn_cuni (.cv x))) (syn_cpw1 (.cv z)) (.cv y) p0025
  have p0027 :=
    @g_ceqsexv (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x)))) (.classEq (.cv y) (syn_cpw1 (.cv z))) x (syn_csn (.cv z)) dv_cache_0008 dv_cache_0009 p0019 p0026
  have p0028 :=
    @g_exbii (syn_wex x (syn_wa (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x)))))) (.classEq (.cv y) (syn_cpw1 (.cv z))) z p0027
  have p0029 :=
    @g_bitri (syn_wex x (syn_wex z (syn_wa (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x))))))) (syn_wex z (syn_wex x (syn_wa (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x))))))) (syn_wex z (.classEq (.cv y) (syn_cpw1 (.cv z)))) p0018 p0028
  have p0030 :=
    @g_n_3bitri (syn_wrex x (syn_c1c) (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x))))) (syn_wex x (syn_wa (.classMem (.cv x) (syn_c1c)) (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x)))))) (syn_wex x (syn_wex z (syn_wa (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x))))))) (syn_wex z (.classEq (.cv y) (syn_cpw1 (.cv z)))) p0012 p0017 p0029
  have p0031 :=
    @g_n_3bitr4i (syn_wss (.cv y) (syn_c1c)) (syn_wex z (.classEq (.cv y) (syn_cpw1 (.cv z)))) (.classMem (.cv y) (syn_cpw (syn_c1c))) (syn_wrex x (syn_c1c) (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x))))) p0010 p0011 p0030
  have p0032 :=
    @g_eqabi (syn_wrex x (syn_c1c) (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x))))) y (syn_cpw (syn_c1c)) dv_cache_0010 p0031
  have p0033 :=
    @g_eqtr4i (syn_crn (syn_cpw1fn)) (.cab y (syn_wrex x (syn_c1c) (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x)))))) (syn_cpw (syn_c1c)) p0002 p0032
  have p0034 :=
    @g_el1c a (.cv x) dv_cache_0011
  have p0035 :=
    @g_el1c b (.cv y) dv_cache_0012
  have p0036 :=
    @g_anbi12i (.classMem (.cv x) (syn_c1c)) (syn_wex a (.classEq (.cv x) (syn_csn (.cv a)))) (.classMem (.cv y) (syn_c1c)) (syn_wex b (.classEq (.cv y) (syn_csn (.cv b)))) p0034 p0035
  have p0037 :=
    @g_eeanv (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))) a b dv_cache_0013 dv_cache_0014
  have p0038 :=
    @g_bitr4i (syn_wa (.classMem (.cv x) (syn_c1c)) (.classMem (.cv y) (syn_c1c))) (syn_wa (syn_wex a (.classEq (.cv x) (syn_csn (.cv a)))) (syn_wex b (.classEq (.cv y) (syn_csn (.cv b))))) (syn_wex a (syn_wex b (syn_wa (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b)))))) p0036 p0037
  have p0039 :=
    @g_pw111 (.cv a) (.cv b)
  have p0040_e00_recanon : Nominal.NPrf (syn_wb (.classEq (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (.objEq a b)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cpw syn_wss syn_c1c syn_wex syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
      p0039
  have p0040 :=
    @g_biimpi (.classEq (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (.objEq a b) p0040_e00_recanon
  have p0041 :=
    @g_a1i (.imp (.classEq (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (.objEq a b)) (syn_wa (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b)))) p0040
  have p0042 :=
    @g_fveq2 (.cv x) (syn_csn (.cv a)) (syn_cpw1fn)
  have p0043 :=
    @g_vex a
  have p0044 :=
    @g_pw1fnval (.cv a) p0043
  have p0045 :=
    @g_syl6eq (.classEq (.cv x) (syn_csn (.cv a))) (syn_cfv (syn_cpw1fn) (.cv x)) (syn_cfv (syn_cpw1fn) (syn_csn (.cv a))) (syn_cpw1 (.cv a)) p0042 p0044
  have p0046 :=
    @g_fveq2 (.cv y) (syn_csn (.cv b)) (syn_cpw1fn)
  have p0047 :=
    @g_vex b
  have p0048 :=
    @g_pw1fnval (.cv b) p0047
  have p0049 :=
    @g_syl6eq (.classEq (.cv y) (syn_csn (.cv b))) (syn_cfv (syn_cpw1fn) (.cv y)) (syn_cfv (syn_cpw1fn) (syn_csn (.cv b))) (syn_cpw1 (.cv b)) p0046 p0048
  have p0050 :=
    @g_eqeqan12d (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))) (syn_cfv (syn_cpw1fn) (.cv x)) (syn_cpw1 (.cv a)) (syn_cfv (syn_cpw1fn) (.cv y)) (syn_cpw1 (.cv b)) p0045 p0049
  have p0051 :=
    @g_eqeq12 (.cv x) (syn_csn (.cv a)) (.cv y) (syn_csn (.cv b))
  have p0052 :=
    @g_sneqb (.cv a) (.cv b) p0043
  have p0053_e00_recanon : Nominal.NPrf (.imp (syn_wa (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b)))) (syn_wb (.objEq x y) (.classEq (syn_csn (.cv a)) (syn_csn (.cv b))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_csn syn_wb
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
      p0051
  have p0053_e01_recanon : Nominal.NPrf (syn_wb (.classEq (syn_csn (.cv a)) (syn_csn (.cv b))) (.objEq a b)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
      p0052
  have p0053 :=
    @g_syl6bb (syn_wa (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b)))) (.objEq x y) (.classEq (syn_csn (.cv a)) (syn_csn (.cv b))) (.objEq a b) p0053_e00_recanon p0053_e01_recanon
  have p0054 :=
    @g_n_3imtr4d (syn_wa (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b)))) (.classEq (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (.objEq a b) (.classEq (syn_cfv (syn_cpw1fn) (.cv x)) (syn_cfv (syn_cpw1fn) (.cv y))) (.objEq x y) p0041 p0050 p0053
  have p0055 :=
    @g_exlimivv (syn_wa (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b)))) (.imp (.classEq (syn_cfv (syn_cpw1fn) (.cv x)) (syn_cfv (syn_cpw1fn) (.cv y))) (.objEq x y)) a b dv_cache_0015 dv_cache_0016 p0054
  have p0056 :=
    @g_sylbi (syn_wa (.classMem (.cv x) (syn_c1c)) (.classMem (.cv y) (syn_c1c))) (syn_wex a (syn_wex b (syn_wa (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b)))))) (.imp (.classEq (syn_cfv (syn_cpw1fn) (.cv x)) (syn_cfv (syn_cpw1fn) (.cv y))) (.objEq x y)) p0038 p0055
  have p0057 :=
    @g_rgen2a (.imp (.classEq (syn_cfv (syn_cpw1fn) (.cv x)) (syn_cfv (syn_cpw1fn) (.cv y))) (.objEq x y)) x y (syn_c1c) dv_cache_0001 p0056
  have p0058 :=
    @g_dff1o6 x y (syn_c1c) (syn_cpw (syn_c1c)) (syn_cpw1fn) dv_cache_0017 dv_cache_0001 dv_cache_0018 dv_cache_0019 dv_cache_0003
  have p0059_e03_recanon : Nominal.NPrf (syn_wb (syn_wf1o (syn_cpw1fn) (syn_c1c) (syn_cpw (syn_c1c))) (syn_w3a (syn_wfn (syn_cpw1fn) (syn_c1c)) (.classEq (syn_crn (syn_cpw1fn)) (syn_cpw (syn_c1c))) (syn_wral x (syn_c1c) (syn_wral y (syn_c1c) (.imp (.classEq (syn_cfv (syn_cpw1fn) (.cv x)) (syn_cfv (syn_cpw1fn) (.cv y))) (.objEq x y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wf1o syn_wa syn_wf1 syn_wfo syn_cpw1fn syn_cmpt syn_copab syn_wex syn_c1c syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_cpw syn_wss syn_cuni syn_w3a syn_wfn syn_crn syn_cima syn_wrex syn_wbr syn_cop syn_cun syn_cvv syn_wral
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
                apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                ·
                  exact Nominal.RecanonTransportDev.TRecanonWff.same _
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
                apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                ·
                  exact Nominal.RecanonTransportDev.TRecanonWff.same _
                ·
                  apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  ·
                    exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  ·
                    exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0058
  have p0059 :=
    @g_mpbir3an (syn_wf1o (syn_cpw1fn) (syn_c1c) (syn_cpw (syn_c1c))) (syn_wfn (syn_cpw1fn) (syn_c1c)) (.classEq (syn_crn (syn_cpw1fn)) (syn_cpw (syn_c1c))) (syn_wral x (syn_c1c) (syn_wral y (syn_c1c) (.imp (.classEq (syn_cfv (syn_cpw1fn) (.cv x)) (syn_cfv (syn_cpw1fn) (.cv y))) (.objEq x y)))) p0000 p0033 p0057 p0059_e03_recanon
  exact p0059

#print axioms g_pw1fnf1o

end NFChoice.DirectNominalPrf.WPPReplay
