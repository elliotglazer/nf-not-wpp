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
import NominalWPPReplayChunk013Compact001Part018

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

noncomputable def g_refex
     :
    Nominal.NPrf (.classMem (syn_cref) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let r : Var := freshVar proofSupport 1
  let a : Var := freshVar proofSupport 2
  let p : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_x_ne_r : x ≠ r := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_r_ne_x : r ≠ x :=
    Ne.symm fresh_x_ne_r
  have fresh_x_ne_a : x ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_a_ne_x : a ≠ x :=
    Ne.symm fresh_x_ne_a
  have fresh_x_ne_p : x ≠ p := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_p_ne_x : p ≠ x :=
    Ne.symm fresh_x_ne_p
  have fresh_r_ne_a : r ≠ a := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_a_ne_r : a ≠ r :=
    Ne.symm fresh_r_ne_a
  have fresh_r_ne_p : r ≠ p := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_p_ne_r : p ≠ r :=
    Ne.symm fresh_r_ne_p
  have fresh_a_ne_p : a ≠ p := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_p_ne_a : p ≠ a :=
    Ne.symm fresh_a_ne_p
  have dv_cache_0001 : a ≠ r := by
    exact (show a ≠ r from (by exact fresh_a_ne_r))
  have dv_cache_0002 : a ≠ x := by
    clear dv_cache_0001
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0003 : r ≠ x := by
    clear dv_cache_0001 dv_cache_0002
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0004 : x ∉ ((syn_cop (.cv r) (.cv a))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_r, fresh_x_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_ctxp (syn_ccompl (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c))) (syn_csset))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : p ∉ ((syn_cop (syn_csn (.cv x)) (.cv r))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_x, fresh_p_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : p ∉ ((syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : p ∉ ((syn_cop (.cv x) (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : p ∉ ((Class.cv r)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : r ∉ ((syn_ccompl (syn_cima (syn_ctxp (syn_ccompl (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c))) (syn_csset)) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : a ∉ ((syn_ccompl (syn_cima (syn_ctxp (syn_ccompl (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c))) (syn_csset)) (syn_c1c)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : r ≠ a := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show r ≠ a from (by exact fresh_r_ne_a))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ref x r a dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_vex r
  have p0002 :=
    @g_vex a
  have p0003 :=
    @g_opex (.cv r) (.cv a) p0001 p0002
  have p0004 :=
    @g_elcompl (syn_cop (.cv r) (.cv a)) (syn_cima (syn_ctxp (syn_ccompl (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c))) (syn_csset)) (syn_c1c)) p0003
  have p0005 :=
    @g_elima1c x (syn_cop (.cv r) (.cv a)) (syn_ctxp (syn_ccompl (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c))) (syn_csset)) dv_cache_0004 dv_cache_0005
  have p0006 :=
    @g_oteltxp (syn_csn (.cv x)) (.cv r) (.cv a) (syn_ccompl (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c))) (syn_csset)
  have p0007 :=
    @g_snex (.cv x)
  have p0008 :=
    @g_opex (syn_csn (.cv x)) (.cv r) p0007 p0001
  have p0009 :=
    @g_elcompl (syn_cop (syn_csn (.cv x)) (.cv r)) (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c)) p0008
  have p0010 :=
    @g_elima1c p (syn_cop (syn_csn (.cv x)) (.cv r)) (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) dv_cache_0006 dv_cache_0007
  have p0011 :=
    @g_oteltxp (syn_csn (.cv p)) (syn_csn (.cv x)) (.cv r) (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)
  have p0012 :=
    @g_vex p
  have p0013 :=
    @g_vex x
  have p0014 :=
    @g_opsnelsi (.cv p) (.cv x) (syn_cin (syn_c1st) (syn_c2nd)) p0012 p0013
  have p0015 :=
    @g_elin (syn_cop (.cv p) (.cv x)) (syn_c1st) (syn_c2nd)
  have p0016 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv p) (syn_c1st) (.cv x))))
  have p0017 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv p) (syn_c2nd) (.cv x))))
  have p0018 :=
    @g_anbi12i (syn_wbr (.cv p) (syn_c1st) (.cv x)) (.classMem (syn_cop (.cv p) (.cv x)) (syn_c1st)) (syn_wbr (.cv p) (syn_c2nd) (.cv x)) (.classMem (syn_cop (.cv p) (.cv x)) (syn_c2nd)) p0016 p0017
  have p0019 :=
    @g_op1st2nd (.cv x) (.cv x) (.cv p) p0013 p0013
  have p0020 :=
    @g_n_3bitr2i (.classMem (syn_cop (.cv p) (.cv x)) (syn_cin (syn_c1st) (syn_c2nd))) (syn_wa (.classMem (syn_cop (.cv p) (.cv x)) (syn_c1st)) (.classMem (syn_cop (.cv p) (.cv x)) (syn_c2nd))) (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv x)) (syn_wbr (.cv p) (syn_c2nd) (.cv x))) (.classEq (.cv p) (syn_cop (.cv x) (.cv x))) p0015 p0018 p0019
  have p0021 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv p)) (syn_csn (.cv x))) (syn_csi (syn_cin (syn_c1st) (syn_c2nd)))) (.classMem (syn_cop (.cv p) (.cv x)) (syn_cin (syn_c1st) (syn_c2nd))) (.classEq (.cv p) (syn_cop (.cv x) (.cv x))) p0014 p0020
  have p0022 :=
    @g_opelssetsn (.cv p) (.cv r) p0012 p0001
  have p0023_e01_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv p)) (.cv r)) (syn_csset)) (.objMem p r)) :=
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
      p0022
  have p0023 :=
    @g_anbi12i (.classMem (syn_cop (syn_csn (.cv p)) (syn_csn (.cv x))) (syn_csi (syn_cin (syn_c1st) (syn_c2nd)))) (.classEq (.cv p) (syn_cop (.cv x) (.cv x))) (.classMem (syn_cop (syn_csn (.cv p)) (.cv r)) (syn_csset)) (.objMem p r) p0021 p0023_e01_recanon
  have p0024 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset))) (syn_wa (.classMem (syn_cop (syn_csn (.cv p)) (syn_csn (.cv x))) (syn_csi (syn_cin (syn_c1st) (syn_c2nd)))) (.classMem (syn_cop (syn_csn (.cv p)) (.cv r)) (syn_csset))) (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv x))) (.objMem p r)) p0011 p0023
  have p0025 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset))) (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv x))) (.objMem p r)) p p0024
  have p0026 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv x)) (.cv r)) (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c))) (syn_wex p (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)))) (syn_wex p (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv x))) (.objMem p r))) p0010 p0025
  have p0027 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) (.cv r) (.cv x))))
  have p0028 :=
    (by simpa [NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfClelGoal, syn_wb, syn_wex, syn_wa, Wff.biimp, Wff.ex, Wff.conj, Wff.neg] using (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV p (syn_cop (.cv x) (.cv x)) (.cv r) dv_cache_0008 dv_cache_0009))
  have p0029_e01_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (.cv x) (.cv x)) (.cv r)) (syn_wex p (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv x))) (.objMem p r)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0028
  have p0029 :=
    @g_bitri (syn_wbr (.cv x) (.cv r) (.cv x)) (.classMem (syn_cop (.cv x) (.cv x)) (.cv r)) (syn_wex p (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv x))) (.objMem p r))) p0027 p0029_e01_recanon
  have p0030 :=
    @g_bitr4i (.classMem (syn_cop (syn_csn (.cv x)) (.cv r)) (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c))) (syn_wex p (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv x))) (.objMem p r))) (syn_wbr (.cv x) (.cv r) (.cv x)) p0026 p0029
  have p0031 :=
    @g_xchbinx (.classMem (syn_cop (syn_csn (.cv x)) (.cv r)) (syn_ccompl (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c)))) (.classMem (syn_cop (syn_csn (.cv x)) (.cv r)) (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c))) (syn_wbr (.cv x) (.cv r) (.cv x)) p0009 p0030
  have p0032 :=
    @g_opelssetsn (.cv x) (.cv a) p0013 p0002
  have p0033_e01_recanon : Nominal.NPrf (syn_wb (.classMem (syn_cop (syn_csn (.cv x)) (.cv a)) (syn_csset)) (.objMem x a)) :=
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
      p0032
  have p0033 :=
    @g_anbi12ci (.classMem (syn_cop (syn_csn (.cv x)) (.cv r)) (syn_ccompl (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c)))) (.neg (syn_wbr (.cv x) (.cv r) (.cv x))) (.classMem (syn_cop (syn_csn (.cv x)) (.cv a)) (syn_csset)) (.objMem x a) p0031 p0033_e01_recanon
  have p0034 :=
    @g_bitri (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_ctxp (syn_ccompl (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c))) (syn_csset))) (syn_wa (.classMem (syn_cop (syn_csn (.cv x)) (.cv r)) (syn_ccompl (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c)))) (.classMem (syn_cop (syn_csn (.cv x)) (.cv a)) (syn_csset))) (syn_wa (.objMem x a) (.neg (syn_wbr (.cv x) (.cv r) (.cv x)))) p0006 p0033
  have p0035 :=
    @g_exbii (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_ctxp (syn_ccompl (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c))) (syn_csset))) (syn_wa (.objMem x a) (.neg (syn_wbr (.cv x) (.cv r) (.cv x)))) x p0034
  have p0036 :=
    @g_bitri (.classMem (syn_cop (.cv r) (.cv a)) (syn_cima (syn_ctxp (syn_ccompl (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c))) (syn_csset)) (syn_c1c))) (syn_wex x (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_ctxp (syn_ccompl (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c))) (syn_csset)))) (syn_wex x (syn_wa (.objMem x a) (.neg (syn_wbr (.cv x) (.cv r) (.cv x))))) p0005 p0035
  have p0037 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex x (.cv a) (.neg (syn_wbr (.cv x) (.cv r) (.cv x))))))
  have p0038 :=
    @g_rexnal (syn_wbr (.cv x) (.cv r) (.cv x)) x (.cv a)
  have p0039_e01_recanon : Nominal.NPrf (syn_wb (syn_wrex x (.cv a) (.neg (syn_wbr (.cv x) (.cv r) (.cv x)))) (syn_wex x (syn_wa (.objMem x a) (.neg (syn_wbr (.cv x) (.cv r) (.cv x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wrex syn_wex syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem]
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
      p0037
  have p0039 :=
    @g_n_3bitr2i (.classMem (syn_cop (.cv r) (.cv a)) (syn_cima (syn_ctxp (syn_ccompl (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c))) (syn_csset)) (syn_c1c))) (syn_wex x (syn_wa (.objMem x a) (.neg (syn_wbr (.cv x) (.cv r) (.cv x))))) (syn_wrex x (.cv a) (.neg (syn_wbr (.cv x) (.cv r) (.cv x)))) (.neg (syn_wral x (.cv a) (syn_wbr (.cv x) (.cv r) (.cv x)))) p0036 p0039_e01_recanon p0038
  have p0040 :=
    @g_con2bii (.classMem (syn_cop (.cv r) (.cv a)) (syn_cima (syn_ctxp (syn_ccompl (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c))) (syn_csset)) (syn_c1c))) (syn_wral x (.cv a) (syn_wbr (.cv x) (.cv r) (.cv x))) p0039
  have p0041 :=
    @g_bitr4i (.classMem (syn_cop (.cv r) (.cv a)) (syn_ccompl (syn_cima (syn_ctxp (syn_ccompl (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c))) (syn_csset)) (syn_c1c)))) (.neg (.classMem (syn_cop (.cv r) (.cv a)) (syn_cima (syn_ctxp (syn_ccompl (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c))) (syn_csset)) (syn_c1c)))) (syn_wral x (.cv a) (syn_wbr (.cv x) (.cv r) (.cv x))) p0004 p0040
  have p0042 :=
    @g_opabbi2i (syn_wral x (.cv a) (syn_wbr (.cv x) (.cv r) (.cv x))) r a (syn_ccompl (syn_cima (syn_ctxp (syn_ccompl (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c))) (syn_csset)) (syn_c1c))) dv_cache_0010 dv_cache_0011 dv_cache_0012 p0041
  have p0043 :=
    @g_eqtr4i (syn_cref) (syn_copab r a (syn_wral x (.cv a) (syn_wbr (.cv x) (.cv r) (.cv x)))) (syn_ccompl (syn_cima (syn_ctxp (syn_ccompl (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c))) (syn_csset)) (syn_c1c))) p0000 p0042
  have p0044 :=
    @g_n_1stex
  have p0045 :=
    @g_n_2ndex
  have p0046 :=
    @g_inex (syn_c1st) (syn_c2nd) p0044 p0045
  have p0047 :=
    @g_siex (syn_cin (syn_c1st) (syn_c2nd)) p0046
  have p0048 :=
    @g_ssetex
  have p0049 :=
    @g_txpex (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset) p0047 p0048
  have p0050 :=
    @g_n_1cex
  have p0051 :=
    @g_imaex (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c) p0049 p0050
  have p0052 :=
    @g_complex (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c)) p0051
  have p0053 :=
    @g_ssetex
  have p0054 :=
    @g_txpex (syn_ccompl (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c))) (syn_csset) p0052 p0053
  have p0055 :=
    @g_n_1cex
  have p0056 :=
    @g_imaex (syn_ctxp (syn_ccompl (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c))) (syn_csset)) (syn_c1c) p0054 p0055
  have p0057 :=
    @g_complex (syn_cima (syn_ctxp (syn_ccompl (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c))) (syn_csset)) (syn_c1c)) p0056
  have p0058 :=
    @g_eqeltri (syn_cref) (syn_ccompl (syn_cima (syn_ctxp (syn_ccompl (syn_cima (syn_ctxp (syn_csi (syn_cin (syn_c1st) (syn_c2nd))) (syn_csset)) (syn_c1c))) (syn_csset)) (syn_c1c))) (syn_cvv) p0043 p0057
  exact p0058

#print axioms g_refex

end NFChoice.DirectNominalPrf.WPPReplay
