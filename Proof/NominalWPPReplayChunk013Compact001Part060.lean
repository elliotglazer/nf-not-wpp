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
import NominalWPPReplayChunk013Compact001Part059

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

noncomputable def g_fntcfn
     :
    Nominal.NPrf (syn_wfn (syn_ctcfn) (syn_c1c)) := by
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_tcfn x
  have p0001 :=
    @g_fnmpt x (syn_c1c) (syn_ctc (syn_cuni (.cv x))) (syn_ctcfn) (syn_cvv) dv_cache_0001 p0000
  have p0002 :=
    @g_tcex (syn_cuni (.cv x))
  have p0003 :=
    @g_a1i (.classMem (syn_ctc (syn_cuni (.cv x))) (syn_cvv)) (.classMem (.cv x) (syn_c1c)) p0002
  have p0004 :=
    @g_mprg (.classMem (syn_ctc (syn_cuni (.cv x))) (syn_cvv)) (syn_wfn (syn_ctcfn) (syn_c1c)) x (syn_c1c) p0001 p0003
  exact p0004

noncomputable def g_brtcfn
    (A : Class) (B : Class) (hyp_brtcfn_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wb (syn_wbr (syn_csn A) (syn_ctcfn) B) (.classEq B (syn_ctc A))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((syn_csn A)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_ctc A)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_c1c)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_snel1c A hyp_brtcfn_1
  have p0001 :=
    @g_unieq (.cv x) (syn_csn A)
  have p0002 :=
    @g_unisn A hyp_brtcfn_1
  have p0003 :=
    @g_syl6eq (.classEq (.cv x) (syn_csn A)) (syn_cuni (.cv x)) (syn_cuni (syn_csn A)) A p0001 p0002
  have p0004 :=
    @g_tceq (syn_cuni (.cv x)) A
  have p0005 :=
    @g_syl (.classEq (.cv x) (syn_csn A)) (.classEq (syn_cuni (.cv x)) A) (.classEq (syn_ctc (syn_cuni (.cv x))) (syn_ctc A)) p0003 p0004
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_tcfn x
  have p0007 :=
    @g_tcex A
  have p0008 :=
    @g_fvmpt x (syn_csn A) (syn_ctc (syn_cuni (.cv x))) (syn_ctc A) (syn_c1c) (syn_ctcfn) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0005 p0006 p0007
  have p0009 :=
    Nominal.mp p0000 p0008
  have p0010 :=
    @g_eqeq1i (syn_cfv (syn_ctcfn) (syn_csn A)) (syn_ctc A) B p0009
  have p0011 :=
    @g_fntcfn
  have p0012 :=
    @g_fnbrfvb (syn_c1c) (syn_csn A) B (syn_ctcfn)
  have p0013 :=
    @g_mp2an (syn_wfn (syn_ctcfn) (syn_c1c)) (.classMem (syn_csn A) (syn_c1c)) (syn_wb (.classEq (syn_cfv (syn_ctcfn) (syn_csn A)) B) (syn_wbr (syn_csn A) (syn_ctcfn) B)) p0011 p0000 p0012
  have p0014 :=
    @g_eqcom (syn_ctc A) B
  have p0015 :=
    @g_n_3bitr3i (.classEq (syn_cfv (syn_ctcfn) (syn_csn A)) B) (.classEq (syn_ctc A) B) (syn_wbr (syn_csn A) (syn_ctcfn) B) (.classEq B (syn_ctc A)) p0010 p0013 p0014
  exact p0015

noncomputable def g_addcdi
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))) (.classEq (syn_co A (syn_cmuc) (syn_cplc B C)) (syn_cplc (syn_co A (syn_cmuc) B) (syn_co A (syn_cmuc) C)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_C : z ∉ C.fv := by
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
  have dv_cache_0001 : x ∉ ((syn_cplc B C)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0009 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ ((Wff.imp (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0)) (.classEq (syn_co A (syn_cmuc) (syn_cplc (syn_cnc (.cv y)) (syn_cnc (.cv z)))) (syn_cplc (syn_co A (syn_cmuc) (syn_cnc (.cv y))) (syn_co A (syn_cmuc) (syn_cnc (.cv z))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cmuc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, fresh_x_ne_z, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((Wff.classEq (syn_co A (syn_cmuc) (syn_cplc B C)) (syn_cplc (syn_co A (syn_cmuc) B) (syn_co A (syn_cmuc) C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cmuc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : z ∉ ((Wff.classEq (syn_co A (syn_cmuc) (syn_cplc B C)) (syn_cplc (syn_co A (syn_cmuc) B) (syn_co A (syn_cmuc) C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cmuc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, fresh_z_not_B, fresh_z_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : y ∉ ((syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : z ∉ ((syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_C, fresh_z_not_A, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ ((Wff.classEq (syn_co A (syn_cmuc) (syn_cplc B C)) (syn_cplc (syn_co A (syn_cmuc) B) (syn_co A (syn_cmuc) C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cmuc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : x ∉ ((syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_C, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_ncaddccl B C
  have p0001 :=
    @g_n_3adant1 (.classMem B (syn_cncs)) (.classMem C (syn_cncs)) (.classMem (syn_cplc B C) (syn_cncs)) (.classMem A (syn_cncs)) p0000
  have p0002 :=
    @g_elncs x (syn_cplc B C) dv_cache_0001
  have p0003 :=
    @g_vex x
  have p0004 :=
    @g_ncid (.cv x) p0003
  have p0005 :=
    @g_eleq2 (syn_cplc B C) (syn_cnc (.cv x)) (.cv x)
  have p0006 :=
    @g_mpbiri (.classEq (syn_cplc B C) (syn_cnc (.cv x))) (.classMem (.cv x) (syn_cplc B C)) (.classMem (.cv x) (syn_cnc (.cv x))) p0004 p0005
  have p0007 :=
    @g_eladdc (.cv x) B C y z dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0008 :=
    @g_ncseqnc B (.cv y)
  have p0009 :=
    @g_ncseqnc C (.cv z)
  have p0010 :=
    @g_bi2anan9 (.classMem B (syn_cncs)) (.classEq B (syn_cnc (.cv y))) (.classMem (.cv y) B) (.classMem C (syn_cncs)) (.classEq C (syn_cnc (.cv z))) (.classMem (.cv z) C) p0008 p0009
  have p0011 :=
    @g_n_3adant1 (.classMem B (syn_cncs)) (.classMem C (syn_cncs)) (syn_wb (syn_wa (.classEq B (syn_cnc (.cv y))) (.classEq C (syn_cnc (.cv z)))) (syn_wa (.classMem (.cv y) B) (.classMem (.cv z) C))) (.classMem A (syn_cncs)) p0010
  have p0012 :=
    @g_elncs x A dv_cache_0009
  have p0013 :=
    @g_vex y
  have p0014 :=
    @g_vex z
  have p0015 :=
    @g_ncdisjun (.cv y) (.cv z) p0013 p0014
  have p0016 :=
    @g_oveq2d (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0)) (syn_cnc (syn_cun (.cv y) (.cv z))) (syn_cplc (syn_cnc (.cv y)) (syn_cnc (.cv z))) (syn_cnc (.cv x)) (syn_cmuc) p0015
  have p0017 :=
    @g_xpdisj2 (.cv y) (.cv z) (.cv x) (.cv x)
  have p0018 :=
    @g_xpex (.cv x) (.cv y) p0003 p0013
  have p0019 :=
    @g_xpex (.cv x) (.cv z) p0003 p0014
  have p0020 :=
    @g_ncdisjun (syn_cxp (.cv x) (.cv y)) (syn_cxp (.cv x) (.cv z)) p0018 p0019
  have p0021 :=
    @g_syl (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0)) (.classEq (syn_cin (syn_cxp (.cv x) (.cv y)) (syn_cxp (.cv x) (.cv z))) (syn_c0)) (.classEq (syn_cnc (syn_cun (syn_cxp (.cv x) (.cv y)) (syn_cxp (.cv x) (.cv z)))) (syn_cplc (syn_cnc (syn_cxp (.cv x) (.cv y))) (syn_cnc (syn_cxp (.cv x) (.cv z))))) p0017 p0020
  have p0022 :=
    @g_unex (.cv y) (.cv z) p0013 p0014
  have p0023 :=
    @g_mucnc (.cv x) (syn_cun (.cv y) (.cv z)) p0003 p0022
  have p0024 :=
    @g_xpundi (.cv x) (.cv y) (.cv z)
  have p0025 :=
    @g_nceqi (syn_cxp (.cv x) (syn_cun (.cv y) (.cv z))) (syn_cun (syn_cxp (.cv x) (.cv y)) (syn_cxp (.cv x) (.cv z))) p0024
  have p0026 :=
    @g_eqtri (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (syn_cun (.cv y) (.cv z)))) (syn_cnc (syn_cxp (.cv x) (syn_cun (.cv y) (.cv z)))) (syn_cnc (syn_cun (syn_cxp (.cv x) (.cv y)) (syn_cxp (.cv x) (.cv z)))) p0023 p0025
  have p0027 :=
    @g_mucnc (.cv x) (.cv y) p0003 p0013
  have p0028 :=
    @g_mucnc (.cv x) (.cv z) p0003 p0014
  have p0029 :=
    @g_addceq12i (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (.cv y))) (syn_cnc (syn_cxp (.cv x) (.cv y))) (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (.cv z))) (syn_cnc (syn_cxp (.cv x) (.cv z))) p0027 p0028
  have p0030 :=
    @g_n_3eqtr4g (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0)) (syn_cnc (syn_cun (syn_cxp (.cv x) (.cv y)) (syn_cxp (.cv x) (.cv z)))) (syn_cplc (syn_cnc (syn_cxp (.cv x) (.cv y))) (syn_cnc (syn_cxp (.cv x) (.cv z)))) (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (syn_cun (.cv y) (.cv z)))) (syn_cplc (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (.cv y))) (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (.cv z)))) p0021 p0026 p0029
  have p0031 :=
    @g_eqtr3d (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0)) (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (syn_cun (.cv y) (.cv z)))) (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cplc (syn_cnc (.cv y)) (syn_cnc (.cv z)))) (syn_cplc (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (.cv y))) (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (.cv z)))) p0016 p0030
  have p0032 :=
    @g_oveq1 A (syn_cnc (.cv x)) (syn_cplc (syn_cnc (.cv y)) (syn_cnc (.cv z))) (syn_cmuc)
  have p0033 :=
    @g_oveq1 A (syn_cnc (.cv x)) (syn_cnc (.cv y)) (syn_cmuc)
  have p0034 :=
    @g_oveq1 A (syn_cnc (.cv x)) (syn_cnc (.cv z)) (syn_cmuc)
  have p0035 :=
    @g_addceq12d (.classEq A (syn_cnc (.cv x))) (syn_co A (syn_cmuc) (syn_cnc (.cv y))) (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (.cv y))) (syn_co A (syn_cmuc) (syn_cnc (.cv z))) (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (.cv z))) p0033 p0034
  have p0036 :=
    @g_eqeq12d (.classEq A (syn_cnc (.cv x))) (syn_co A (syn_cmuc) (syn_cplc (syn_cnc (.cv y)) (syn_cnc (.cv z)))) (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cplc (syn_cnc (.cv y)) (syn_cnc (.cv z)))) (syn_cplc (syn_co A (syn_cmuc) (syn_cnc (.cv y))) (syn_co A (syn_cmuc) (syn_cnc (.cv z)))) (syn_cplc (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (.cv y))) (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (.cv z)))) p0032 p0035
  have p0037 :=
    @g_syl5ibr (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0)) (.classEq (syn_co A (syn_cmuc) (syn_cplc (syn_cnc (.cv y)) (syn_cnc (.cv z)))) (syn_cplc (syn_co A (syn_cmuc) (syn_cnc (.cv y))) (syn_co A (syn_cmuc) (syn_cnc (.cv z))))) (.classEq A (syn_cnc (.cv x))) (.classEq (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cplc (syn_cnc (.cv y)) (syn_cnc (.cv z)))) (syn_cplc (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (.cv y))) (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (.cv z))))) p0031 p0036
  have p0038 :=
    @g_exlimiv (.classEq A (syn_cnc (.cv x))) (.imp (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0)) (.classEq (syn_co A (syn_cmuc) (syn_cplc (syn_cnc (.cv y)) (syn_cnc (.cv z)))) (syn_cplc (syn_co A (syn_cmuc) (syn_cnc (.cv y))) (syn_co A (syn_cmuc) (syn_cnc (.cv z)))))) x dv_cache_0010 p0037
  have p0039 :=
    @g_sylbi (.classMem A (syn_cncs)) (syn_wex x (.classEq A (syn_cnc (.cv x)))) (.imp (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0)) (.classEq (syn_co A (syn_cmuc) (syn_cplc (syn_cnc (.cv y)) (syn_cnc (.cv z)))) (syn_cplc (syn_co A (syn_cmuc) (syn_cnc (.cv y))) (syn_co A (syn_cmuc) (syn_cnc (.cv z)))))) p0012 p0038
  have p0040 :=
    @g_adantrd (.classMem A (syn_cncs)) (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0)) (.classEq (syn_co A (syn_cmuc) (syn_cplc (syn_cnc (.cv y)) (syn_cnc (.cv z)))) (syn_cplc (syn_co A (syn_cmuc) (syn_cnc (.cv y))) (syn_co A (syn_cmuc) (syn_cnc (.cv z))))) (.classEq (.cv x) (syn_cun (.cv y) (.cv z))) p0039
  have p0041 :=
    @g_addceq12 B C (syn_cnc (.cv y)) (syn_cnc (.cv z))
  have p0042 :=
    @g_oveq2d (syn_wa (.classEq B (syn_cnc (.cv y))) (.classEq C (syn_cnc (.cv z)))) (syn_cplc B C) (syn_cplc (syn_cnc (.cv y)) (syn_cnc (.cv z))) A (syn_cmuc) p0041
  have p0043 :=
    @g_oveq2 B (syn_cnc (.cv y)) A (syn_cmuc)
  have p0044 :=
    @g_adantr (.classEq B (syn_cnc (.cv y))) (.classEq (syn_co A (syn_cmuc) B) (syn_co A (syn_cmuc) (syn_cnc (.cv y)))) (.classEq C (syn_cnc (.cv z))) p0043
  have p0045 :=
    @g_oveq2 C (syn_cnc (.cv z)) A (syn_cmuc)
  have p0046 :=
    @g_adantl (.classEq C (syn_cnc (.cv z))) (.classEq (syn_co A (syn_cmuc) C) (syn_co A (syn_cmuc) (syn_cnc (.cv z)))) (.classEq B (syn_cnc (.cv y))) p0045
  have p0047 :=
    @g_addceq12d (syn_wa (.classEq B (syn_cnc (.cv y))) (.classEq C (syn_cnc (.cv z)))) (syn_co A (syn_cmuc) B) (syn_co A (syn_cmuc) (syn_cnc (.cv y))) (syn_co A (syn_cmuc) C) (syn_co A (syn_cmuc) (syn_cnc (.cv z))) p0044 p0046
  have p0048 :=
    @g_eqeq12d (syn_wa (.classEq B (syn_cnc (.cv y))) (.classEq C (syn_cnc (.cv z)))) (syn_co A (syn_cmuc) (syn_cplc B C)) (syn_co A (syn_cmuc) (syn_cplc (syn_cnc (.cv y)) (syn_cnc (.cv z)))) (syn_cplc (syn_co A (syn_cmuc) B) (syn_co A (syn_cmuc) C)) (syn_cplc (syn_co A (syn_cmuc) (syn_cnc (.cv y))) (syn_co A (syn_cmuc) (syn_cnc (.cv z)))) p0042 p0047
  have p0049 :=
    @g_imbi2d (syn_wa (.classEq B (syn_cnc (.cv y))) (.classEq C (syn_cnc (.cv z)))) (.classEq (syn_co A (syn_cmuc) (syn_cplc B C)) (syn_cplc (syn_co A (syn_cmuc) B) (syn_co A (syn_cmuc) C))) (.classEq (syn_co A (syn_cmuc) (syn_cplc (syn_cnc (.cv y)) (syn_cnc (.cv z)))) (syn_cplc (syn_co A (syn_cmuc) (syn_cnc (.cv y))) (syn_co A (syn_cmuc) (syn_cnc (.cv z))))) (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv y) (.cv z)))) p0048
  have p0050 :=
    @g_syl5ibrcom (.classMem A (syn_cncs)) (.imp (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv y) (.cv z)))) (.classEq (syn_co A (syn_cmuc) (syn_cplc B C)) (syn_cplc (syn_co A (syn_cmuc) B) (syn_co A (syn_cmuc) C)))) (syn_wa (.classEq B (syn_cnc (.cv y))) (.classEq C (syn_cnc (.cv z)))) (.imp (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv y) (.cv z)))) (.classEq (syn_co A (syn_cmuc) (syn_cplc (syn_cnc (.cv y)) (syn_cnc (.cv z)))) (syn_cplc (syn_co A (syn_cmuc) (syn_cnc (.cv y))) (syn_co A (syn_cmuc) (syn_cnc (.cv z)))))) p0040 p0049
  have p0051 :=
    @g_n_3ad2ant1 (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.imp (syn_wa (.classEq B (syn_cnc (.cv y))) (.classEq C (syn_cnc (.cv z)))) (.imp (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv y) (.cv z)))) (.classEq (syn_co A (syn_cmuc) (syn_cplc B C)) (syn_cplc (syn_co A (syn_cmuc) B) (syn_co A (syn_cmuc) C))))) (.classMem C (syn_cncs)) p0050
  have p0052 :=
    @g_sylbird (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))) (syn_wa (.classMem (.cv y) B) (.classMem (.cv z) C)) (syn_wa (.classEq B (syn_cnc (.cv y))) (.classEq C (syn_cnc (.cv z)))) (.imp (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv y) (.cv z)))) (.classEq (syn_co A (syn_cmuc) (syn_cplc B C)) (syn_cplc (syn_co A (syn_cmuc) B) (syn_co A (syn_cmuc) C)))) p0011 p0051
  have p0053 :=
    @g_rexlimdvv (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))) (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv y) (.cv z)))) (.classEq (syn_co A (syn_cmuc) (syn_cplc B C)) (syn_cplc (syn_co A (syn_cmuc) B) (syn_co A (syn_cmuc) C))) y z B C dv_cache_0005 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0008 p0052
  have p0054 :=
    @g_syl5bi (.classMem (.cv x) (syn_cplc B C)) (syn_wrex y B (syn_wrex z C (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv y) (.cv z)))))) (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))) (.classEq (syn_co A (syn_cmuc) (syn_cplc B C)) (syn_cplc (syn_co A (syn_cmuc) B) (syn_co A (syn_cmuc) C))) p0007 p0053
  have p0055 :=
    @g_syl5 (.classEq (syn_cplc B C) (syn_cnc (.cv x))) (.classMem (.cv x) (syn_cplc B C)) (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))) (.classEq (syn_co A (syn_cmuc) (syn_cplc B C)) (syn_cplc (syn_co A (syn_cmuc) B) (syn_co A (syn_cmuc) C))) p0006 p0054
  have p0056 :=
    @g_exlimdv (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))) (.classEq (syn_cplc B C) (syn_cnc (.cv x))) (.classEq (syn_co A (syn_cmuc) (syn_cplc B C)) (syn_cplc (syn_co A (syn_cmuc) B) (syn_co A (syn_cmuc) C))) x dv_cache_0015 dv_cache_0016 p0055
  have p0057 :=
    @g_syl5bi (.classMem (syn_cplc B C) (syn_cncs)) (syn_wex x (.classEq (syn_cplc B C) (syn_cnc (.cv x)))) (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))) (.classEq (syn_co A (syn_cmuc) (syn_cplc B C)) (syn_cplc (syn_co A (syn_cmuc) B) (syn_co A (syn_cmuc) C))) p0002 p0056
  have p0058 :=
    @g_mpd (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))) (.classMem (syn_cplc B C) (syn_cncs)) (.classEq (syn_co A (syn_cmuc) (syn_cplc B C)) (syn_cplc (syn_co A (syn_cmuc) B) (syn_co A (syn_cmuc) C))) p0001 p0057
  exact p0058

noncomputable def g_addcdir
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))) (.classEq (syn_co (syn_cplc A B) (syn_cmuc) C) (syn_cplc (syn_co A (syn_cmuc) C) (syn_co B (syn_cmuc) C)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_addcdi C A B
  have p0001 :=
    @g_n_3coml (.classMem C (syn_cncs)) (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classEq (syn_co C (syn_cmuc) (syn_cplc A B)) (syn_cplc (syn_co C (syn_cmuc) A) (syn_co C (syn_cmuc) B))) p0000
  have p0002 :=
    @g_ncaddccl A B
  have p0003 :=
    @g_n_3adant3 (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem (syn_cplc A B) (syn_cncs)) (.classMem C (syn_cncs)) p0002
  have p0004 :=
    @g_simp3 (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))
  have p0005 :=
    @g_muccom (syn_cplc A B) C
  have p0006 :=
    @g_syl2anc (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))) (.classMem (syn_cplc A B) (syn_cncs)) (.classMem C (syn_cncs)) (.classEq (syn_co (syn_cplc A B) (syn_cmuc) C) (syn_co C (syn_cmuc) (syn_cplc A B))) p0003 p0004 p0005
  have p0007 :=
    @g_muccom A C
  have p0008 :=
    @g_n_3adant2 (.classMem A (syn_cncs)) (.classMem C (syn_cncs)) (.classEq (syn_co A (syn_cmuc) C) (syn_co C (syn_cmuc) A)) (.classMem B (syn_cncs)) p0007
  have p0009 :=
    @g_muccom B C
  have p0010 :=
    @g_n_3adant1 (.classMem B (syn_cncs)) (.classMem C (syn_cncs)) (.classEq (syn_co B (syn_cmuc) C) (syn_co C (syn_cmuc) B)) (.classMem A (syn_cncs)) p0009
  have p0011 :=
    @g_addceq12d (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))) (syn_co A (syn_cmuc) C) (syn_co C (syn_cmuc) A) (syn_co B (syn_cmuc) C) (syn_co C (syn_cmuc) B) p0008 p0010
  have p0012 :=
    @g_n_3eqtr4d (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))) (syn_co C (syn_cmuc) (syn_cplc A B)) (syn_cplc (syn_co C (syn_cmuc) A) (syn_co C (syn_cmuc) B)) (syn_co (syn_cplc A B) (syn_cmuc) C) (syn_cplc (syn_co A (syn_cmuc) C) (syn_co B (syn_cmuc) C)) p0001 p0006 p0011
  exact p0012

noncomputable def g_lemuc1
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))) (syn_wbr A (syn_clec) B)) (syn_wbr (syn_co A (syn_cmuc) C) (syn_clec) (syn_co B (syn_cmuc) C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_q_not_B : q ∉ B.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_not_C : q ∉ C.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have dv_cache_0001 : q ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((syn_wbr (syn_co A (syn_cmuc) C) (syn_clec) (syn_co B (syn_cmuc) C))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cmuc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, fresh_q_not_C, fresh_q_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((syn_wa (.classMem A (syn_cncs)) (.classMem C (syn_cncs)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, fresh_q_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_dflec2 A B q dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_n_3adant3 (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (syn_wb (syn_wbr A (syn_clec) B) (syn_wrex q (syn_cncs) (.classEq B (syn_cplc A (.cv q))))) (.classMem C (syn_cncs)) p0000
  have p0002 :=
    @g_muccl A C
  have p0003 :=
    @g_adantr (syn_wa (.classMem A (syn_cncs)) (.classMem C (syn_cncs))) (.classMem (syn_co A (syn_cmuc) C) (syn_cncs)) (.classMem (.cv q) (syn_cncs)) p0002
  have p0004 :=
    @g_muccl (.cv q) C
  have p0005 :=
    @g_ancoms (.classMem (.cv q) (syn_cncs)) (.classMem C (syn_cncs)) (.classMem (syn_co (.cv q) (syn_cmuc) C) (syn_cncs)) p0004
  have p0006 :=
    @g_adantll (.classMem C (syn_cncs)) (.classMem (.cv q) (syn_cncs)) (.classMem (syn_co (.cv q) (syn_cmuc) C) (syn_cncs)) (.classMem A (syn_cncs)) p0005
  have p0007 :=
    @g_addlecncs (syn_co A (syn_cmuc) C) (syn_co (.cv q) (syn_cmuc) C)
  have p0008 :=
    @g_syl2anc (syn_wa (syn_wa (.classMem A (syn_cncs)) (.classMem C (syn_cncs))) (.classMem (.cv q) (syn_cncs))) (.classMem (syn_co A (syn_cmuc) C) (syn_cncs)) (.classMem (syn_co (.cv q) (syn_cmuc) C) (syn_cncs)) (syn_wbr (syn_co A (syn_cmuc) C) (syn_clec) (syn_cplc (syn_co A (syn_cmuc) C) (syn_co (.cv q) (syn_cmuc) C))) p0003 p0006 p0007
  have p0009 :=
    @g_simpll (.classMem A (syn_cncs)) (.classMem C (syn_cncs)) (.classMem (.cv q) (syn_cncs))
  have p0010 :=
    @g_simpr (syn_wa (.classMem A (syn_cncs)) (.classMem C (syn_cncs))) (.classMem (.cv q) (syn_cncs))
  have p0011 :=
    @g_simplr (.classMem A (syn_cncs)) (.classMem C (syn_cncs)) (.classMem (.cv q) (syn_cncs))
  have p0012 :=
    @g_addcdir A (.cv q) C
  have p0013 :=
    @g_syl3anc (syn_wa (syn_wa (.classMem A (syn_cncs)) (.classMem C (syn_cncs))) (.classMem (.cv q) (syn_cncs))) (.classMem A (syn_cncs)) (.classMem (.cv q) (syn_cncs)) (.classMem C (syn_cncs)) (.classEq (syn_co (syn_cplc A (.cv q)) (syn_cmuc) C) (syn_cplc (syn_co A (syn_cmuc) C) (syn_co (.cv q) (syn_cmuc) C))) p0009 p0010 p0011 p0012
  have p0014 :=
    @g_breqtrrd (syn_wa (syn_wa (.classMem A (syn_cncs)) (.classMem C (syn_cncs))) (.classMem (.cv q) (syn_cncs))) (syn_co A (syn_cmuc) C) (syn_cplc (syn_co A (syn_cmuc) C) (syn_co (.cv q) (syn_cmuc) C)) (syn_co (syn_cplc A (.cv q)) (syn_cmuc) C) (syn_clec) p0008 p0013
  have p0015 :=
    @g_oveq1 B (syn_cplc A (.cv q)) C (syn_cmuc)
  have p0016 :=
    @g_breq2d (.classEq B (syn_cplc A (.cv q))) (syn_co B (syn_cmuc) C) (syn_co (syn_cplc A (.cv q)) (syn_cmuc) C) (syn_co A (syn_cmuc) C) (syn_clec) p0015
  have p0017 :=
    @g_syl5ibrcom (syn_wa (syn_wa (.classMem A (syn_cncs)) (.classMem C (syn_cncs))) (.classMem (.cv q) (syn_cncs))) (syn_wbr (syn_co A (syn_cmuc) C) (syn_clec) (syn_co B (syn_cmuc) C)) (.classEq B (syn_cplc A (.cv q))) (syn_wbr (syn_co A (syn_cmuc) C) (syn_clec) (syn_co (syn_cplc A (.cv q)) (syn_cmuc) C)) p0014 p0016
  have p0018 :=
    @g_rexlimdva (syn_wa (.classMem A (syn_cncs)) (.classMem C (syn_cncs))) (.classEq B (syn_cplc A (.cv q))) (syn_wbr (syn_co A (syn_cmuc) C) (syn_clec) (syn_co B (syn_cmuc) C)) q (syn_cncs) dv_cache_0003 dv_cache_0004 p0017
  have p0019 :=
    @g_n_3adant2 (.classMem A (syn_cncs)) (.classMem C (syn_cncs)) (.imp (syn_wrex q (syn_cncs) (.classEq B (syn_cplc A (.cv q)))) (syn_wbr (syn_co A (syn_cmuc) C) (syn_clec) (syn_co B (syn_cmuc) C))) (.classMem B (syn_cncs)) p0018
  have p0020 :=
    @g_sylbid (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))) (syn_wbr A (syn_clec) B) (syn_wrex q (syn_cncs) (.classEq B (syn_cplc A (.cv q)))) (syn_wbr (syn_co A (syn_cmuc) C) (syn_clec) (syn_co B (syn_cmuc) C)) p0001 p0019
  have p0021 :=
    @g_imp (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))) (syn_wbr A (syn_clec) B) (syn_wbr (syn_co A (syn_cmuc) C) (syn_clec) (syn_co B (syn_cmuc) C)) p0020
  exact p0021

noncomputable def g_lemuc2
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))) (syn_wbr B (syn_clec) C)) (syn_wbr (syn_co A (syn_cmuc) B) (syn_clec) (syn_co A (syn_cmuc) C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_n_3anrot (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))
  have p0001 :=
    @g_lemuc1 B C A
  have p0002 :=
    @g_sylanb (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))) (syn_w3a (.classMem B (syn_cncs)) (.classMem C (syn_cncs)) (.classMem A (syn_cncs))) (syn_wbr B (syn_clec) C) (syn_wbr (syn_co B (syn_cmuc) A) (syn_clec) (syn_co C (syn_cmuc) A)) p0000 p0001
  have p0003 :=
    @g_simpl1 (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs)) (syn_wbr B (syn_clec) C)
  have p0004 :=
    @g_simpl2 (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs)) (syn_wbr B (syn_clec) C)
  have p0005 :=
    @g_muccom A B
  have p0006 :=
    @g_syl2anc (syn_wa (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))) (syn_wbr B (syn_clec) C)) (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classEq (syn_co A (syn_cmuc) B) (syn_co B (syn_cmuc) A)) p0003 p0004 p0005
  have p0007 :=
    @g_simpl3 (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs)) (syn_wbr B (syn_clec) C)
  have p0008 :=
    @g_muccom A C
  have p0009 :=
    @g_syl2anc (syn_wa (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))) (syn_wbr B (syn_clec) C)) (.classMem A (syn_cncs)) (.classMem C (syn_cncs)) (.classEq (syn_co A (syn_cmuc) C) (syn_co C (syn_cmuc) A)) p0003 p0007 p0008
  have p0010 :=
    @g_n_3brtr4d (syn_wa (syn_w3a (.classMem A (syn_cncs)) (.classMem B (syn_cncs)) (.classMem C (syn_cncs))) (syn_wbr B (syn_clec) C)) (syn_co B (syn_cmuc) A) (syn_co C (syn_cmuc) A) (syn_co A (syn_cmuc) B) (syn_co A (syn_cmuc) C) (syn_clec) p0002 p0006 p0009
  exact p0010

noncomputable def g_n_0lt1c
     :
    Nominal.NPrf (syn_wbr (syn_c0c) (syn_cltc) (syn_c1c)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have p0000 :=
    @g_df0c2
  have p0001 :=
    @g_n_0ss (syn_csn (.cv x))
  have p0002 :=
    @g_n_0ex
  have p0003 :=
    @g_snex (.cv x)
  have p0004 :=
    @g_nclec (syn_c0) (syn_csn (.cv x)) p0002 p0003
  have p0005 :=
    Nominal.mp p0001 p0004
  have p0006 :=
    @g_eqbrtri (syn_c0c) (syn_cnc (syn_c0)) (syn_cnc (syn_csn (.cv x))) (syn_clec) p0000 p0005
  have p0007 :=
    @g_vex x
  have p0008 :=
    @g_snnz (.cv x) p0007
  have p0009 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (syn_csn (.cv x)) (syn_c0))))
  have p0010 :=
    @g_mpbi (syn_wne (syn_csn (.cv x)) (syn_c0)) (.neg (.classEq (syn_csn (.cv x)) (syn_c0))) p0008 p0009
  have p0011 :=
    @g_ncid (syn_csn (.cv x)) p0003
  have p0012 :=
    @g_eleq2 (syn_c0c) (syn_cnc (syn_csn (.cv x))) (syn_csn (.cv x))
  have p0013 :=
    @g_mpbiri (.classEq (syn_c0c) (syn_cnc (syn_csn (.cv x)))) (.classMem (syn_csn (.cv x)) (syn_c0c)) (.classMem (syn_csn (.cv x)) (syn_cnc (syn_csn (.cv x)))) p0011 p0012
  have p0014 :=
    @g_el0c (syn_csn (.cv x))
  have p0015 :=
    @g_sylib (.classEq (syn_c0c) (syn_cnc (syn_csn (.cv x)))) (.classMem (syn_csn (.cv x)) (syn_c0c)) (.classEq (syn_csn (.cv x)) (syn_c0)) p0013 p0014
  have p0016 :=
    @g_mto (.classEq (syn_c0c) (syn_cnc (syn_csn (.cv x)))) (.classEq (syn_csn (.cv x)) (syn_c0)) p0010 p0015
  have p0017 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (syn_c0c) (syn_cnc (syn_csn (.cv x))))))
  have p0018 :=
    @g_mpbir (syn_wne (syn_c0c) (syn_cnc (syn_csn (.cv x)))) (.neg (.classEq (syn_c0c) (syn_cnc (syn_csn (.cv x))))) p0016 p0017
  have p0019 :=
    @g_brltc (syn_c0c) (syn_cnc (syn_csn (.cv x)))
  have p0020 :=
    @g_mpbir2an (syn_wbr (syn_c0c) (syn_cltc) (syn_cnc (syn_csn (.cv x)))) (syn_wbr (syn_c0c) (syn_clec) (syn_cnc (syn_csn (.cv x)))) (syn_wne (syn_c0c) (syn_cnc (syn_csn (.cv x)))) p0006 p0018 p0019
  have p0021 :=
    @g_df1c3 (.cv x) p0007
  have p0022 :=
    @g_breqtrri (syn_c0c) (syn_cnc (syn_csn (.cv x))) (syn_c1c) (syn_cltc) p0020 p0021
  exact p0022

#print axioms g_n_0lt1c

end NFChoice.DirectNominalPrf.WPPReplay
