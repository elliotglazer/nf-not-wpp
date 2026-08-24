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
import NominalWPPReplayChunk016Compact001Part045

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

noncomputable def g_hwcardstcclndv
    (K : Class) :
    Nominal.NPrf (.imp (.classMem K (syn_chwcards (syn_cvv))) (.classMem (syn_ctc K) (syn_chwcards (syn_cvv)))) := by
  let proofSupport : Finset Var := K.fv
  let s : Var := freshVar proofSupport 0
  let d : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  let x : Var := freshVar proofSupport 3
  have fresh_s : s ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_s_not_K : s ∉ K.fv := by
    intro h
    exact fresh_s (h)
  have fresh_d : d ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_d_not_K : d ∉ K.fv := by
    intro h
    exact fresh_d (h)
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_K : y ∉ K.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_x_not_K : x ∉ K.fv := by
    intro h
    exact fresh_x (h)
  have fresh_s_ne_d : s ≠ d := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_d_ne_s : d ≠ s :=
    Ne.symm fresh_s_ne_d
  have fresh_s_ne_y : s ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_s : y ≠ s :=
    Ne.symm fresh_s_ne_y
  have fresh_s_ne_x : s ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_x_ne_s : x ≠ s :=
    Ne.symm fresh_s_ne_x
  have fresh_d_ne_y : d ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_d : y ≠ d :=
    Ne.symm fresh_d_ne_y
  have fresh_d_ne_x : d ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_x_ne_d : x ≠ d :=
    Ne.symm fresh_d_ne_x
  have fresh_y_ne_x : y ≠ x := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have dv_cache_0001 : d ∉ (K).fv := by
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_K, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : s ∉ (K).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_K, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : d ≠ s := by
    clear dv_cache_0001 dv_cache_0002
    exact (show d ≠ s from (by exact fresh_d_ne_s))
  have dv_cache_0004 : y ∉ ((syn_csi (.cv s))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_s, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_wa (syn_wbr (syn_csi (.cv s)) (syn_cwe) (syn_cpw1 (.cv d))) (.classEq (syn_ctc K) (syn_cnc (syn_cpw1 (.cv d)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_s, fresh_y_ne_d, fresh_y_not_K, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((Wff.classEq (.cv x) (syn_cpw1 (.cv d)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_cpw1 (.cv d))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_wex y (syn_wa (syn_wbr (.cv y) (syn_cwe) (syn_cpw1 (.cv d))) (.classEq (syn_ctc K) (syn_cnc (syn_cpw1 (.cv d))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, fresh_x_ne_d, fresh_x_not_K, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((syn_ctc K)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_K, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((syn_ctc K)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_K, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0012 : d ∉ ((Wff.classMem (syn_ctc K) (syn_chwcards (syn_cvv)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_K, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : s ∉ ((Wff.classMem (syn_ctc K) (syn_chwcards (syn_cvv)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_K, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classMem K (syn_chwcards (syn_cvv)))
  have p0001 :=
    @g_id (.classMem K (syn_chwcards (syn_cvv)))
  have p0002 :=
    @g_elex K (syn_chwcards (syn_cvv))
  have p0003 :=
    @g_syl (.classMem K (syn_chwcards (syn_cvv))) (.classMem K (syn_chwcards (syn_cvv))) (.classMem K (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_elhwcardsweclndv K s d dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0005 :=
    @g_syl (.classMem K (syn_chwcards (syn_cvv))) (.classMem K (syn_cvv)) (syn_wb (.classMem K (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))))) p0003 p0004
  have p0006 :=
    @g_mpbid (.classMem K (syn_chwcards (syn_cvv))) (.classMem K (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))))) p0000 p0005
  have p0007 :=
    @g_simpl (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))
  have p0008 :=
    @g_siwendv (.cv d) (.cv s)
  have p0009 :=
    @g_syl (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))) (syn_wbr (.cv s) (syn_cwe) (.cv d)) (syn_wbr (syn_csi (.cv s)) (syn_cwe) (syn_cpw1 (.cv d))) p0007 p0008
  have p0010 :=
    @g_simpr (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))
  have p0011 :=
    @g_tceq K (syn_cnc (.cv d))
  have p0012 :=
    @g_syl (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))) (.classEq K (syn_cnc (.cv d))) (.classEq (syn_ctc K) (syn_ctc (syn_cnc (.cv d)))) p0010 p0011
  have p0013 :=
    @g_simpl (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))
  have p0014 :=
    @g_brex (.cv s) (.cv d) (syn_cwe)
  have p0015 :=
    @g_simpr (.classMem (.cv s) (syn_cvv)) (.classMem (.cv d) (syn_cvv))
  have p0016 :=
    @g_syl (syn_wbr (.cv s) (syn_cwe) (.cv d)) (syn_wa (.classMem (.cv s) (syn_cvv)) (.classMem (.cv d) (syn_cvv))) (.classMem (.cv d) (syn_cvv)) p0014 p0015
  have p0017 :=
    @g_syl (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))) (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classMem (.cv d) (syn_cvv)) p0013 p0016
  have p0018 :=
    @g_tcncg (.cv d) (syn_cvv)
  have p0019 :=
    @g_syl (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))) (.classMem (.cv d) (syn_cvv)) (.classEq (syn_ctc (syn_cnc (.cv d))) (syn_cnc (syn_cpw1 (.cv d)))) p0017 p0018
  have p0020 :=
    @g_eqtrd (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))) (syn_ctc K) (syn_ctc (syn_cnc (.cv d))) (syn_cnc (syn_cpw1 (.cv d))) p0012 p0019
  have p0021 :=
    @g_jca (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))) (syn_wbr (syn_csi (.cv s)) (syn_cwe) (syn_cpw1 (.cv d))) (.classEq (syn_ctc K) (syn_cnc (syn_cpw1 (.cv d)))) p0009 p0020
  have p0022 :=
    @g_simpl (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))
  have p0023 :=
    @g_brex (.cv s) (.cv d) (syn_cwe)
  have p0024 :=
    @g_simpl (.classMem (.cv s) (syn_cvv)) (.classMem (.cv d) (syn_cvv))
  have p0025 :=
    @g_syl (syn_wbr (.cv s) (syn_cwe) (.cv d)) (syn_wa (.classMem (.cv s) (syn_cvv)) (.classMem (.cv d) (syn_cvv))) (.classMem (.cv s) (syn_cvv)) p0023 p0024
  have p0026 :=
    @g_syl (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))) (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classMem (.cv s) (syn_cvv)) p0022 p0025
  have p0027 :=
    @g_siexg (.cv s) (syn_cvv)
  have p0028 :=
    @g_syl (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))) (.classMem (.cv s) (syn_cvv)) (.classMem (syn_csi (.cv s)) (syn_cvv)) p0026 p0027
  have p0029 :=
    @g_id (.classEq (.cv y) (syn_csi (.cv s)))
  have p0030 :=
    @g_breq1d (.classEq (.cv y) (syn_csi (.cv s))) (.cv y) (syn_csi (.cv s)) (syn_cpw1 (.cv d)) (syn_cwe) p0029
  have p0031 :=
    @g_anbi1d (.classEq (.cv y) (syn_csi (.cv s))) (syn_wbr (.cv y) (syn_cwe) (syn_cpw1 (.cv d))) (syn_wbr (syn_csi (.cv s)) (syn_cwe) (syn_cpw1 (.cv d))) (.classEq (syn_ctc K) (syn_cnc (syn_cpw1 (.cv d)))) p0030
  have p0032 :=
    @g_spcegv (syn_wa (syn_wbr (.cv y) (syn_cwe) (syn_cpw1 (.cv d))) (.classEq (syn_ctc K) (syn_cnc (syn_cpw1 (.cv d))))) (syn_wa (syn_wbr (syn_csi (.cv s)) (syn_cwe) (syn_cpw1 (.cv d))) (.classEq (syn_ctc K) (syn_cnc (syn_cpw1 (.cv d))))) y (syn_csi (.cv s)) (syn_cvv) dv_cache_0004 dv_cache_0005 p0031
  have p0033 :=
    @g_syl (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))) (.classMem (syn_csi (.cv s)) (syn_cvv)) (.imp (syn_wa (syn_wbr (syn_csi (.cv s)) (syn_cwe) (syn_cpw1 (.cv d))) (.classEq (syn_ctc K) (syn_cnc (syn_cpw1 (.cv d))))) (syn_wex y (syn_wa (syn_wbr (.cv y) (syn_cwe) (syn_cpw1 (.cv d))) (.classEq (syn_ctc K) (syn_cnc (syn_cpw1 (.cv d))))))) p0028 p0032
  have p0034 :=
    @g_mpd (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))) (syn_wa (syn_wbr (syn_csi (.cv s)) (syn_cwe) (syn_cpw1 (.cv d))) (.classEq (syn_ctc K) (syn_cnc (syn_cpw1 (.cv d))))) (syn_wex y (syn_wa (syn_wbr (.cv y) (syn_cwe) (syn_cpw1 (.cv d))) (.classEq (syn_ctc K) (syn_cnc (syn_cpw1 (.cv d)))))) p0021 p0033
  have p0035 :=
    @g_simpl (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))
  have p0036 :=
    @g_brex (.cv s) (.cv d) (syn_cwe)
  have p0037 :=
    @g_simpr (.classMem (.cv s) (syn_cvv)) (.classMem (.cv d) (syn_cvv))
  have p0038 :=
    @g_syl (syn_wbr (.cv s) (syn_cwe) (.cv d)) (syn_wa (.classMem (.cv s) (syn_cvv)) (.classMem (.cv d) (syn_cvv))) (.classMem (.cv d) (syn_cvv)) p0036 p0037
  have p0039 :=
    @g_syl (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))) (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classMem (.cv d) (syn_cvv)) p0035 p0038
  have p0040 :=
    @g_pw1exg (.cv d) (syn_cvv)
  have p0041 :=
    @g_syl (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))) (.classMem (.cv d) (syn_cvv)) (.classMem (syn_cpw1 (.cv d)) (syn_cvv)) p0039 p0040
  have p0042 :=
    @g_id (.classEq (.cv x) (syn_cpw1 (.cv d)))
  have p0043 :=
    @g_breq2d (.classEq (.cv x) (syn_cpw1 (.cv d))) (.cv x) (syn_cpw1 (.cv d)) (.cv y) (syn_cwe) p0042
  have p0044 :=
    @g_id (.classEq (.cv x) (syn_cpw1 (.cv d)))
  have p0045 :=
    @g_nceqd (.classEq (.cv x) (syn_cpw1 (.cv d))) (.cv x) (syn_cpw1 (.cv d)) p0044
  have p0046 :=
    @g_eqeq2d (.classEq (.cv x) (syn_cpw1 (.cv d))) (syn_cnc (.cv x)) (syn_cnc (syn_cpw1 (.cv d))) (syn_ctc K) p0045
  have p0047 :=
    @g_anbi12d (.classEq (.cv x) (syn_cpw1 (.cv d))) (syn_wbr (.cv y) (syn_cwe) (.cv x)) (syn_wbr (.cv y) (syn_cwe) (syn_cpw1 (.cv d))) (.classEq (syn_ctc K) (syn_cnc (.cv x))) (.classEq (syn_ctc K) (syn_cnc (syn_cpw1 (.cv d)))) p0043 p0046
  have p0048 :=
    @g_exbidv (.classEq (.cv x) (syn_cpw1 (.cv d))) (syn_wa (syn_wbr (.cv y) (syn_cwe) (.cv x)) (.classEq (syn_ctc K) (syn_cnc (.cv x)))) (syn_wa (syn_wbr (.cv y) (syn_cwe) (syn_cpw1 (.cv d))) (.classEq (syn_ctc K) (syn_cnc (syn_cpw1 (.cv d))))) y dv_cache_0006 p0047
  have p0049 :=
    @g_spcegv (syn_wex y (syn_wa (syn_wbr (.cv y) (syn_cwe) (.cv x)) (.classEq (syn_ctc K) (syn_cnc (.cv x))))) (syn_wex y (syn_wa (syn_wbr (.cv y) (syn_cwe) (syn_cpw1 (.cv d))) (.classEq (syn_ctc K) (syn_cnc (syn_cpw1 (.cv d)))))) x (syn_cpw1 (.cv d)) (syn_cvv) dv_cache_0007 dv_cache_0008 p0048
  have p0050 :=
    @g_syl (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))) (.classMem (syn_cpw1 (.cv d)) (syn_cvv)) (.imp (syn_wex y (syn_wa (syn_wbr (.cv y) (syn_cwe) (syn_cpw1 (.cv d))) (.classEq (syn_ctc K) (syn_cnc (syn_cpw1 (.cv d)))))) (syn_wex x (syn_wex y (syn_wa (syn_wbr (.cv y) (syn_cwe) (.cv x)) (.classEq (syn_ctc K) (syn_cnc (.cv x))))))) p0041 p0049
  have p0051 :=
    @g_mpd (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))) (syn_wex y (syn_wa (syn_wbr (.cv y) (syn_cwe) (syn_cpw1 (.cv d))) (.classEq (syn_ctc K) (syn_cnc (syn_cpw1 (.cv d)))))) (syn_wex x (syn_wex y (syn_wa (syn_wbr (.cv y) (syn_cwe) (.cv x)) (.classEq (syn_ctc K) (syn_cnc (.cv x)))))) p0034 p0050
  have p0052 :=
    @g_tcex K
  have p0053 :=
    @g_elhwcardsweclndv (syn_ctc K) y x dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0054 :=
    Nominal.mp p0052 p0053
  have p0055 :=
    @g_biimpri (.classMem (syn_ctc K) (syn_chwcards (syn_cvv))) (syn_wex x (syn_wex y (syn_wa (syn_wbr (.cv y) (syn_cwe) (.cv x)) (.classEq (syn_ctc K) (syn_cnc (.cv x)))))) p0054
  have p0056 :=
    @g_syl (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))) (syn_wex x (syn_wex y (syn_wa (syn_wbr (.cv y) (syn_cwe) (.cv x)) (.classEq (syn_ctc K) (syn_cnc (.cv x)))))) (.classMem (syn_ctc K) (syn_chwcards (syn_cvv))) p0051 p0055
  have p0057 :=
    @g_exlimivv (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))) (.classMem (syn_ctc K) (syn_chwcards (syn_cvv))) d s dv_cache_0012 dv_cache_0013 p0056
  have p0058 :=
    @g_syl (.classMem K (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))))) (.classMem (syn_ctc K) (syn_chwcards (syn_cvv))) p0006 p0057
  exact p0058

noncomputable def g_hwcardsdownltcndv
    (C : Class) (d : Var) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_chwcards (syn_cvv)))) := by
  let proofSupport : Finset Var := C.fv ∪ ({d} : Finset Var)
  let r : Var := freshVar proofSupport 0
  let e : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  let s : Var := freshVar proofSupport 3
  let a : Var := freshVar proofSupport 4
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_not_C : r ∉ C.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (h))
  have fresh_r_ne_d : r ≠ d := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_d_ne_r : d ≠ r :=
    Ne.symm fresh_r_ne_d
  have fresh_e : e ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_e_not_C : e ∉ C.fv := by
    intro h
    exact fresh_e (Finset.mem_union_left _ (h))
  have fresh_e_ne_d : e ≠ d := by
    intro h
    exact fresh_e (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_d_ne_e : d ≠ e :=
    Ne.symm fresh_e_ne_d
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_ne_d : x ≠ d := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_d_ne_x : d ≠ x :=
    Ne.symm fresh_x_ne_d
  have fresh_s : s ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_s_not_C : s ∉ C.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (h))
  have fresh_s_ne_d : s ≠ d := by
    intro h
    exact fresh_s (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_d_ne_s : d ≠ s :=
    Ne.symm fresh_s_ne_d
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_a_not_C : a ∉ C.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (h))
  have fresh_a_ne_d : a ≠ d := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_d_ne_a : d ≠ a :=
    Ne.symm fresh_a_ne_d
  have fresh_r_ne_e : r ≠ e := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_e_ne_r : e ≠ r :=
    Ne.symm fresh_r_ne_e
  have fresh_r_ne_x : r ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_r : x ≠ r :=
    Ne.symm fresh_r_ne_x
  have fresh_r_ne_s : r ≠ s := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_s_ne_r : s ≠ r :=
    Ne.symm fresh_r_ne_s
  have fresh_r_ne_a : r ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_a_ne_r : a ≠ r :=
    Ne.symm fresh_r_ne_a
  have fresh_e_ne_x : e ≠ x := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_e : x ≠ e :=
    Ne.symm fresh_e_ne_x
  have fresh_e_ne_s : e ≠ s := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_s_ne_e : s ≠ e :=
    Ne.symm fresh_e_ne_s
  have fresh_e_ne_a : e ≠ a := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_a_ne_e : a ≠ e :=
    Ne.symm fresh_e_ne_a
  have fresh_x_ne_s : x ≠ s := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_s_ne_x : s ≠ x :=
    Ne.symm fresh_x_ne_s
  have fresh_x_ne_a : x ≠ a := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_a_ne_x : a ≠ x :=
    Ne.symm fresh_x_ne_a
  have fresh_s_ne_a : s ≠ a := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_a_ne_s : a ≠ s :=
    Ne.symm fresh_s_ne_a
  have dv_cache_0001 : e ∉ (C).fv := by
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_e_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : r ∉ (C).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : e ≠ r := by
    clear dv_cache_0001 dv_cache_0002
    exact (show e ≠ r from (by exact fresh_e_ne_r))
  have dv_cache_0004 : x ∉ ((Class.cv e)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_e, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Class.cv d)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : a ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : s ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : a ∉ ((syn_cin (.cv r) (syn_cxp (.cv x) (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_r, fresh_a_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : s ∉ ((syn_cin (.cv r) (syn_cxp (.cv x) (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_ne_r, fresh_s_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : a ∉ ((syn_wa (syn_wbr (syn_cin (.cv r) (syn_cxp (.cv x) (.cv x))) (syn_cwe) (.cv x)) (.classEq (.cv d) (syn_cnc (.cv x))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_r, fresh_a_ne_x, fresh_a_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : s ∉ ((syn_wa (syn_wbr (syn_cin (.cv r) (syn_cxp (.cv x) (.cv x))) (syn_cwe) (.cv x)) (.classEq (.cv d) (syn_cnc (.cv x))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_ne_r, fresh_s_ne_x, fresh_s_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : a ≠ s := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show a ≠ s from (by exact fresh_a_ne_s))
  have dv_cache_0013 : a ≠ d := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show a ≠ d from (by exact fresh_a_ne_d))
  have dv_cache_0014 : d ≠ s := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show d ≠ s from (by exact fresh_d_ne_s))
  have dv_cache_0015 : x ∉ ((Wff.classMem (.cv d) (syn_chwcards (syn_cvv)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : x ∉ ((syn_wa (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_d, fresh_x_not_C, fresh_x_ne_r, fresh_x_ne_e, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : e ∉ ((Wff.classMem (.cv d) (syn_chwcards (syn_cvv)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_e_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : r ∉ ((Wff.classMem (.cv d) (syn_chwcards (syn_cvv)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : e ∉ ((syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_e_ne_d, fresh_e_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : r ∉ ((syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_d, fresh_r_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)
  have p0001 :=
    @g_simpr (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))
  have p0002 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (.classMem C (syn_chwcards (syn_cvv))) p0000 p0001
  have p0003 :=
    @g_simpl (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)
  have p0004 :=
    @g_simpr (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))
  have p0005 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (.classMem C (syn_chwcards (syn_cvv))) p0003 p0004
  have p0006 :=
    @g_elex C (syn_chwcards (syn_cvv))
  have p0007 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem C (syn_chwcards (syn_cvv))) (.classMem C (syn_cvv)) p0005 p0006
  have p0008 :=
    @g_elhwcardsweclndv C r e dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0009 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem C (syn_cvv)) (syn_wb (.classMem C (syn_chwcards (syn_cvv))) (syn_wex e (syn_wex r (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))))) p0007 p0008
  have p0010 :=
    @g_mpbid (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem C (syn_chwcards (syn_cvv))) (syn_wex e (syn_wex r (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))))) p0002 p0009
  have p0011 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))
  have p0012 :=
    @g_simpr (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)
  have p0013 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))) (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wbr (.cv d) (syn_clec) C) p0011 p0012
  have p0014 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))
  have p0015 :=
    @g_simpr (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))
  have p0016 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))) (.classEq C (syn_cnc (.cv e))) p0014 p0015
  have p0017 :=
    @g_breq2d (syn_wa (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))) C (syn_cnc (.cv e)) (.cv d) (syn_clec) p0016
  have p0018 :=
    @g_mpbid (syn_wa (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))) (syn_wbr (.cv d) (syn_clec) C) (syn_wbr (.cv d) (syn_clec) (syn_cnc (.cv e))) p0013 p0017
  have p0019 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))
  have p0020 :=
    @g_simpl (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)
  have p0021 :=
    @g_simpl (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))
  have p0022 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (.classMem (.cv d) (syn_cncs)) p0020 p0021
  have p0023 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))) (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cncs)) p0019 p0022
  have p0024 :=
    @g_vex e
  have p0025 :=
    @g_lenc x (.cv e) (.cv d) dv_cache_0004 dv_cache_0005 p0024
  have p0026 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))) (.classMem (.cv d) (syn_cncs)) (syn_wb (syn_wbr (.cv d) (syn_clec) (syn_cnc (.cv e))) (syn_wrex x (.cv d) (syn_wss (.cv x) (.cv e)))) p0023 p0025
  have p0027 :=
    @g_mpbid (syn_wa (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))) (syn_wbr (.cv d) (syn_clec) (syn_cnc (.cv e))) (syn_wrex x (.cv d) (syn_wss (.cv x) (.cv e))) p0018 p0026
  have p0028 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))) (syn_wa (.classMem (.cv x) (.cv d)) (syn_wss (.cv x) (.cv e)))
  have p0029 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))
  have p0030 :=
    @g_simpl (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))
  have p0031 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))) (syn_wbr (.cv r) (syn_cwe) (.cv e)) p0029 p0030
  have p0032 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))) (syn_wa (.classMem (.cv x) (.cv d)) (syn_wss (.cv x) (.cv e)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))) (syn_wbr (.cv r) (syn_cwe) (.cv e)) p0028 p0031
  have p0033 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))) (syn_wa (.classMem (.cv x) (.cv d)) (syn_wss (.cv x) (.cv e)))
  have p0034 :=
    @g_simpr (.classMem (.cv x) (.cv d)) (syn_wss (.cv x) (.cv e))
  have p0035 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))) (syn_wa (.classMem (.cv x) (.cv d)) (syn_wss (.cv x) (.cv e)))) (syn_wa (.classMem (.cv x) (.cv d)) (syn_wss (.cv x) (.cv e))) (syn_wss (.cv x) (.cv e)) p0033 p0034
  have p0036 :=
    @g_vex x
  have p0037 :=
    @g_a1i (.classMem (.cv x) (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))) (syn_wa (.classMem (.cv x) (.cv d)) (syn_wss (.cv x) (.cv e)))) p0036
  have p0038 :=
    @g_werestrndv (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))) (syn_wa (.classMem (.cv x) (.cv d)) (syn_wss (.cv x) (.cv e)))) (.cv x) (.cv e) (.cv r) p0032 p0035 p0037
  have p0039 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))) (syn_wa (.classMem (.cv x) (.cv d)) (syn_wss (.cv x) (.cv e)))
  have p0040 :=
    @g_simpl (.classMem (.cv x) (.cv d)) (syn_wss (.cv x) (.cv e))
  have p0041 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))) (syn_wa (.classMem (.cv x) (.cv d)) (syn_wss (.cv x) (.cv e)))) (syn_wa (.classMem (.cv x) (.cv d)) (syn_wss (.cv x) (.cv e))) (.classMem (.cv x) (.cv d)) p0039 p0040
  have p0042 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))) (syn_wa (.classMem (.cv x) (.cv d)) (syn_wss (.cv x) (.cv e)))
  have p0043 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))
  have p0044 :=
    @g_simpl (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)
  have p0045 :=
    @g_simpl (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))
  have p0046 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (.classMem (.cv d) (syn_cncs)) p0044 p0045
  have p0047 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))) (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cncs)) p0043 p0046
  have p0048 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))) (syn_wa (.classMem (.cv x) (.cv d)) (syn_wss (.cv x) (.cv e)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))) (.classMem (.cv d) (syn_cncs)) p0042 p0047
  have p0049 :=
    @g_ncseqnc (.cv d) (.cv x)
  have p0050 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))) (syn_wa (.classMem (.cv x) (.cv d)) (syn_wss (.cv x) (.cv e)))) (.classMem (.cv d) (syn_cncs)) (syn_wb (.classEq (.cv d) (syn_cnc (.cv x))) (.classMem (.cv x) (.cv d))) p0048 p0049
  have p0051 :=
    @g_mpbird (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))) (syn_wa (.classMem (.cv x) (.cv d)) (syn_wss (.cv x) (.cv e)))) (.classEq (.cv d) (syn_cnc (.cv x))) (.classMem (.cv x) (.cv d)) p0041 p0050
  have p0052 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))) (syn_wa (.classMem (.cv x) (.cv d)) (syn_wss (.cv x) (.cv e)))) (syn_wbr (syn_cin (.cv r) (syn_cxp (.cv x) (.cv x))) (syn_cwe) (.cv x)) (.classEq (.cv d) (syn_cnc (.cv x))) p0038 p0051
  have p0053 :=
    @g_vex x
  have p0054 :=
    @g_vex r
  have p0055 :=
    @g_vex x
  have p0056 :=
    @g_vex x
  have p0057 :=
    @g_xpex (.cv x) (.cv x) p0055 p0056
  have p0058 :=
    @g_inex (.cv r) (syn_cxp (.cv x) (.cv x)) p0054 p0057
  have p0059 :=
    @g_pm3_2i (.classMem (.cv x) (syn_cvv)) (.classMem (syn_cin (.cv r) (syn_cxp (.cv x) (.cv x))) (syn_cvv)) p0053 p0058
  have p0060 :=
    @g_simpr (.classEq (.cv a) (.cv x)) (.classEq (.cv s) (syn_cin (.cv r) (syn_cxp (.cv x) (.cv x))))
  have p0061 :=
    @g_simpl (.classEq (.cv a) (.cv x)) (.classEq (.cv s) (syn_cin (.cv r) (syn_cxp (.cv x) (.cv x))))
  have p0062 :=
    @g_breq12d (syn_wa (.classEq (.cv a) (.cv x)) (.classEq (.cv s) (syn_cin (.cv r) (syn_cxp (.cv x) (.cv x))))) (.cv s) (syn_cin (.cv r) (syn_cxp (.cv x) (.cv x))) (.cv a) (.cv x) (syn_cwe) p0060 p0061
  have p0063 :=
    @g_simpl (.classEq (.cv a) (.cv x)) (.classEq (.cv s) (syn_cin (.cv r) (syn_cxp (.cv x) (.cv x))))
  have p0064 :=
    @g_nceqd (syn_wa (.classEq (.cv a) (.cv x)) (.classEq (.cv s) (syn_cin (.cv r) (syn_cxp (.cv x) (.cv x))))) (.cv a) (.cv x) p0063
  have p0065 :=
    @g_eqeq2d (syn_wa (.classEq (.cv a) (.cv x)) (.classEq (.cv s) (syn_cin (.cv r) (syn_cxp (.cv x) (.cv x))))) (syn_cnc (.cv a)) (syn_cnc (.cv x)) (.cv d) p0064
  have p0066 :=
    @g_anbi12d (syn_wa (.classEq (.cv a) (.cv x)) (.classEq (.cv s) (syn_cin (.cv r) (syn_cxp (.cv x) (.cv x))))) (syn_wbr (.cv s) (syn_cwe) (.cv a)) (syn_wbr (syn_cin (.cv r) (syn_cxp (.cv x) (.cv x))) (syn_cwe) (.cv x)) (.classEq (.cv d) (syn_cnc (.cv a))) (.classEq (.cv d) (syn_cnc (.cv x))) p0062 p0065
  have p0067 :=
    @g_spc2egv (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv a)) (.classEq (.cv d) (syn_cnc (.cv a)))) (syn_wa (syn_wbr (syn_cin (.cv r) (syn_cxp (.cv x) (.cv x))) (syn_cwe) (.cv x)) (.classEq (.cv d) (syn_cnc (.cv x)))) a s (.cv x) (syn_cin (.cv r) (syn_cxp (.cv x) (.cv x))) (syn_cvv) (syn_cvv) dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 p0066
  have p0068 :=
    Nominal.mp p0059 p0067
  have p0069 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))) (syn_wa (.classMem (.cv x) (.cv d)) (syn_wss (.cv x) (.cv e)))) (syn_wa (syn_wbr (syn_cin (.cv r) (syn_cxp (.cv x) (.cv x))) (syn_cwe) (.cv x)) (.classEq (.cv d) (syn_cnc (.cv x)))) (syn_wex a (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv a)) (.classEq (.cv d) (syn_cnc (.cv a)))))) p0052 p0068
  have p0070 :=
    @g_elhwcardswev d s a dv_cache_0013 dv_cache_0012 dv_cache_0014
  have p0071 :=
    @g_biimpri (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wex a (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv a)) (.classEq (.cv d) (syn_cnc (.cv a)))))) p0070
  have p0072 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))) (syn_wa (.classMem (.cv x) (.cv d)) (syn_wss (.cv x) (.cv e)))) (syn_wex a (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv a)) (.classEq (.cv d) (syn_cnc (.cv a)))))) (.classMem (.cv d) (syn_chwcards (syn_cvv))) p0069 p0071
  have p0073 :=
    @g_rexlimdvaa (syn_wa (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))) (syn_wss (.cv x) (.cv e)) (.classMem (.cv d) (syn_chwcards (syn_cvv))) x (.cv d) dv_cache_0015 dv_cache_0016 p0072
  have p0074 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))) (syn_wrex x (.cv d) (syn_wss (.cv x) (.cv e))) (.classMem (.cv d) (syn_chwcards (syn_cvv))) p0027 p0073
  have p0075 :=
    @g_ex (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))) (.classMem (.cv d) (syn_chwcards (syn_cvv))) p0074
  have p0076 :=
    @g_exlimdvv (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))) (.classMem (.cv d) (syn_chwcards (syn_cvv))) e r dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 p0075
  have p0077 :=
    @g_mpd (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wex e (syn_wex r (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))))) (.classMem (.cv d) (syn_chwcards (syn_cvv))) p0010 p0076
  exact p0077

#print axioms g_hwcardsdownltcndv

end NFChoice.DirectNominalPrf.WPPReplay
