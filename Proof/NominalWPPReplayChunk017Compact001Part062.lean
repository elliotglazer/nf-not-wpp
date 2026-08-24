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
import NominalWPPReplayChunk017Compact001Part061

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

noncomputable def g_hwcardslecconnexndv
    (K : Class) (L : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wo (syn_wbr K (syn_clec) L) (syn_wbr L (syn_clec) K))) := by
  let proofSupport : Finset Var := K.fv ∪ L.fv
  let r : Var := freshVar proofSupport 0
  let d : Var := freshVar proofSupport 1
  let s : Var := freshVar proofSupport 2
  let e : Var := freshVar proofSupport 3
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_not_K : r ∉ K.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (h))
  have fresh_r_not_L : r ∉ L.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_d : d ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_d_not_K : d ∉ K.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (h))
  have fresh_d_not_L : d ∉ L.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_s : s ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_s_not_K : s ∉ K.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (h))
  have fresh_s_not_L : s ∉ L.fv := by
    intro h
    exact fresh_s (Finset.mem_union_right _ (h))
  have fresh_e : e ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_e_not_K : e ∉ K.fv := by
    intro h
    exact fresh_e (Finset.mem_union_left _ (h))
  have fresh_e_not_L : e ∉ L.fv := by
    intro h
    exact fresh_e (Finset.mem_union_right _ (h))
  have fresh_r_ne_d : r ≠ d := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_d_ne_r : d ≠ r :=
    Ne.symm fresh_r_ne_d
  have fresh_r_ne_s : r ≠ s := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_s_ne_r : s ≠ r :=
    Ne.symm fresh_r_ne_s
  have fresh_r_ne_e : r ≠ e := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_e_ne_r : e ≠ r :=
    Ne.symm fresh_r_ne_e
  have fresh_d_ne_s : d ≠ s := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_s_ne_d : s ≠ d :=
    Ne.symm fresh_d_ne_s
  have fresh_d_ne_e : d ≠ e := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_e_ne_d : e ≠ d :=
    Ne.symm fresh_d_ne_e
  have fresh_s_ne_e : s ≠ e := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_e_ne_s : e ≠ s :=
    Ne.symm fresh_s_ne_e
  have dv_cache_0001 : d ∉ (K).fv := by
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_K, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : r ∉ (K).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_K, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : d ≠ r := by
    clear dv_cache_0001 dv_cache_0002
    exact (show d ≠ r from (by exact fresh_d_ne_r))
  have dv_cache_0004 : e ∉ (L).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_e_not_L, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : s ∉ (L).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_L, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : e ≠ s := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show e ≠ s from (by exact fresh_e_ne_s))
  have dv_cache_0007 : e ∉ ((syn_wo (syn_wbr K (syn_clec) L) (syn_wbr L (syn_clec) K))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_e_not_K, fresh_e_not_L, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : s ∉ ((syn_wo (syn_wbr K (syn_clec) L) (syn_wbr L (syn_clec) K))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_K, fresh_s_not_L, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : e ∉ ((syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_e_not_K, fresh_e_not_L, fresh_e_ne_r, fresh_e_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : s ∉ ((syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_K, fresh_s_not_L, fresh_s_ne_r, fresh_s_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : d ∉ ((syn_wo (syn_wbr K (syn_clec) L) (syn_wbr L (syn_clec) K))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_K, fresh_d_not_L, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : r ∉ ((syn_wo (syn_wbr K (syn_clec) L) (syn_wbr L (syn_clec) K))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_K, fresh_r_not_L, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : d ∉ ((syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_K, fresh_d_not_L, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : r ∉ ((syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_K, fresh_r_not_L, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))
  have p0001 :=
    @g_simpl (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))
  have p0002 :=
    @g_elex K (syn_chwcards (syn_cvv))
  have p0003 :=
    @g_syl (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (.classMem K (syn_chwcards (syn_cvv))) (.classMem K (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_elhwcardsweclndv K r d dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0005 :=
    @g_syl (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (.classMem K (syn_cvv)) (syn_wb (.classMem K (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex r (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))))) p0003 p0004
  have p0006 :=
    @g_mpbid (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (.classMem K (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex r (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))))) p0000 p0005
  have p0007 :=
    @g_simpl (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))
  have p0008 :=
    @g_simpr (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))
  have p0009 :=
    @g_simpr (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))
  have p0010 :=
    @g_elex L (syn_chwcards (syn_cvv))
  have p0011 :=
    @g_syl (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (.classMem L (syn_chwcards (syn_cvv))) (.classMem L (syn_cvv)) p0009 p0010
  have p0012 :=
    @g_elhwcardsweclndv L s e dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0013 :=
    @g_syl (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (.classMem L (syn_cvv)) (syn_wb (.classMem L (syn_chwcards (syn_cvv))) (syn_wex e (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e))))))) p0011 p0012
  have p0014 :=
    @g_mpbid (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (.classMem L (syn_chwcards (syn_cvv))) (syn_wex e (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e)))))) p0008 p0013
  have p0015 :=
    @g_syl (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))) (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wex e (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e)))))) p0007 p0014
  have p0016 :=
    @g_simpl (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e))))
  have p0017 :=
    @g_simpr (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))
  have p0018 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e))))) (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))) p0016 p0017
  have p0019 :=
    @g_simpl (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))
  have p0020 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e))))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))) (syn_wbr (.cv r) (syn_cwe) (.cv d)) p0018 p0019
  have p0021 :=
    @g_simpr (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e))))
  have p0022 :=
    @g_simpl (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e)))
  have p0023 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e))))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e)))) (syn_wbr (.cv s) (syn_cwe) (.cv e)) p0021 p0022
  have p0024 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e))))) (syn_wbr (.cv r) (syn_cwe) (.cv d)) (syn_wbr (.cv s) (syn_cwe) (.cv e)) p0020 p0023
  have p0025 :=
    @g_wecomparisonnclecandndv e s r d
  have p0026 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e))))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (syn_wbr (.cv s) (syn_cwe) (.cv e))) (syn_wo (syn_wbr (syn_cnc (.cv d)) (syn_clec) (syn_cnc (.cv e))) (syn_wbr (syn_cnc (.cv e)) (syn_clec) (syn_cnc (.cv d)))) p0024 p0025
  have p0027 :=
    @g_simpl (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e))))
  have p0028 :=
    @g_simpr (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))
  have p0029 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e))))) (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))) p0027 p0028
  have p0030 :=
    @g_simpr (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))
  have p0031 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e))))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))) (.classEq K (syn_cnc (.cv d))) p0029 p0030
  have p0032 :=
    @g_eqcomd (syn_wa (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e))))) K (syn_cnc (.cv d)) p0031
  have p0033 :=
    @g_simpr (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e))))
  have p0034 :=
    @g_simpr (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e)))
  have p0035 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e))))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e)))) (.classEq L (syn_cnc (.cv e))) p0033 p0034
  have p0036 :=
    @g_eqcomd (syn_wa (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e))))) L (syn_cnc (.cv e)) p0035
  have p0037 :=
    @g_breq12d (syn_wa (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e))))) (syn_cnc (.cv d)) K (syn_cnc (.cv e)) L (syn_clec) p0032 p0036
  have p0038 :=
    @g_simpr (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e))))
  have p0039 :=
    @g_simpr (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e)))
  have p0040 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e))))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e)))) (.classEq L (syn_cnc (.cv e))) p0038 p0039
  have p0041 :=
    @g_eqcomd (syn_wa (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e))))) L (syn_cnc (.cv e)) p0040
  have p0042 :=
    @g_simpl (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e))))
  have p0043 :=
    @g_simpr (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))
  have p0044 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e))))) (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))) p0042 p0043
  have p0045 :=
    @g_simpr (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))
  have p0046 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e))))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))) (.classEq K (syn_cnc (.cv d))) p0044 p0045
  have p0047 :=
    @g_eqcomd (syn_wa (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e))))) K (syn_cnc (.cv d)) p0046
  have p0048 :=
    @g_breq12d (syn_wa (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e))))) (syn_cnc (.cv e)) L (syn_cnc (.cv d)) K (syn_clec) p0041 p0047
  have p0049 :=
    @g_orbi12d (syn_wa (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e))))) (syn_wbr (syn_cnc (.cv d)) (syn_clec) (syn_cnc (.cv e))) (syn_wbr K (syn_clec) L) (syn_wbr (syn_cnc (.cv e)) (syn_clec) (syn_cnc (.cv d))) (syn_wbr L (syn_clec) K) p0037 p0048
  have p0050 :=
    @g_mpbid (syn_wa (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e))))) (syn_wo (syn_wbr (syn_cnc (.cv d)) (syn_clec) (syn_cnc (.cv e))) (syn_wbr (syn_cnc (.cv e)) (syn_clec) (syn_cnc (.cv d)))) (syn_wo (syn_wbr K (syn_clec) L) (syn_wbr L (syn_clec) K)) p0026 p0049
  have p0051 :=
    @g_ex (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e)))) (syn_wo (syn_wbr K (syn_clec) L) (syn_wbr L (syn_clec) K)) p0050
  have p0052 :=
    @g_exlimdvv (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e)))) (syn_wo (syn_wbr K (syn_clec) L) (syn_wbr L (syn_clec) K)) e s dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 p0051
  have p0053 :=
    @g_mpd (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))) (syn_wex e (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e)))))) (syn_wo (syn_wbr K (syn_clec) L) (syn_wbr L (syn_clec) K)) p0015 p0052
  have p0054 :=
    @g_ex (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))) (syn_wo (syn_wbr K (syn_clec) L) (syn_wbr L (syn_clec) K)) p0053
  have p0055 :=
    @g_exlimdvv (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))) (syn_wo (syn_wbr K (syn_clec) L) (syn_wbr L (syn_clec) K)) d r dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 p0054
  have p0056 :=
    @g_mpd (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))) (syn_wex d (syn_wex r (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))))) (syn_wo (syn_wbr K (syn_clec) L) (syn_wbr L (syn_clec) K)) p0006 p0055
  exact p0056

noncomputable def g_wpporbithwcldmndv
    (F : Class) (I : Class) (q : Var) (dv_F_q : q ∉ F.fv) (dv_I_q : q ∉ I.fv) (hyp_wpporbithwcldmndv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wpporbithwcldmndv_2 : Nominal.NPrf (.classMem I (syn_cdm F))) (hyp_wpporbithwcldmndv_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) (hyp_wpporbithwcldmndv_4 : Nominal.NPrf (.classEq (syn_cdm F) (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_chwcards (syn_cvv)))) := by
  let proofSupport : Finset Var := F.fv ∪ I.fv ∪ ({q} : Finset Var)
  have p0000 :=
    @g_n_3pm3_2i (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F)) hyp_wpporbithwcldmndv_1 hyp_wpporbithwcldmndv_2 hyp_wpporbithwcldmndv_3
  have p0001 :=
    @g_id (.classMem (.cv q) (syn_cnnc))
  have p0002 :=
    @g_frecdomfv F I (.cv q)
  have p0003 :=
    @g_sylancr (.classMem (.cv q) (syn_cnnc)) (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cdm F)) p0000 p0001 p0002
  have p0004 :=
    @g_eleq2i (syn_cdm F) (syn_chwcards (syn_cvv)) (syn_cfv (syn_cfrec F I) (.cv q)) hyp_wpporbithwcldmndv_4
  have p0005 :=
    @g_sylib (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cdm F)) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_chwcards (syn_cvv))) p0003 p0004
  have p0006 :=
    Nominal.gen p0005 q
  have p0007 :=
    (by simpa [syn_wb, syn_wral] using (Nominal.biimpRefl (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_chwcards (syn_cvv))))))
  have p0008 :=
    @g_mpbir (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_chwcards (syn_cvv)))) (.all q (.imp (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_chwcards (syn_cvv))))) p0006 p0007
  exact p0008

#print axioms g_wpporbithwcldmndv

end NFChoice.DirectNominalPrf.WPPReplay
