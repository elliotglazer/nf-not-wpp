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
import NominalWPPReplayChunk017Compact001Part048

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

noncomputable def g_hncardhwcardsndv
    (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cvv)) (.classMem (syn_chncard A) (syn_chwcards (syn_cvv)))) := by
  let proofSupport : Finset Var := A.fv
  let s : Var := freshVar proofSupport 0
  let t : Var := freshVar proofSupport 1
  let d : Var := freshVar proofSupport 2
  let k : Var := freshVar proofSupport 3
  have fresh_s : s ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_s_not_A : s ∉ A.fv := by
    intro h
    exact fresh_s (h)
  have fresh_t : t ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (h)
  have fresh_d : d ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (h)
  have fresh_k : k ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_k_not_A : k ∉ A.fv := by
    intro h
    exact fresh_k (h)
  have fresh_s_ne_t : s ≠ t := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_t_ne_s : t ≠ s :=
    Ne.symm fresh_s_ne_t
  have fresh_s_ne_d : s ≠ d := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_d_ne_s : d ≠ s :=
    Ne.symm fresh_s_ne_d
  have fresh_s_ne_k : s ≠ k := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_k_ne_s : k ≠ s :=
    Ne.symm fresh_s_ne_k
  have fresh_t_ne_d : t ≠ d := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_d_ne_t : d ≠ t :=
    Ne.symm fresh_t_ne_d
  have fresh_t_ne_k : t ≠ k := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_k_ne_t : k ≠ t :=
    Ne.symm fresh_t_ne_k
  have fresh_d_ne_k : d ≠ k := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_k_ne_d : k ≠ d :=
    Ne.symm fresh_d_ne_k
  have dv_cache_0001 : s ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : d ∉ ((syn_chnord A)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : t ∉ ((syn_chnord A)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : d ∉ ((Class.cv s)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_s, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : t ∉ ((Class.cv s)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_s, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : d ∉ ((syn_wa (syn_wbr (.cv s) (syn_cwe) (syn_chnord A)) (.classEq (syn_chncard A) (syn_cnc (syn_chnord A))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_s, fresh_d_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : t ∉ ((syn_wa (syn_wbr (.cv s) (syn_cwe) (syn_chnord A)) (.classEq (syn_chncard A) (syn_cnc (syn_chnord A))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_s, fresh_t_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : d ≠ t := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show d ≠ t from (by exact fresh_d_ne_t))
  have dv_cache_0009 : s ∉ ((syn_wex d (syn_wex t (syn_wa (syn_wbr (.cv t) (syn_cwe) (.cv d)) (.classEq (syn_chncard A) (syn_cnc (.cv d))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_ne_t, fresh_s_ne_d, fresh_s_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : t ∉ ((Wff.classEq (.cv k) (syn_chncard A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_t_ne_k, fresh_t_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : d ∉ ((Wff.classEq (.cv k) (syn_chncard A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_k, fresh_d_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : d ≠ k := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show d ≠ k from (by exact fresh_d_ne_k))
  have dv_cache_0013 : k ≠ t := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show k ≠ t from (by exact fresh_k_ne_t))
  have dv_cache_0014 : k ∉ ((syn_chncard A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : k ∉ ((syn_wb (.classMem (syn_chncard A) (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex t (syn_wa (syn_wbr (.cv t) (syn_cwe) (.cv d)) (.classEq (syn_chncard A) (syn_cnc (.cv d)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_A, fresh_k_ne_t, fresh_k_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_hnordwendv A s dv_cache_0001
  have p0001 :=
    @g_id (syn_wbr (.cv s) (syn_cwe) (syn_chnord A))
  have p0002 :=
    (by simpa [syn_chncard] using (Nominal.classEqRefl (syn_chncard A)))
  have p0003 :=
    @g_a1i (.classEq (syn_chncard A) (syn_cnc (syn_chnord A))) (syn_wbr (.cv s) (syn_cwe) (syn_chnord A)) p0002
  have p0004 :=
    @g_jca (syn_wbr (.cv s) (syn_cwe) (syn_chnord A)) (syn_wbr (.cv s) (syn_cwe) (syn_chnord A)) (.classEq (syn_chncard A) (syn_cnc (syn_chnord A))) p0001 p0003
  have p0005 :=
    @g_brex (.cv s) (syn_chnord A) (syn_cwe)
  have p0006 :=
    @g_ancom (.classMem (syn_chnord A) (syn_cvv)) (.classMem (.cv s) (syn_cvv))
  have p0007 :=
    @g_sylibr (syn_wbr (.cv s) (syn_cwe) (syn_chnord A)) (syn_wa (.classMem (.cv s) (syn_cvv)) (.classMem (syn_chnord A) (syn_cvv))) (syn_wa (.classMem (syn_chnord A) (syn_cvv)) (.classMem (.cv s) (syn_cvv))) p0005 p0006
  have p0008 :=
    @g_simpr (.classEq (.cv d) (syn_chnord A)) (.classEq (.cv t) (.cv s))
  have p0009 :=
    @g_simpl (.classEq (.cv d) (syn_chnord A)) (.classEq (.cv t) (.cv s))
  have p0010 :=
    @g_breq12d (syn_wa (.classEq (.cv d) (syn_chnord A)) (.classEq (.cv t) (.cv s))) (.cv t) (.cv s) (.cv d) (syn_chnord A) (syn_cwe) p0008 p0009
  have p0011 :=
    @g_simpl (.classEq (.cv d) (syn_chnord A)) (.classEq (.cv t) (.cv s))
  have p0012 :=
    @g_nceqd (syn_wa (.classEq (.cv d) (syn_chnord A)) (.classEq (.cv t) (.cv s))) (.cv d) (syn_chnord A) p0011
  have p0013 :=
    @g_eqeq2d (syn_wa (.classEq (.cv d) (syn_chnord A)) (.classEq (.cv t) (.cv s))) (syn_cnc (.cv d)) (syn_cnc (syn_chnord A)) (syn_chncard A) p0012
  have p0014 :=
    @g_anbi12d (syn_wa (.classEq (.cv d) (syn_chnord A)) (.classEq (.cv t) (.cv s))) (syn_wbr (.cv t) (syn_cwe) (.cv d)) (syn_wbr (.cv s) (syn_cwe) (syn_chnord A)) (.classEq (syn_chncard A) (syn_cnc (.cv d))) (.classEq (syn_chncard A) (syn_cnc (syn_chnord A))) p0010 p0013
  have p0015 :=
    @g_spc2egv (syn_wa (syn_wbr (.cv t) (syn_cwe) (.cv d)) (.classEq (syn_chncard A) (syn_cnc (.cv d)))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (syn_chnord A)) (.classEq (syn_chncard A) (syn_cnc (syn_chnord A)))) d t (syn_chnord A) (.cv s) (syn_cvv) (syn_cvv) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 p0014
  have p0016 :=
    @g_syl (syn_wbr (.cv s) (syn_cwe) (syn_chnord A)) (syn_wa (.classMem (syn_chnord A) (syn_cvv)) (.classMem (.cv s) (syn_cvv))) (.imp (syn_wa (syn_wbr (.cv s) (syn_cwe) (syn_chnord A)) (.classEq (syn_chncard A) (syn_cnc (syn_chnord A)))) (syn_wex d (syn_wex t (syn_wa (syn_wbr (.cv t) (syn_cwe) (.cv d)) (.classEq (syn_chncard A) (syn_cnc (.cv d))))))) p0007 p0015
  have p0017 :=
    @g_mpd (syn_wbr (.cv s) (syn_cwe) (syn_chnord A)) (syn_wa (syn_wbr (.cv s) (syn_cwe) (syn_chnord A)) (.classEq (syn_chncard A) (syn_cnc (syn_chnord A)))) (syn_wex d (syn_wex t (syn_wa (syn_wbr (.cv t) (syn_cwe) (.cv d)) (.classEq (syn_chncard A) (syn_cnc (.cv d)))))) p0004 p0016
  have p0018 :=
    @g_exlimiv (syn_wbr (.cv s) (syn_cwe) (syn_chnord A)) (syn_wex d (syn_wex t (syn_wa (syn_wbr (.cv t) (syn_cwe) (.cv d)) (.classEq (syn_chncard A) (syn_cnc (.cv d)))))) s dv_cache_0009 p0017
  have p0019 :=
    @g_hncardex A
  have p0020 :=
    @g_id (.classEq (.cv k) (syn_chncard A))
  have p0021 :=
    @g_eleq1d (.classEq (.cv k) (syn_chncard A)) (.cv k) (syn_chncard A) (syn_chwcards (syn_cvv)) p0020
  have p0022 :=
    @g_id (.classEq (.cv k) (syn_chncard A))
  have p0023 :=
    @g_eqeq1d (.classEq (.cv k) (syn_chncard A)) (.cv k) (syn_chncard A) (syn_cnc (.cv d)) p0022
  have p0024 :=
    @g_anbi2d (.classEq (.cv k) (syn_chncard A)) (.classEq (.cv k) (syn_cnc (.cv d))) (.classEq (syn_chncard A) (syn_cnc (.cv d))) (syn_wbr (.cv t) (syn_cwe) (.cv d)) p0023
  have p0025 :=
    @g_exbidv (.classEq (.cv k) (syn_chncard A)) (syn_wa (syn_wbr (.cv t) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d)))) (syn_wa (syn_wbr (.cv t) (syn_cwe) (.cv d)) (.classEq (syn_chncard A) (syn_cnc (.cv d)))) t dv_cache_0010 p0024
  have p0026 :=
    @g_exbidv (.classEq (.cv k) (syn_chncard A)) (syn_wex t (syn_wa (syn_wbr (.cv t) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d))))) (syn_wex t (syn_wa (syn_wbr (.cv t) (syn_cwe) (.cv d)) (.classEq (syn_chncard A) (syn_cnc (.cv d))))) d dv_cache_0011 p0025
  have p0027 :=
    @g_bibi12d (.classEq (.cv k) (syn_chncard A)) (.classMem (.cv k) (syn_chwcards (syn_cvv))) (.classMem (syn_chncard A) (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex t (syn_wa (syn_wbr (.cv t) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d)))))) (syn_wex d (syn_wex t (syn_wa (syn_wbr (.cv t) (syn_cwe) (.cv d)) (.classEq (syn_chncard A) (syn_cnc (.cv d)))))) p0021 p0026
  have p0028 :=
    @g_elhwcardswev k t d dv_cache_0012 dv_cache_0008 dv_cache_0013
  have p0029 :=
    @g_vtoclg (syn_wb (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex t (syn_wa (syn_wbr (.cv t) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d))))))) (syn_wb (.classMem (syn_chncard A) (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex t (syn_wa (syn_wbr (.cv t) (syn_cwe) (.cv d)) (.classEq (syn_chncard A) (syn_cnc (.cv d))))))) k (syn_chncard A) (syn_cvv) dv_cache_0014 dv_cache_0015 p0027 p0028
  have p0030 :=
    Nominal.mp p0019 p0029
  have p0031 :=
    @g_biimpri (.classMem (syn_chncard A) (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex t (syn_wa (syn_wbr (.cv t) (syn_cwe) (.cv d)) (.classEq (syn_chncard A) (syn_cnc (.cv d)))))) p0030
  have p0032 :=
    @g_syl (syn_wex s (syn_wbr (.cv s) (syn_cwe) (syn_chnord A))) (syn_wex d (syn_wex t (syn_wa (syn_wbr (.cv t) (syn_cwe) (.cv d)) (.classEq (syn_chncard A) (syn_cnc (.cv d)))))) (.classMem (syn_chncard A) (syn_chwcards (syn_cvv))) p0018 p0031
  have p0033 :=
    @g_syl (.classMem A (syn_cvv)) (syn_wex s (syn_wbr (.cv s) (syn_cwe) (syn_chnord A))) (.classMem (syn_chncard A) (syn_chwcards (syn_cvv))) p0000 p0032
  exact p0033

noncomputable def g_wppconcrete6canonicaltchomndv
    (X : Class) (hyp_wppconcrete6canonicaltchomndv_1 : Nominal.NPrf (.classMem X (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_ctc (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X))))))))) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X)))))))))) := by
  let proofSupport : Finset Var := X.fv
  have p0000 :=
    @g_wppconcrete6fnvalndv X hyp_wppconcrete6canonicaltchomndv_1
  have p0001 :=
    @g_tceq (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X)))))))) (syn_chncard (syn_chnord (syn_cpw (syn_cpw X))))
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_pwex X hyp_wppconcrete6canonicaltchomndv_1
  have p0004 :=
    @g_pwex (syn_cpw X) p0003
  have p0005 :=
    @g_hnordexg (syn_cpw (syn_cpw X))
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_hncardtcshiftndv (syn_chnord (syn_cpw (syn_cpw X))) p0006
  have p0008 :=
    @g_eqtri (syn_ctc (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X))))))))) (syn_ctc (syn_chncard (syn_chnord (syn_cpw (syn_cpw X))))) (syn_chncard (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw X))))) p0002 p0007
  have p0009 :=
    @g_pwex X hyp_wppconcrete6canonicaltchomndv_1
  have p0010 :=
    @g_pwex (syn_cpw X) p0009
  have p0011 :=
    @g_hnordexg (syn_cpw (syn_cpw X))
  have p0012 :=
    Nominal.mp p0010 p0011
  have p0013 :=
    @g_pw1ex (syn_chnord (syn_cpw (syn_cpw X))) p0012
  have p0014 :=
    @g_pw1ex X hyp_wppconcrete6canonicaltchomndv_1
  have p0015 :=
    @g_pwex (syn_cpw1 X) p0014
  have p0016 :=
    @g_pwex (syn_cpw (syn_cpw1 X)) p0015
  have p0017 :=
    @g_hnordexg (syn_cpw (syn_cpw (syn_cpw1 X)))
  have p0018 :=
    Nominal.mp p0016 p0017
  have p0019 :=
    @g_pwex X hyp_wppconcrete6canonicaltchomndv_1
  have p0020 :=
    @g_pwex (syn_cpw X) p0019
  have p0021 :=
    @g_hnordpw1shiftenndv (syn_cpw (syn_cpw X)) p0020
  have p0022 :=
    @g_pwex X hyp_wppconcrete6canonicaltchomndv_1
  have p0023 :=
    @g_pwex (syn_cpw X) p0022
  have p0024 :=
    @g_hnordexg (syn_cpw (syn_cpw X))
  have p0025 :=
    Nominal.mp p0023 p0024
  have p0026 :=
    @g_pw1ex (syn_chnord (syn_cpw (syn_cpw X))) p0025
  have p0027 :=
    @g_eqnc (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw X)))) (syn_chnord (syn_cpw1 (syn_cpw (syn_cpw X)))) p0026
  have p0028 :=
    @g_mpbir (.classEq (syn_cnc (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw X))))) (syn_cnc (syn_chnord (syn_cpw1 (syn_cpw (syn_cpw X)))))) (syn_wbr (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw X)))) (syn_cen) (syn_chnord (syn_cpw1 (syn_cpw (syn_cpw X))))) p0021 p0027
  have p0029 :=
    (by simpa [syn_chncard] using (Nominal.classEqRefl (syn_chncard (syn_cpw1 (syn_cpw (syn_cpw X))))))
  have p0030 :=
    @g_eqcomi (syn_chncard (syn_cpw1 (syn_cpw (syn_cpw X)))) (syn_cnc (syn_chnord (syn_cpw1 (syn_cpw (syn_cpw X))))) p0029
  have p0031 :=
    @g_pwex X hyp_wppconcrete6canonicaltchomndv_1
  have p0032 :=
    @g_pwex (syn_cpw X) p0031
  have p0033 :=
    @g_pw1ex (syn_cpw (syn_cpw X)) p0032
  have p0034 :=
    @g_pw1ex X hyp_wppconcrete6canonicaltchomndv_1
  have p0035 :=
    @g_pwex (syn_cpw1 X) p0034
  have p0036 :=
    @g_pwex (syn_cpw (syn_cpw1 X)) p0035
  have p0037 :=
    @g_ncpw1pw2 X hyp_wppconcrete6canonicaltchomndv_1
  have p0038 :=
    @g_hncardnceqndv (syn_cpw1 (syn_cpw (syn_cpw X))) (syn_cpw (syn_cpw (syn_cpw1 X))) p0033 p0036 p0037
  have p0039 :=
    (by simpa [syn_chncard] using (Nominal.classEqRefl (syn_chncard (syn_cpw (syn_cpw (syn_cpw1 X))))))
  have p0040 :=
    @g_eqtri (syn_chncard (syn_cpw1 (syn_cpw (syn_cpw X)))) (syn_chncard (syn_cpw (syn_cpw (syn_cpw1 X)))) (syn_cnc (syn_chnord (syn_cpw (syn_cpw (syn_cpw1 X))))) p0038 p0039
  have p0041 :=
    @g_eqtri (syn_cnc (syn_chnord (syn_cpw1 (syn_cpw (syn_cpw X))))) (syn_chncard (syn_cpw1 (syn_cpw (syn_cpw X)))) (syn_cnc (syn_chnord (syn_cpw (syn_cpw (syn_cpw1 X))))) p0030 p0040
  have p0042 :=
    @g_eqtri (syn_cnc (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw X))))) (syn_cnc (syn_chnord (syn_cpw1 (syn_cpw (syn_cpw X))))) (syn_cnc (syn_chnord (syn_cpw (syn_cpw (syn_cpw1 X))))) p0028 p0041
  have p0043 :=
    @g_hncardnceqndv (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw X)))) (syn_chnord (syn_cpw (syn_cpw (syn_cpw1 X)))) p0013 p0018 p0042
  have p0044 :=
    @g_eqtri (syn_ctc (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X))))))))) (syn_chncard (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw X))))) (syn_chncard (syn_chnord (syn_cpw (syn_cpw (syn_cpw1 X))))) p0008 p0043
  have p0045 :=
    @g_tcnc X hyp_wppconcrete6canonicaltchomndv_1
  have p0046 :=
    @g_eqcomi (syn_ctc (syn_cnc X)) (syn_cnc (syn_cpw1 X)) p0045
  have p0047 :=
    @g_tceq (syn_cnc (syn_cpw1 X)) (syn_ctc (syn_cnc X))
  have p0048 :=
    Nominal.mp p0046 p0047
  have p0049 :=
    @g_tceq (syn_ctc (syn_cnc (syn_cpw1 X))) (syn_ctc (syn_ctc (syn_cnc X)))
  have p0050 :=
    Nominal.mp p0048 p0049
  have p0051 :=
    @g_tceq (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 X)))) (syn_ctc (syn_ctc (syn_ctc (syn_cnc X))))
  have p0052 :=
    Nominal.mp p0050 p0051
  have p0053 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 X))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X)))))
  have p0054 :=
    Nominal.mp p0052 p0053
  have p0055 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 X)))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X))))))
  have p0056 :=
    Nominal.mp p0054 p0055
  have p0057 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 X))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X)))))))
  have p0058 :=
    Nominal.mp p0056 p0057
  have p0059 :=
    @g_fveq2i (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 X)))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X)))))))) (syn_cwppconcrete6fn) p0058
  have p0060 :=
    @g_eqcomi (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 X))))))))) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X))))))))) p0059
  have p0061 :=
    @g_pw1ex X hyp_wppconcrete6canonicaltchomndv_1
  have p0062 :=
    @g_wppconcrete6fnvalndv (syn_cpw1 X) p0061
  have p0063 :=
    @g_eqtri (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X))))))))) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 X))))))))) (syn_chncard (syn_chnord (syn_cpw (syn_cpw (syn_cpw1 X))))) p0060 p0062
  have p0064 :=
    @g_eqcomi (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X))))))))) (syn_chncard (syn_chnord (syn_cpw (syn_cpw (syn_cpw1 X))))) p0063
  have p0065 :=
    @g_eqtri (syn_ctc (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X))))))))) (syn_chncard (syn_chnord (syn_cpw (syn_cpw (syn_cpw1 X))))) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X))))))))) p0044 p0064
  exact p0065

noncomputable def g_hncardtc6oneeqndv
     :
    Nominal.NPrf (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_n_1cex
  have p0001 :=
    @g_hncardtcshiftndv (syn_c1c) p0000
  have p0002 :=
    @g_tceq (syn_ctc (syn_chncard (syn_c1c))) (syn_chncard (syn_cpw1 (syn_c1c)))
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    @g_n_1cex
  have p0005 :=
    @g_pw1ex (syn_c1c) p0004
  have p0006 :=
    @g_hncardtcshiftndv (syn_cpw1 (syn_c1c)) p0005
  have p0007 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))) (syn_ctc (syn_chncard (syn_cpw1 (syn_c1c)))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0003 p0006
  have p0008 :=
    @g_tceq (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_c1c))))
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_n_1cex
  have p0011 :=
    @g_pw1ex (syn_c1c) p0010
  have p0012 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0011
  have p0013 :=
    @g_hncardtcshiftndv (syn_cpw1 (syn_cpw1 (syn_c1c))) p0012
  have p0014 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0009 p0013
  have p0015 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
  have p0016 :=
    Nominal.mp p0014 p0015
  have p0017 :=
    @g_n_1cex
  have p0018 :=
    @g_pw1ex (syn_c1c) p0017
  have p0019 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0018
  have p0020 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0019
  have p0021 :=
    @g_hncardtcshiftndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0020
  have p0022 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0016 p0021
  have p0023 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
  have p0024 :=
    Nominal.mp p0022 p0023
  have p0025 :=
    @g_n_1cex
  have p0026 :=
    @g_pw1ex (syn_c1c) p0025
  have p0027 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0026
  have p0028 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0027
  have p0029 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0028
  have p0030 :=
    @g_hncardtcshiftndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0029
  have p0031 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) p0024 p0030
  have p0032 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
  have p0033 :=
    Nominal.mp p0031 p0032
  have p0034 :=
    @g_n_1cex
  have p0035 :=
    @g_pw1ex (syn_c1c) p0034
  have p0036 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0035
  have p0037 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0036
  have p0038 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0037
  have p0039 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0038
  have p0040 :=
    @g_hncardtcshiftndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0039
  have p0041 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) p0033 p0040
  exact p0041

noncomputable def g_hncardtc7oneeqndv
     :
    Nominal.NPrf (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_n_1cex
  have p0001 :=
    @g_hncardtcshiftndv (syn_c1c) p0000
  have p0002 :=
    @g_tceq (syn_ctc (syn_chncard (syn_c1c))) (syn_chncard (syn_cpw1 (syn_c1c)))
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    @g_n_1cex
  have p0005 :=
    @g_pw1ex (syn_c1c) p0004
  have p0006 :=
    @g_hncardtcshiftndv (syn_cpw1 (syn_c1c)) p0005
  have p0007 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))) (syn_ctc (syn_chncard (syn_cpw1 (syn_c1c)))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0003 p0006
  have p0008 :=
    @g_tceq (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_c1c))))
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_n_1cex
  have p0011 :=
    @g_pw1ex (syn_c1c) p0010
  have p0012 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0011
  have p0013 :=
    @g_hncardtcshiftndv (syn_cpw1 (syn_cpw1 (syn_c1c))) p0012
  have p0014 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0009 p0013
  have p0015 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
  have p0016 :=
    Nominal.mp p0014 p0015
  have p0017 :=
    @g_n_1cex
  have p0018 :=
    @g_pw1ex (syn_c1c) p0017
  have p0019 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0018
  have p0020 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0019
  have p0021 :=
    @g_hncardtcshiftndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0020
  have p0022 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0016 p0021
  have p0023 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
  have p0024 :=
    Nominal.mp p0022 p0023
  have p0025 :=
    @g_n_1cex
  have p0026 :=
    @g_pw1ex (syn_c1c) p0025
  have p0027 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0026
  have p0028 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0027
  have p0029 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0028
  have p0030 :=
    @g_hncardtcshiftndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0029
  have p0031 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) p0024 p0030
  have p0032 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
  have p0033 :=
    Nominal.mp p0031 p0032
  have p0034 :=
    @g_n_1cex
  have p0035 :=
    @g_pw1ex (syn_c1c) p0034
  have p0036 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0035
  have p0037 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0036
  have p0038 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0037
  have p0039 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0038
  have p0040 :=
    @g_hncardtcshiftndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0039
  have p0041 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) p0033 p0040
  have p0042 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
  have p0043 :=
    Nominal.mp p0041 p0042
  have p0044 :=
    @g_n_1cex
  have p0045 :=
    @g_pw1ex (syn_c1c) p0044
  have p0046 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0045
  have p0047 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0046
  have p0048 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0047
  have p0049 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0048
  have p0050 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0049
  have p0051 :=
    @g_hncardtcshiftndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) p0050
  have p0052 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) p0043 p0051
  exact p0052

noncomputable def g_wppconcrete6thresholdtclecndv
     :
    Nominal.NPrf (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_pw1ss1c (syn_c1c)
  have p0001 :=
    @g_pw1ss (syn_cpw1 (syn_c1c)) (syn_c1c)
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_pw1ss (syn_cpw1 (syn_cpw1 (syn_c1c))) (syn_cpw1 (syn_c1c))
  have p0004 :=
    Nominal.mp p0002 p0003
  have p0005 :=
    @g_pw1ss (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_pw1ss (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_pw1ss (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
  have p0010 :=
    Nominal.mp p0008 p0009
  have p0011 :=
    @g_pw1ss (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
  have p0012 :=
    Nominal.mp p0010 p0011
  have p0013 :=
    @g_n_1cex
  have p0014 :=
    @g_pw1ex (syn_c1c) p0013
  have p0015 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0014
  have p0016 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0015
  have p0017 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0016
  have p0018 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0017
  have p0019 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0018
  have p0020 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) p0019
  have p0021 :=
    @g_n_1cex
  have p0022 :=
    @g_pw1ex (syn_c1c) p0021
  have p0023 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0022
  have p0024 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0023
  have p0025 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0024
  have p0026 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0025
  have p0027 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0026
  have p0028 :=
    @g_hncardmono (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) p0012 p0020 p0027
  have p0029 :=
    @g_hncardtc7oneeqndv
  have p0030 :=
    @g_hncardtc6oneeqndv
  have p0031 :=
    @g_breq12i (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_clec) p0029 p0030
  have p0032 :=
    @g_mpbir (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wbr (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_clec) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) p0028 p0031
  exact p0032

noncomputable def g_hnwpw1argclcndv
    (C : Class) (D : Class) :
    Nominal.NPrf (.imp (.classMem C (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni C) D) (.classEq C (syn_csn (syn_cuni C))))) := by
  let proofSupport : Finset Var := C.fv ∪ D.fv
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_C : q ∉ C.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (h))
  have fresh_q_not_D : q ∉ D.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have dv_cache_0001 : q ∉ (C).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ ((syn_cpw1 D)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((syn_wa (.classMem (syn_cuni C) D) (.classEq C (syn_csn (syn_cuni C))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_C, fresh_q_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_unieq (.cv q) C
  have p0001 :=
    @g_eleq1d (.classEq (.cv q) C) (syn_cuni (.cv q)) (syn_cuni C) D p0000
  have p0002 :=
    @g_id (.classEq (.cv q) C)
  have p0003 :=
    @g_unieq (.cv q) C
  have p0004 :=
    @g_sneqd (.classEq (.cv q) C) (syn_cuni (.cv q)) (syn_cuni C) p0003
  have p0005 :=
    @g_eqeq12d (.classEq (.cv q) C) (.cv q) C (syn_csn (syn_cuni (.cv q))) (syn_csn (syn_cuni C)) p0002 p0004
  have p0006 :=
    @g_anbi12d (.classEq (.cv q) C) (.classMem (syn_cuni (.cv q)) D) (.classMem (syn_cuni C) D) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) (.classEq C (syn_csn (syn_cuni C))) p0001 p0005
  have p0007 :=
    @g_hnwpw1argcl D q
  have p0008 :=
    @g_vtoclga (syn_wa (.classMem (syn_cuni (.cv q)) D) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) (syn_wa (.classMem (syn_cuni C) D) (.classEq C (syn_csn (syn_cuni C)))) q C (syn_cpw1 D) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0006 p0007
  exact p0008

noncomputable def g_wppsifnndv
    (A : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfn F A) (syn_wfn (syn_csi F) (syn_cpw1 A))) := by
  let proofSupport : Finset Var := A.fv ∪ F.fv
  have p0000 :=
    @g_fnfun A F
  have p0001 :=
    @g_funsi F
  have p0002 :=
    @g_syl (syn_wfn F A) (syn_wfun F) (syn_wfun (syn_csi F)) p0000 p0001
  have p0003 :=
    @g_dmsi F
  have p0004 :=
    @g_a1i (.classEq (syn_cdm (syn_csi F)) (syn_cpw1 (syn_cdm F))) (syn_wfn F A) p0003
  have p0005 :=
    @g_fndm A F
  have p0006 :=
    @g_pw1eq (syn_cdm F) A
  have p0007 :=
    @g_syl (syn_wfn F A) (.classEq (syn_cdm F) A) (.classEq (syn_cpw1 (syn_cdm F)) (syn_cpw1 A)) p0005 p0006
  have p0008 :=
    @g_eqtrd (syn_wfn F A) (syn_cdm (syn_csi F)) (syn_cpw1 (syn_cdm F)) (syn_cpw1 A) p0004 p0007
  have p0009 :=
    @g_jca (syn_wfn F A) (syn_wfun (syn_csi F)) (.classEq (syn_cdm (syn_csi F)) (syn_cpw1 A)) p0002 p0008
  have p0010 :=
    (by simpa [syn_wb, syn_wfn] using (Nominal.biimpRefl (syn_wfn (syn_csi F) (syn_cpw1 A))))
  have p0011 :=
    @g_sylibr (syn_wfn F A) (syn_wa (syn_wfun (syn_csi F)) (.classEq (syn_cdm (syn_csi F)) (syn_cpw1 A))) (syn_wfn (syn_csi F) (syn_cpw1 A)) p0009 p0010
  exact p0011

noncomputable def g_wpptxpfnvalndv
    (x : Var) (A : Class) (F : Class) (G : Class) (dv_A_x : x ∉ A.fv) (dv_F_x : x ∉ F.fv) (dv_G_x : x ∉ G.fv) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A)) (.classEq (syn_cfv (syn_ctxp F G) (.cv x)) (syn_cop (syn_cfv F (.cv x)) (syn_cfv G (.cv x))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ F.fv ∪ G.fv
  have p0000 :=
    @g_eqid (syn_cfv F (.cv x))
  have p0001 :=
    @g_a1i (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv x))) (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A)) p0000
  have p0002 :=
    @g_simpl (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A)
  have p0003 :=
    @g_simpl (syn_wfn F A) (syn_wfn G A)
  have p0004 :=
    @g_syl (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A)) (syn_wa (syn_wfn F A) (syn_wfn G A)) (syn_wfn F A) p0002 p0003
  have p0005 :=
    @g_simpr (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A)
  have p0006 :=
    @g_jca (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A)) (syn_wfn F A) (.classMem (.cv x) A) p0004 p0005
  have p0007 :=
    @g_fnbrfvb A (.cv x) (syn_cfv F (.cv x)) F
  have p0008 :=
    @g_syl (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A)) (syn_wa (syn_wfn F A) (.classMem (.cv x) A)) (syn_wb (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv x))) (syn_wbr (.cv x) F (syn_cfv F (.cv x)))) p0006 p0007
  have p0009 :=
    @g_mpbid (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A)) (.classEq (syn_cfv F (.cv x)) (syn_cfv F (.cv x))) (syn_wbr (.cv x) F (syn_cfv F (.cv x))) p0001 p0008
  have p0010 :=
    @g_eqid (syn_cfv G (.cv x))
  have p0011 :=
    @g_a1i (.classEq (syn_cfv G (.cv x)) (syn_cfv G (.cv x))) (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A)) p0010
  have p0012 :=
    @g_simpl (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A)
  have p0013 :=
    @g_simpr (syn_wfn F A) (syn_wfn G A)
  have p0014 :=
    @g_syl (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A)) (syn_wa (syn_wfn F A) (syn_wfn G A)) (syn_wfn G A) p0012 p0013
  have p0015 :=
    @g_simpr (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A)
  have p0016 :=
    @g_jca (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A)) (syn_wfn G A) (.classMem (.cv x) A) p0014 p0015
  have p0017 :=
    @g_fnbrfvb A (.cv x) (syn_cfv G (.cv x)) G
  have p0018 :=
    @g_syl (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A)) (syn_wa (syn_wfn G A) (.classMem (.cv x) A)) (syn_wb (.classEq (syn_cfv G (.cv x)) (syn_cfv G (.cv x))) (syn_wbr (.cv x) G (syn_cfv G (.cv x)))) p0016 p0017
  have p0019 :=
    @g_mpbid (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A)) (.classEq (syn_cfv G (.cv x)) (syn_cfv G (.cv x))) (syn_wbr (.cv x) G (syn_cfv G (.cv x))) p0011 p0018
  have p0020 :=
    @g_jca (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A)) (syn_wbr (.cv x) F (syn_cfv F (.cv x))) (syn_wbr (.cv x) G (syn_cfv G (.cv x))) p0009 p0019
  have p0021 :=
    @g_trtxp (.cv x) (syn_cfv F (.cv x)) (syn_cfv G (.cv x)) F G
  have p0022 :=
    @g_sylibr (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A)) (syn_wa (syn_wbr (.cv x) F (syn_cfv F (.cv x))) (syn_wbr (.cv x) G (syn_cfv G (.cv x)))) (syn_wbr (.cv x) (syn_ctxp F G) (syn_cop (syn_cfv F (.cv x)) (syn_cfv G (.cv x)))) p0020 p0021
  have p0023 :=
    @g_simpl (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A)
  have p0024 :=
    @g_fntxp A A F G
  have p0025 :=
    @g_syl (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A)) (syn_wa (syn_wfn F A) (syn_wfn G A)) (syn_wfn (syn_ctxp F G) (syn_cin A A)) p0023 p0024
  have p0026 :=
    @g_inidm A
  have p0027 :=
    @g_fneq2i (syn_cin A A) A (syn_ctxp F G) p0026
  have p0028 :=
    @g_sylib (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A)) (syn_wfn (syn_ctxp F G) (syn_cin A A)) (syn_wfn (syn_ctxp F G) A) p0025 p0027
  have p0029 :=
    @g_simpr (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A)
  have p0030 :=
    @g_jca (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A)) (syn_wfn (syn_ctxp F G) A) (.classMem (.cv x) A) p0028 p0029
  have p0031 :=
    @g_fnbrfvb A (.cv x) (syn_cop (syn_cfv F (.cv x)) (syn_cfv G (.cv x))) (syn_ctxp F G)
  have p0032 :=
    @g_syl (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A)) (syn_wa (syn_wfn (syn_ctxp F G) A) (.classMem (.cv x) A)) (syn_wb (.classEq (syn_cfv (syn_ctxp F G) (.cv x)) (syn_cop (syn_cfv F (.cv x)) (syn_cfv G (.cv x)))) (syn_wbr (.cv x) (syn_ctxp F G) (syn_cop (syn_cfv F (.cv x)) (syn_cfv G (.cv x))))) p0030 p0031
  have p0033 :=
    @g_mpbird (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A)) (.classEq (syn_cfv (syn_ctxp F G) (.cv x)) (syn_cop (syn_cfv F (.cv x)) (syn_cfv G (.cv x)))) (syn_wbr (.cv x) (syn_ctxp F G) (syn_cop (syn_cfv F (.cv x)) (syn_cfv G (.cv x)))) p0022 p0032
  exact p0033

#print axioms g_wpptxpfnvalndv

end NFChoice.DirectNominalPrf.WPPReplay
