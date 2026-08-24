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
import NominalWPPReplayChunk014Compact001Part052

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

noncomputable def g_hnwcutmapf1
    (D : Class) (R : Class) (dv_D_R : Disjoint D.fv R.fv) (hyp_hnwcutmapf1_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (syn_wf1 (syn_chnwcutmap R D) (syn_cpw1 (syn_cpw1 D)) (syn_chnord D)) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  let q : Var := freshVar proofSupport 0
  let r : Var := freshVar proofSupport 1
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_D : q ∉ D.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (h))
  have fresh_q_not_R : q ∉ R.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_r_not_D : r ∉ D.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (h))
  have fresh_r_not_R : r ∉ R.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_q_ne_r : q ≠ r := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_r_ne_q : r ≠ q :=
    Ne.symm fresh_q_ne_r
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0002 : r ∉ ((syn_cpw1 (syn_cpw1 D))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((syn_wbr R (syn_cwe) D)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_R, fresh_q_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : r ∉ ((syn_wbr R (syn_cwe) D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_R, fresh_r_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : q ≠ r := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show q ≠ r from (by exact fresh_q_ne_r))
  have dv_cache_0006 : q ∉ ((syn_cpw1 (syn_cpw1 D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : q ∉ ((syn_chnwcutmap R D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutmap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_D, fresh_q_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : r ∉ ((syn_chnwcutmap R D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutmap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_D, fresh_r_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_hnwcutmapf D R dv_cache_0001 hyp_hnwcutmapf1_1
  have p0001 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cfv (syn_chnwcutmap R D) (.cv r)))
  have p0002 :=
    @g_simpr (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))
  have p0003 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))
  have p0004 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) p0002 p0003
  have p0005 :=
    @g_pw12argcl (.cv q) D
  have p0006 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) D) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))))) p0004 p0005
  have p0007 :=
    @g_simprd (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classMem (syn_cuni (syn_cuni (.cv q))) D) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0006
  have p0008 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cfv (syn_chnwcutmap R D) (.cv r)))) (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0001 p0007
  have p0009 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cfv (syn_chnwcutmap R D) (.cv r)))
  have p0010 :=
    @g_simpr (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))
  have p0011 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))
  have p0012 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) p0010 p0011
  have p0013 :=
    @g_hnwcutmapval D R q dv_cache_0001 hyp_hnwcutmapf1_1
  have p0014 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D))) p0012 p0013
  have p0015 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cfv (syn_chnwcutmap R D) (.cv r)))) (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D))) p0009 p0014
  have p0016 :=
    @g_eqcomd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cfv (syn_chnwcutmap R D) (.cv r)))) (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D)) p0015
  have p0017 :=
    @g_simpr (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cfv (syn_chnwcutmap R D) (.cv r)))
  have p0018 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cfv (syn_chnwcutmap R D) (.cv r)))) (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D)) (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cfv (syn_chnwcutmap R D) (.cv r)) p0016 p0017
  have p0019 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cfv (syn_chnwcutmap R D) (.cv r)))
  have p0020 :=
    @g_simpr (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))
  have p0021 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))
  have p0022 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))) p0020 p0021
  have p0023 :=
    @g_hnwcutmapval D R r dv_cache_0001 hyp_hnwcutmapf1_1
  have p0024 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))) (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv r)) (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv r)))) (syn_chwniso D))) p0022 p0023
  have p0025 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cfv (syn_chnwcutmap R D) (.cv r)))) (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv r)) (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv r)))) (syn_chwniso D))) p0019 p0024
  have p0026 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cfv (syn_chnwcutmap R D) (.cv r)))) (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D)) (syn_cfv (syn_chnwcutmap R D) (.cv r)) (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv r)))) (syn_chwniso D)) p0018 p0025
  have p0027 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cfv (syn_chnwcutmap R D) (.cv r)))
  have p0028 :=
    @g_simpr (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))
  have p0029 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))
  have p0030 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) p0028 p0029
  have p0031 :=
    @g_pw12argcl (.cv q) D
  have p0032 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) D) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))))) p0030 p0031
  have p0033 :=
    @g_simpld (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classMem (syn_cuni (syn_cuni (.cv q))) D) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0032
  have p0034 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cfv (syn_chnwcutmap R D) (.cv r)))) (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classMem (syn_cuni (syn_cuni (.cv q))) D) p0027 p0033
  have p0035 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cfv (syn_chnwcutmap R D) (.cv r)))
  have p0036 :=
    @g_simpr (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))
  have p0037 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))
  have p0038 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))) p0036 p0037
  have p0039 :=
    @g_pw12argcl (.cv r) D
  have p0040 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv r))) D) (.classEq (.cv r) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r))))))) p0038 p0039
  have p0041 :=
    @g_simpld (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classMem (syn_cuni (syn_cuni (.cv r))) D) (.classEq (.cv r) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r)))))) p0040
  have p0042 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cfv (syn_chnwcutmap R D) (.cv r)))) (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classMem (syn_cuni (syn_cuni (.cv r))) D) p0035 p0041
  have p0043 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cfv (syn_chnwcutmap R D) (.cv r)))) (.classMem (syn_cuni (syn_cuni (.cv q))) D) (.classMem (syn_cuni (syn_cuni (.cv r))) D) p0034 p0042
  have p0044 :=
    @g_hnwcutclassinjcl (syn_cuni (syn_cuni (.cv q))) (syn_cuni (syn_cuni (.cv r))) D R dv_cache_0001 hyp_hnwcutmapf1_1
  have p0045 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cfv (syn_chnwcutmap R D) (.cv r)))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) D) (.classMem (syn_cuni (syn_cuni (.cv r))) D)) (.imp (.classEq (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv r)))) (syn_chwniso D))) (.classEq (syn_cuni (syn_cuni (.cv q))) (syn_cuni (syn_cuni (.cv r))))) p0043 p0044
  have p0046 :=
    @g_mpd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cfv (syn_chnwcutmap R D) (.cv r)))) (.classEq (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv r)))) (syn_chwniso D))) (.classEq (syn_cuni (syn_cuni (.cv q))) (syn_cuni (syn_cuni (.cv r)))) p0026 p0045
  have p0047 :=
    @g_sneqd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cfv (syn_chnwcutmap R D) (.cv r)))) (syn_cuni (syn_cuni (.cv q))) (syn_cuni (syn_cuni (.cv r))) p0046
  have p0048 :=
    @g_sneqd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cfv (syn_chnwcutmap R D) (.cv r)))) (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_csn (syn_cuni (syn_cuni (.cv r)))) p0047
  have p0049 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cfv (syn_chnwcutmap R D) (.cv r)))) (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r))))) p0008 p0048
  have p0050 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cfv (syn_chnwcutmap R D) (.cv r)))
  have p0051 :=
    @g_simpr (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))
  have p0052 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))
  have p0053 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))) p0051 p0052
  have p0054 :=
    @g_pw12argcl (.cv r) D
  have p0055 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv r))) D) (.classEq (.cv r) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r))))))) p0053 p0054
  have p0056 :=
    @g_simprd (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classMem (syn_cuni (syn_cuni (.cv r))) D) (.classEq (.cv r) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r)))))) p0055
  have p0057 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cfv (syn_chnwcutmap R D) (.cv r)))) (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (.cv r) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r)))))) p0050 p0056
  have p0058 :=
    @g_eqcomd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cfv (syn_chnwcutmap R D) (.cv r)))) (.cv r) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r))))) p0057
  have p0059 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cfv (syn_chnwcutmap R D) (.cv r)))) (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r))))) (.cv r) p0049 p0058
  have p0060 :=
    @g_ex (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cfv (syn_chnwcutmap R D) (.cv r))) (.classEq (.cv q) (.cv r)) p0059
  have p0061 :=
    @g_ralrimivva (syn_wbr R (syn_cwe) D) (.imp (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cfv (syn_chnwcutmap R D) (.cv r))) (.classEq (.cv q) (.cv r))) q r (syn_cpw1 (syn_cpw1 D)) (syn_cpw1 (syn_cpw1 D)) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 p0060
  have p0062 :=
    Nominal.mp hyp_hnwcutmapf1_1 p0061
  have p0063 :=
    @g_pm3_2i (syn_wf (syn_chnwcutmap R D) (syn_cpw1 (syn_cpw1 D)) (syn_chnord D)) (syn_wral q (syn_cpw1 (syn_cpw1 D)) (syn_wral r (syn_cpw1 (syn_cpw1 D)) (.imp (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cfv (syn_chnwcutmap R D) (.cv r))) (.classEq (.cv q) (.cv r))))) p0000 p0062
  have p0064 :=
    @g_dff13 q r (syn_cpw1 (syn_cpw1 D)) (syn_chnord D) (syn_chnwcutmap R D) dv_cache_0006 dv_cache_0002 dv_cache_0007 dv_cache_0008 dv_cache_0005
  have p0065_e01_recanon : Nominal.NPrf (syn_wb (syn_wf1 (syn_chnwcutmap R D) (syn_cpw1 (syn_cpw1 D)) (syn_chnord D)) (syn_wa (syn_wf (syn_chnwcutmap R D) (syn_cpw1 (syn_cpw1 D)) (syn_chnord D)) (syn_wral q (syn_cpw1 (syn_cpw1 D)) (syn_wral r (syn_cpw1 (syn_cpw1 D)) (.imp (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cfv (syn_chnwcutmap R D) (.cv r))) (.classEq (.cv q) (.cv r))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wf1 syn_wa syn_wf syn_wfun syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_ccom syn_copab syn_wex syn_ccnv syn_cid syn_chnwcutmap syn_cmpt syn_cpw1 syn_cec syn_cima syn_wrex syn_wbr syn_cop syn_cun syn_csn syn_chnwcutcode syn_cuni syn_chwniso syn_chnord syn_cqs syn_chwcn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutmap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
                    exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
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
                    exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0064
  have p0065 :=
    @g_mpbir (syn_wf1 (syn_chnwcutmap R D) (syn_cpw1 (syn_cpw1 D)) (syn_chnord D)) (syn_wa (syn_wf (syn_chnwcutmap R D) (syn_cpw1 (syn_cpw1 D)) (syn_chnord D)) (syn_wral q (syn_cpw1 (syn_cpw1 D)) (syn_wral r (syn_cpw1 (syn_cpw1 D)) (.imp (.classEq (syn_cfv (syn_chnwcutmap R D) (.cv q)) (syn_cfv (syn_chnwcutmap R D) (.cv r))) (.classEq (.cv q) (.cv r)))))) p0063 p0065_e01_recanon
  exact p0065

noncomputable def g_hnqmap1exg
    (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cvv)) (.classMem (syn_chnqmap1 A) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    (by simpa [syn_chnqmap1] using (Nominal.classEqRefl (syn_chnqmap1 A)))
  have p0001 :=
    @g_hwnisoexg A
  have p0002 :=
    @g_imageexg (syn_chwniso A) (syn_cvv)
  have p0003 :=
    @g_syl (.classMem A (syn_cvv)) (.classMem (syn_chwniso A) (syn_cvv)) (.classMem (syn_cimage (syn_chwniso A)) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_hwcnexg A
  have p0005 :=
    @g_pw1exg (syn_chwcn A) (syn_cvv)
  have p0006 :=
    @g_syl (.classMem A (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)) (.classMem (syn_cpw1 (syn_chwcn A)) (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_cimage (syn_chwniso A)) (syn_cvv)) (.classMem (syn_cpw1 (syn_chwcn A)) (syn_cvv)) p0003 p0006
  have p0008 :=
    @g_resexg (syn_cimage (syn_chwniso A)) (syn_cpw1 (syn_chwcn A)) (syn_cvv) (syn_cvv)
  have p0009 :=
    @g_syl (.classMem A (syn_cvv)) (syn_wa (.classMem (syn_cimage (syn_chwniso A)) (syn_cvv)) (.classMem (syn_cpw1 (syn_chwcn A)) (syn_cvv))) (.classMem (syn_cres (syn_cimage (syn_chwniso A)) (syn_cpw1 (syn_chwcn A))) (syn_cvv)) p0007 p0008
  have p0010 :=
    @g_syl5eqel (.classMem A (syn_cvv)) (syn_chnqmap1 A) (syn_cres (syn_cimage (syn_chwniso A)) (syn_cpw1 (syn_chwcn A))) (syn_cvv) p0000 p0009
  exact p0010

noncomputable def g_hnqmap1fn
    (A : Class) (hyp_hnqmap1fn_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wfn (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_hwnisoexg A
  have p0001 :=
    Nominal.mp hyp_hnqmap1fn_1 p0000
  have p0002 :=
    @g_wppimagefn (syn_chwniso A) p0001
  have p0003 :=
    @g_ssv (syn_cpw1 (syn_chwcn A))
  have p0004 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_chwniso A)) (syn_cvv)) (syn_wss (syn_cpw1 (syn_chwcn A)) (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_fnssres (syn_cvv) (syn_cpw1 (syn_chwcn A)) (syn_cimage (syn_chwniso A))
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    (by simpa [syn_chnqmap1] using (Nominal.classEqRefl (syn_chnqmap1 A)))
  have p0008 :=
    @g_fneq1i (syn_cpw1 (syn_chwcn A)) (syn_chnqmap1 A) (syn_cres (syn_cimage (syn_chwniso A)) (syn_cpw1 (syn_chwcn A))) p0007
  have p0009 :=
    @g_mpbir (syn_wfn (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A))) (syn_wfn (syn_cres (syn_cimage (syn_chwniso A)) (syn_cpw1 (syn_chwcn A))) (syn_cpw1 (syn_chwcn A))) p0006 p0008
  exact p0009

noncomputable def g_hnqmap1val
    (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) (hyp_hnqmap1val_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u))) (syn_cec (.cv u) (syn_chwniso A)))) := by
  let proofSupport : Finset Var := ({u} : Finset Var) ∪ A.fv
  have dv_cache_0001 : Disjoint ((syn_csn (.cv u))).fv ((syn_chwniso A)).fv := by
    exact (show Disjoint ((syn_csn (.cv u))).fv ((syn_chwniso A)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso]; exact (show Disjoint (((Class.cv u)).fv) ((A).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({u} : Finset Var)) ((A).fv) from (Finset.disjoint_singleton_left.mpr (show u ∉ (A).fv from (by exact dv_A_u))))))))
  have p0000 :=
    (by simpa [syn_chnqmap1] using (Nominal.classEqRefl (syn_chnqmap1 A)))
  have p0001 :=
    @g_fveq1i (syn_csn (.cv u)) (syn_chnqmap1 A) (syn_cres (syn_cimage (syn_chwniso A)) (syn_cpw1 (syn_chwcn A))) p0000
  have p0002 :=
    @g_snelpw1 (.cv u) (syn_chwcn A)
  have p0003 :=
    @g_biimpri (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv u) (syn_chwcn A)) p0002
  have p0004 :=
    @g_fvres (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A)) (syn_cimage (syn_chwniso A))
  have p0005 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A)) (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A))) (.classEq (syn_cfv (syn_cres (syn_cimage (syn_chwniso A)) (syn_cpw1 (syn_chwcn A))) (syn_csn (.cv u))) (syn_cfv (syn_cimage (syn_chwniso A)) (syn_csn (.cv u)))) p0003 p0004
  have p0006 :=
    @g_syl5eq (.classMem (.cv u) (syn_chwcn A)) (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u))) (syn_cfv (syn_cres (syn_cimage (syn_chwniso A)) (syn_cpw1 (syn_chwcn A))) (syn_csn (.cv u))) (syn_cfv (syn_cimage (syn_chwniso A)) (syn_csn (.cv u))) p0001 p0005
  have p0007 :=
    @g_hwnisoexg A
  have p0008 :=
    Nominal.mp hyp_hnqmap1val_1 p0007
  have p0009 :=
    @g_snex (.cv u)
  have p0010 :=
    @g_wppfvimage (syn_csn (.cv u)) (syn_chwniso A) dv_cache_0001 p0008 p0009
  have p0011 :=
    (by simpa [syn_cec] using (Nominal.classEqRefl (syn_cec (.cv u) (syn_chwniso A))))
  have p0012 :=
    @g_eqtr4i (syn_cfv (syn_cimage (syn_chwniso A)) (syn_csn (.cv u))) (syn_cima (syn_chwniso A) (syn_csn (.cv u))) (syn_cec (.cv u) (syn_chwniso A)) p0010 p0011
  have p0013 :=
    @g_syl6eq (.classMem (.cv u) (syn_chwcn A)) (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u))) (syn_cfv (syn_cimage (syn_chwniso A)) (syn_csn (.cv u))) (syn_cec (.cv u) (syn_chwniso A)) p0006 p0012
  exact p0013

noncomputable def g_hnqmap1f
    (A : Class) (hyp_hnqmap1f_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wf (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A)) (syn_chnord A)) := by
  let proofSupport : Finset Var := A.fv
  let q : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (h)
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (h)
  have fresh_q_ne_u : q ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_q : u ≠ q :=
    Ne.symm fresh_q_ne_u
  have dv_cache_0001 : u ∉ ((Class.cv q)).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ ((syn_chwcn A)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : u ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : u ∉ ((Wff.classMem (syn_cfv (syn_chnqmap1 A) (.cv q)) (syn_chnord A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_q, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : q ∉ ((syn_cpw1 (syn_chwcn A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : q ∉ ((syn_chnord A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : q ∉ ((syn_chnqmap1 A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_hnqmap1fn A hyp_hnqmap1f_1
  have p0001 :=
    @g_hnqmap1fn A hyp_hnqmap1f_1
  have p0002 :=
    @g_elpw1 u (.cv q) (syn_chwcn A) dv_cache_0001 dv_cache_0002
  have p0003 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv u)))
  have p0004 :=
    @g_fveq2 (.cv q) (syn_csn (.cv u)) (syn_chnqmap1 A)
  have p0005 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv u)))) (.classEq (.cv q) (syn_csn (.cv u))) (.classEq (syn_cfv (syn_chnqmap1 A) (.cv q)) (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u)))) p0003 p0004
  have p0006 :=
    @g_hnqmap1val u A dv_cache_0003 hyp_hnqmap1f_1
  have p0007 :=
    @g_hwnisoclasselhnord u A dv_cache_0003 hyp_hnqmap1f_1
  have p0008 :=
    @g_eqeltrd (.classMem (.cv u) (syn_chwcn A)) (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u))) (syn_cec (.cv u) (syn_chwniso A)) (syn_chnord A) p0006 p0007
  have p0009 :=
    @g_adantr (.classMem (.cv u) (syn_chwcn A)) (.classMem (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u))) (syn_chnord A)) (.classEq (.cv q) (syn_csn (.cv u))) p0008
  have p0010 :=
    @g_eqeltrd (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (.cv q) (syn_csn (.cv u)))) (syn_cfv (syn_chnqmap1 A) (.cv q)) (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u))) (syn_chnord A) p0005 p0009
  have p0011 :=
    @g_rexlimiva (.classEq (.cv q) (syn_csn (.cv u))) (.classMem (syn_cfv (syn_chnqmap1 A) (.cv q)) (syn_chnord A)) u (syn_chwcn A) dv_cache_0004 p0010
  have p0012 :=
    @g_sylbi (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (syn_wrex u (syn_chwcn A) (.classEq (.cv q) (syn_csn (.cv u)))) (.classMem (syn_cfv (syn_chnqmap1 A) (.cv q)) (syn_chnord A)) p0002 p0011
  have p0013 :=
    @g_rgen (.classMem (syn_cfv (syn_chnqmap1 A) (.cv q)) (syn_chnord A)) q (syn_cpw1 (syn_chwcn A)) p0012
  have p0014 :=
    @g_pm3_2i (syn_wfn (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A))) (syn_wral q (syn_cpw1 (syn_chwcn A)) (.classMem (syn_cfv (syn_chnqmap1 A) (.cv q)) (syn_chnord A))) p0001 p0013
  have p0015 :=
    @g_fnfvrnss q (syn_cpw1 (syn_chwcn A)) (syn_chnord A) (syn_chnqmap1 A) dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0016 :=
    Nominal.mp p0014 p0015
  have p0017 :=
    @g_pm3_2i (syn_wfn (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A))) (syn_wss (syn_crn (syn_chnqmap1 A)) (syn_chnord A)) p0000 p0016
  have p0018 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A)) (syn_chnord A))))
  have p0019 :=
    @g_mpbir (syn_wf (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A)) (syn_chnord A)) (syn_wa (syn_wfn (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A))) (syn_wss (syn_crn (syn_chnqmap1 A)) (syn_chnord A))) p0017 p0018
  exact p0019

noncomputable def g_hnqmap1rn
    (A : Class) (hyp_hnqmap1rn_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_crn (syn_chnqmap1 A)) (syn_chnord A)) := by
  let proofSupport : Finset Var := A.fv
  let z : Var := freshVar proofSupport 0
  let q : Var := freshVar proofSupport 1
  let u : Var := freshVar proofSupport 2
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (h)
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (h)
  have fresh_z_ne_q : z ≠ q := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_q_ne_z : q ≠ z :=
    Ne.symm fresh_z_ne_q
  have fresh_z_ne_u : z ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_u_ne_z : u ≠ z :=
    Ne.symm fresh_z_ne_u
  have fresh_q_ne_u : q ≠ u := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_u_ne_q : u ≠ q :=
    Ne.symm fresh_q_ne_u
  have dv_cache_0001 : u ∉ ((syn_chwcn A)).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : u ∉ ((syn_chwniso A)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : u ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : q ∉ ((syn_csn (.cv u))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : q ∉ ((syn_cpw1 (syn_chwcn A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : q ∉ ((Wff.classEq (.cv z) (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_z, fresh_q_ne_u, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : u ∉ ((syn_wrex q (syn_cpw1 (syn_chwcn A)) (.classEq (.cv z) (syn_cfv (syn_chnqmap1 A) (.cv q))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, fresh_u_ne_z, fresh_u_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((syn_cpw1 (syn_chwcn A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : q ∉ ((syn_chnord A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : z ∉ ((syn_chnord A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : q ∉ ((syn_chnqmap1 A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : z ∉ ((syn_chnqmap1 A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : q ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show q ≠ z from (by exact fresh_q_ne_z))
  have p0000 :=
    @g_hnqmap1f A hyp_hnqmap1rn_1
  have p0001 :=
    (by simpa [syn_chnord] using (Nominal.classEqRefl (syn_chnord A)))
  have p0002 :=
    @g_eleq2i (syn_chnord A) (syn_cqs (syn_chwcn A) (syn_chwniso A)) (.cv z) p0001
  have p0003 :=
    @g_biimpi (.classMem (.cv z) (syn_chnord A)) (.classMem (.cv z) (syn_cqs (syn_chwcn A) (syn_chwniso A))) p0002
  have p0004 :=
    @g_elqsi u (syn_chwcn A) (.cv z) (syn_chwniso A) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0005 :=
    @g_syl (.classMem (.cv z) (syn_chnord A)) (.classMem (.cv z) (syn_cqs (syn_chwcn A) (syn_chwniso A))) (syn_wrex u (syn_chwcn A) (.classEq (.cv z) (syn_cec (.cv u) (syn_chwniso A)))) p0003 p0004
  have p0006 :=
    @g_snelpw1 (.cv u) (syn_chwcn A)
  have p0007 :=
    @g_biimpri (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A))) (.classMem (.cv u) (syn_chwcn A)) p0006
  have p0008 :=
    @g_adantr (.classMem (.cv u) (syn_chwcn A)) (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv z) (syn_cec (.cv u) (syn_chwniso A))) p0007
  have p0009 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv u) (syn_chwniso A)))
  have p0010 :=
    @g_hnqmap1val u A dv_cache_0004 hyp_hnqmap1rn_1
  have p0011 :=
    @g_adantr (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u))) (syn_cec (.cv u) (syn_chwniso A))) (.classEq (.cv z) (syn_cec (.cv u) (syn_chwniso A))) p0010
  have p0012 :=
    @g_eqtr4d (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv u) (syn_chwniso A)))) (.cv z) (syn_cec (.cv u) (syn_chwniso A)) (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u))) p0009 p0011
  have p0013 :=
    @g_jca (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv u) (syn_chwniso A)))) (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv z) (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u)))) p0008 p0012
  have p0014 :=
    @g_fveq2 (.cv q) (syn_csn (.cv u)) (syn_chnqmap1 A)
  have p0015 :=
    @g_eqeq2d (.classEq (.cv q) (syn_csn (.cv u))) (syn_cfv (syn_chnqmap1 A) (.cv q)) (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u))) (.cv z) p0014
  have p0016 :=
    @g_rspcev (.classEq (.cv z) (syn_cfv (syn_chnqmap1 A) (.cv q))) (.classEq (.cv z) (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u)))) q (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A)) dv_cache_0005 dv_cache_0006 dv_cache_0007 p0015
  have p0017 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (.cv z) (syn_cec (.cv u) (syn_chwniso A)))) (syn_wa (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A))) (.classEq (.cv z) (syn_cfv (syn_chnqmap1 A) (syn_csn (.cv u))))) (syn_wrex q (syn_cpw1 (syn_chwcn A)) (.classEq (.cv z) (syn_cfv (syn_chnqmap1 A) (.cv q)))) p0013 p0016
  have p0018 :=
    @g_rexlimiva (.classEq (.cv z) (syn_cec (.cv u) (syn_chwniso A))) (syn_wrex q (syn_cpw1 (syn_chwcn A)) (.classEq (.cv z) (syn_cfv (syn_chnqmap1 A) (.cv q)))) u (syn_chwcn A) dv_cache_0008 p0017
  have p0019 :=
    @g_syl (.classMem (.cv z) (syn_chnord A)) (syn_wrex u (syn_chwcn A) (.classEq (.cv z) (syn_cec (.cv u) (syn_chwniso A)))) (syn_wrex q (syn_cpw1 (syn_chwcn A)) (.classEq (.cv z) (syn_cfv (syn_chnqmap1 A) (.cv q)))) p0005 p0018
  have p0020 :=
    @g_rgen (syn_wrex q (syn_cpw1 (syn_chwcn A)) (.classEq (.cv z) (syn_cfv (syn_chnqmap1 A) (.cv q)))) z (syn_chnord A) p0019
  have p0021 :=
    @g_pm3_2i (syn_wf (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A)) (syn_chnord A)) (syn_wral z (syn_chnord A) (syn_wrex q (syn_cpw1 (syn_chwcn A)) (.classEq (.cv z) (syn_cfv (syn_chnqmap1 A) (.cv q))))) p0000 p0020
  have p0022 :=
    @g_dffo3 q z (syn_cpw1 (syn_chwcn A)) (syn_chnord A) (syn_chnqmap1 A) dv_cache_0006 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
  have p0023 :=
    @g_mpbir (syn_wfo (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A)) (syn_chnord A)) (syn_wa (syn_wf (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A)) (syn_chnord A)) (syn_wral z (syn_chnord A) (syn_wrex q (syn_cpw1 (syn_chwcn A)) (.classEq (.cv z) (syn_cfv (syn_chnqmap1 A) (.cv q)))))) p0021 p0022
  have p0024 :=
    @g_dffo2 (syn_cpw1 (syn_chwcn A)) (syn_chnord A) (syn_chnqmap1 A)
  have p0025 :=
    @g_mpbi (syn_wfo (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A)) (syn_chnord A)) (syn_wa (syn_wf (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A)) (syn_chnord A)) (.classEq (syn_crn (syn_chnqmap1 A)) (syn_chnord A))) p0023 p0024
  have p0026 :=
    @g_simpri (syn_wf (syn_chnqmap1 A) (syn_cpw1 (syn_chwcn A)) (syn_chnord A)) (.classEq (syn_crn (syn_chnqmap1 A)) (syn_chnord A)) p0025
  exact p0026

noncomputable def g_brlnker
    (R : Class) (X : Class) (Y : Class) :
    Nominal.NPrf (syn_wb (syn_wbr X (syn_clnker R) Y) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X))) := by
  let proofSupport : Finset Var := R.fv ∪ X.fv ∪ Y.fv
  have p0000 :=
    (by simpa [syn_clnker] using (Nominal.classEqRefl (syn_clnker R)))
  have p0001 :=
    @g_breqi X Y (syn_clnker R) (syn_cin R (syn_ccnv R)) p0000
  have p0002 :=
    @g_brin X Y R (syn_ccnv R)
  have p0003 :=
    @g_brcnv X Y R
  have p0004 :=
    @g_anbi2i (syn_wbr X (syn_ccnv R) Y) (syn_wbr Y R X) (syn_wbr X R Y) p0003
  have p0005 :=
    @g_bitri (syn_wbr X (syn_cin R (syn_ccnv R)) Y) (syn_wa (syn_wbr X R Y) (syn_wbr X (syn_ccnv R) Y)) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)) p0002 p0004
  have p0006 :=
    @g_bitri (syn_wbr X (syn_clnker R) Y) (syn_wbr X (syn_cin R (syn_ccnv R)) Y) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)) p0001 p0005
  exact p0006

noncomputable def g_lnkerex
    (R : Class) (hyp_lnkerex_1 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_clnker R) (syn_cvv)) := by
  let proofSupport : Finset Var := R.fv
  have p0000 :=
    (by simpa [syn_clnker] using (Nominal.classEqRefl (syn_clnker R)))
  have p0001 :=
    @g_cnvex R hyp_lnkerex_1
  have p0002 :=
    @g_inex R (syn_ccnv R) hyp_lnkerex_1 p0001
  have p0003 :=
    @g_eqeltri (syn_clnker R) (syn_cin R (syn_ccnv R)) (syn_cvv) p0000 p0002
  exact p0003

noncomputable def g_ellnquo
    (x : Var) (A : Class) (B : Class) (R : Class) (dv_A_B : Disjoint A.fv B.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_A_x : x ∉ A.fv) (dv_B_R : Disjoint B.fv R.fv) (dv_B_x : x ∉ B.fv) (dv_R_x : x ∉ R.fv) (hyp_ellnquo_1 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem B (syn_clnquo R A)) (syn_wrex x A (.classEq B (syn_cec (.cv x) (syn_clnker R))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ B.fv ∪ R.fv
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
  have dv_cache_0003 : x ∉ ((syn_clnker R)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    (by simpa [syn_clnquo] using (Nominal.classEqRefl (syn_clnquo R A)))
  have p0001 :=
    @g_eleq2i (syn_clnquo R A) (syn_cqs A (syn_clnker R)) B p0000
  have p0002 :=
    @g_elqs x A B (syn_clnker R) dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_ellnquo_1
  have p0003 :=
    @g_bitri (.classMem B (syn_clnquo R A)) (.classMem B (syn_cqs A (syn_clnker R))) (syn_wrex x A (.classEq B (syn_cec (.cv x) (syn_clnker R)))) p0001 p0002
  exact p0003

#print axioms g_ellnquo

end NFChoice.DirectNominalPrf.WPPReplay
