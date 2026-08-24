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
import NominalWPPReplayChunk017Compact001Part078

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

noncomputable def g_hnwcutambfactorf1noarndv
    (A : Class) (D : Class) (R : Class) (hyp_hnwcutambfactorf1noarndv_1 : Nominal.NPrf (syn_wss D A)) (hyp_hnwcutambfactorf1noarndv_2 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) (hyp_hnwcutambfactorf1noarndv_3 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wf1 (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (syn_cpw1 (syn_cpw1 D)) (syn_chnord A)) := by
  let proofSupport : Finset Var := A.fv ∪ D.fv ∪ R.fv
  let q : Var := freshVar proofSupport 0
  let r : Var := freshVar proofSupport 1
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_q_not_D : q ∉ D.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_not_R : q ∉ R.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_r_not_D : r ∉ D.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_not_R : r ∉ R.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_q_ne_r : q ≠ r := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_r_ne_q : r ≠ q :=
    Ne.symm fresh_q_ne_r
  have dv_cache_0001 : q ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ (R).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : r ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : r ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : r ∉ ((syn_cpw1 (syn_cpw1 D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : q ∉ ((syn_wbr R (syn_cwe) D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_R, fresh_q_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : r ∉ ((syn_wbr R (syn_cwe) D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_R, fresh_r_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : q ≠ r := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show q ≠ r from (by exact fresh_q_ne_r))
  have dv_cache_0009 : q ∉ ((syn_cpw1 (syn_cpw1 D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : q ∉ ((syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, fresh_q_not_D, fresh_q_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : r ∉ ((syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, fresh_r_not_D, fresh_r_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_hnwcutambfactorfnnoarndv A D R hyp_hnwcutambfactorf1noarndv_1 hyp_hnwcutambfactorf1noarndv_2 hyp_hnwcutambfactorf1noarndv_3
  have p0001 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r)))
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
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r)))) (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0001 p0007
  have p0009 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r)))
  have p0010 :=
    @g_simpr (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))
  have p0011 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))
  have p0012 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) p0010 p0011
  have p0013 :=
    @g_hnwcutambfactorvalnoarndv A D R q dv_cache_0001 dv_cache_0002 hyp_hnwcutambfactorf1noarndv_1 hyp_hnwcutambfactorf1noarndv_2 hyp_hnwcutambfactorf1noarndv_3
  have p0014 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q)) (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A))) p0012 p0013
  have p0015 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r)))) (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q)) (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A))) p0009 p0014
  have p0016 :=
    @g_eqcomd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r)))) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q)) (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A)) p0015
  have p0017 :=
    @g_simpr (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r)))
  have p0018 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r)))) (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r)) p0016 p0017
  have p0019 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r)))
  have p0020 :=
    @g_simpr (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))
  have p0021 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))
  have p0022 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D)))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))) p0020 p0021
  have p0023 :=
    @g_hnwcutambfactorvalnoarndv A D R r dv_cache_0003 dv_cache_0004 hyp_hnwcutambfactorf1noarndv_1 hyp_hnwcutambfactorf1noarndv_2 hyp_hnwcutambfactorf1noarndv_3
  have p0024 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r)) (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv r)))) (syn_chwniso A))) p0022 p0023
  have p0025 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r)))) (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r)) (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv r)))) (syn_chwniso A))) p0019 p0024
  have p0026 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r)))) (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r)) (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv r)))) (syn_chwniso A)) p0018 p0025
  have p0027 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r)))
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
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r)))) (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classMem (syn_cuni (syn_cuni (.cv q))) D) p0027 p0033
  have p0035 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r)))
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
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r)))) (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classMem (syn_cuni (syn_cuni (.cv r))) D) p0035 p0041
  have p0043 :=
    @g_jca (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r)))) (.classMem (syn_cuni (syn_cuni (.cv q))) D) (.classMem (syn_cuni (syn_cuni (.cv r))) D) p0034 p0042
  have p0044 :=
    @g_hnwcutclassinjambnoarndv A (syn_cuni (syn_cuni (.cv q))) (syn_cuni (syn_cuni (.cv r))) D R hyp_hnwcutambfactorf1noarndv_1 hyp_hnwcutambfactorf1noarndv_2 hyp_hnwcutambfactorf1noarndv_3
  have p0045 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r)))) (syn_wa (.classMem (syn_cuni (syn_cuni (.cv q))) D) (.classMem (syn_cuni (syn_cuni (.cv r))) D)) (.imp (.classEq (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A)) (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv r)))) (syn_chwniso A))) (.classEq (syn_cuni (syn_cuni (.cv q))) (syn_cuni (syn_cuni (.cv r))))) p0043 p0044
  have p0046 :=
    @g_mpd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r)))) (.classEq (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A)) (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv r)))) (syn_chwniso A))) (.classEq (syn_cuni (syn_cuni (.cv q))) (syn_cuni (syn_cuni (.cv r)))) p0026 p0045
  have p0047 :=
    @g_sneqd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r)))) (syn_cuni (syn_cuni (.cv q))) (syn_cuni (syn_cuni (.cv r))) p0046
  have p0048 :=
    @g_sneqd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r)))) (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_csn (syn_cuni (syn_cuni (.cv r)))) p0047
  have p0049 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r)))) (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q))))) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r))))) p0008 p0048
  have p0050 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r)))
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
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r)))) (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (.cv r) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r)))))) p0050 p0056
  have p0058 :=
    @g_eqcomd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r)))) (.cv r) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r))))) p0057
  have p0059 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r)))) (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv r))))) (.cv r) p0049 p0058
  have p0060 :=
    @g_ex (syn_wa (syn_wbr R (syn_cwe) D) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (.cv r) (syn_cpw1 (syn_cpw1 D))))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r))) (.classEq (.cv q) (.cv r)) p0059
  have p0061 :=
    @g_ralrimivva (syn_wbr R (syn_cwe) D) (.imp (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r))) (.classEq (.cv q) (.cv r))) q r (syn_cpw1 (syn_cpw1 D)) (syn_cpw1 (syn_cpw1 D)) dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 p0060
  have p0062 :=
    Nominal.mp hyp_hnwcutambfactorf1noarndv_2 p0061
  have p0063 :=
    @g_pm3_2i (syn_wf (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (syn_cpw1 (syn_cpw1 D)) (syn_chnord A)) (syn_wral q (syn_cpw1 (syn_cpw1 D)) (syn_wral r (syn_cpw1 (syn_cpw1 D)) (.imp (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r))) (.classEq (.cv q) (.cv r))))) p0000 p0062
  have p0064 :=
    @g_dff13 q r (syn_cpw1 (syn_cpw1 D)) (syn_chnord A) (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) dv_cache_0009 dv_cache_0005 dv_cache_0010 dv_cache_0011 dv_cache_0008
  have p0065_e01_recanon : Nominal.NPrf (syn_wb (syn_wf1 (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (syn_cpw1 (syn_cpw1 D)) (syn_chnord A)) (syn_wa (syn_wf (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (syn_cpw1 (syn_cpw1 D)) (syn_chnord A)) (syn_wral q (syn_cpw1 (syn_cpw1 D)) (syn_wral r (syn_cpw1 (syn_cpw1 D)) (.imp (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r))) (.classEq (.cv q) (.cv r))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wf1 syn_wa syn_wf syn_wfun syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_ccom syn_copab syn_wex syn_ccnv syn_cid syn_cpw1 syn_chnord syn_cqs syn_wrex syn_cec syn_cima syn_csn syn_chwcn syn_chwniso
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
    @g_mpbir (syn_wf1 (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (syn_cpw1 (syn_cpw1 D)) (syn_chnord A)) (syn_wa (syn_wf (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (syn_cpw1 (syn_cpw1 D)) (syn_chnord A)) (syn_wral q (syn_cpw1 (syn_cpw1 D)) (syn_wral r (syn_cpw1 (syn_cpw1 D)) (.imp (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv r))) (.classEq (.cv q) (.cv r)))))) p0063 p0065_e01_recanon
  exact p0065

noncomputable def g_hnwcutambfactorf1codendv
    (A : Class) (B : Class) (hyp_hnwcutambfactorf1codendv_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_hnwcutambfactorf1codendv_2 : Nominal.NPrf (.classMem B (syn_chwcn A))) :
    Nominal.NPrf (syn_wf1 (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) B))) (syn_chnord A)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_hwcnbaseclndv A B
  have p0001 :=
    Nominal.mp hyp_hnwcutambfactorf1codendv_2 p0000
  have p0002 :=
    @g_hwcnweclndv A B
  have p0003 :=
    Nominal.mp hyp_hnwcutambfactorf1codendv_2 p0002
  have p0004 :=
    @g_hnwcutambfactorf1noarndv A (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c1st) B) p0001 p0003 hyp_hnwcutambfactorf1codendv_1
  exact p0004

noncomputable def g_hnwcutambfactorf1impclndv
    (A : Class) (B : Class) (hyp_hnwcutambfactorf1impclndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem B (syn_chwcn A)) (syn_wf1 (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) B))) (syn_chnord A))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_id (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
  have p0001 :=
    @g_fveq2d (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (syn_c1st) p0000
  have p0002 :=
    @g_id (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
  have p0003 :=
    @g_fveq2d (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (syn_c2nd) p0002
  have p0004 :=
    @g_hnwcutreleq12dndv (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) p0001 p0003
  have p0005 :=
    @g_sieqdndv (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_chnwcutrel (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)) (syn_chnwcutrel (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))) p0004
  have p0006 :=
    @g_coeq2d (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B))) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))))) (syn_chnqmap1 A) p0005
  have p0007 :=
    @g_f1eq1 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) B))) (syn_chnord A) (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)))) (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))))))
  have p0008 :=
    @g_syl (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (.classEq (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)))) (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))))))) (syn_wb (syn_wf1 (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) B))) (syn_chnord A)) (syn_wf1 (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) B))) (syn_chnord A))) p0006 p0007
  have p0009 :=
    @g_id (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
  have p0010 :=
    @g_fveq2d (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (syn_c2nd) p0009
  have p0011 :=
    @g_pw1eq (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
  have p0012 :=
    @g_syl (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (.classEq (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))) (.classEq (syn_cpw1 (syn_cfv (syn_c2nd) B)) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))))) p0010 p0011
  have p0013 :=
    @g_pw1eq (syn_cpw1 (syn_cfv (syn_c2nd) B)) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))))
  have p0014 :=
    @g_syl (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (.classEq (syn_cpw1 (syn_cfv (syn_c2nd) B)) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))))) (.classEq (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) B))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))))) p0012 p0013
  have p0015 :=
    @g_f1eq2 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) B))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))))) (syn_chnord A) (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))))))
  have p0016 :=
    @g_syl (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (.classEq (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) B))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))))) (syn_wb (syn_wf1 (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) B))) (syn_chnord A)) (syn_wf1 (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))))) (syn_chnord A))) p0014 p0015
  have p0017 :=
    @g_bitrd (.classEq B (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_wf1 (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) B))) (syn_chnord A)) (syn_wf1 (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) B))) (syn_chnord A)) (syn_wf1 (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))))) (syn_chnord A)) p0008 p0016
  have p0018 :=
    @g_eqid (syn_c0)
  have p0019 :=
    @g_simpr (.classEq (syn_c0) (syn_c0)) (.classMem B (syn_chwcn A))
  have p0020 :=
    @g_hncodecmpdefaultcnndv A
  have p0021 :=
    @g_a1i (.classMem (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)) (syn_chwcn A)) (syn_wa (.classEq (syn_c0) (syn_c0)) (.neg (.classMem B (syn_chwcn A)))) p0020
  have p0022 :=
    @g_ifclda (.classEq (syn_c0) (syn_c0)) (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)) (syn_chwcn A) p0019 p0021
  have p0023 :=
    Nominal.mp p0018 p0022
  have p0024 :=
    @g_hnwcutambfactorf1codendv A (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) hyp_hnwcutambfactorf1impclndv_1 p0023
  have p0025 :=
    @g_dedth (.classMem B (syn_chwcn A)) (syn_wf1 (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) B))) (syn_chnord A)) (syn_wf1 (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cif (.classMem B (syn_chwcn A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))))) (syn_chnord A)) B (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)) p0017 p0024
  exact p0025

noncomputable def g_hnwcutambfactorf1impndv
    (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) (hyp_hnwcutambfactorf1impndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem (.cv u) (syn_chwcn A)) (syn_wf1 (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_chnord A))) := by
  let proofSupport : Finset Var := ({u} : Finset Var) ∪ A.fv
  have p0000 :=
    @g_hnwcutambfactorf1impclndv A (.cv u) hyp_hnwcutambfactorf1impndv_1
  exact p0000

#print axioms g_hnwcutambfactorf1impndv

end NFChoice.DirectNominalPrf.WPPReplay
