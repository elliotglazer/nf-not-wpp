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
import NominalWPPReplayChunk017Compact001Part049

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

noncomputable def g_pw1xpshiftsetndv
    (A : Class) (B : Class) (p : Var) (dv_A_p : p ∉ A.fv) (dv_B_p : p ∉ B.fv) (hyp_pw1xpshiftsetndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_pw1xpshiftsetndv_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cmpt p (syn_cpw1 (syn_cxp A B)) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))) (syn_cvv)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ ({p} : Finset Var)
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
  have fresh_q_ne_p : q ≠ p := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_q : p ≠ q :=
    Ne.symm fresh_q_ne_p
  have dv_cache_0001 : p ∉ ((syn_cpw1 (syn_cvv))).fv := by
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((syn_csi (syn_c1st))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : p ∉ ((syn_csi (syn_c2nd))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : p ∉ ((syn_cpw1 (syn_cxp A B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_p, dv_B_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : q ∉ ((syn_cpw1 (syn_cxp A B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, fresh_q_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : q ∉ ((syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : p ∉ ((syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : p ∉ ((syn_cres (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd))) (syn_cpw1 (syn_cxp A B)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_p, dv_B_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : p ∉ ((syn_cmpt q (syn_cpw1 (syn_cxp A B)) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_p, dv_B_p, fresh_p_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
  have p0001 :=
    @g_fvres (.cv p) (syn_cpw1 (syn_cxp A B)) (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd)))
  have p0002 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classEq (syn_cfv (syn_cres (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd))) (syn_cpw1 (syn_cxp A B))) (.cv p)) (syn_cfv (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd))) (.cv p))) p0000 p0001
  have p0003 :=
    @g_n_1stfo
  have p0004 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_wppsifnndv (syn_cvv) (syn_c1st)
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_n_2ndfo
  have p0009 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0010 :=
    Nominal.mp p0008 p0009
  have p0011 :=
    @g_wppsifnndv (syn_cvv) (syn_c2nd)
  have p0012 :=
    Nominal.mp p0010 p0011
  have p0013 :=
    @g_pm3_2i (syn_wfn (syn_csi (syn_c1st)) (syn_cpw1 (syn_cvv))) (syn_wfn (syn_csi (syn_c2nd)) (syn_cpw1 (syn_cvv))) p0007 p0012
  have p0014 :=
    @g_a1i (syn_wa (syn_wfn (syn_csi (syn_c1st)) (syn_cpw1 (syn_cvv))) (syn_wfn (syn_csi (syn_c2nd)) (syn_cpw1 (syn_cvv)))) (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) p0013
  have p0015 :=
    @g_id (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
  have p0016 :=
    @g_ssv (syn_cxp A B)
  have p0017 :=
    @g_pw1ss (syn_cxp A B) (syn_cvv)
  have p0018 :=
    Nominal.mp p0016 p0017
  have p0019 :=
    @g_sseli (syn_cpw1 (syn_cxp A B)) (syn_cpw1 (syn_cvv)) (.cv p) p0018
  have p0020 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv p) (syn_cpw1 (syn_cvv))) p0015 p0019
  have p0021 :=
    @g_jca (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (syn_wa (syn_wfn (syn_csi (syn_c1st)) (syn_cpw1 (syn_cvv))) (syn_wfn (syn_csi (syn_c2nd)) (syn_cpw1 (syn_cvv)))) (.classMem (.cv p) (syn_cpw1 (syn_cvv))) p0014 p0020
  have p0022 :=
    @g_wpptxpfnvalndv p (syn_cpw1 (syn_cvv)) (syn_csi (syn_c1st)) (syn_csi (syn_c2nd)) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0023 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (syn_wa (syn_wa (syn_wfn (syn_csi (syn_c1st)) (syn_cpw1 (syn_cvv))) (syn_wfn (syn_csi (syn_c2nd)) (syn_cpw1 (syn_cvv)))) (.classMem (.cv p) (syn_cpw1 (syn_cvv)))) (.classEq (syn_cfv (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd))) (.cv p)) (syn_cop (syn_cfv (syn_csi (syn_c1st)) (.cv p)) (syn_cfv (syn_csi (syn_c2nd)) (.cv p)))) p0021 p0022
  have p0024 :=
    @g_eqid (syn_cfv (syn_c1st) (syn_cuni (.cv p)))
  have p0025 :=
    @g_n_1stfo
  have p0026 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0027 :=
    Nominal.mp p0025 p0026
  have p0028 :=
    @g_vex p
  have p0029 :=
    @g_uniex (.cv p) p0028
  have p0030 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (.classMem (syn_cuni (.cv p)) (syn_cvv)) p0027 p0029
  have p0031 :=
    @g_fnbrfvb (syn_cvv) (syn_cuni (.cv p)) (syn_cfv (syn_c1st) (syn_cuni (.cv p))) (syn_c1st)
  have p0032 :=
    Nominal.mp p0030 p0031
  have p0033 :=
    @g_mpbi (.classEq (syn_cfv (syn_c1st) (syn_cuni (.cv p))) (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_wbr (syn_cuni (.cv p)) (syn_c1st) (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) p0024 p0032
  have p0034 :=
    @g_vex p
  have p0035 :=
    @g_uniex (.cv p) p0034
  have p0036 :=
    @g_fvex (syn_cuni (.cv p)) (syn_c1st)
  have p0037 :=
    @g_brsnsi (syn_cuni (.cv p)) (syn_cfv (syn_c1st) (syn_cuni (.cv p))) (syn_c1st) p0035 p0036
  have p0038 :=
    @g_mpbir (syn_wbr (syn_csn (syn_cuni (.cv p))) (syn_csi (syn_c1st)) (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))) (syn_wbr (syn_cuni (.cv p)) (syn_c1st) (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) p0033 p0037
  have p0039 :=
    @g_a1i (syn_wbr (syn_csn (syn_cuni (.cv p))) (syn_csi (syn_c1st)) (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))) (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) p0038
  have p0040 :=
    @g_hnwpw1argcl (syn_cxp A B) p
  have p0041 :=
    @g_simpr (.classMem (syn_cuni (.cv p)) (syn_cxp A B)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))
  have p0042 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (syn_wa (.classMem (syn_cuni (.cv p)) (syn_cxp A B)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0040 p0041
  have p0043 :=
    @g_breq1d (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.cv p) (syn_csn (syn_cuni (.cv p))) (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csi (syn_c1st)) p0042
  have p0044 :=
    @g_mpbird (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (syn_wbr (.cv p) (syn_csi (syn_c1st)) (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))) (syn_wbr (syn_csn (syn_cuni (.cv p))) (syn_csi (syn_c1st)) (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))) p0039 p0043
  have p0045 :=
    @g_n_1stfo
  have p0046 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0047 :=
    Nominal.mp p0045 p0046
  have p0048 :=
    @g_wppsifnndv (syn_cvv) (syn_c1st)
  have p0049 :=
    Nominal.mp p0047 p0048
  have p0050 :=
    @g_a1i (syn_wfn (syn_csi (syn_c1st)) (syn_cpw1 (syn_cvv))) (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) p0049
  have p0051 :=
    @g_id (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
  have p0052 :=
    @g_ssv (syn_cxp A B)
  have p0053 :=
    @g_pw1ss (syn_cxp A B) (syn_cvv)
  have p0054 :=
    Nominal.mp p0052 p0053
  have p0055 :=
    @g_sseli (syn_cpw1 (syn_cxp A B)) (syn_cpw1 (syn_cvv)) (.cv p) p0054
  have p0056 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv p) (syn_cpw1 (syn_cvv))) p0051 p0055
  have p0057 :=
    @g_jca (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (syn_wfn (syn_csi (syn_c1st)) (syn_cpw1 (syn_cvv))) (.classMem (.cv p) (syn_cpw1 (syn_cvv))) p0050 p0056
  have p0058 :=
    @g_fnbrfvb (syn_cpw1 (syn_cvv)) (.cv p) (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csi (syn_c1st))
  have p0059 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (syn_wa (syn_wfn (syn_csi (syn_c1st)) (syn_cpw1 (syn_cvv))) (.classMem (.cv p) (syn_cpw1 (syn_cvv)))) (syn_wb (.classEq (syn_cfv (syn_csi (syn_c1st)) (.cv p)) (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))) (syn_wbr (.cv p) (syn_csi (syn_c1st)) (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))))) p0057 p0058
  have p0060 :=
    @g_mpbird (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classEq (syn_cfv (syn_csi (syn_c1st)) (.cv p)) (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))) (syn_wbr (.cv p) (syn_csi (syn_c1st)) (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p))))) p0044 p0059
  have p0061 :=
    @g_eqid (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))
  have p0062 :=
    @g_n_2ndfo
  have p0063 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0064 :=
    Nominal.mp p0062 p0063
  have p0065 :=
    @g_vex p
  have p0066 :=
    @g_uniex (.cv p) p0065
  have p0067 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (.classMem (syn_cuni (.cv p)) (syn_cvv)) p0064 p0066
  have p0068 :=
    @g_fnbrfvb (syn_cvv) (syn_cuni (.cv p)) (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) (syn_c2nd)
  have p0069 :=
    Nominal.mp p0067 p0068
  have p0070 :=
    @g_mpbi (.classEq (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))) (syn_wbr (syn_cuni (.cv p)) (syn_c2nd) (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))) p0061 p0069
  have p0071 :=
    @g_vex p
  have p0072 :=
    @g_uniex (.cv p) p0071
  have p0073 :=
    @g_fvex (syn_cuni (.cv p)) (syn_c2nd)
  have p0074 :=
    @g_brsnsi (syn_cuni (.cv p)) (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) (syn_c2nd) p0072 p0073
  have p0075 :=
    @g_mpbir (syn_wbr (syn_csn (syn_cuni (.cv p))) (syn_csi (syn_c2nd)) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))) (syn_wbr (syn_cuni (.cv p)) (syn_c2nd) (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))) p0070 p0074
  have p0076 :=
    @g_a1i (syn_wbr (syn_csn (syn_cuni (.cv p))) (syn_csi (syn_c2nd)) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))) (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) p0075
  have p0077 :=
    @g_hnwpw1argcl (syn_cxp A B) p
  have p0078 :=
    @g_simpr (.classMem (syn_cuni (.cv p)) (syn_cxp A B)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))
  have p0079 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (syn_wa (.classMem (syn_cuni (.cv p)) (syn_cxp A B)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0077 p0078
  have p0080 :=
    @g_breq1d (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.cv p) (syn_csn (syn_cuni (.cv p))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))) (syn_csi (syn_c2nd)) p0079
  have p0081 :=
    @g_mpbird (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (syn_wbr (.cv p) (syn_csi (syn_c2nd)) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))) (syn_wbr (syn_csn (syn_cuni (.cv p))) (syn_csi (syn_c2nd)) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))) p0076 p0080
  have p0082 :=
    @g_n_2ndfo
  have p0083 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0084 :=
    Nominal.mp p0082 p0083
  have p0085 :=
    @g_wppsifnndv (syn_cvv) (syn_c2nd)
  have p0086 :=
    Nominal.mp p0084 p0085
  have p0087 :=
    @g_a1i (syn_wfn (syn_csi (syn_c2nd)) (syn_cpw1 (syn_cvv))) (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) p0086
  have p0088 :=
    @g_id (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
  have p0089 :=
    @g_ssv (syn_cxp A B)
  have p0090 :=
    @g_pw1ss (syn_cxp A B) (syn_cvv)
  have p0091 :=
    Nominal.mp p0089 p0090
  have p0092 :=
    @g_sseli (syn_cpw1 (syn_cxp A B)) (syn_cpw1 (syn_cvv)) (.cv p) p0091
  have p0093 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv p) (syn_cpw1 (syn_cvv))) p0088 p0092
  have p0094 :=
    @g_jca (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (syn_wfn (syn_csi (syn_c2nd)) (syn_cpw1 (syn_cvv))) (.classMem (.cv p) (syn_cpw1 (syn_cvv))) p0087 p0093
  have p0095 :=
    @g_fnbrfvb (syn_cpw1 (syn_cvv)) (.cv p) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))) (syn_csi (syn_c2nd))
  have p0096 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (syn_wa (syn_wfn (syn_csi (syn_c2nd)) (syn_cpw1 (syn_cvv))) (.classMem (.cv p) (syn_cpw1 (syn_cvv)))) (syn_wb (.classEq (syn_cfv (syn_csi (syn_c2nd)) (.cv p)) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))) (syn_wbr (.cv p) (syn_csi (syn_c2nd)) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))) p0094 p0095
  have p0097 :=
    @g_mpbird (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classEq (syn_cfv (syn_csi (syn_c2nd)) (.cv p)) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))) (syn_wbr (.cv p) (syn_csi (syn_c2nd)) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))) p0081 p0096
  have p0098 :=
    @g_opeq12d (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (syn_cfv (syn_csi (syn_c1st)) (.cv p)) (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_cfv (syn_csi (syn_c2nd)) (.cv p)) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))) p0060 p0097
  have p0099 :=
    @g_eqtrd (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (syn_cfv (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd))) (.cv p)) (syn_cop (syn_cfv (syn_csi (syn_c1st)) (.cv p)) (syn_cfv (syn_csi (syn_c2nd)) (.cv p))) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))) p0023 p0098
  have p0100 :=
    @g_eqtrd (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (syn_cfv (syn_cres (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd))) (syn_cpw1 (syn_cxp A B))) (.cv p)) (syn_cfv (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd))) (.cv p)) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))) p0002 p0099
  have p0101 :=
    @g_id (.classEq (.cv p) (.cv q))
  have p0102 :=
    @g_unieqd (.classEq (.cv p) (.cv q)) (.cv p) (.cv q) p0101
  have p0103 :=
    @g_fveq2d (.classEq (.cv p) (.cv q)) (syn_cuni (.cv p)) (syn_cuni (.cv q)) (syn_c1st) p0102
  have p0104 :=
    @g_sneqd (.classEq (.cv p) (.cv q)) (syn_cfv (syn_c1st) (syn_cuni (.cv p))) (syn_cfv (syn_c1st) (syn_cuni (.cv q))) p0103
  have p0105 :=
    @g_id (.classEq (.cv p) (.cv q))
  have p0106 :=
    @g_unieqd (.classEq (.cv p) (.cv q)) (.cv p) (.cv q) p0105
  have p0107 :=
    @g_fveq2d (.classEq (.cv p) (.cv q)) (syn_cuni (.cv p)) (syn_cuni (.cv q)) (syn_c2nd) p0106
  have p0108 :=
    @g_sneqd (.classEq (.cv p) (.cv q)) (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) p0107
  have p0109 :=
    @g_opeq12d (.classEq (.cv p) (.cv q)) (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) p0104 p0108
  have p0110_e00_recanon : Nominal.NPrf (.imp (.objEq p q) (.classEq (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_csn syn_cfv syn_cio syn_cuni syn_wbr syn_c1st syn_copab
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0109
  have p0110 :=
    @g_cbvmptv p q (syn_cpw1 (syn_cxp A B)) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))) dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 p0110_e00_recanon
  have p0111 :=
    @g_fveq1i (.cv p) (syn_cmpt p (syn_cpw1 (syn_cxp A B)) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))) (syn_cmpt q (syn_cpw1 (syn_cxp A B)) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))) p0110
  have p0112 :=
    @g_eqcomi (syn_cfv (syn_cmpt p (syn_cpw1 (syn_cxp A B)) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))) (.cv p)) (syn_cfv (syn_cmpt q (syn_cpw1 (syn_cxp A B)) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))) (.cv p)) p0111
  have p0113 :=
    @g_a1i (.classEq (syn_cfv (syn_cmpt q (syn_cpw1 (syn_cxp A B)) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))) (.cv p)) (syn_cfv (syn_cmpt p (syn_cpw1 (syn_cxp A B)) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))) (.cv p))) (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) p0112
  have p0114 :=
    @g_id (.classMem (.cv p) (syn_cpw1 (syn_cxp A B)))
  have p0115 :=
    @g_snex (syn_cfv (syn_c1st) (syn_cuni (.cv p)))
  have p0116 :=
    @g_snex (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))
  have p0117 :=
    @g_opex (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))) p0115 p0116
  have p0118 :=
    @g_a1i (.classMem (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))) (syn_cvv)) (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) p0117
  have p0119 :=
    @g_jca (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))) (syn_cvv)) p0114 p0118
  have p0120 :=
    @g_eqid (syn_cmpt p (syn_cpw1 (syn_cxp A B)) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))))
  have p0121 :=
    @g_fvmpt2 p (syn_cpw1 (syn_cxp A B)) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))) (syn_cvv) (syn_cmpt p (syn_cpw1 (syn_cxp A B)) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))) dv_cache_0004 p0120
  have p0122 :=
    @g_syl (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (.classMem (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))) (syn_cvv))) (.classEq (syn_cfv (syn_cmpt p (syn_cpw1 (syn_cxp A B)) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))) (.cv p)) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))) p0119 p0121
  have p0123 :=
    @g_eqtrd (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (syn_cfv (syn_cmpt q (syn_cpw1 (syn_cxp A B)) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))) (.cv p)) (syn_cfv (syn_cmpt p (syn_cpw1 (syn_cxp A B)) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))) (.cv p)) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))) p0113 p0122
  have p0124 :=
    @g_eqtr4d (.classMem (.cv p) (syn_cpw1 (syn_cxp A B))) (syn_cfv (syn_cres (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd))) (syn_cpw1 (syn_cxp A B))) (.cv p)) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))) (syn_cfv (syn_cmpt q (syn_cpw1 (syn_cxp A B)) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))) (.cv p)) p0100 p0123
  have p0125 :=
    @g_rgen (.classEq (syn_cfv (syn_cres (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd))) (syn_cpw1 (syn_cxp A B))) (.cv p)) (syn_cfv (syn_cmpt q (syn_cpw1 (syn_cxp A B)) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))) (.cv p))) p (syn_cpw1 (syn_cxp A B)) p0124
  have p0126 :=
    @g_n_1stfo
  have p0127 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0128 :=
    Nominal.mp p0126 p0127
  have p0129 :=
    @g_wppsifnndv (syn_cvv) (syn_c1st)
  have p0130 :=
    Nominal.mp p0128 p0129
  have p0131 :=
    @g_n_2ndfo
  have p0132 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0133 :=
    Nominal.mp p0131 p0132
  have p0134 :=
    @g_wppsifnndv (syn_cvv) (syn_c2nd)
  have p0135 :=
    Nominal.mp p0133 p0134
  have p0136 :=
    @g_pm3_2i (syn_wfn (syn_csi (syn_c1st)) (syn_cpw1 (syn_cvv))) (syn_wfn (syn_csi (syn_c2nd)) (syn_cpw1 (syn_cvv))) p0130 p0135
  have p0137 :=
    @g_fntxp (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)) (syn_csi (syn_c1st)) (syn_csi (syn_c2nd))
  have p0138 :=
    Nominal.mp p0136 p0137
  have p0139 :=
    @g_inidm (syn_cpw1 (syn_cvv))
  have p0140 :=
    @g_fneq2i (syn_cin (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cvv)) (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd))) p0139
  have p0141 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd))) (syn_cin (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)))) (syn_wfn (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd))) (syn_cpw1 (syn_cvv))) p0138 p0140
  have p0142 :=
    @g_ssv (syn_cxp A B)
  have p0143 :=
    @g_pw1ss (syn_cxp A B) (syn_cvv)
  have p0144 :=
    Nominal.mp p0142 p0143
  have p0145 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd))) (syn_cpw1 (syn_cvv))) (syn_wss (syn_cpw1 (syn_cxp A B)) (syn_cpw1 (syn_cvv))) p0141 p0144
  have p0146 :=
    @g_fnssres (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cxp A B)) (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd)))
  have p0147 :=
    Nominal.mp p0145 p0146
  have p0148 :=
    @g_snex (syn_cfv (syn_c1st) (syn_cuni (.cv q)))
  have p0149 :=
    @g_snex (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))
  have p0150 :=
    @g_opex (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) p0148 p0149
  have p0151 :=
    @g_eqid (syn_cmpt q (syn_cpw1 (syn_cxp A B)) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))))
  have p0152 :=
    @g_fnmpti q (syn_cpw1 (syn_cxp A B)) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))) (syn_cmpt q (syn_cpw1 (syn_cxp A B)) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))) dv_cache_0005 p0150 p0151
  have p0153 :=
    @g_pm3_2i (syn_wfn (syn_cres (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd))) (syn_cpw1 (syn_cxp A B))) (syn_cpw1 (syn_cxp A B))) (syn_wfn (syn_cmpt q (syn_cpw1 (syn_cxp A B)) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))) (syn_cpw1 (syn_cxp A B))) p0147 p0152
  have p0154 :=
    @g_eqfnfv p (syn_cpw1 (syn_cxp A B)) (syn_cres (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd))) (syn_cpw1 (syn_cxp A B))) (syn_cmpt q (syn_cpw1 (syn_cxp A B)) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))) dv_cache_0004 dv_cache_0008 dv_cache_0009
  have p0155 :=
    Nominal.mp p0153 p0154
  have p0156 :=
    @g_mpbir (.classEq (syn_cres (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd))) (syn_cpw1 (syn_cxp A B))) (syn_cmpt q (syn_cpw1 (syn_cxp A B)) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))))) (syn_wral p (syn_cpw1 (syn_cxp A B)) (.classEq (syn_cfv (syn_cres (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd))) (syn_cpw1 (syn_cxp A B))) (.cv p)) (syn_cfv (syn_cmpt q (syn_cpw1 (syn_cxp A B)) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))) (.cv p)))) p0125 p0155
  have p0157 :=
    @g_id (.classEq (.cv p) (.cv q))
  have p0158 :=
    @g_unieqd (.classEq (.cv p) (.cv q)) (.cv p) (.cv q) p0157
  have p0159 :=
    @g_fveq2d (.classEq (.cv p) (.cv q)) (syn_cuni (.cv p)) (syn_cuni (.cv q)) (syn_c1st) p0158
  have p0160 :=
    @g_sneqd (.classEq (.cv p) (.cv q)) (syn_cfv (syn_c1st) (syn_cuni (.cv p))) (syn_cfv (syn_c1st) (syn_cuni (.cv q))) p0159
  have p0161 :=
    @g_id (.classEq (.cv p) (.cv q))
  have p0162 :=
    @g_unieqd (.classEq (.cv p) (.cv q)) (.cv p) (.cv q) p0161
  have p0163 :=
    @g_fveq2d (.classEq (.cv p) (.cv q)) (syn_cuni (.cv p)) (syn_cuni (.cv q)) (syn_c2nd) p0162
  have p0164 :=
    @g_sneqd (.classEq (.cv p) (.cv q)) (syn_cfv (syn_c2nd) (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (syn_cuni (.cv q))) p0163
  have p0165 :=
    @g_opeq12d (.classEq (.cv p) (.cv q)) (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))) p0160 p0164
  have p0166_e00_recanon : Nominal.NPrf (.imp (.objEq p q) (.classEq (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_csn syn_cfv syn_cio syn_cuni syn_wbr syn_c1st syn_copab
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0165
  have p0166 :=
    @g_cbvmptv p q (syn_cpw1 (syn_cxp A B)) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p))))) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q))))) dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 p0166_e00_recanon
  have p0167 :=
    @g_eqtr4i (syn_cres (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd))) (syn_cpw1 (syn_cxp A B))) (syn_cmpt q (syn_cpw1 (syn_cxp A B)) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv q)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv q)))))) (syn_cmpt p (syn_cpw1 (syn_cxp A B)) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))) p0156 p0166
  have p0168 :=
    @g_n_1stex
  have p0169 :=
    @g_siex (syn_c1st) p0168
  have p0170 :=
    @g_n_2ndex
  have p0171 :=
    @g_siex (syn_c2nd) p0170
  have p0172 :=
    @g_txpex (syn_csi (syn_c1st)) (syn_csi (syn_c2nd)) p0169 p0171
  have p0173 :=
    @g_xpex A B hyp_pw1xpshiftsetndv_1 hyp_pw1xpshiftsetndv_2
  have p0174 :=
    @g_pw1ex (syn_cxp A B) p0173
  have p0175 :=
    @g_resex (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd))) (syn_cpw1 (syn_cxp A B)) p0172 p0174
  have p0176 :=
    @g_eqeltrri (syn_cres (syn_ctxp (syn_csi (syn_c1st)) (syn_csi (syn_c2nd))) (syn_cpw1 (syn_cxp A B))) (syn_cmpt p (syn_cpw1 (syn_cxp A B)) (syn_cop (syn_csn (syn_cfv (syn_c1st) (syn_cuni (.cv p)))) (syn_csn (syn_cfv (syn_c2nd) (syn_cuni (.cv p)))))) (syn_cvv) p0167 p0175
  exact p0176

#print axioms g_pw1xpshiftsetndv

end NFChoice.DirectNominalPrf.WPPReplay
