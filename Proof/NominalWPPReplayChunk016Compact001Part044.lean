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
import NominalWPPReplayChunk016Compact001Part043

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

noncomputable def g_wppcardtfnf1ndv
     :
    Nominal.NPrf (syn_wf1 (syn_cwppcardtfn) (syn_cpw1 (syn_cncs)) (syn_cncs)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let p : Var := freshVar proofSupport 0
  let q : Var := freshVar proofSupport 1
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_p_ne_q : p ≠ q := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_q_ne_p : q ≠ p :=
    Ne.symm fresh_p_ne_q
  have dv_cache_0001 : q ∉ ((Wff.classMem (.cv p) (syn_cpw1 (syn_cncs)))).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((syn_cpw1 (syn_cncs))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((syn_cpw1 (syn_cncs))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : p ∉ ((syn_cwppcardtfn)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcardtfn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : q ∉ ((syn_cwppcardtfn)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcardtfn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : p ≠ q := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show p ≠ q from (by exact fresh_p_ne_q))
  have p0000 :=
    @g_wppcardtfnmapndv
  have p0001 :=
    @g_simp1 (.classMem (.cv p) (syn_cpw1 (syn_cncs))) (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q)))
  have p0002 :=
    @g_hnwpw1argcl (syn_cncs) p
  have p0003 :=
    @g_syl (syn_w3a (.classMem (.cv p) (syn_cpw1 (syn_cncs))) (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q)))) (.classMem (.cv p) (syn_cpw1 (syn_cncs))) (syn_wa (.classMem (syn_cuni (.cv p)) (syn_cncs)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))) p0001 p0002
  have p0004 :=
    @g_simprd (syn_w3a (.classMem (.cv p) (syn_cpw1 (syn_cncs))) (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q)))) (.classMem (syn_cuni (.cv p)) (syn_cncs)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0003
  have p0005 :=
    @g_simp3 (.classMem (.cv p) (syn_cpw1 (syn_cncs))) (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q)))
  have p0006 :=
    @g_simp1 (.classMem (.cv p) (syn_cpw1 (syn_cncs))) (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q)))
  have p0007 :=
    @g_wppcardtfnvalndv p
  have p0008 :=
    @g_syl (syn_w3a (.classMem (.cv p) (syn_cpw1 (syn_cncs))) (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q)))) (.classMem (.cv p) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_ctc (syn_cuni (.cv p)))) p0006 p0007
  have p0009 :=
    @g_simp2 (.classMem (.cv p) (syn_cpw1 (syn_cncs))) (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q)))
  have p0010 :=
    @g_wppcardtfnvalndv q
  have p0011 :=
    @g_syl (syn_w3a (.classMem (.cv p) (syn_cpw1 (syn_cncs))) (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q)))) (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv q)) (syn_ctc (syn_cuni (.cv q)))) p0009 p0010
  have p0012 :=
    @g_n_3eqtr3d (syn_w3a (.classMem (.cv p) (syn_cpw1 (syn_cncs))) (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q)))) (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q)) (syn_ctc (syn_cuni (.cv p))) (syn_ctc (syn_cuni (.cv q))) p0005 p0008 p0011
  have p0013 :=
    @g_simp1 (.classMem (.cv p) (syn_cpw1 (syn_cncs))) (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q)))
  have p0014 :=
    @g_hnwpw1argcl (syn_cncs) p
  have p0015 :=
    @g_syl (syn_w3a (.classMem (.cv p) (syn_cpw1 (syn_cncs))) (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q)))) (.classMem (.cv p) (syn_cpw1 (syn_cncs))) (syn_wa (.classMem (syn_cuni (.cv p)) (syn_cncs)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))) p0013 p0014
  have p0016 :=
    @g_simpld (syn_w3a (.classMem (.cv p) (syn_cpw1 (syn_cncs))) (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q)))) (.classMem (syn_cuni (.cv p)) (syn_cncs)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0015
  have p0017 :=
    @g_simp2 (.classMem (.cv p) (syn_cpw1 (syn_cncs))) (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q)))
  have p0018 :=
    @g_hnwpw1argcl (syn_cncs) q
  have p0019 :=
    @g_syl (syn_w3a (.classMem (.cv p) (syn_cpw1 (syn_cncs))) (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q)))) (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cncs)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) p0017 p0018
  have p0020 :=
    @g_simpld (syn_w3a (.classMem (.cv p) (syn_cpw1 (syn_cncs))) (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q)))) (.classMem (syn_cuni (.cv q)) (syn_cncs)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0019
  have p0021 :=
    @g_jca (syn_w3a (.classMem (.cv p) (syn_cpw1 (syn_cncs))) (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q)))) (.classMem (syn_cuni (.cv p)) (syn_cncs)) (.classMem (syn_cuni (.cv q)) (syn_cncs)) p0016 p0020
  have p0022 :=
    @g_tc11 (syn_cuni (.cv p)) (syn_cuni (.cv q))
  have p0023 :=
    @g_syl (syn_w3a (.classMem (.cv p) (syn_cpw1 (syn_cncs))) (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q)))) (syn_wa (.classMem (syn_cuni (.cv p)) (syn_cncs)) (.classMem (syn_cuni (.cv q)) (syn_cncs))) (syn_wb (.classEq (syn_ctc (syn_cuni (.cv p))) (syn_ctc (syn_cuni (.cv q)))) (.classEq (syn_cuni (.cv p)) (syn_cuni (.cv q)))) p0021 p0022
  have p0024 :=
    @g_biimpd (syn_w3a (.classMem (.cv p) (syn_cpw1 (syn_cncs))) (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q)))) (.classEq (syn_ctc (syn_cuni (.cv p))) (syn_ctc (syn_cuni (.cv q)))) (.classEq (syn_cuni (.cv p)) (syn_cuni (.cv q))) p0023
  have p0025 :=
    @g_mpd (syn_w3a (.classMem (.cv p) (syn_cpw1 (syn_cncs))) (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q)))) (.classEq (syn_ctc (syn_cuni (.cv p))) (syn_ctc (syn_cuni (.cv q)))) (.classEq (syn_cuni (.cv p)) (syn_cuni (.cv q))) p0012 p0024
  have p0026 :=
    @g_sneqd (syn_w3a (.classMem (.cv p) (syn_cpw1 (syn_cncs))) (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q)))) (syn_cuni (.cv p)) (syn_cuni (.cv q)) p0025
  have p0027 :=
    @g_eqtrd (syn_w3a (.classMem (.cv p) (syn_cpw1 (syn_cncs))) (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q)))) (.cv p) (syn_csn (syn_cuni (.cv p))) (syn_csn (syn_cuni (.cv q))) p0004 p0026
  have p0028 :=
    @g_simp2 (.classMem (.cv p) (syn_cpw1 (syn_cncs))) (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q)))
  have p0029 :=
    @g_hnwpw1argcl (syn_cncs) q
  have p0030 :=
    @g_syl (syn_w3a (.classMem (.cv p) (syn_cpw1 (syn_cncs))) (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q)))) (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cncs)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) p0028 p0029
  have p0031 :=
    @g_simprd (syn_w3a (.classMem (.cv p) (syn_cpw1 (syn_cncs))) (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q)))) (.classMem (syn_cuni (.cv q)) (syn_cncs)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0030
  have p0032 :=
    @g_eqcomd (syn_w3a (.classMem (.cv p) (syn_cpw1 (syn_cncs))) (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q)))) (.cv q) (syn_csn (syn_cuni (.cv q))) p0031
  have p0033 :=
    @g_eqtrd (syn_w3a (.classMem (.cv p) (syn_cpw1 (syn_cncs))) (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q)))) (.cv p) (syn_csn (syn_cuni (.cv q))) (.cv q) p0027 p0032
  have p0034 :=
    @g_n_3exp (.classMem (.cv p) (syn_cpw1 (syn_cncs))) (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q))) (.classEq (.cv p) (.cv q)) p0033
  have p0035 :=
    @g_ralrimiv (.classMem (.cv p) (syn_cpw1 (syn_cncs))) (.imp (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q))) (.classEq (.cv p) (.cv q))) q (syn_cpw1 (syn_cncs)) dv_cache_0001 p0034
  have p0036 :=
    @g_rgen (syn_wral q (syn_cpw1 (syn_cncs)) (.imp (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q))) (.classEq (.cv p) (.cv q)))) p (syn_cpw1 (syn_cncs)) p0035
  have p0037 :=
    @g_pm3_2i (syn_wf (syn_cwppcardtfn) (syn_cpw1 (syn_cncs)) (syn_cncs)) (syn_wral p (syn_cpw1 (syn_cncs)) (syn_wral q (syn_cpw1 (syn_cncs)) (.imp (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q))) (.classEq (.cv p) (.cv q))))) p0000 p0036
  have p0038 :=
    @g_dff13 p q (syn_cpw1 (syn_cncs)) (syn_cncs) (syn_cwppcardtfn) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0039_e01_recanon : Nominal.NPrf (syn_wb (syn_wf1 (syn_cwppcardtfn) (syn_cpw1 (syn_cncs)) (syn_cncs)) (syn_wa (syn_wf (syn_cwppcardtfn) (syn_cpw1 (syn_cncs)) (syn_cncs)) (syn_wral p (syn_cpw1 (syn_cncs)) (syn_wral q (syn_cpw1 (syn_cncs)) (.imp (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q))) (.classEq (.cv p) (.cv q))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wf1 syn_wa syn_wf syn_wfun syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_ccom syn_copab syn_wex syn_ccnv syn_cid syn_cwppcardtfn syn_cres syn_ctcfn syn_cmpt syn_c1c syn_ctc syn_cio syn_cuni syn_csn syn_cpw1 syn_cncs syn_cqs syn_wrex syn_cec syn_cima syn_cvv syn_cen
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcardtfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
      p0038
  have p0039 :=
    @g_mpbir (syn_wf1 (syn_cwppcardtfn) (syn_cpw1 (syn_cncs)) (syn_cncs)) (syn_wa (syn_wf (syn_cwppcardtfn) (syn_cpw1 (syn_cncs)) (syn_cncs)) (syn_wral p (syn_cpw1 (syn_cncs)) (syn_wral q (syn_cpw1 (syn_cncs)) (.imp (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q))) (.classEq (.cv p) (.cv q)))))) p0037 p0039_e01_recanon
  exact p0039

noncomputable def g_wppcardtfnvalsingndv
    (D : Class) :
    Nominal.NPrf (.imp (.classMem D (syn_cncs)) (.classEq (syn_cfv (syn_cwppcardtfn) (syn_csn D)) (syn_ctc D))) := by
  let proofSupport : Finset Var := D.fv
  have p0000 :=
    (by simpa [syn_cwppcardtfn] using (Nominal.classEqRefl (syn_cwppcardtfn)))
  have p0001 :=
    @g_fveq1i (syn_csn D) (syn_cwppcardtfn) (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cncs))) p0000
  have p0002 :=
    @g_a1i (.classEq (syn_cfv (syn_cwppcardtfn) (syn_csn D)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cncs))) (syn_csn D))) (.classMem D (syn_cncs)) p0001
  have p0003 :=
    @g_snelpw1 D (syn_cncs)
  have p0004 :=
    @g_biimpri (.classMem (syn_csn D) (syn_cpw1 (syn_cncs))) (.classMem D (syn_cncs)) p0003
  have p0005 :=
    @g_fvres (syn_csn D) (syn_cpw1 (syn_cncs)) (syn_ctcfn)
  have p0006 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_csn D) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cncs))) (syn_csn D)) (syn_cfv (syn_ctcfn) (syn_csn D))) p0004 p0005
  have p0007 :=
    @g_eqtrd (.classMem D (syn_cncs)) (syn_cfv (syn_cwppcardtfn) (syn_csn D)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cncs))) (syn_csn D)) (syn_cfv (syn_ctcfn) (syn_csn D)) p0002 p0006
  have p0008 :=
    @g_id (.classMem D (syn_cncs))
  have p0009 :=
    @g_elex D (syn_cncs)
  have p0010 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem D (syn_cncs)) (.classMem D (syn_cvv)) p0008 p0009
  have p0011 :=
    @g_tcfnfvcl D
  have p0012 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem D (syn_cvv)) (.classEq (syn_cfv (syn_ctcfn) (syn_csn D)) (syn_ctc D)) p0010 p0011
  have p0013 :=
    @g_eqtrd (.classMem D (syn_cncs)) (syn_cfv (syn_cwppcardtfn) (syn_csn D)) (syn_cfv (syn_ctcfn) (syn_csn D)) (syn_ctc D) p0007 p0012
  exact p0013

noncomputable def g_wppreachorbitextcbidv
    (x : Var) (C : Class) (D : Class) (F : Class) (G : Class) (r : Var) (p : Var) (a : Var) (dv_C_a : a ∉ C.fv) (dv_C_p : p ∉ C.fv) (dv_D_a : a ∉ D.fv) (dv_D_p : p ∉ D.fv) (dv_D_r : r ∉ D.fv) (dv_D_x : x ∉ D.fv) (dv_F_a : a ∉ F.fv) (dv_F_p : p ∉ F.fv) (dv_F_r : r ∉ F.fv) (dv_F_x : x ∉ F.fv) (dv_G_a : a ∉ G.fv) (dv_G_p : p ∉ G.fv) (dv_G_x : x ∉ G.fv) (dv_a_p : a ≠ p) (dv_a_r : a ≠ r) (hyp_wppreachorbitextcbidv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppreachorbitextcbidv_2 : Nominal.NPrf (.classMem D (syn_cdm F))) (hyp_wppreachorbitextcbidv_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) (hyp_wppreachorbitextcbidv_4 : Nominal.NPrf (.classMem G (syn_cfuns))) (hyp_wppreachorbitextcbidv_5 : Nominal.NPrf (.classMem (syn_ctc D) (syn_cdm G))) (hyp_wppreachorbitextcbidv_6 : Nominal.NPrf (syn_wss (syn_crn G) (syn_cdm G))) (hyp_wppreachorbitextcbidv_7 : Nominal.NPrf (syn_wral x (syn_cdm F) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv G (syn_ctc (.cv x)))))) (hyp_wppreachorbitextcbidv_8 : Nominal.NPrf (.classMem C (syn_cncs))) (hyp_wppreachorbitextcbidv_9 : Nominal.NPrf (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F D) (.cv r)) (syn_cncs)))) :
    Nominal.NPrf (syn_wb (syn_wrex a (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a)))) (syn_wrex p (syn_cnnc) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ C.fv ∪ D.fv ∪ F.fv ∪ G.fv ∪ ({r} : Finset Var) ∪ ({p} : Finset Var) ∪ ({a} : Finset Var)
  let n : Var := freshVar proofSupport 0
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_ne_x : n ≠ x := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))))
  have fresh_x_ne_n : x ≠ n :=
    Ne.symm fresh_n_ne_x
  have fresh_n_not_C : n ∉ C.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))))
  have fresh_n_not_D : n ∉ D.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_n_not_F : n ∉ F.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_n_not_G : n ∉ G.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_n_ne_r : n ≠ r := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_r_ne_n : r ≠ n :=
    Ne.symm fresh_n_ne_r
  have fresh_n_ne_p : n ≠ p := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_p_ne_n : p ≠ n :=
    Ne.symm fresh_n_ne_p
  have fresh_n_ne_a : n ≠ a := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_a_ne_n : a ≠ n :=
    Ne.symm fresh_n_ne_a
  have dv_cache_0001 : r ∉ ((Class.cv a)).fv := by
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_a_r), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : r ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : r ∉ ((Wff.classMem (syn_cfv (syn_cfrec F D) (.cv a)) (syn_cncs))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_a_r), dv_F_r, dv_D_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_G_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : p ∉ ((syn_ctc (.cv a))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_a_p), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : p ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : p ∉ ((syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (syn_ctc (.cv a))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_p, (Ne.symm dv_a_p), dv_G_p, dv_D_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : a ∉ ((syn_wrex p (syn_cnnc) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_a, dv_a_p, dv_G_a, dv_D_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : n ∉ ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : r ∉ ((Class.cv n)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : r ∉ ((Wff.classMem (syn_cfv (syn_cfrec F D) (.cv n)) (syn_cncs))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_n, dv_F_r, dv_D_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : a ∉ ((Class.cv n)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : a ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : a ∉ ((syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_a, fresh_a_ne_n, dv_F_a, dv_D_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : n ∉ ((syn_wrex a (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_C, fresh_n_ne_a, fresh_n_not_F, fresh_n_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : n ∉ ((syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_p, fresh_n_not_C, fresh_n_not_G, fresh_n_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : p ∉ ((syn_wrex a (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_p, (Ne.symm dv_a_p), dv_F_p, dv_D_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (.classMem (.cv a) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a)))
  have p0001 :=
    @g_nntccl (.cv a)
  have p0002 :=
    @g_syl (syn_wa (.classMem (.cv a) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a)))) (.classMem (.cv a) (syn_cnnc)) (.classMem (syn_ctc (.cv a)) (syn_cnnc)) p0000 p0001
  have p0003 :=
    @g_a1i (.classMem C (syn_cncs)) (.classMem (.cv a) (syn_cnnc)) hyp_wppreachorbitextcbidv_8
  have p0004 :=
    @g_a1i (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F D) (.cv r)) (syn_cncs))) (.classMem (.cv a) (syn_cnnc)) hyp_wppreachorbitextcbidv_9
  have p0005 :=
    @g_id (.classEq (.cv r) (.cv a))
  have p0006 :=
    @g_fveq2d (.classEq (.cv r) (.cv a)) (.cv r) (.cv a) (syn_cfrec F D) p0005
  have p0007 :=
    @g_eleq1d (.classEq (.cv r) (.cv a)) (syn_cfv (syn_cfrec F D) (.cv r)) (syn_cfv (syn_cfrec F D) (.cv a)) (syn_cncs) p0006
  have p0008 :=
    @g_rspcv (.classMem (syn_cfv (syn_cfrec F D) (.cv r)) (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F D) (.cv a)) (syn_cncs)) r (.cv a) (syn_cnnc) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0007
  have p0009 :=
    @g_mpd (.classMem (.cv a) (syn_cnnc)) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F D) (.cv r)) (syn_cncs))) (.classMem (syn_cfv (syn_cfrec F D) (.cv a)) (syn_cncs)) p0004 p0008
  have p0010 :=
    @g_jca (.classMem (.cv a) (syn_cnnc)) (.classMem C (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F D) (.cv a)) (syn_cncs)) p0003 p0009
  have p0011 :=
    @g_tlecg C (syn_cfv (syn_cfrec F D) (.cv a))
  have p0012 :=
    @g_syl (.classMem (.cv a) (syn_cnnc)) (syn_wa (.classMem C (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F D) (.cv a)) (syn_cncs))) (syn_wb (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a))) (syn_wbr (syn_ctc C) (syn_clec) (syn_ctc (syn_cfv (syn_cfrec F D) (.cv a))))) p0010 p0011
  have p0013 :=
    @g_frectchom0 x F G D (.cv a) dv_cache_0004 dv_cache_0005 dv_cache_0006 hyp_wppreachorbitextcbidv_1 hyp_wppreachorbitextcbidv_2 hyp_wppreachorbitextcbidv_3 hyp_wppreachorbitextcbidv_4 hyp_wppreachorbitextcbidv_5 hyp_wppreachorbitextcbidv_6 hyp_wppreachorbitextcbidv_7
  have p0014 :=
    @g_breq2d (.classMem (.cv a) (syn_cnnc)) (syn_ctc (syn_cfv (syn_cfrec F D) (.cv a))) (syn_cfv (syn_cfrec G (syn_ctc D)) (syn_ctc (.cv a))) (syn_ctc C) (syn_clec) p0013
  have p0015 :=
    @g_bitrd (.classMem (.cv a) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a))) (syn_wbr (syn_ctc C) (syn_clec) (syn_ctc (syn_cfv (syn_cfrec F D) (.cv a)))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (syn_ctc (.cv a)))) p0012 p0014
  have p0016 :=
    @g_biimpd (.classMem (.cv a) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (syn_ctc (.cv a)))) p0015
  have p0017 :=
    @g_imp (.classMem (.cv a) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (syn_ctc (.cv a)))) p0016
  have p0018 :=
    @g_jca (syn_wa (.classMem (.cv a) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a)))) (.classMem (syn_ctc (.cv a)) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (syn_ctc (.cv a)))) p0002 p0017
  have p0019 :=
    @g_id (.classEq (.cv p) (syn_ctc (.cv a)))
  have p0020 :=
    @g_fveq2d (.classEq (.cv p) (syn_ctc (.cv a))) (.cv p) (syn_ctc (.cv a)) (syn_cfrec G (syn_ctc D)) p0019
  have p0021 :=
    @g_breq2d (.classEq (.cv p) (syn_ctc (.cv a))) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p)) (syn_cfv (syn_cfrec G (syn_ctc D)) (syn_ctc (.cv a))) (syn_ctc C) (syn_clec) p0020
  have p0022 :=
    @g_rspcev (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (syn_ctc (.cv a)))) p (syn_ctc (.cv a)) (syn_cnnc) dv_cache_0007 dv_cache_0008 dv_cache_0009 p0021
  have p0023 :=
    @g_syl (syn_wa (.classMem (.cv a) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a)))) (syn_wa (.classMem (syn_ctc (.cv a)) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (syn_ctc (.cv a))))) (syn_wrex p (syn_cnnc) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p)))) p0018 p0022
  have p0024 :=
    @g_rexlimiva (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a))) (syn_wrex p (syn_cnnc) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p)))) a (syn_cnnc) dv_cache_0010 p0023
  have p0025 :=
    @g_simpl (.classMem (.cv p) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p)))
  have p0026 :=
    @g_nntcpreim n (.cv p) dv_cache_0011
  have p0027 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p)))) (.classMem (.cv p) (syn_cnnc)) (syn_wrex n (syn_cnnc) (.classEq (syn_ctc (.cv n)) (.cv p))) p0025 p0026
  have p0028 :=
    @g_simp2 (syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p)))) (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv p))
  have p0029 :=
    @g_simp1 (syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p)))) (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv p))
  have p0030 :=
    @g_simpr (.classMem (.cv p) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p)))
  have p0031 :=
    @g_syl (syn_w3a (syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p)))) (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv p))) (syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p)))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p))) p0029 p0030
  have p0032 :=
    @g_simp3 (syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p)))) (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv p))
  have p0033 :=
    @g_id (.classEq (syn_ctc (.cv n)) (.cv p))
  have p0034 :=
    @g_fveq2d (.classEq (syn_ctc (.cv n)) (.cv p)) (syn_ctc (.cv n)) (.cv p) (syn_cfrec G (syn_ctc D)) p0033
  have p0035 :=
    @g_breq2d (.classEq (syn_ctc (.cv n)) (.cv p)) (syn_cfv (syn_cfrec G (syn_ctc D)) (syn_ctc (.cv n))) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p)) (syn_ctc C) (syn_clec) p0034
  have p0036 :=
    @g_syl (syn_w3a (syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p)))) (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv p))) (.classEq (syn_ctc (.cv n)) (.cv p)) (syn_wb (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (syn_ctc (.cv n)))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p)))) p0032 p0035
  have p0037 :=
    @g_mpbird (syn_w3a (syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p)))) (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv p))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (syn_ctc (.cv n)))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p))) p0031 p0036
  have p0038 :=
    @g_simp2 (syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p)))) (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv p))
  have p0039 :=
    @g_a1i (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc)) hyp_wppreachorbitextcbidv_8
  have p0040 :=
    @g_a1i (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F D) (.cv r)) (syn_cncs))) (.classMem (.cv n) (syn_cnnc)) hyp_wppreachorbitextcbidv_9
  have p0041 :=
    @g_id (.classEq (.cv r) (.cv n))
  have p0042 :=
    @g_fveq2d (.classEq (.cv r) (.cv n)) (.cv r) (.cv n) (syn_cfrec F D) p0041
  have p0043 :=
    @g_eleq1d (.classEq (.cv r) (.cv n)) (syn_cfv (syn_cfrec F D) (.cv r)) (syn_cfv (syn_cfrec F D) (.cv n)) (syn_cncs) p0042
  have p0044 :=
    @g_rspcv (.classMem (syn_cfv (syn_cfrec F D) (.cv r)) (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F D) (.cv n)) (syn_cncs)) r (.cv n) (syn_cnnc) dv_cache_0012 dv_cache_0002 dv_cache_0013 p0043
  have p0045 :=
    @g_mpd (.classMem (.cv n) (syn_cnnc)) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F D) (.cv r)) (syn_cncs))) (.classMem (syn_cfv (syn_cfrec F D) (.cv n)) (syn_cncs)) p0040 p0044
  have p0046 :=
    @g_jca (.classMem (.cv n) (syn_cnnc)) (.classMem C (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F D) (.cv n)) (syn_cncs)) p0039 p0045
  have p0047 :=
    @g_tlecg C (syn_cfv (syn_cfrec F D) (.cv n))
  have p0048 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem C (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F D) (.cv n)) (syn_cncs))) (syn_wb (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n))) (syn_wbr (syn_ctc C) (syn_clec) (syn_ctc (syn_cfv (syn_cfrec F D) (.cv n))))) p0046 p0047
  have p0049 :=
    @g_frectchom0 x F G D (.cv n) dv_cache_0004 dv_cache_0005 dv_cache_0006 hyp_wppreachorbitextcbidv_1 hyp_wppreachorbitextcbidv_2 hyp_wppreachorbitextcbidv_3 hyp_wppreachorbitextcbidv_4 hyp_wppreachorbitextcbidv_5 hyp_wppreachorbitextcbidv_6 hyp_wppreachorbitextcbidv_7
  have p0050 :=
    @g_breq2d (.classMem (.cv n) (syn_cnnc)) (syn_ctc (syn_cfv (syn_cfrec F D) (.cv n))) (syn_cfv (syn_cfrec G (syn_ctc D)) (syn_ctc (.cv n))) (syn_ctc C) (syn_clec) p0049
  have p0051 :=
    @g_bitrd (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n))) (syn_wbr (syn_ctc C) (syn_clec) (syn_ctc (syn_cfv (syn_cfrec F D) (.cv n)))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (syn_ctc (.cv n)))) p0048 p0050
  have p0052 :=
    @g_syl (syn_w3a (syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p)))) (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv p))) (.classMem (.cv n) (syn_cnnc)) (syn_wb (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (syn_ctc (.cv n))))) p0038 p0051
  have p0053 :=
    @g_mpbird (syn_w3a (syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p)))) (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv p))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (syn_ctc (.cv n)))) p0037 p0052
  have p0054 :=
    @g_jca (syn_w3a (syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p)))) (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv p))) (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n))) p0028 p0053
  have p0055 :=
    @g_id (.classEq (.cv a) (.cv n))
  have p0056 :=
    @g_fveq2d (.classEq (.cv a) (.cv n)) (.cv a) (.cv n) (syn_cfrec F D) p0055
  have p0057 :=
    @g_breq2d (.classEq (.cv a) (.cv n)) (syn_cfv (syn_cfrec F D) (.cv a)) (syn_cfv (syn_cfrec F D) (.cv n)) C (syn_clec) p0056
  have p0058 :=
    @g_rspcev (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n))) a (.cv n) (syn_cnnc) dv_cache_0014 dv_cache_0015 dv_cache_0016 p0057
  have p0059 :=
    @g_syl (syn_w3a (syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p)))) (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv p))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n)))) (syn_wrex a (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a)))) p0054 p0058
  have p0060 :=
    @g_rexlimdv3a (syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p)))) (.classEq (syn_ctc (.cv n)) (.cv p)) (syn_wrex a (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a)))) n (syn_cnnc) dv_cache_0017 dv_cache_0018 p0059
  have p0061 :=
    @g_mpd (syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p)))) (syn_wrex n (syn_cnnc) (.classEq (syn_ctc (.cv n)) (.cv p))) (syn_wrex a (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a)))) p0027 p0060
  have p0062 :=
    @g_rexlimiva (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p))) (syn_wrex a (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a)))) p (syn_cnnc) dv_cache_0019 p0061
  have p0063 :=
    @g_impbii (syn_wrex a (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a)))) (syn_wrex p (syn_cnnc) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p)))) p0024 p0062
  exact p0063

noncomputable def g_wppreachorbitfnvndv
    (C : Class) (F : Class) (hyp_wppreachorbitfnvndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (syn_wfn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_cnnc)) := by
  let proofSupport : Finset Var := C.fv ∪ F.fv
  have p0000 :=
    @g_wppreachopfn F hyp_wppreachorbitfnvndv_1
  have p0001 :=
    @g_fnfun (syn_cvv) (syn_cimage (syn_ccnv F))
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_cnvex F hyp_wppreachorbitfnvndv_1
  have p0004 :=
    @g_imageex (syn_ccnv F) p0003
  have p0005 :=
    @g_elfuns (syn_cimage (syn_ccnv F)) p0004
  have p0006 :=
    @g_mpbir (.classMem (syn_cimage (syn_ccnv F)) (syn_cfuns)) (syn_wfun (syn_cimage (syn_ccnv F))) p0002 p0005
  have p0007 :=
    @g_wppreachupperex C
  have p0008 :=
    @g_wppreachopfn F hyp_wppreachorbitfnvndv_1
  have p0009 :=
    @g_fndm (syn_cvv) (syn_cimage (syn_ccnv F))
  have p0010 :=
    Nominal.mp p0008 p0009
  have p0011 :=
    @g_eleqtrri (syn_cima (syn_clec) (syn_csn C)) (syn_cvv) (syn_cdm (syn_cimage (syn_ccnv F))) p0007 p0010
  have p0012 :=
    @g_ssv (syn_crn (syn_cimage (syn_ccnv F)))
  have p0013 :=
    @g_wppreachopfn F hyp_wppreachorbitfnvndv_1
  have p0014 :=
    @g_fndm (syn_cvv) (syn_cimage (syn_ccnv F))
  have p0015 :=
    Nominal.mp p0013 p0014
  have p0016 :=
    @g_sseqtr4i (syn_crn (syn_cimage (syn_ccnv F))) (syn_cvv) (syn_cdm (syn_cimage (syn_ccnv F))) p0012 p0015
  have p0017 :=
    @g_n_3pm3_2i (.classMem (syn_cimage (syn_ccnv F)) (syn_cfuns)) (.classMem (syn_cima (syn_clec) (syn_csn C)) (syn_cdm (syn_cimage (syn_ccnv F)))) (syn_wss (syn_crn (syn_cimage (syn_ccnv F))) (syn_cdm (syn_cimage (syn_ccnv F)))) p0006 p0011 p0016
  have p0018 :=
    @g_wpporbitfnndv (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))
  have p0019 :=
    Nominal.mp p0017 p0018
  exact p0019

noncomputable def g_elwppreachvndv
    (C : Class) (D : Class) (n : Var) (F : Class) (dv_C_n : n ∉ C.fv) (dv_D_n : n ∉ D.fv) (dv_F_n : n ∉ F.fv) (hyp_elwppreachvndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem D (syn_cwppreach F C)) (syn_wrex n (syn_cnnc) (.classMem D (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (.cv n))))) := by
  let proofSupport : Finset Var := C.fv ∪ D.fv ∪ ({n} : Finset Var) ∪ F.fv
  have dv_cache_0001 : n ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : n ∉ ((syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_n, dv_C_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : n ∉ ((syn_cdm (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_n, dv_C_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : n ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    (by simpa [syn_cwppreach] using (Nominal.classEqRefl (syn_cwppreach F C)))
  have p0001 :=
    @g_eleq2i (syn_cwppreach F C) (syn_cuni (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))))) D p0000
  have p0002 :=
    @g_wppreachorbitfnvndv C F hyp_elwppreachvndv_1
  have p0003 :=
    @g_fnfun (syn_cnnc) (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
  have p0004 :=
    Nominal.mp p0002 p0003
  have p0005 :=
    @g_elunirn n D (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) dv_cache_0001 dv_cache_0002
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_bitri (.classMem D (syn_cwppreach F C)) (.classMem D (syn_cuni (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))))) (syn_wrex n (syn_cdm (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))) (.classMem D (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (.cv n)))) p0001 p0006
  have p0008 :=
    @g_wppreachorbitfnvndv C F hyp_elwppreachvndv_1
  have p0009 :=
    @g_fndm (syn_cnnc) (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
  have p0010 :=
    Nominal.mp p0008 p0009
  have p0011 :=
    @g_rexeqi (.classMem D (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (.cv n))) n (syn_cdm (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))) (syn_cnnc) dv_cache_0003 dv_cache_0004 p0010
  have p0012 :=
    @g_bitri (.classMem D (syn_cwppreach F C)) (syn_wrex n (syn_cdm (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))) (.classMem D (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (.cv n)))) (syn_wrex n (syn_cnnc) (.classMem D (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (.cv n)))) p0007 p0011
  exact p0012

#print axioms g_elwppreachvndv

end NFChoice.DirectNominalPrf.WPPReplay
