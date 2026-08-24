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
import NominalWPPReplayChunk015Compact001Part024

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

noncomputable def g_tcnnf1
     :
    Nominal.NPrf (syn_wf1 (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)) (syn_cnnc)) := by
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
  have dv_cache_0001 : q ∉ ((Wff.classMem (.cv p) (syn_cpw1 (syn_cnnc)))).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((syn_cpw1 (syn_cnnc))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((syn_cpw1 (syn_cnnc))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : p ∉ ((syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctcfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : q ∉ ((syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctcfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : p ≠ q := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show p ≠ q from (by exact fresh_p_ne_q))
  have p0000 :=
    @g_tcnnfo
  have p0001 :=
    @g_fof (syn_cpw1 (syn_cnnc)) (syn_cnnc) (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc)))
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_simpl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))
  have p0004 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
  have p0005 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) p0003 p0004
  have p0006 :=
    @g_hnwpw1argcl (syn_cnnc) p
  have p0007 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (syn_wa (.classMem (syn_cuni (.cv p)) (syn_cnnc)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))) p0005 p0006
  have p0008 :=
    @g_simpr (.classMem (syn_cuni (.cv p)) (syn_cnnc)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))
  have p0009 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (syn_wa (.classMem (syn_cuni (.cv p)) (syn_cnnc)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0007 p0008
  have p0010 :=
    @g_simpl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))
  have p0011 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
  have p0012 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) p0010 p0011
  have p0013 :=
    @g_fvres (.cv p) (syn_cpw1 (syn_cnnc)) (syn_ctcfn)
  have p0014 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_ctcfn) (.cv p))) p0012 p0013
  have p0015 :=
    @g_simpl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))
  have p0016 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
  have p0017 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) p0015 p0016
  have p0018 :=
    @g_hnwpw1argcl (syn_cnnc) p
  have p0019 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (syn_wa (.classMem (syn_cuni (.cv p)) (syn_cnnc)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))) p0017 p0018
  have p0020 :=
    @g_simpr (.classMem (syn_cuni (.cv p)) (syn_cnnc)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))
  have p0021 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (syn_wa (.classMem (syn_cuni (.cv p)) (syn_cnnc)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0019 p0020
  have p0022 :=
    @g_fveq2d (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (.cv p) (syn_csn (syn_cuni (.cv p))) (syn_ctcfn) p0021
  have p0023 :=
    @g_eqtrd (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_ctcfn) (.cv p)) (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv p)))) p0014 p0022
  have p0024 :=
    @g_simpl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))
  have p0025 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
  have p0026 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) p0024 p0025
  have p0027 :=
    @g_hnwpw1argcl (syn_cnnc) p
  have p0028 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (syn_wa (.classMem (syn_cuni (.cv p)) (syn_cnnc)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))) p0026 p0027
  have p0029 :=
    @g_simpl (.classMem (syn_cuni (.cv p)) (syn_cnnc)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))
  have p0030 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (syn_wa (.classMem (syn_cuni (.cv p)) (syn_cnnc)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))) (.classMem (syn_cuni (.cv p)) (syn_cnnc)) p0028 p0029
  have p0031 :=
    @g_elex (syn_cuni (.cv p)) (syn_cnnc)
  have p0032 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (.classMem (syn_cuni (.cv p)) (syn_cnnc)) (.classMem (syn_cuni (.cv p)) (syn_cvv)) p0030 p0031
  have p0033 :=
    @g_tcfnfvcl (syn_cuni (.cv p))
  have p0034 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (.classMem (syn_cuni (.cv p)) (syn_cvv)) (.classEq (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv p)))) (syn_ctc (syn_cuni (.cv p)))) p0032 p0033
  have p0035 :=
    @g_eqtrd (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv p)))) (syn_ctc (syn_cuni (.cv p))) p0023 p0034
  have p0036 :=
    @g_eqcomd (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_ctc (syn_cuni (.cv p))) p0035
  have p0037 :=
    @g_simpr (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))
  have p0038 :=
    @g_eqtrd (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (syn_ctc (syn_cuni (.cv p))) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) p0036 p0037
  have p0039 :=
    @g_simpl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))
  have p0040 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
  have p0041 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) p0039 p0040
  have p0042 :=
    @g_fvres (.cv q) (syn_cpw1 (syn_cnnc)) (syn_ctcfn)
  have p0043 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) (syn_cfv (syn_ctcfn) (.cv q))) p0041 p0042
  have p0044 :=
    @g_simpl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))
  have p0045 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
  have p0046 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) p0044 p0045
  have p0047 :=
    @g_hnwpw1argcl (syn_cnnc) q
  have p0048 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) p0046 p0047
  have p0049 :=
    @g_simpr (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0050 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0048 p0049
  have p0051 :=
    @g_fveq2d (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (.cv q) (syn_csn (syn_cuni (.cv q))) (syn_ctcfn) p0050
  have p0052 :=
    @g_eqtrd (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) (syn_cfv (syn_ctcfn) (.cv q)) (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv q)))) p0043 p0051
  have p0053 :=
    @g_simpl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))
  have p0054 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
  have p0055 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) p0053 p0054
  have p0056 :=
    @g_hnwpw1argcl (syn_cnnc) q
  have p0057 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) p0055 p0056
  have p0058 :=
    @g_simpl (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0059 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) (.classMem (syn_cuni (.cv q)) (syn_cnnc)) p0057 p0058
  have p0060 :=
    @g_elex (syn_cuni (.cv q)) (syn_cnnc)
  have p0061 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classMem (syn_cuni (.cv q)) (syn_cvv)) p0059 p0060
  have p0062 :=
    @g_tcfnfvcl (syn_cuni (.cv q))
  have p0063 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (.classMem (syn_cuni (.cv q)) (syn_cvv)) (.classEq (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv q)))) (syn_ctc (syn_cuni (.cv q)))) p0061 p0062
  have p0064 :=
    @g_eqtrd (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv q)))) (syn_ctc (syn_cuni (.cv q))) p0052 p0063
  have p0065 :=
    @g_eqtrd (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (syn_ctc (syn_cuni (.cv p))) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) (syn_ctc (syn_cuni (.cv q))) p0038 p0064
  have p0066 :=
    @g_simpl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))
  have p0067 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
  have p0068 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) p0066 p0067
  have p0069 :=
    @g_hnwpw1argcl (syn_cnnc) p
  have p0070 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (syn_wa (.classMem (syn_cuni (.cv p)) (syn_cnnc)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))) p0068 p0069
  have p0071 :=
    @g_simpl (.classMem (syn_cuni (.cv p)) (syn_cnnc)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))
  have p0072 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (syn_wa (.classMem (syn_cuni (.cv p)) (syn_cnnc)) (.classEq (.cv p) (syn_csn (syn_cuni (.cv p))))) (.classMem (syn_cuni (.cv p)) (syn_cnnc)) p0070 p0071
  have p0073 :=
    @g_nnnc (syn_cuni (.cv p))
  have p0074 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (.classMem (syn_cuni (.cv p)) (syn_cnnc)) (.classMem (syn_cuni (.cv p)) (syn_cncs)) p0072 p0073
  have p0075 :=
    @g_simpl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))
  have p0076 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
  have p0077 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) p0075 p0076
  have p0078 :=
    @g_hnwpw1argcl (syn_cnnc) q
  have p0079 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) p0077 p0078
  have p0080 :=
    @g_simpl (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0081 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) (.classMem (syn_cuni (.cv q)) (syn_cnnc)) p0079 p0080
  have p0082 :=
    @g_nnnc (syn_cuni (.cv q))
  have p0083 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classMem (syn_cuni (.cv q)) (syn_cncs)) p0081 p0082
  have p0084 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (.classMem (syn_cuni (.cv p)) (syn_cncs)) (.classMem (syn_cuni (.cv q)) (syn_cncs)) p0074 p0083
  have p0085 :=
    @g_tc11 (syn_cuni (.cv p)) (syn_cuni (.cv q))
  have p0086 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (syn_wa (.classMem (syn_cuni (.cv p)) (syn_cncs)) (.classMem (syn_cuni (.cv q)) (syn_cncs))) (syn_wb (.classEq (syn_ctc (syn_cuni (.cv p))) (syn_ctc (syn_cuni (.cv q)))) (.classEq (syn_cuni (.cv p)) (syn_cuni (.cv q)))) p0084 p0085
  have p0087 :=
    @g_mpbid (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (.classEq (syn_ctc (syn_cuni (.cv p))) (syn_ctc (syn_cuni (.cv q)))) (.classEq (syn_cuni (.cv p)) (syn_cuni (.cv q))) p0065 p0086
  have p0088 :=
    @g_sneqd (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (syn_cuni (.cv p)) (syn_cuni (.cv q)) p0087
  have p0089 :=
    @g_eqtrd (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (.cv p) (syn_csn (syn_cuni (.cv p))) (syn_csn (syn_cuni (.cv q))) p0009 p0088
  have p0090 :=
    @g_simpl (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))
  have p0091 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))
  have p0092 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) p0090 p0091
  have p0093 :=
    @g_hnwpw1argcl (syn_cnnc) q
  have p0094 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) p0092 p0093
  have p0095 :=
    @g_simpr (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0096 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0094 p0095
  have p0097 :=
    @g_eqcomd (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (.cv q) (syn_csn (syn_cuni (.cv q))) p0096
  have p0098 :=
    @g_eqtrd (syn_wa (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (.cv p) (syn_csn (syn_cuni (.cv q))) (.cv q) p0089 p0097
  have p0099 :=
    @g_ex (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc)))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))) (.classEq (.cv p) (.cv q)) p0098
  have p0100 :=
    @g_ex (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.imp (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))) (.classEq (.cv p) (.cv q))) p0099
  have p0101 :=
    @g_ralrimiv (.classMem (.cv p) (syn_cpw1 (syn_cnnc))) (.imp (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))) (.classEq (.cv p) (.cv q))) q (syn_cpw1 (syn_cnnc)) dv_cache_0001 p0100
  have p0102 :=
    @g_rgen (syn_wral q (syn_cpw1 (syn_cnnc)) (.imp (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))) (.classEq (.cv p) (.cv q)))) p (syn_cpw1 (syn_cnnc)) p0101
  have p0103 :=
    @g_pm3_2i (syn_wf (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)) (syn_cnnc)) (syn_wral p (syn_cpw1 (syn_cnnc)) (syn_wral q (syn_cpw1 (syn_cnnc)) (.imp (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))) (.classEq (.cv p) (.cv q))))) p0002 p0102
  have p0104 :=
    @g_dff13 p q (syn_cpw1 (syn_cnnc)) (syn_cnnc) (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0105_e01_recanon : Nominal.NPrf (syn_wb (syn_wf1 (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)) (syn_cnnc)) (syn_wa (syn_wf (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)) (syn_cnnc)) (syn_wral p (syn_cpw1 (syn_cnnc)) (syn_wral q (syn_cpw1 (syn_cnnc)) (.imp (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))) (.classEq (.cv p) (.cv q))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wf1 syn_wa syn_wf syn_wfun syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_ccom syn_copab syn_wex syn_ccnv syn_cid syn_cres syn_ctcfn syn_cmpt syn_c1c syn_ctc syn_cio syn_cuni syn_csn syn_cpw1 syn_cnnc syn_cint
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctcfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
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
      p0104
  have p0105 :=
    @g_mpbir (syn_wf1 (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)) (syn_cnnc)) (syn_wa (syn_wf (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)) (syn_cnnc)) (syn_wral p (syn_cpw1 (syn_cnnc)) (syn_wral q (syn_cpw1 (syn_cnnc)) (.imp (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv p)) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))) (.classEq (.cv p) (.cv q)))))) p0103 p0105_e01_recanon
  exact p0105

noncomputable def g_tcnnf1o
     :
    Nominal.NPrf (syn_wf1o (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)) (syn_cnnc)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_tcnnf1
  have p0001 :=
    @g_tcnnfo
  have p0002 :=
    @g_pm3_2i (syn_wf1 (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)) (syn_cnnc)) (syn_wfo (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)) (syn_cnnc)) p0000 p0001
  have p0003 :=
    (by simpa [syn_wb, syn_wf1o] using (Nominal.biimpRefl (syn_wf1o (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)) (syn_cnnc))))
  have p0004 :=
    @g_mpbir (syn_wf1o (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)) (syn_cnnc)) (syn_wa (syn_wf1 (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)) (syn_cnnc)) (syn_wfo (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)) (syn_cnnc))) p0002 p0003
  exact p0004

noncomputable def g_nntcpreim
    (x : Var) (P : Class) (dv_P_x : x ∉ P.fv) :
    Nominal.NPrf (.imp (.classMem P (syn_cnnc)) (syn_wrex x (syn_cnnc) (.classEq (syn_ctc (.cv x)) P))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ P.fv
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_ne_x : q ≠ x := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_q : x ≠ q :=
    Ne.symm fresh_q_ne_x
  have fresh_q_not_P : q ∉ P.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have dv_cache_0001 : q ∉ ((syn_cpw1 (syn_cnnc))).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ (P).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_P, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctcfn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_cuni (.cv q))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Wff.classEq (syn_ctc (syn_cuni (.cv q))) P)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_q, dv_P_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : q ∉ ((syn_wrex x (syn_cnnc) (.classEq (syn_ctc (.cv x)) P))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_x, fresh_q_not_P, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_tcnnfo
  have p0001 :=
    @g_a1i (syn_wfo (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)) (syn_cnnc)) (.classMem P (syn_cnnc)) p0000
  have p0002 :=
    @g_id (.classMem P (syn_cnnc))
  have p0003 :=
    @g_jca (.classMem P (syn_cnnc)) (syn_wfo (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)) (syn_cnnc)) (.classMem P (syn_cnnc)) p0001 p0002
  have p0004 :=
    @g_foelrn q (syn_cpw1 (syn_cnnc)) (syn_cnnc) P (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0005 :=
    @g_syl (.classMem P (syn_cnnc)) (syn_wa (syn_wfo (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)) (syn_cnnc)) (.classMem P (syn_cnnc))) (syn_wrex q (syn_cpw1 (syn_cnnc)) (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) p0003 p0004
  have p0006 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))
  have p0007 :=
    @g_hnwpw1argcl (syn_cnnc) q
  have p0008 :=
    @g_simpl (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0009 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) (.classMem (syn_cuni (.cv q)) (syn_cnnc)) p0007 p0008
  have p0010 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classMem (syn_cuni (.cv q)) (syn_cnnc)) p0006 p0009
  have p0011 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))
  have p0012 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))
  have p0013 :=
    @g_fvres (.cv q) (syn_cpw1 (syn_cnnc)) (syn_ctcfn)
  have p0014 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) (syn_cfv (syn_ctcfn) (.cv q))) p0012 p0013
  have p0015 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))
  have p0016 :=
    @g_hnwpw1argcl (syn_cnnc) q
  have p0017 :=
    @g_simpr (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0018 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0016 p0017
  have p0019 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0015 p0018
  have p0020 :=
    @g_fveq2d (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (.cv q) (syn_csn (syn_cuni (.cv q))) (syn_ctcfn) p0019
  have p0021 :=
    @g_eqtrd (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) (syn_cfv (syn_ctcfn) (.cv q)) (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv q)))) p0014 p0020
  have p0022 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))
  have p0023 :=
    @g_hnwpw1argcl (syn_cnnc) q
  have p0024 :=
    @g_simpl (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0025 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) (.classMem (syn_cuni (.cv q)) (syn_cnnc)) p0023 p0024
  have p0026 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classMem (syn_cuni (.cv q)) (syn_cnnc)) p0022 p0025
  have p0027 :=
    @g_elex (syn_cuni (.cv q)) (syn_cnnc)
  have p0028 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classMem (syn_cuni (.cv q)) (syn_cvv)) p0026 p0027
  have p0029 :=
    @g_tcfnfvcl (syn_cuni (.cv q))
  have p0030 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (.classMem (syn_cuni (.cv q)) (syn_cvv)) (.classEq (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv q)))) (syn_ctc (syn_cuni (.cv q)))) p0028 p0029
  have p0031 :=
    @g_eqtrd (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv q)))) (syn_ctc (syn_cuni (.cv q))) p0021 p0030
  have p0032 :=
    @g_eqtrd (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)) (syn_ctc (syn_cuni (.cv q))) p0011 p0031
  have p0033 :=
    @g_eqcomd (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) P (syn_ctc (syn_cuni (.cv q))) p0032
  have p0034 :=
    @g_jca (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classEq (syn_ctc (syn_cuni (.cv q))) P) p0010 p0033
  have p0035 :=
    @g_tceq (.cv x) (syn_cuni (.cv q))
  have p0036 :=
    @g_eqeq1d (.classEq (.cv x) (syn_cuni (.cv q))) (syn_ctc (.cv x)) (syn_ctc (syn_cuni (.cv q))) P p0035
  have p0037 :=
    @g_rspcev (.classEq (syn_ctc (.cv x)) P) (.classEq (syn_ctc (syn_cuni (.cv q))) P) x (syn_cuni (.cv q)) (syn_cnnc) dv_cache_0005 dv_cache_0006 dv_cache_0007 p0036
  have p0038 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cnnc))) (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cnnc)) (.classEq (syn_ctc (syn_cuni (.cv q))) P)) (syn_wrex x (syn_cnnc) (.classEq (syn_ctc (.cv x)) P)) p0034 p0037
  have p0039 :=
    @g_rexlimiva (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q))) (syn_wrex x (syn_cnnc) (.classEq (syn_ctc (.cv x)) P)) q (syn_cpw1 (syn_cnnc)) dv_cache_0008 p0038
  have p0040 :=
    @g_syl (.classMem P (syn_cnnc)) (syn_wrex q (syn_cpw1 (syn_cnnc)) (.classEq P (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) (.cv q)))) (syn_wrex x (syn_cnnc) (.classEq (syn_ctc (.cv x)) P)) p0005 p0039
  exact p0040

noncomputable def g_pwpullex
    (R : Class) (F : Class) (hyp_pwpullex_1 : Nominal.NPrf (.classMem F (syn_cvv))) (hyp_pwpullex_2 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cpwpull F R) (syn_cvv)) := by
  let proofSupport : Finset Var := R.fv ∪ F.fv
  have p0000 :=
    (by simpa [syn_cpwpull] using (Nominal.classEqRefl (syn_cpwpull F R)))
  have p0001 :=
    @g_cnvex F hyp_pwpullex_1
  have p0002 :=
    @g_coex (syn_ccnv F) R p0001 hyp_pwpullex_2
  have p0003 :=
    @g_coex (syn_ccom (syn_ccnv F) R) F p0002 hyp_pwpullex_1
  have p0004 :=
    @g_eqeltri (syn_cpwpull F R) (syn_ccom (syn_ccom (syn_ccnv F) R) F) (syn_cvv) p0000 p0003
  exact p0004

#print axioms g_pwpullex

end NFChoice.DirectNominalPrf.WPPReplay
