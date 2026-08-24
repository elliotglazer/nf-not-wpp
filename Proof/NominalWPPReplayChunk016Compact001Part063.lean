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
import NominalWPPReplayChunk016Compact001Part062

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

noncomputable def g_letc4w6ndv
    (M : Class) (N : Class) (p : Var) (dv_M_p : p ∉ M.fv) (dv_N_p : p ∉ N.fv) :
    Nominal.NPrf (.imp (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))) := by
  let proofSupport : Finset Var := M.fv ∪ N.fv ∪ ({p} : Finset Var)
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_M : q ∉ M.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_q_not_N : q ∉ N.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_ne_p : q ≠ p := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_q : p ≠ q :=
    Ne.symm fresh_q_ne_p
  have dv_cache_0001 : q ∉ (M).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((Class.cv q)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : p ∉ (N).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_N_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : p ∉ ((syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_M_p, dv_N_p, fresh_p_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : q ∉ ((syn_wrex p (syn_cncs) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_M, fresh_q_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : q ∉ ((syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_M, fresh_q_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_n_3simpa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))
  have p0001 :=
    @g_simpl (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
  have p0002 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classMem M (syn_cncs)) p0000 p0001
  have p0003 :=
    @g_n_3simpa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))
  have p0004 :=
    @g_simpr (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
  have p0005 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classMem N (syn_cncs)) p0003 p0004
  have p0006 :=
    @g_tccl N
  have p0007 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem N (syn_cncs)) (.classMem (syn_ctc N) (syn_cncs)) p0005 p0006
  have p0008 :=
    @g_tccl (syn_ctc N)
  have p0009 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (syn_ctc N) (syn_cncs)) (.classMem (syn_ctc (syn_ctc N)) (syn_cncs)) p0007 p0008
  have p0010 :=
    @g_tccl (syn_ctc (syn_ctc N))
  have p0011 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (syn_ctc (syn_ctc N)) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc N))) (syn_cncs)) p0009 p0010
  have p0012 :=
    @g_n_3simpb (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))
  have p0013 :=
    @g_simpr (.classMem M (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))
  have p0014 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (syn_wa (.classMem M (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))) p0012 p0013
  have p0015 :=
    @g_n_3jca (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem M (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc N))) (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))) p0002 p0011 p0014
  have p0016 :=
    @g_letc M (syn_ctc (syn_ctc (syn_ctc N))) q dv_cache_0001
  have p0017 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (syn_w3a (.classMem M (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc N))) (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (syn_wrex q (syn_cncs) (.classEq M (syn_ctc (.cv q)))) p0015 p0016
  have p0018 :=
    @g_simpl (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))
  have p0019 :=
    @g_simpr (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))
  have p0020 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classMem (.cv q) (syn_cncs)) p0018 p0019
  have p0021 :=
    @g_simpl (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))
  have p0022 :=
    @g_simpl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))
  have p0023 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) p0021 p0022
  have p0024 :=
    @g_n_3simpa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))
  have p0025 :=
    @g_simpr (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
  have p0026 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classMem N (syn_cncs)) p0024 p0025
  have p0027 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem N (syn_cncs)) p0023 p0026
  have p0028 :=
    @g_simpl (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))
  have p0029 :=
    @g_simpl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))
  have p0030 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) p0028 p0029
  have p0031 :=
    @g_n_3simpb (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))
  have p0032 :=
    @g_simpr (.classMem M (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))
  have p0033 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (syn_wa (.classMem M (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))) p0031 p0032
  have p0034 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))) p0030 p0033
  have p0035 :=
    @g_simpr (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))
  have p0036 :=
    @g_breq1d (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) M (syn_ctc (.cv q)) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))) (syn_clec) p0035
  have p0037 :=
    @g_mpbid (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))) (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))) p0034 p0036
  have p0038 :=
    @g_simpl (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))
  have p0039 :=
    @g_simpr (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))
  have p0040 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classMem (.cv q) (syn_cncs)) p0038 p0039
  have p0041 :=
    @g_simpl (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))
  have p0042 :=
    @g_simpl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))
  have p0043 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) p0041 p0042
  have p0044 :=
    @g_n_3simpa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))
  have p0045 :=
    @g_simpr (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
  have p0046 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classMem N (syn_cncs)) p0044 p0045
  have p0047 :=
    @g_tccl N
  have p0048 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem N (syn_cncs)) (.classMem (syn_ctc N) (syn_cncs)) p0046 p0047
  have p0049 :=
    @g_tccl (syn_ctc N)
  have p0050 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (syn_ctc N) (syn_cncs)) (.classMem (syn_ctc (syn_ctc N)) (syn_cncs)) p0048 p0049
  have p0051 :=
    @g_tccl (syn_ctc (syn_ctc N))
  have p0052 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (syn_ctc (syn_ctc N)) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc N))) (syn_cncs)) p0050 p0051
  have p0053 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (syn_ctc (syn_ctc (syn_ctc N))) (syn_cncs)) p0043 p0052
  have p0054 :=
    @g_jca (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv q) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc N))) (syn_cncs)) p0040 p0053
  have p0055 :=
    @g_tlecg (.cv q) (syn_ctc (syn_ctc (syn_ctc N)))
  have p0056 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc N))) (syn_cncs))) (syn_wb (syn_wbr (.cv q) (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))) (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) p0054 p0055
  have p0057 :=
    @g_mpbird (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_wbr (.cv q) (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))) (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))) p0037 p0056
  have p0058 :=
    @g_n_3jca (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv q) (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr (.cv q) (syn_clec) (syn_ctc (syn_ctc (syn_ctc N)))) p0020 p0027 p0057
  have p0059 :=
    @g_letc3w6ndv (.cv q) N p dv_cache_0002 dv_cache_0003
  have p0060 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_w3a (.classMem (.cv q) (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr (.cv q) (syn_clec) (syn_ctc (syn_ctc (syn_ctc N))))) (syn_wrex p (syn_cncs) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (.cv p)))))) p0058 p0059
  have p0061 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs))) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (.cv p)))))
  have p0062 :=
    @g_simpl (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs))
  have p0063 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs))) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (.cv p)))))) (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs))) (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) p0061 p0062
  have p0064 :=
    @g_simpr (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))
  have p0065 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs))) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (.cv p)))))) (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classEq M (syn_ctc (.cv q))) p0063 p0064
  have p0066 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs))) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (.cv p)))))
  have p0067 :=
    @g_tceq (.cv q) (syn_ctc (syn_ctc (syn_ctc (.cv p))))
  have p0068 :=
    @g_a1i (.imp (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (.cv p))))) (.classEq (syn_ctc (.cv q)) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs))) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (.cv p)))))) p0067
  have p0069 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs))) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (.cv p)))))) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (.cv p))))) (.classEq (syn_ctc (.cv q)) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))) p0066 p0068
  have p0070 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs))) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (.cv p)))))) M (syn_ctc (.cv q)) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))) p0065 p0069
  have p0071 :=
    @g_ex (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs))) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (.cv p))))) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))) p0070
  have p0072 :=
    @g_reximdva (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (.cv p))))) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))) p (syn_cncs) dv_cache_0004 p0071
  have p0073 :=
    @g_mpd (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_wrex p (syn_cncs) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (.cv p)))))) (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))) p0060 p0072
  have p0074 :=
    @g_ex (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))) (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))) p0073
  have p0075 :=
    @g_rexlimdva (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (.classEq M (syn_ctc (.cv q))) (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))) q (syn_cncs) dv_cache_0005 dv_cache_0006 p0074
  have p0076 :=
    @g_mpd (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (syn_wrex q (syn_cncs) (.classEq M (syn_ctc (.cv q)))) (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))) p0017 p0075
  exact p0076

noncomputable def g_letc5w6ndv
    (M : Class) (N : Class) (p : Var) (dv_M_p : p ∉ M.fv) (dv_N_p : p ∉ N.fv) :
    Nominal.NPrf (.imp (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))) := by
  let proofSupport : Finset Var := M.fv ∪ N.fv ∪ ({p} : Finset Var)
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_M : q ∉ M.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_q_not_N : q ∉ N.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_ne_p : q ≠ p := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_q : p ≠ q :=
    Ne.symm fresh_q_ne_p
  have dv_cache_0001 : q ∉ (M).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((Class.cv q)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : p ∉ (N).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_N_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : p ∉ ((syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_M_p, dv_N_p, fresh_p_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : q ∉ ((syn_wrex p (syn_cncs) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_M, fresh_q_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : q ∉ ((syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_M, fresh_q_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_n_3simpa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
  have p0001 :=
    @g_simpl (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
  have p0002 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classMem M (syn_cncs)) p0000 p0001
  have p0003 :=
    @g_n_3simpa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
  have p0004 :=
    @g_simpr (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
  have p0005 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classMem N (syn_cncs)) p0003 p0004
  have p0006 :=
    @g_tccl N
  have p0007 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem N (syn_cncs)) (.classMem (syn_ctc N) (syn_cncs)) p0005 p0006
  have p0008 :=
    @g_tccl (syn_ctc N)
  have p0009 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (syn_ctc N) (syn_cncs)) (.classMem (syn_ctc (syn_ctc N)) (syn_cncs)) p0007 p0008
  have p0010 :=
    @g_tccl (syn_ctc (syn_ctc N))
  have p0011 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (syn_ctc (syn_ctc N)) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc N))) (syn_cncs)) p0009 p0010
  have p0012 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc N)))
  have p0013 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (syn_ctc (syn_ctc (syn_ctc N))) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))) (syn_cncs)) p0011 p0012
  have p0014 :=
    @g_n_3simpb (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
  have p0015 :=
    @g_simpr (.classMem M (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
  have p0016 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (syn_wa (.classMem M (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) p0014 p0015
  have p0017 :=
    @g_n_3jca (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem M (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))) (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) p0002 p0013 p0016
  have p0018 :=
    @g_letc M (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))) q dv_cache_0001
  have p0019 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (syn_w3a (.classMem M (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))) (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (syn_wrex q (syn_cncs) (.classEq M (syn_ctc (.cv q)))) p0017 p0018
  have p0020 :=
    @g_simpl (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))
  have p0021 :=
    @g_simpr (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))
  have p0022 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classMem (.cv q) (syn_cncs)) p0020 p0021
  have p0023 :=
    @g_simpl (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))
  have p0024 :=
    @g_simpl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))
  have p0025 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) p0023 p0024
  have p0026 :=
    @g_n_3simpa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
  have p0027 :=
    @g_simpr (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
  have p0028 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classMem N (syn_cncs)) p0026 p0027
  have p0029 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem N (syn_cncs)) p0025 p0028
  have p0030 :=
    @g_simpl (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))
  have p0031 :=
    @g_simpl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))
  have p0032 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) p0030 p0031
  have p0033 :=
    @g_n_3simpb (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
  have p0034 :=
    @g_simpr (.classMem M (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
  have p0035 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (syn_wa (.classMem M (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) p0033 p0034
  have p0036 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) p0032 p0035
  have p0037 :=
    @g_simpr (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))
  have p0038 :=
    @g_breq1d (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) M (syn_ctc (.cv q)) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))) (syn_clec) p0037
  have p0039 :=
    @g_mpbid (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) p0036 p0038
  have p0040 :=
    @g_simpl (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))
  have p0041 :=
    @g_simpr (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))
  have p0042 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classMem (.cv q) (syn_cncs)) p0040 p0041
  have p0043 :=
    @g_simpl (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))
  have p0044 :=
    @g_simpl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))
  have p0045 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) p0043 p0044
  have p0046 :=
    @g_n_3simpa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))
  have p0047 :=
    @g_simpr (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
  have p0048 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classMem N (syn_cncs)) p0046 p0047
  have p0049 :=
    @g_tccl N
  have p0050 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem N (syn_cncs)) (.classMem (syn_ctc N) (syn_cncs)) p0048 p0049
  have p0051 :=
    @g_tccl (syn_ctc N)
  have p0052 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (syn_ctc N) (syn_cncs)) (.classMem (syn_ctc (syn_ctc N)) (syn_cncs)) p0050 p0051
  have p0053 :=
    @g_tccl (syn_ctc (syn_ctc N))
  have p0054 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (syn_ctc (syn_ctc N)) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc N))) (syn_cncs)) p0052 p0053
  have p0055 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc N)))
  have p0056 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (syn_ctc (syn_ctc (syn_ctc N))) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))) (syn_cncs)) p0054 p0055
  have p0057 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))) (syn_cncs)) p0045 p0056
  have p0058 :=
    @g_jca (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv q) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))) (syn_cncs)) p0042 p0057
  have p0059 :=
    @g_tlecg (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))
  have p0060 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))) (syn_cncs))) (syn_wb (syn_wbr (.cv q) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))) (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) p0058 p0059
  have p0061 :=
    @g_mpbird (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_wbr (.cv q) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))) (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) p0039 p0060
  have p0062 :=
    @g_n_3jca (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv q) (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr (.cv q) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))) p0022 p0029 p0061
  have p0063 :=
    @g_letc4w6ndv (.cv q) N p dv_cache_0002 dv_cache_0003
  have p0064 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_w3a (.classMem (.cv q) (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr (.cv q) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (syn_wrex p (syn_cncs) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))) p0062 p0063
  have p0065 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs))) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))
  have p0066 :=
    @g_simpl (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs))
  have p0067 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs))) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))) (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs))) (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) p0065 p0066
  have p0068 :=
    @g_simpr (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))
  have p0069 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs))) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))) (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classEq M (syn_ctc (.cv q))) p0067 p0068
  have p0070 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs))) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))
  have p0071 :=
    @g_tceq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))
  have p0072 :=
    @g_a1i (.imp (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))) (.classEq (syn_ctc (.cv q)) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs))) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))) p0071
  have p0073 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs))) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))) (.classEq (syn_ctc (.cv q)) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))) p0070 p0072
  have p0074 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs))) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))) M (syn_ctc (.cv q)) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))) p0069 p0073
  have p0075 :=
    @g_ex (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs))) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))) p0074
  have p0076 :=
    @g_reximdva (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))) p (syn_cncs) dv_cache_0004 p0075
  have p0077 :=
    @g_mpd (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_wrex p (syn_cncs) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))) (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))) p0064 p0076
  have p0078 :=
    @g_ex (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))) (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))) p0077
  have p0079 :=
    @g_rexlimdva (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (.classEq M (syn_ctc (.cv q))) (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))) q (syn_cncs) dv_cache_0005 dv_cache_0006 p0078
  have p0080 :=
    @g_mpd (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (syn_wrex q (syn_cncs) (.classEq M (syn_ctc (.cv q)))) (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))) p0019 p0079
  exact p0080

#print axioms g_letc5w6ndv

end NFChoice.DirectNominalPrf.WPPReplay
