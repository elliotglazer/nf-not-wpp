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
import NominalWPPReplayChunk016Compact001Part063

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

noncomputable def g_letc6w6ndv
    (M : Class) (N : Class) (p : Var) (dv_M_p : p ∉ M.fv) (dv_N_p : p ∉ N.fv) :
    Nominal.NPrf (.imp (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))))) := by
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
  have dv_cache_0004 : p ∉ ((syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_M_p, dv_N_p, fresh_p_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : q ∉ ((syn_wrex p (syn_cncs) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_M, fresh_q_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : q ∉ ((syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_M, fresh_q_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_n_3simpa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
  have p0001 :=
    @g_simpl (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
  have p0002 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classMem M (syn_cncs)) p0000 p0001
  have p0003 :=
    @g_n_3simpa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
  have p0004 :=
    @g_simpr (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
  have p0005 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classMem N (syn_cncs)) p0003 p0004
  have p0006 :=
    @g_tccl N
  have p0007 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem N (syn_cncs)) (.classMem (syn_ctc N) (syn_cncs)) p0005 p0006
  have p0008 :=
    @g_tccl (syn_ctc N)
  have p0009 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (syn_ctc N) (syn_cncs)) (.classMem (syn_ctc (syn_ctc N)) (syn_cncs)) p0007 p0008
  have p0010 :=
    @g_tccl (syn_ctc (syn_ctc N))
  have p0011 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (syn_ctc (syn_ctc N)) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc N))) (syn_cncs)) p0009 p0010
  have p0012 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc N)))
  have p0013 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (syn_ctc (syn_ctc (syn_ctc N))) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))) (syn_cncs)) p0011 p0012
  have p0014 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))
  have p0015 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))) (syn_cncs)) p0013 p0014
  have p0016 :=
    @g_n_3simpb (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
  have p0017 :=
    @g_simpr (.classMem M (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
  have p0018 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (syn_wa (.classMem M (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) p0016 p0017
  have p0019 :=
    @g_n_3jca (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem M (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))) (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) p0002 p0015 p0018
  have p0020 :=
    @g_letc M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))) q dv_cache_0001
  have p0021 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (syn_w3a (.classMem M (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))) (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (syn_wrex q (syn_cncs) (.classEq M (syn_ctc (.cv q)))) p0019 p0020
  have p0022 :=
    @g_simpl (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))
  have p0023 :=
    @g_simpr (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))
  have p0024 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classMem (.cv q) (syn_cncs)) p0022 p0023
  have p0025 :=
    @g_simpl (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))
  have p0026 :=
    @g_simpl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))
  have p0027 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) p0025 p0026
  have p0028 :=
    @g_n_3simpa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
  have p0029 :=
    @g_simpr (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
  have p0030 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classMem N (syn_cncs)) p0028 p0029
  have p0031 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem N (syn_cncs)) p0027 p0030
  have p0032 :=
    @g_simpl (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))
  have p0033 :=
    @g_simpl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))
  have p0034 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) p0032 p0033
  have p0035 :=
    @g_n_3simpb (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
  have p0036 :=
    @g_simpr (.classMem M (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
  have p0037 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (syn_wa (.classMem M (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) p0035 p0036
  have p0038 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) p0034 p0037
  have p0039 :=
    @g_simpr (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))
  have p0040 :=
    @g_breq1d (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) M (syn_ctc (.cv q)) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (syn_clec) p0039
  have p0041 :=
    @g_mpbid (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) p0038 p0040
  have p0042 :=
    @g_simpl (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))
  have p0043 :=
    @g_simpr (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))
  have p0044 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classMem (.cv q) (syn_cncs)) p0042 p0043
  have p0045 :=
    @g_simpl (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))
  have p0046 :=
    @g_simpl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))
  have p0047 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) p0045 p0046
  have p0048 :=
    @g_n_3simpa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))
  have p0049 :=
    @g_simpr (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
  have p0050 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classMem N (syn_cncs)) p0048 p0049
  have p0051 :=
    @g_tccl N
  have p0052 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem N (syn_cncs)) (.classMem (syn_ctc N) (syn_cncs)) p0050 p0051
  have p0053 :=
    @g_tccl (syn_ctc N)
  have p0054 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (syn_ctc N) (syn_cncs)) (.classMem (syn_ctc (syn_ctc N)) (syn_cncs)) p0052 p0053
  have p0055 :=
    @g_tccl (syn_ctc (syn_ctc N))
  have p0056 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (syn_ctc (syn_ctc N)) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc N))) (syn_cncs)) p0054 p0055
  have p0057 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc N)))
  have p0058 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (syn_ctc (syn_ctc (syn_ctc N))) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))) (syn_cncs)) p0056 p0057
  have p0059 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))
  have p0060 :=
    @g_syl (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))) (syn_cncs)) p0058 p0059
  have p0061 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))) (syn_cncs)) p0047 p0060
  have p0062 :=
    @g_jca (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv q) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))) (syn_cncs)) p0044 p0061
  have p0063 :=
    @g_tlecg (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))
  have p0064 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))) (syn_cncs))) (syn_wb (syn_wbr (.cv q) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) p0062 p0063
  have p0065 :=
    @g_mpbird (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_wbr (.cv q) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) p0041 p0064
  have p0066 :=
    @g_n_3jca (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv q) (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr (.cv q) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))) p0024 p0031 p0065
  have p0067 :=
    @g_letc5w6ndv (.cv q) N p dv_cache_0002 dv_cache_0003
  have p0068 :=
    @g_syl (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_w3a (.classMem (.cv q) (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr (.cv q) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))) (syn_wrex p (syn_cncs) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))) p0066 p0067
  have p0069 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs))) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))
  have p0070 :=
    @g_simpl (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs))
  have p0071 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs))) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))) (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs))) (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) p0069 p0070
  have p0072 :=
    @g_simpr (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))
  have p0073 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs))) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))) (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classEq M (syn_ctc (.cv q))) p0071 p0072
  have p0074 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs))) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))
  have p0075 :=
    @g_tceq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))
  have p0076 :=
    @g_a1i (.imp (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))) (.classEq (syn_ctc (.cv q)) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs))) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))) p0075
  have p0077 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs))) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))) (.classEq (syn_ctc (.cv q)) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))) p0074 p0076
  have p0078 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs))) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))) M (syn_ctc (.cv q)) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))) p0073 p0077
  have p0079 :=
    @g_ex (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classMem (.cv p) (syn_cncs))) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))) p0078
  have p0080 :=
    @g_reximdva (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))) p (syn_cncs) dv_cache_0004 p0079
  have p0081 :=
    @g_mpd (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q)))) (syn_wrex p (syn_cncs) (.classEq (.cv q) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))) (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))) p0068 p0080
  have p0082 :=
    @g_ex (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq M (syn_ctc (.cv q))) (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))) p0081
  have p0083 :=
    @g_rexlimdva (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (.classEq M (syn_ctc (.cv q))) (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))) q (syn_cncs) dv_cache_0005 dv_cache_0006 p0082
  have p0084 :=
    @g_mpd (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (syn_wrex q (syn_cncs) (.classEq M (syn_ctc (.cv q)))) (syn_wrex p (syn_cncs) (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))) p0021 p0083
  exact p0084

noncomputable def g_wppconcrete6dmcovndv
    (D : Class) (p : Var) (dv_D_p : p ∉ D.fv) (hyp_wppconcrete6dmcovndv_1 : Nominal.NPrf (.classMem D (syn_cncs))) :
    Nominal.NPrf (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))))) := by
  let proofSupport : Finset Var := D.fv ∪ ({p} : Finset Var)
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_D : q ∉ D.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (h))
  have fresh_q_ne_p : q ≠ p := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_q : p ≠ q :=
    Ne.symm fresh_q_ne_p
  have dv_cache_0001 : q ∉ ((Class.cv p)).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ (D).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((Wff.classMem (.cv p) (syn_crn (syn_cwppcardt6fn)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcardt6fn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_p, fresh_q_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
  have p0001 :=
    @g_hwcardssnc (syn_cvv)
  have p0002 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (.cv p) p0001
  have p0003 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv p) (syn_cncs)) p0000 p0002
  have p0004 :=
    @g_a1i (.classMem D (syn_cncs)) (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) hyp_wppconcrete6dmcovndv_1
  have p0005 :=
    @g_simpr (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
  have p0006 :=
    @g_n_3jca (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (.classMem (.cv p) (syn_cncs)) (.classMem D (syn_cncs)) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) p0003 p0004 p0005
  have p0007 :=
    @g_letc6w6ndv (.cv p) D q dv_cache_0001 dv_cache_0002
  have p0008 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (syn_w3a (.classMem (.cv p) (syn_cncs)) (.classMem D (syn_cncs)) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (syn_wrex q (syn_cncs) (.classEq (.cv p) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q))))))))) p0006 p0007
  have p0009 :=
    @g_wppcardt6fnmapndv
  have p0010 :=
    @g_ffn (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_cncs) (syn_cwppcardt6fn)
  have p0011 :=
    Nominal.mp p0009 p0010
  have p0012 :=
    @g_a1i (syn_wfn (syn_cwppcardt6fn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq (.cv p) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q))))))))) p0011
  have p0013 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq (.cv p) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q))))))))
  have p0014 :=
    @g_simpr (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (.classMem (.cv q) (syn_cncs))
  have p0015 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq (.cv p) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q))))))))) (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (.classMem (.cv q) (syn_cncs))) (.classMem (.cv q) (syn_cncs)) p0013 p0014
  have p0016 :=
    @g_snelpw1 (.cv q) (syn_cncs)
  have p0017 :=
    @g_biimpri (.classMem (syn_csn (.cv q)) (syn_cpw1 (syn_cncs))) (.classMem (.cv q) (syn_cncs)) p0016
  have p0018 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq (.cv p) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q))))))))) (.classMem (.cv q) (syn_cncs)) (.classMem (syn_csn (.cv q)) (syn_cpw1 (syn_cncs))) p0015 p0017
  have p0019 :=
    @g_snelpw1 (syn_csn (.cv q)) (syn_cpw1 (syn_cncs))
  have p0020 :=
    @g_biimpri (.classMem (syn_csn (syn_csn (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classMem (syn_csn (.cv q)) (syn_cpw1 (syn_cncs))) p0019
  have p0021 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq (.cv p) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q))))))))) (.classMem (syn_csn (.cv q)) (syn_cpw1 (syn_cncs))) (.classMem (syn_csn (syn_csn (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0018 p0020
  have p0022 :=
    @g_snelpw1 (syn_csn (syn_csn (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cncs)))
  have p0023 :=
    @g_biimpri (.classMem (syn_csn (syn_csn (syn_csn (.cv q)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (.classMem (syn_csn (syn_csn (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) p0022
  have p0024 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq (.cv p) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q))))))))) (.classMem (syn_csn (syn_csn (.cv q))) (syn_cpw1 (syn_cpw1 (syn_cncs)))) (.classMem (syn_csn (syn_csn (syn_csn (.cv q)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) p0021 p0023
  have p0025 :=
    @g_snelpw1 (syn_csn (syn_csn (syn_csn (.cv q)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))
  have p0026 :=
    @g_biimpri (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (.cv q))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.classMem (syn_csn (syn_csn (syn_csn (.cv q)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) p0025
  have p0027 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq (.cv p) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q))))))))) (.classMem (syn_csn (syn_csn (syn_csn (.cv q)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))) (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (.cv q))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) p0024 p0026
  have p0028 :=
    @g_snelpw1 (syn_csn (syn_csn (syn_csn (syn_csn (.cv q))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))
  have p0029 :=
    @g_biimpri (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv q)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (.cv q))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) p0028
  have p0030 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq (.cv p) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q))))))))) (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (.cv q))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))) (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv q)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) p0027 p0029
  have p0031 :=
    @g_snelpw1 (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv q)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))
  have p0032 :=
    @g_biimpri (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv q))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv q)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) p0031
  have p0033 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq (.cv p) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q))))))))) (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv q)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv q))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) p0030 p0032
  have p0034 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq (.cv p) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q))))))))) (syn_wfn (syn_cwppcardt6fn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv q))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) p0012 p0033
  have p0035 :=
    @g_fnfvelrn (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv q))))))) (syn_cwppcardt6fn)
  have p0036 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq (.cv p) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q))))))))) (syn_wa (syn_wfn (syn_cwppcardt6fn) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs)))))))) (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv q))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cncs))))))))) (.classMem (syn_cfv (syn_cwppcardt6fn) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv q)))))))) (syn_crn (syn_cwppcardt6fn))) p0034 p0035
  have p0037 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq (.cv p) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q))))))))
  have p0038 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq (.cv p) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q))))))))
  have p0039 :=
    @g_simpr (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (.classMem (.cv q) (syn_cncs))
  have p0040 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq (.cv p) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q))))))))) (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (.classMem (.cv q) (syn_cncs))) (.classMem (.cv q) (syn_cncs)) p0038 p0039
  have p0041 :=
    @g_wppcardt6fnvalsingndv (.cv q)
  have p0042 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq (.cv p) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q))))))))) (.classMem (.cv q) (syn_cncs)) (.classEq (syn_cfv (syn_cwppcardt6fn) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv q)))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q)))))))) p0040 p0041
  have p0043 :=
    @g_eqcomd (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq (.cv p) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q))))))))) (syn_cfv (syn_cwppcardt6fn) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv q)))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q))))))) p0042
  have p0044 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq (.cv p) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q))))))))) (.cv p) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q))))))) (syn_cfv (syn_cwppcardt6fn) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv q)))))))) p0037 p0043
  have p0045 :=
    @g_eleq1d (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq (.cv p) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q))))))))) (.cv p) (syn_cfv (syn_cwppcardt6fn) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv q)))))))) (syn_crn (syn_cwppcardt6fn)) p0044
  have p0046 :=
    @g_mpbird (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq (.cv p) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q))))))))) (.classMem (.cv p) (syn_crn (syn_cwppcardt6fn))) (.classMem (syn_cfv (syn_cwppcardt6fn) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv q)))))))) (syn_crn (syn_cwppcardt6fn))) p0036 p0045
  have p0047 :=
    @g_ex (syn_wa (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (.classMem (.cv q) (syn_cncs))) (.classEq (.cv p) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q)))))))) (.classMem (.cv p) (syn_crn (syn_cwppcardt6fn))) p0046
  have p0048 :=
    @g_rexlimdva (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (.classEq (.cv p) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q)))))))) (.classMem (.cv p) (syn_crn (syn_cwppcardt6fn))) q (syn_cncs) dv_cache_0003 dv_cache_0004 p0047
  have p0049 :=
    @g_mpd (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (syn_wrex q (syn_cncs) (.classEq (.cv p) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv q))))))))) (.classMem (.cv p) (syn_crn (syn_cwppcardt6fn))) p0008 p0048
  have p0050 :=
    @g_ex (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (.classMem (.cv p) (syn_crn (syn_cwppcardt6fn))) p0049
  have p0051 :=
    @g_wppconcrete6fndmndv
  have p0052 :=
    @g_eleq2i (syn_cdm (syn_cwppconcrete6fn)) (syn_crn (syn_cwppcardt6fn)) (.cv p) p0051
  have p0053 :=
    @g_a1i (syn_wb (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (.cv p) (syn_crn (syn_cwppcardt6fn)))) (.classMem (.cv p) (syn_chwcards (syn_cvv))) p0052
  have p0054 :=
    @g_sylibrd (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (.classMem (.cv p) (syn_crn (syn_cwppcardt6fn))) (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))) p0050 p0053
  have p0055 :=
    @g_rgen (.imp (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn)))) p (syn_chwcards (syn_cvv)) p0054
  exact p0055

#print axioms g_wppconcrete6dmcovndv

end NFChoice.DirectNominalPrf.WPPReplay
