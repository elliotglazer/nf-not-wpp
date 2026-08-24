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
import NominalWPPReplayChunk013Compact001Part055

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

noncomputable def g_tlecg
    (M : Class) (N : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (syn_wb (syn_wbr M (syn_clec) N) (syn_wbr (syn_ctc M) (syn_clec) (syn_ctc N)))) := by
  let proofSupport : Finset Var := M.fv ∪ N.fv
  let p : Var := freshVar proofSupport 0
  let q : Var := freshVar proofSupport 1
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_not_M : p ∉ M.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (h))
  have fresh_p_not_N : p ∉ N.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_q_not_M : q ∉ M.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (h))
  have fresh_q_not_N : q ∉ N.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_p_ne_q : p ≠ q := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_q_ne_p : q ≠ p :=
    Ne.symm fresh_p_ne_q
  have dv_cache_0001 : p ∉ (M).fv := by
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ (N).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : p ∉ ((syn_wbr (syn_ctc M) (syn_clec) (syn_ctc N))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_M, fresh_p_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : p ∉ ((Wff.classMem M (syn_cncs))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : p ∉ ((syn_ctc M)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_M, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : p ∉ ((syn_ctc N)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : q ∉ ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : q ∉ ((syn_wbr M (syn_clec) N)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_M, fresh_q_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : q ∉ ((syn_wa (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (.cv p))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_M, fresh_q_not_N, fresh_q_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : p ∉ ((syn_wbr M (syn_clec) N)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_M, fresh_p_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : p ∉ ((syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_M, fresh_p_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_dflec2 M N p dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_tccl M
  have p0002 :=
    @g_tccl (.cv p)
  have p0003 :=
    @g_addlecncs (syn_ctc M) (syn_ctc (.cv p))
  have p0004 :=
    @g_syl2an (.classMem M (syn_cncs)) (.classMem (syn_ctc M) (syn_cncs)) (.classMem (syn_ctc (.cv p)) (syn_cncs)) (syn_wbr (syn_ctc M) (syn_clec) (syn_cplc (syn_ctc M) (syn_ctc (.cv p)))) (.classMem (.cv p) (syn_cncs)) p0001 p0002 p0003
  have p0005 :=
    @g_tcdi M (.cv p)
  have p0006 :=
    @g_breqtrrd (syn_wa (.classMem M (syn_cncs)) (.classMem (.cv p) (syn_cncs))) (syn_ctc M) (syn_cplc (syn_ctc M) (syn_ctc (.cv p))) (syn_ctc (syn_cplc M (.cv p))) (syn_clec) p0004 p0005
  have p0007 :=
    @g_tceq N (syn_cplc M (.cv p))
  have p0008 :=
    @g_breq2d (.classEq N (syn_cplc M (.cv p))) (syn_ctc N) (syn_ctc (syn_cplc M (.cv p))) (syn_ctc M) (syn_clec) p0007
  have p0009 :=
    @g_syl5ibrcom (syn_wa (.classMem M (syn_cncs)) (.classMem (.cv p) (syn_cncs))) (syn_wbr (syn_ctc M) (syn_clec) (syn_ctc N)) (.classEq N (syn_cplc M (.cv p))) (syn_wbr (syn_ctc M) (syn_clec) (syn_ctc (syn_cplc M (.cv p)))) p0006 p0008
  have p0010 :=
    @g_rexlimdva (.classMem M (syn_cncs)) (.classEq N (syn_cplc M (.cv p))) (syn_wbr (syn_ctc M) (syn_clec) (syn_ctc N)) p (syn_cncs) dv_cache_0003 dv_cache_0004 p0009
  have p0011 :=
    @g_adantr (.classMem M (syn_cncs)) (.imp (syn_wrex p (syn_cncs) (.classEq N (syn_cplc M (.cv p)))) (syn_wbr (syn_ctc M) (syn_clec) (syn_ctc N))) (.classMem N (syn_cncs)) p0010
  have p0012 :=
    @g_sylbid (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (syn_wbr M (syn_clec) N) (syn_wrex p (syn_cncs) (.classEq N (syn_cplc M (.cv p)))) (syn_wbr (syn_ctc M) (syn_clec) (syn_ctc N)) p0000 p0011
  have p0013 :=
    @g_tccl N
  have p0014 :=
    @g_dflec2 (syn_ctc M) (syn_ctc N) p dv_cache_0005 dv_cache_0006
  have p0015 :=
    @g_syl2an (.classMem M (syn_cncs)) (.classMem (syn_ctc M) (syn_cncs)) (.classMem (syn_ctc N) (syn_cncs)) (syn_wb (syn_wbr (syn_ctc M) (syn_clec) (syn_ctc N)) (syn_wrex p (syn_cncs) (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (.cv p))))) (.classMem N (syn_cncs)) p0001 p0013 p0014
  have p0016 :=
    @g_simplr (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wa (.classMem (.cv p) (syn_cncs)) (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (.cv p))))
  have p0017 :=
    @g_simpll (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wa (.classMem (.cv p) (syn_cncs)) (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (.cv p))))
  have p0018 :=
    @g_simprl (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classMem (.cv p) (syn_cncs)) (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (.cv p)))
  have p0019 :=
    @g_simprr (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classMem (.cv p) (syn_cncs)) (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (.cv p)))
  have p0020 :=
    @g_taddc N M (.cv p) q dv_cache_0007
  have p0021 :=
    @g_syl31anc (syn_wa (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (syn_wa (.classMem (.cv p) (syn_cncs)) (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (.cv p))))) (.classMem N (syn_cncs)) (.classMem M (syn_cncs)) (.classMem (.cv p) (syn_cncs)) (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (.cv p))) (syn_wrex q (syn_cncs) (.classEq (.cv p) (syn_ctc (.cv q)))) p0016 p0017 p0018 p0019 p0020
  have p0022 :=
    @g_addceq2 (.cv p) (syn_ctc (.cv q)) (syn_ctc M)
  have p0023 :=
    @g_eqeq2d (.classEq (.cv p) (syn_ctc (.cv q))) (syn_cplc (syn_ctc M) (.cv p)) (syn_cplc (syn_ctc M) (syn_ctc (.cv q))) (syn_ctc N) p0022
  have p0024 :=
    @g_biimpac (.classEq (.cv p) (syn_ctc (.cv q))) (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (.cv p))) (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (syn_ctc (.cv q)))) p0023
  have p0025 :=
    @g_tcdi M (.cv q)
  have p0026 :=
    @g_adantlr (.classMem M (syn_cncs)) (.classMem (.cv q) (syn_cncs)) (.classEq (syn_ctc (syn_cplc M (.cv q))) (syn_cplc (syn_ctc M) (syn_ctc (.cv q)))) (.classMem N (syn_cncs)) p0025
  have p0027 :=
    @g_eqeq2d (syn_wa (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classMem (.cv q) (syn_cncs))) (syn_ctc (syn_cplc M (.cv q))) (syn_cplc (syn_ctc M) (syn_ctc (.cv q))) (syn_ctc N) p0026
  have p0028 :=
    @g_simplr (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (.classMem (.cv q) (syn_cncs))
  have p0029 :=
    @g_ncaddccl M (.cv q)
  have p0030 :=
    @g_adantlr (.classMem M (syn_cncs)) (.classMem (.cv q) (syn_cncs)) (.classMem (syn_cplc M (.cv q)) (syn_cncs)) (.classMem N (syn_cncs)) p0029
  have p0031 :=
    @g_tc11 N (syn_cplc M (.cv q))
  have p0032 :=
    @g_syl2anc (syn_wa (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classMem (.cv q) (syn_cncs))) (.classMem N (syn_cncs)) (.classMem (syn_cplc M (.cv q)) (syn_cncs)) (syn_wb (.classEq (syn_ctc N) (syn_ctc (syn_cplc M (.cv q)))) (.classEq N (syn_cplc M (.cv q)))) p0028 p0030 p0031
  have p0033 :=
    @g_addlecncs M (.cv q)
  have p0034 :=
    @g_breq2 N (syn_cplc M (.cv q)) M (syn_clec)
  have p0035 :=
    @g_syl5ibrcom (syn_wa (.classMem M (syn_cncs)) (.classMem (.cv q) (syn_cncs))) (syn_wbr M (syn_clec) N) (.classEq N (syn_cplc M (.cv q))) (syn_wbr M (syn_clec) (syn_cplc M (.cv q))) p0033 p0034
  have p0036 :=
    @g_adantlr (.classMem M (syn_cncs)) (.classMem (.cv q) (syn_cncs)) (.imp (.classEq N (syn_cplc M (.cv q))) (syn_wbr M (syn_clec) N)) (.classMem N (syn_cncs)) p0035
  have p0037 :=
    @g_sylbid (syn_wa (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classMem (.cv q) (syn_cncs))) (.classEq (syn_ctc N) (syn_ctc (syn_cplc M (.cv q)))) (.classEq N (syn_cplc M (.cv q))) (syn_wbr M (syn_clec) N) p0032 p0036
  have p0038 :=
    @g_sylbird (syn_wa (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classMem (.cv q) (syn_cncs))) (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (syn_ctc (.cv q)))) (.classEq (syn_ctc N) (syn_ctc (syn_cplc M (.cv q)))) (syn_wbr M (syn_clec) N) p0027 p0037
  have p0039 :=
    @g_syl5 (syn_wa (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (.cv p))) (.classEq (.cv p) (syn_ctc (.cv q)))) (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (syn_ctc (.cv q)))) (syn_wa (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classMem (.cv q) (syn_cncs))) (syn_wbr M (syn_clec) N) p0024 p0038
  have p0040 :=
    @g_expdimp (syn_wa (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classMem (.cv q) (syn_cncs))) (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (.cv p))) (.classEq (.cv p) (syn_ctc (.cv q))) (syn_wbr M (syn_clec) N) p0039
  have p0041 :=
    @g_an32s (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classMem (.cv q) (syn_cncs)) (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (.cv p))) (.imp (.classEq (.cv p) (syn_ctc (.cv q))) (syn_wbr M (syn_clec) N)) p0040
  have p0042 :=
    @g_rexlimdva (syn_wa (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (.cv p)))) (.classEq (.cv p) (syn_ctc (.cv q))) (syn_wbr M (syn_clec) N) q (syn_cncs) dv_cache_0008 dv_cache_0009 p0041
  have p0043 :=
    @g_adantrl (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (.cv p))) (.imp (syn_wrex q (syn_cncs) (.classEq (.cv p) (syn_ctc (.cv q)))) (syn_wbr M (syn_clec) N)) (.classMem (.cv p) (syn_cncs)) p0042
  have p0044 :=
    @g_mpd (syn_wa (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (syn_wa (.classMem (.cv p) (syn_cncs)) (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (.cv p))))) (syn_wrex q (syn_cncs) (.classEq (.cv p) (syn_ctc (.cv q)))) (syn_wbr M (syn_clec) N) p0021 p0043
  have p0045 :=
    @g_expr (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classMem (.cv p) (syn_cncs)) (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (.cv p))) (syn_wbr M (syn_clec) N) p0044
  have p0046 :=
    @g_rexlimdva (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (.cv p))) (syn_wbr M (syn_clec) N) p (syn_cncs) dv_cache_0010 dv_cache_0011 p0045
  have p0047 :=
    @g_sylbid (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (syn_wbr (syn_ctc M) (syn_clec) (syn_ctc N)) (syn_wrex p (syn_cncs) (.classEq (syn_ctc N) (syn_cplc (syn_ctc M) (.cv p)))) (syn_wbr M (syn_clec) N) p0015 p0046
  have p0048 :=
    @g_impbid (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs))) (syn_wbr M (syn_clec) N) (syn_wbr (syn_ctc M) (syn_clec) (syn_ctc N)) p0012 p0047
  exact p0048

#print axioms g_tlecg

end NFChoice.DirectNominalPrf.WPPReplay
