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
import NominalWPPReplayChunk016Compact001Part064

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

noncomputable def g_wppconcrete6dmpaircovndv
    (D : Class) (p : Var) (dv_D_p : p ∉ D.fv) (hyp_wppconcrete6dmpaircovndv_1 : Nominal.NPrf (.classMem D (syn_cncs))) (hyp_wppconcrete6dmpaircovndv_2 : Nominal.NPrf (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) :
    Nominal.NPrf (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn)))))) := by
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
  have dv_cache_0001 : q ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ ((Class.cv p)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((syn_chwcards (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((Wff.imp (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppconcrete6fn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_p, fresh_q_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : q ∉ ((syn_ctc (.cv p))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : q ∉ ((Wff.imp (syn_wbr (syn_ctc (.cv p)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppconcrete6fn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_p, fresh_q_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpr (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
  have p0001 :=
    @g_simpl (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
  have p0002 :=
    @g_wppconcrete6dmcovndv D q dv_cache_0001 hyp_wppconcrete6dmpaircovndv_1
  have p0003 :=
    @g_id (.classEq (.cv q) (.cv p))
  have p0004 :=
    @g_breq1d (.classEq (.cv q) (.cv p)) (.cv q) (.cv p) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))) (syn_clec) p0003
  have p0005 :=
    @g_id (.classEq (.cv q) (.cv p))
  have p0006 :=
    @g_eleq1d (.classEq (.cv q) (.cv p)) (.cv q) (.cv p) (syn_cdm (syn_cwppconcrete6fn)) p0005
  have p0007 :=
    @g_imbi12d (.classEq (.cv q) (.cv p)) (syn_wbr (.cv q) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (.classMem (.cv q) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))) p0004 p0006
  have p0008 :=
    @g_rspcv (.imp (syn_wbr (.cv q) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (.classMem (.cv q) (syn_cdm (syn_cwppconcrete6fn)))) (.imp (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn)))) q (.cv p) (syn_chwcards (syn_cvv)) dv_cache_0002 dv_cache_0003 dv_cache_0004 p0007
  have p0009 :=
    @g_com12 (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wral q (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv q) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (.classMem (.cv q) (syn_cdm (syn_cwppconcrete6fn))))) (.imp (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn)))) p0008
  have p0010 :=
    Nominal.mp p0002 p0009
  have p0011 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn)))) p0001 p0010
  have p0012 :=
    @g_mpd (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))) p0000 p0011
  have p0013 :=
    @g_simpr (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
  have p0014 :=
    @g_simpl (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
  have p0015 :=
    @g_hwcardssnc (syn_cvv)
  have p0016 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (.cv p) p0015
  have p0017 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv p) (syn_cncs)) p0014 p0016
  have p0018 :=
    @g_tccl D
  have p0019 :=
    Nominal.mp hyp_wppconcrete6dmpaircovndv_1 p0018
  have p0020 :=
    @g_tccl (syn_ctc D)
  have p0021 :=
    Nominal.mp p0019 p0020
  have p0022 :=
    @g_tccl (syn_ctc (syn_ctc D))
  have p0023 :=
    Nominal.mp p0021 p0022
  have p0024 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc D)))
  have p0025 :=
    Nominal.mp p0023 p0024
  have p0026 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))
  have p0027 :=
    Nominal.mp p0025 p0026
  have p0028 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))
  have p0029 :=
    Nominal.mp p0027 p0028
  have p0030 :=
    @g_a1i (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))) (syn_cncs)) (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) p0029
  have p0031 :=
    @g_jca (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (.classMem (.cv p) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))) (syn_cncs)) p0017 p0030
  have p0032 :=
    @g_tlecg (.cv p) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))
  have p0033 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (syn_wa (.classMem (.cv p) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))) (syn_cncs))) (syn_wb (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (syn_wbr (syn_ctc (.cv p)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))))) p0031 p0032
  have p0034 :=
    @g_mpbid (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (syn_wbr (syn_ctc (.cv p)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) p0013 p0033
  have p0035 :=
    @g_a1i (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) hyp_wppconcrete6dmpaircovndv_2
  have p0036 :=
    @g_jca (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (syn_wbr (syn_ctc (.cv p)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) p0034 p0035
  have p0037 :=
    @g_simpl (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
  have p0038 :=
    @g_hwcardssnc (syn_cvv)
  have p0039 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (.cv p) p0038
  have p0040 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv p) (syn_cncs)) p0037 p0039
  have p0041 :=
    @g_tccl (.cv p)
  have p0042 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (.classMem (.cv p) (syn_cncs)) (.classMem (syn_ctc (.cv p)) (syn_cncs)) p0040 p0041
  have p0043 :=
    @g_tccl D
  have p0044 :=
    Nominal.mp hyp_wppconcrete6dmpaircovndv_1 p0043
  have p0045 :=
    @g_tccl (syn_ctc D)
  have p0046 :=
    Nominal.mp p0044 p0045
  have p0047 :=
    @g_tccl (syn_ctc (syn_ctc D))
  have p0048 :=
    Nominal.mp p0046 p0047
  have p0049 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc D)))
  have p0050 :=
    Nominal.mp p0048 p0049
  have p0051 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))
  have p0052 :=
    Nominal.mp p0050 p0051
  have p0053 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))
  have p0054 :=
    Nominal.mp p0052 p0053
  have p0055 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))
  have p0056 :=
    Nominal.mp p0054 p0055
  have p0057 :=
    @g_a1i (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (syn_cncs)) (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) p0056
  have p0058 :=
    @g_tccl D
  have p0059 :=
    Nominal.mp hyp_wppconcrete6dmpaircovndv_1 p0058
  have p0060 :=
    @g_tccl (syn_ctc D)
  have p0061 :=
    Nominal.mp p0059 p0060
  have p0062 :=
    @g_tccl (syn_ctc (syn_ctc D))
  have p0063 :=
    Nominal.mp p0061 p0062
  have p0064 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc D)))
  have p0065 :=
    Nominal.mp p0063 p0064
  have p0066 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))
  have p0067 :=
    Nominal.mp p0065 p0066
  have p0068 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))
  have p0069 :=
    Nominal.mp p0067 p0068
  have p0070 :=
    @g_a1i (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))) (syn_cncs)) (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) p0069
  have p0071 :=
    @g_n_3jca (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (.classMem (syn_ctc (.cv p)) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))) (syn_cncs)) p0042 p0057 p0070
  have p0072 :=
    @g_lectr (syn_ctc (.cv p)) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))
  have p0073 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (syn_w3a (.classMem (syn_ctc (.cv p)) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))) (syn_cncs))) (.imp (syn_wa (syn_wbr (syn_ctc (.cv p)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (syn_wbr (syn_ctc (.cv p)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) p0071 p0072
  have p0074 :=
    @g_mpd (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (syn_wa (syn_wbr (syn_ctc (.cv p)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (syn_wbr (syn_ctc (.cv p)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) p0036 p0073
  have p0075 :=
    @g_simpl (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))
  have p0076 :=
    @g_hwcardstcclndv (.cv p)
  have p0077 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (syn_ctc (.cv p)) (syn_chwcards (syn_cvv))) p0075 p0076
  have p0078 :=
    @g_wppconcrete6dmcovndv D q dv_cache_0001 hyp_wppconcrete6dmpaircovndv_1
  have p0079 :=
    @g_id (.classEq (.cv q) (syn_ctc (.cv p)))
  have p0080 :=
    @g_breq1d (.classEq (.cv q) (syn_ctc (.cv p))) (.cv q) (syn_ctc (.cv p)) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))) (syn_clec) p0079
  have p0081 :=
    @g_id (.classEq (.cv q) (syn_ctc (.cv p)))
  have p0082 :=
    @g_eleq1d (.classEq (.cv q) (syn_ctc (.cv p))) (.cv q) (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn)) p0081
  have p0083 :=
    @g_imbi12d (.classEq (.cv q) (syn_ctc (.cv p))) (syn_wbr (.cv q) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (syn_wbr (syn_ctc (.cv p)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (.classMem (.cv q) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn))) p0080 p0082
  have p0084 :=
    @g_rspcv (.imp (syn_wbr (.cv q) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (.classMem (.cv q) (syn_cdm (syn_cwppconcrete6fn)))) (.imp (syn_wbr (syn_ctc (.cv p)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn)))) q (syn_ctc (.cv p)) (syn_chwcards (syn_cvv)) dv_cache_0005 dv_cache_0003 dv_cache_0006 p0083
  have p0085 :=
    @g_com12 (.classMem (syn_ctc (.cv p)) (syn_chwcards (syn_cvv))) (syn_wral q (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv q) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (.classMem (.cv q) (syn_cdm (syn_cwppconcrete6fn))))) (.imp (syn_wbr (syn_ctc (.cv p)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn)))) p0084
  have p0086 :=
    Nominal.mp p0078 p0085
  have p0087 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (.classMem (syn_ctc (.cv p)) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (syn_ctc (.cv p)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn)))) p0077 p0086
  have p0088 :=
    @g_mpd (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (syn_wbr (syn_ctc (.cv p)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn))) p0074 p0087
  have p0089 :=
    @g_jca (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D)))))))) (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn))) p0012 p0088
  have p0090 :=
    @g_ex (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn)))) p0089
  have p0091 :=
    @g_rgen (.imp (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc D))))))) (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn))))) p (syn_chwcards (syn_cvv)) p0090
  exact p0091

noncomputable def g_hncardnc1ndv
     :
    Nominal.NPrf (.classMem (syn_chncard (syn_c1c)) (syn_cncs)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_n_1cex
  have p0001 :=
    @g_hncardnc (syn_c1c)
  have p0002 :=
    Nominal.mp p0000 p0001
  exact p0002

noncomputable def g_wppconcrete6hncard1dmcovndv
    (p : Var) :
    Nominal.NPrf (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))))) := by
  let proofSupport : Finset Var := ({p} : Finset Var)
  have dv_cache_0001 : p ∉ ((syn_chncard (syn_c1c))).fv := by
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_n_1cex
  have p0001 :=
    @g_hncardnc (syn_c1c)
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_wppconcrete6dmcovndv (syn_chncard (syn_c1c)) p dv_cache_0001 p0002
  exact p0003

noncomputable def g_wppconcrete6hncard1dmpaircovndv
    (p : Var) (hyp_wppconcrete6hncard1dmpaircovndv_1 : Nominal.NPrf (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) :
    Nominal.NPrf (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn)))))) := by
  let proofSupport : Finset Var := ({p} : Finset Var)
  have dv_cache_0001 : p ∉ ((syn_chncard (syn_c1c))).fv := by
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_n_1cex
  have p0001 :=
    @g_hncardnc (syn_c1c)
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_wppconcrete6dmpaircovndv (syn_chncard (syn_c1c)) p dv_cache_0001 p0002 hyp_wppconcrete6hncard1dmpaircovndv_1
  exact p0003

noncomputable def g_hncardtcshiftcondndv
    (A : Class) (hyp_hncardtcshiftcondndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_hncardtcshiftcondndv_2 : Nominal.NPrf (syn_wbr (syn_cpw1 (syn_chnord A)) (syn_cen) (syn_chnord (syn_cpw1 A)))) :
    Nominal.NPrf (.classEq (syn_ctc (syn_chncard A)) (syn_chncard (syn_cpw1 A))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_hncardtc A hyp_hncardtcshiftcondndv_1
  have p0001 :=
    @g_hnordex A hyp_hncardtcshiftcondndv_1
  have p0002 :=
    @g_pw1ex (syn_chnord A) p0001
  have p0003 :=
    @g_eqnc (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A)) p0002
  have p0004 :=
    @g_mpbir (.classEq (syn_cnc (syn_cpw1 (syn_chnord A))) (syn_cnc (syn_chnord (syn_cpw1 A)))) (syn_wbr (syn_cpw1 (syn_chnord A)) (syn_cen) (syn_chnord (syn_cpw1 A))) hyp_hncardtcshiftcondndv_2 p0003
  have p0005 :=
    @g_eqtri (syn_ctc (syn_chncard A)) (syn_cnc (syn_cpw1 (syn_chnord A))) (syn_cnc (syn_chnord (syn_cpw1 A))) p0000 p0004
  have p0006 :=
    (by simpa [syn_chncard] using (Nominal.classEqRefl (syn_chncard (syn_cpw1 A))))
  have p0007 :=
    @g_eqtr4i (syn_ctc (syn_chncard A)) (syn_cnc (syn_chnord (syn_cpw1 A))) (syn_chncard (syn_cpw1 A)) p0005 p0006
  exact p0007

noncomputable def g_hnsicodeliftfnexndv
     :
    Nominal.NPrf (.classMem (syn_chnsicodeliftfn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_chnsicodeliftfn] using (Nominal.classEqRefl (syn_chnsicodeliftfn)))
  have p0001 :=
    @g_lnpwsirelfnex
  have p0002 :=
    @g_lnpwpw1secondfnex
  have p0003 :=
    @g_txpex (syn_clnpwsirelfn) (syn_clnpwpw1secondfn) p0001 p0002
  have p0004 :=
    @g_eqeltri (syn_chnsicodeliftfn) (syn_ctxp (syn_clnpwsirelfn) (syn_clnpwpw1secondfn)) (syn_cvv) p0000 p0003
  exact p0004

noncomputable def g_hnsicodeliftfnfnndv
     :
    Nominal.NPrf (syn_wfn (syn_chnsicodeliftfn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_lnpwsirelfnfn
  have p0001 :=
    @g_lnpwpw1secondfnfn
  have p0002 :=
    @g_pm3_2i (syn_wfn (syn_clnpwsirelfn) (syn_cvv)) (syn_wfn (syn_clnpwpw1secondfn) (syn_cvv)) p0000 p0001
  have p0003 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_clnpwsirelfn) (syn_clnpwpw1secondfn)
  have p0004 :=
    Nominal.mp p0002 p0003
  have p0005 :=
    @g_inidm (syn_cvv)
  have p0006 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_clnpwsirelfn) (syn_clnpwpw1secondfn)) p0005
  have p0007 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_clnpwsirelfn) (syn_clnpwpw1secondfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_clnpwsirelfn) (syn_clnpwpw1secondfn)) (syn_cvv)) p0004 p0006
  have p0008 :=
    (by simpa [syn_chnsicodeliftfn] using (Nominal.classEqRefl (syn_chnsicodeliftfn)))
  have p0009 :=
    @g_fneq1i (syn_cvv) (syn_chnsicodeliftfn) (syn_ctxp (syn_clnpwsirelfn) (syn_clnpwpw1secondfn)) p0008
  have p0010 :=
    @g_mpbir (syn_wfn (syn_chnsicodeliftfn) (syn_cvv)) (syn_wfn (syn_ctxp (syn_clnpwsirelfn) (syn_clnpwpw1secondfn)) (syn_cvv)) p0007 p0009
  exact p0010

noncomputable def g_sisuppdndv
    (ph : Wff) (D : Class) (R : Class) (hyp_sisuppdndv_1 : Nominal.NPrf (.imp ph (syn_wss R (syn_cxp D D)))) :
    Nominal.NPrf (.imp ph (syn_wss (syn_csi R) (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))) := by
  let proofSupport : Finset Var := ph.fv ∪ D.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_ph : x ∉ ph.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_w_not_D : w ∉ D.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_R : w ∉ R.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_x_ne_w : x ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_w_ne_x : w ≠ x :=
    Ne.symm fresh_x_ne_w
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have fresh_y_ne_w : y ≠ w := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_w_ne_y : w ≠ y :=
    Ne.symm fresh_y_ne_w
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have dv_cache_0001 : z ∉ ((Class.cv x)).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : w ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : w ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : w ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : z ≠ w := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have dv_cache_0008 : z ∉ ((Wff.classMem (syn_cop (.cv x) (.cv y)) (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : w ∉ ((Wff.classMem (syn_cop (.cv x) (.cv y)) (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, fresh_w_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : z ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : w ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((syn_csi R)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : y ∉ ((syn_csi R)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : x ∉ ((syn_cxp (syn_cpw1 D) (syn_cpw1 D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : y ∉ ((syn_cxp (syn_cpw1 D) (syn_cpw1 D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : x ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : y ∉ (ph).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv x) (syn_csi R) (.cv y))))
  have p0001 :=
    @g_biimpri (syn_wbr (.cv x) (syn_csi R) (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) (syn_csi R)) p0000
  have p0002 :=
    @g_brsi z w (.cv x) (.cv y) R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0003 :=
    @g_a1i (syn_wb (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w)))))) (.classMem (syn_cop (.cv x) (.cv y)) (syn_csi R)) p0002
  have p0004 :=
    @g_mpbid (.classMem (syn_cop (.cv x) (.cv y)) (syn_csi R)) (syn_wbr (.cv x) (syn_csi R) (.cv y)) (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w))))) p0001 p0003
  have p0005 :=
    @g_a1i (.imp (.classMem (syn_cop (.cv x) (.cv y)) (syn_csi R)) (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w)))))) ph p0004
  have p0006 :=
    @g_simp3 (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w))
  have p0007 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv z) R (.cv w))))
  have p0008 :=
    @g_a1i (syn_wb (syn_wbr (.cv z) R (.cv w)) (.classMem (syn_cop (.cv z) (.cv w)) R)) (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w))) p0007
  have p0009 :=
    @g_mpbid (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w))) (syn_wbr (.cv z) R (.cv w)) (.classMem (syn_cop (.cv z) (.cv w)) R) p0006 p0008
  have p0010 :=
    @g_a1i (.imp (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w))) (.classMem (syn_cop (.cv z) (.cv w)) R)) ph p0009
  have p0011 :=
    @g_sseld ph R (syn_cxp D D) (syn_cop (.cv z) (.cv w)) hyp_sisuppdndv_1
  have p0012 :=
    @g_syld ph (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w))) (.classMem (syn_cop (.cv z) (.cv w)) R) (.classMem (syn_cop (.cv z) (.cv w)) (syn_cxp D D)) p0010 p0011
  have p0013 :=
    @g_opelxp (.cv z) (.cv w) D D
  have p0014 :=
    @g_biimpi (.classMem (syn_cop (.cv z) (.cv w)) (syn_cxp D D)) (syn_wa (.classMem (.cv z) D) (.classMem (.cv w) D)) p0013
  have p0015 :=
    @g_syl6 ph (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w))) (.classMem (syn_cop (.cv z) (.cv w)) (syn_cxp D D)) (syn_wa (.classMem (.cv z) D) (.classMem (.cv w) D)) p0012 p0014
  have p0016 :=
    @g_simpl (.classMem (.cv z) D) (.classMem (.cv w) D)
  have p0017 :=
    @g_syl6 ph (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w))) (syn_wa (.classMem (.cv z) D) (.classMem (.cv w) D)) (.classMem (.cv z) D) p0015 p0016
  have p0018 :=
    @g_snelpw1 (.cv z) D
  have p0019 :=
    @g_biimpri (.classMem (syn_csn (.cv z)) (syn_cpw1 D)) (.classMem (.cv z) D) p0018
  have p0020 :=
    @g_simp1 (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w))
  have p0021 :=
    @g_eleq1d (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w))) (.cv x) (syn_csn (.cv z)) (syn_cpw1 D) p0020
  have p0022 :=
    @g_biimprd (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w))) (.classMem (.cv x) (syn_cpw1 D)) (.classMem (syn_csn (.cv z)) (syn_cpw1 D)) p0021
  have p0023 :=
    @g_syl5 (.classMem (.cv z) D) (.classMem (syn_csn (.cv z)) (syn_cpw1 D)) (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w))) (.classMem (.cv x) (syn_cpw1 D)) p0019 p0022
  have p0024 :=
    @g_a1i (.imp (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w))) (.imp (.classMem (.cv z) D) (.classMem (.cv x) (syn_cpw1 D)))) ph p0023
  have p0025 :=
    @g_mpdd ph (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w))) (.classMem (.cv z) D) (.classMem (.cv x) (syn_cpw1 D)) p0017 p0024
  have p0026 :=
    @g_simp3 (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w))
  have p0027 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv z) R (.cv w))))
  have p0028 :=
    @g_a1i (syn_wb (syn_wbr (.cv z) R (.cv w)) (.classMem (syn_cop (.cv z) (.cv w)) R)) (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w))) p0027
  have p0029 :=
    @g_mpbid (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w))) (syn_wbr (.cv z) R (.cv w)) (.classMem (syn_cop (.cv z) (.cv w)) R) p0026 p0028
  have p0030 :=
    @g_a1i (.imp (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w))) (.classMem (syn_cop (.cv z) (.cv w)) R)) ph p0029
  have p0031 :=
    @g_sseld ph R (syn_cxp D D) (syn_cop (.cv z) (.cv w)) hyp_sisuppdndv_1
  have p0032 :=
    @g_syld ph (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w))) (.classMem (syn_cop (.cv z) (.cv w)) R) (.classMem (syn_cop (.cv z) (.cv w)) (syn_cxp D D)) p0030 p0031
  have p0033 :=
    @g_opelxp (.cv z) (.cv w) D D
  have p0034 :=
    @g_biimpi (.classMem (syn_cop (.cv z) (.cv w)) (syn_cxp D D)) (syn_wa (.classMem (.cv z) D) (.classMem (.cv w) D)) p0033
  have p0035 :=
    @g_syl6 ph (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w))) (.classMem (syn_cop (.cv z) (.cv w)) (syn_cxp D D)) (syn_wa (.classMem (.cv z) D) (.classMem (.cv w) D)) p0032 p0034
  have p0036 :=
    @g_simpr (.classMem (.cv z) D) (.classMem (.cv w) D)
  have p0037 :=
    @g_syl6 ph (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w))) (syn_wa (.classMem (.cv z) D) (.classMem (.cv w) D)) (.classMem (.cv w) D) p0035 p0036
  have p0038 :=
    @g_snelpw1 (.cv w) D
  have p0039 :=
    @g_biimpri (.classMem (syn_csn (.cv w)) (syn_cpw1 D)) (.classMem (.cv w) D) p0038
  have p0040 :=
    @g_simp2 (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w))
  have p0041 :=
    @g_eleq1d (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w))) (.cv y) (syn_csn (.cv w)) (syn_cpw1 D) p0040
  have p0042 :=
    @g_biimprd (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w))) (.classMem (.cv y) (syn_cpw1 D)) (.classMem (syn_csn (.cv w)) (syn_cpw1 D)) p0041
  have p0043 :=
    @g_syl5 (.classMem (.cv w) D) (.classMem (syn_csn (.cv w)) (syn_cpw1 D)) (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w))) (.classMem (.cv y) (syn_cpw1 D)) p0039 p0042
  have p0044 :=
    @g_a1i (.imp (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w))) (.imp (.classMem (.cv w) D) (.classMem (.cv y) (syn_cpw1 D)))) ph p0043
  have p0045 :=
    @g_mpdd ph (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w))) (.classMem (.cv w) D) (.classMem (.cv y) (syn_cpw1 D)) p0037 p0044
  have p0046 :=
    @g_jcad ph (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w))) (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D)) p0025 p0045
  have p0047 :=
    @g_opelxp (.cv x) (.cv y) (syn_cpw1 D) (syn_cpw1 D)
  have p0048 :=
    @g_biimpri (.classMem (syn_cop (.cv x) (.cv y)) (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) p0047
  have p0049 :=
    @g_syl6 ph (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w))) (syn_wa (.classMem (.cv x) (syn_cpw1 D)) (.classMem (.cv y) (syn_cpw1 D))) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) p0046 p0048
  have p0050 :=
    @g_exlimdvv ph (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w))) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) z w dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 p0049
  have p0051 :=
    @g_syld ph (.classMem (syn_cop (.cv x) (.cv y)) (syn_csi R)) (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv y) (syn_csn (.cv w))) (syn_wbr (.cv z) R (.cv w))))) (.classMem (syn_cop (.cv x) (.cv y)) (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) p0005 p0050
  have p0052 :=
    @g_relssdv ph x y (syn_csi R) (syn_cxp (syn_cpw1 D) (syn_cpw1 D)) dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 p0051
  exact p0052

noncomputable def g_hnsicodeliftcodeclndv
    (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf (.imp (.classMem (.cv u) (syn_chwcn A)) (.classMem (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcn (syn_cpw1 A)))) := by
  let proofSupport : Finset Var := ({u} : Finset Var) ∪ A.fv
  have dv_cache_0001 : u ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : Disjoint ((syn_cpw1 A)).fv ((syn_csi (syn_cfv (syn_c1st) (.cv u)))).fv := by
    clear dv_cache_0001
    exact (show Disjoint ((syn_cpw1 A)).fv ((syn_csi (syn_cfv (syn_c1st) (.cv u)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi]; exact (show Disjoint ((A).fv) (((syn_cfv (syn_c1st) (.cv u))).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv]; exact (show Disjoint ((A).fv) ((((Class.cv u)).fv) ∪ (((syn_c1st)).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint ((A).fv) (((Class.cv u)).fv) from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({u} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show u ∉ (A).fv from (by exact dv_A_u)))))), (show Disjoint ((A).fv) (((syn_c1st)).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st]; exact (show Disjoint ((A).fv) ((∅ : Finset Var)) from (by simp))))⟩))))))
  have p0000 :=
    @g_hwcnwendv u A dv_cache_0001
  have p0001 :=
    @g_siwendv (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u))
  have p0002 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A)) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cwe) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) p0000 p0001
  have p0003 :=
    @g_hwcnbase u A dv_cache_0001
  have p0004 :=
    @g_pw1ss (syn_cfv (syn_c2nd) (.cv u)) A
  have p0005 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A)) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) A) (syn_wss (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))) (syn_cpw1 A)) p0003 p0004
  have p0006 :=
    @g_jca (.classMem (.cv u) (syn_chwcn A)) (syn_wbr (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cwe) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_wss (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))) (syn_cpw1 A)) p0002 p0005
  have p0007 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0008 :=
    @g_siex (syn_cfv (syn_c1st) (.cv u)) p0007
  have p0009 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0010 :=
    @g_pw1ex (syn_cfv (syn_c2nd) (.cv u)) p0009
  have p0011 :=
    @g_elhwcodes (syn_cpw1 A) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))) (syn_csi (syn_cfv (syn_c1st) (.cv u))) dv_cache_0002 p0008 p0010
  have p0012 :=
    @g_biimpri (.classMem (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcodes (syn_cpw1 A))) (syn_wa (syn_wbr (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cwe) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_wss (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))) (syn_cpw1 A))) p0011
  have p0013 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A)) (syn_wa (syn_wbr (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cwe) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_wss (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))) (syn_cpw1 A))) (.classMem (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcodes (syn_cpw1 A))) p0006 p0012
  have p0014 :=
    @g_hwcnsupp u A
  have p0015 :=
    @g_sisuppdndv (.classMem (.cv u) (syn_chwcn A)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) p0014
  have p0016 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0017 :=
    @g_siex (syn_cfv (syn_c1st) (.cv u)) p0016
  have p0018 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0019 :=
    @g_pw1ex (syn_cfv (syn_c2nd) (.cv u)) p0018
  have p0020 :=
    @g_opfv1st (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))) p0017 p0019
  have p0021 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0022 :=
    @g_siex (syn_cfv (syn_c1st) (.cv u)) p0021
  have p0023 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0024 :=
    @g_pw1ex (syn_cfv (syn_c2nd) (.cv u)) p0023
  have p0025 :=
    @g_opfv2nd (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))) p0022 p0024
  have p0026 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0027 :=
    @g_siex (syn_cfv (syn_c1st) (.cv u)) p0026
  have p0028 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0029 :=
    @g_pw1ex (syn_cfv (syn_c2nd) (.cv u)) p0028
  have p0030 :=
    @g_opfv2nd (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))) p0027 p0029
  have p0031 :=
    @g_xpeq12i (syn_cfv (syn_c2nd) (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c2nd) (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))) p0025 p0030
  have p0032 :=
    @g_sseq12i (syn_cfv (syn_c1st) (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c2nd) (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))) (syn_cxp (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) p0020 p0031
  have p0033 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn A)) (syn_wss (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cxp (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c2nd) (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) p0015 p0032
  have p0034 :=
    @g_jca (.classMem (.cv u) (syn_chwcn A)) (.classMem (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcodes (syn_cpw1 A))) (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c2nd) (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))))) p0013 p0033
  have p0035 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0036 :=
    @g_siex (syn_cfv (syn_c1st) (.cv u)) p0035
  have p0037 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0038 :=
    @g_pw1ex (syn_cfv (syn_c2nd) (.cv u)) p0037
  have p0039 :=
    @g_opex (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))) p0036 p0038
  have p0040 :=
    @g_elhwcncl (syn_cpw1 A) (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))
  have p0041 :=
    Nominal.mp p0039 p0040
  have p0042 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcodes (syn_cpw1 A))) (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (syn_cfv (syn_c2nd) (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))))) (.classMem (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv u))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_chwcn (syn_cpw1 A))) p0034 p0041
  exact p0042

noncomputable def g_hnsicodeliftfnvalgndv
    (D : Class) (R : Class) (hyp_hnsicodeliftfnvalgndv_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_hnsicodeliftfnvalgndv_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (.classEq (syn_cfv (syn_chnsicodeliftfn) (syn_csn (syn_cop R D))) (syn_cop (syn_csi R) (syn_cpw1 D)))) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_chnsicodeliftfn] using (Nominal.classEqRefl (syn_chnsicodeliftfn)))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_cop R D)) (syn_chnsicodeliftfn) (syn_ctxp (syn_clnpwsirelfn) (syn_clnpwpw1secondfn)) p0000
  have p0002 :=
    @g_lnpwsirelfnfn
  have p0003 :=
    @g_lnpwpw1secondfnfn
  have p0004 :=
    @g_snex (syn_cop R D)
  have p0005 :=
    @g_fvtxpvv (syn_csn (syn_cop R D)) (syn_clnpwsirelfn) (syn_clnpwpw1secondfn) p0002 p0003 p0004
  have p0006 :=
    @g_eqtri (syn_cfv (syn_chnsicodeliftfn) (syn_csn (syn_cop R D))) (syn_cfv (syn_ctxp (syn_clnpwsirelfn) (syn_clnpwpw1secondfn)) (syn_csn (syn_cop R D))) (syn_cop (syn_cfv (syn_clnpwsirelfn) (syn_csn (syn_cop R D))) (syn_cfv (syn_clnpwpw1secondfn) (syn_csn (syn_cop R D)))) p0001 p0005
  have p0007 :=
    @g_a1i (.classEq (syn_cfv (syn_chnsicodeliftfn) (syn_csn (syn_cop R D))) (syn_cop (syn_cfv (syn_clnpwsirelfn) (syn_csn (syn_cop R D))) (syn_cfv (syn_clnpwpw1secondfn) (syn_csn (syn_cop R D))))) (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) p0006
  have p0008 :=
    @g_lnpwsirelfnvalg D R hyp_hnsicodeliftfnvalgndv_1 hyp_hnsicodeliftfnvalgndv_2
  have p0009 :=
    @g_lnpwpw1secondfnval D R hyp_hnsicodeliftfnvalgndv_1 hyp_hnsicodeliftfnvalgndv_2
  have p0010 :=
    @g_a1i (.classEq (syn_cfv (syn_clnpwpw1secondfn) (syn_csn (syn_cop R D))) (syn_cpw1 D)) (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) p0009
  have p0011 :=
    @g_opeq12d (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (syn_cfv (syn_clnpwsirelfn) (syn_csn (syn_cop R D))) (syn_csi R) (syn_cfv (syn_clnpwpw1secondfn) (syn_csn (syn_cop R D))) (syn_cpw1 D) p0008 p0010
  have p0012 :=
    @g_eqtrd (syn_wss R (syn_cxp (syn_cvv) (syn_cvv))) (syn_cfv (syn_chnsicodeliftfn) (syn_csn (syn_cop R D))) (syn_cop (syn_cfv (syn_clnpwsirelfn) (syn_csn (syn_cop R D))) (syn_cfv (syn_clnpwpw1secondfn) (syn_csn (syn_cop R D)))) (syn_cop (syn_csi R) (syn_cpw1 D)) p0007 p0011
  exact p0012

#print axioms g_hnsicodeliftfnvalgndv

end NFChoice.DirectNominalPrf.WPPReplay
