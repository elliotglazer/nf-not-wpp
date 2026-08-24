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
import NominalWPPReplayChunk017Compact001Part054

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

noncomputable def g_wppconcrete6stoppedtchomndv
    (x : Var) (hyp_wppconcrete6stoppedtchomndv_1 : Nominal.NPrf (syn_wss (syn_crn (syn_cwppconcrete6fn)) (syn_chwcards (syn_cvv)))) (hyp_wppconcrete6stoppedtchomndv_2 : Nominal.NPrf (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf (syn_wral x (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (.classEq (syn_ctc (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.cv x))) (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_ctc (.cv x))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var)
  let p : Var := freshVar proofSupport 0
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_ne_x : p ≠ x := by
    intro h
    exact fresh_p (Finset.mem_singleton.mpr h)
  have fresh_x_ne_p : x ≠ p :=
    Ne.symm fresh_p_ne_x
  have dv_cache_0001 : p ∉ ((Class.cv x)).fv := by
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((syn_chwcards (syn_cvv))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : p ∉ ((Wff.imp (syn_wbr (.cv x) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wa (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (syn_ctc (.cv x)) (syn_cdm (syn_cwppconcrete6fn)))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppconcrete6fn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_wppconcrete6fnfunsndv
  have p0001 :=
    @g_wppstopstepdmndv (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_cwppconcrete6fn) p0000 hyp_wppconcrete6stoppedtchomndv_1
  have p0002 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_chwcards (syn_cvv)) (.cv x) p0001
  have p0003 :=
    @g_biimpi (.classMem (.cv x) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (.classMem (.cv x) (syn_chwcards (syn_cvv))) p0002
  have p0004 :=
    @g_id (.classMem (.cv x) (syn_chwcards (syn_cvv)))
  have p0005 :=
    @g_wppconcrete6thresholdtclecndv
  have p0006 :=
    @g_wppconcrete6hncard1dmpaircovndv p p0005
  have p0007 :=
    @g_a1i (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn)))))) (.classMem (.cv x) (syn_chwcards (syn_cvv))) p0006
  have p0008 :=
    @g_id (.classEq (.cv p) (.cv x))
  have p0009 :=
    @g_breq1d (.classEq (.cv p) (.cv x)) (.cv p) (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) p0008
  have p0010 :=
    @g_id (.classEq (.cv p) (.cv x))
  have p0011 :=
    @g_eleq1d (.classEq (.cv p) (.cv x)) (.cv p) (.cv x) (syn_cdm (syn_cwppconcrete6fn)) p0010
  have p0012 :=
    @g_id (.classEq (.cv p) (.cv x))
  have p0013 :=
    @g_tceq (.cv p) (.cv x)
  have p0014 :=
    @g_syl (.classEq (.cv p) (.cv x)) (.classEq (.cv p) (.cv x)) (.classEq (syn_ctc (.cv p)) (syn_ctc (.cv x))) p0012 p0013
  have p0015 :=
    @g_eleq1d (.classEq (.cv p) (.cv x)) (syn_ctc (.cv p)) (syn_ctc (.cv x)) (syn_cdm (syn_cwppconcrete6fn)) p0014
  have p0016 :=
    @g_anbi12d (.classEq (.cv p) (.cv x)) (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (syn_ctc (.cv x)) (syn_cdm (syn_cwppconcrete6fn))) p0011 p0015
  have p0017 :=
    @g_imbi12d (.classEq (.cv p) (.cv x)) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wbr (.cv x) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn)))) (syn_wa (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (syn_ctc (.cv x)) (syn_cdm (syn_cwppconcrete6fn)))) p0009 p0016
  have p0018 :=
    @g_rspcv (.imp (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn))))) (.imp (syn_wbr (.cv x) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wa (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (syn_ctc (.cv x)) (syn_cdm (syn_cwppconcrete6fn))))) p (.cv x) (syn_chwcards (syn_cvv)) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0017
  have p0019 :=
    @g_mpd (.classMem (.cv x) (syn_chwcards (syn_cvv))) (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn)))))) (.imp (syn_wbr (.cv x) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wa (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (syn_ctc (.cv x)) (syn_cdm (syn_cwppconcrete6fn))))) p0007 p0018
  have p0020 :=
    @g_wppconcrete6thresholdtclecndv
  have p0021 :=
    @g_wppconcrete6hncard1dmpaircovndv p p0020
  have p0022 :=
    @g_a1i (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn)))))) (.classMem (.cv x) (syn_chwcards (syn_cvv))) p0021
  have p0023 :=
    @g_id (.classEq (.cv p) (.cv x))
  have p0024 :=
    @g_breq1d (.classEq (.cv p) (.cv x)) (.cv p) (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) p0023
  have p0025 :=
    @g_id (.classEq (.cv p) (.cv x))
  have p0026 :=
    @g_eleq1d (.classEq (.cv p) (.cv x)) (.cv p) (.cv x) (syn_cdm (syn_cwppconcrete6fn)) p0025
  have p0027 :=
    @g_id (.classEq (.cv p) (.cv x))
  have p0028 :=
    @g_tceq (.cv p) (.cv x)
  have p0029 :=
    @g_syl (.classEq (.cv p) (.cv x)) (.classEq (.cv p) (.cv x)) (.classEq (syn_ctc (.cv p)) (syn_ctc (.cv x))) p0027 p0028
  have p0030 :=
    @g_eleq1d (.classEq (.cv p) (.cv x)) (syn_ctc (.cv p)) (syn_ctc (.cv x)) (syn_cdm (syn_cwppconcrete6fn)) p0029
  have p0031 :=
    @g_anbi12d (.classEq (.cv p) (.cv x)) (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (syn_ctc (.cv x)) (syn_cdm (syn_cwppconcrete6fn))) p0026 p0030
  have p0032 :=
    @g_imbi12d (.classEq (.cv p) (.cv x)) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wbr (.cv x) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn)))) (syn_wa (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (syn_ctc (.cv x)) (syn_cdm (syn_cwppconcrete6fn)))) p0024 p0031
  have p0033 :=
    @g_rspcv (.imp (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn))))) (.imp (syn_wbr (.cv x) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wa (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (syn_ctc (.cv x)) (syn_cdm (syn_cwppconcrete6fn))))) p (.cv x) (syn_chwcards (syn_cvv)) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0032
  have p0034 :=
    @g_mpd (.classMem (.cv x) (syn_chwcards (syn_cvv))) (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppconcrete6fn)))))) (.imp (syn_wbr (.cv x) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wa (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (syn_ctc (.cv x)) (syn_cdm (syn_cwppconcrete6fn))))) p0022 p0033
  have p0035 :=
    @g_simpl (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (syn_ctc (.cv x)) (syn_cdm (syn_cwppconcrete6fn)))
  have p0036 :=
    @g_syl6 (.classMem (.cv x) (syn_chwcards (syn_cvv))) (syn_wbr (.cv x) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wa (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (syn_ctc (.cv x)) (syn_cdm (syn_cwppconcrete6fn)))) (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn))) p0034 p0035
  have p0037 :=
    @g_wppconcrete6tchomdmndv x
  have p0038 :=
    @g_syl6 (.classMem (.cv x) (syn_chwcards (syn_cvv))) (syn_wbr (.cv x) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn))) (.classEq (syn_ctc (syn_cfv (syn_cwppconcrete6fn) (.cv x))) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (.cv x)))) p0036 p0037
  have p0039 :=
    @g_n_3jca (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wa (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (syn_ctc (.cv x)) (syn_cdm (syn_cwppconcrete6fn))))) (.imp (syn_wbr (.cv x) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.classEq (syn_ctc (syn_cfv (syn_cwppconcrete6fn) (.cv x))) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (.cv x))))) p0004 p0019 p0038
  have p0040 :=
    @g_wppconcrete6fnfunsndv
  have p0041 :=
    @g_wppstopsteptchomdndv x (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_cwppconcrete6fn) p0040 hyp_wppconcrete6stoppedtchomndv_1 hyp_wppconcrete6stoppedtchomndv_2
  have p0042 :=
    @g_syl (.classMem (.cv x) (syn_chwcards (syn_cvv))) (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wa (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (syn_ctc (.cv x)) (syn_cdm (syn_cwppconcrete6fn))))) (.imp (syn_wbr (.cv x) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.classEq (syn_ctc (syn_cfv (syn_cwppconcrete6fn) (.cv x))) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (.cv x)))))) (.classEq (syn_ctc (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.cv x))) (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_ctc (.cv x)))) p0039 p0041
  have p0043 :=
    @g_syl (.classMem (.cv x) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.classEq (syn_ctc (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.cv x))) (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_ctc (.cv x)))) p0003 p0042
  have p0044 :=
    @g_rgen (.classEq (syn_ctc (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.cv x))) (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_ctc (.cv x)))) x (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) p0043
  exact p0044

noncomputable def g_wppconcrete6rnhwcardsredndv
    (u : Var) (hyp_wppconcrete6rnhwcardsredndv_1 : Nominal.NPrf (syn_wral u (syn_cvv) (.classMem (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv u))))) (syn_chwcards (syn_cvv))))) :
    Nominal.NPrf (syn_wss (syn_crn (syn_cwppconcrete6fn)) (syn_chwcards (syn_cvv))) := by
  let proofSupport : Finset Var := ({u} : Finset Var)
  let x : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_u : x ≠ u := by
    intro h
    exact fresh_x (Finset.mem_singleton.mpr h)
  have fresh_u_ne_x : u ≠ x :=
    Ne.symm fresh_x_ne_u
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_ne_u : z ≠ u := by
    intro h
    exact fresh_z (Finset.mem_singleton.mpr h)
  have fresh_u_ne_z : u ≠ z :=
    Ne.symm fresh_z_ne_u
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have dv_cache_0001 : x ≠ z := by
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0002 : u ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : u ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : u ∉ ((Wff.classMem (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv z))))) (syn_chwcards (syn_cvv)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((Wff.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv x)) (syn_chwcards (syn_cvv)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppconcrete6fn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_crn (syn_cwppcardt6fn))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcardt6fn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_chwcards (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_cwppconcrete6fn)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppconcrete6fn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_wppconcrete6fnfnndv
  have p0001 :=
    @g_wppconcrete6fndmndv
  have p0002 :=
    @g_eleq2i (syn_cdm (syn_cwppconcrete6fn)) (syn_crn (syn_cwppcardt6fn)) (.cv x) p0001
  have p0003 :=
    @g_biimpri (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (.cv x) (syn_crn (syn_cwppcardt6fn))) p0002
  have p0004 :=
    @g_wppconcrete6dmrepdndv x z dv_cache_0001
  have p0005 :=
    @g_id (.classEq (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
  have p0006 :=
    @g_fveq2d (.classEq (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))) (syn_cwppconcrete6fn) p0005
  have p0007 :=
    @g_vex z
  have p0008 :=
    @g_wppconcrete6fnvalndv (.cv z) p0007
  have p0009 :=
    @g_a1i (.classEq (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv z)))))) (.classEq (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) p0008
  have p0010 :=
    @g_eqtrd (.classEq (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) (syn_cfv (syn_cwppconcrete6fn) (.cv x)) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv z))))) p0006 p0009
  have p0011 :=
    @g_vex z
  have p0012 :=
    @g_id (.classEq (.cv u) (.cv z))
  have p0013 :=
    @g_pweqd (.classEq (.cv u) (.cv z)) (.cv u) (.cv z) p0012
  have p0014 :=
    @g_pweqd (.classEq (.cv u) (.cv z)) (syn_cpw (.cv u)) (syn_cpw (.cv z)) p0013
  have p0015 :=
    @g_hnordeqdndv (syn_cpw (syn_cpw (.cv u))) (syn_cpw (syn_cpw (.cv z)))
  have p0016 :=
    @g_syl (.classEq (.cv u) (.cv z)) (.classEq (syn_cpw (syn_cpw (.cv u))) (syn_cpw (syn_cpw (.cv z)))) (.classEq (syn_chnord (syn_cpw (syn_cpw (.cv u)))) (syn_chnord (syn_cpw (syn_cpw (.cv z))))) p0014 p0015
  have p0017 :=
    @g_hncardeqdndv (syn_chnord (syn_cpw (syn_cpw (.cv u)))) (syn_chnord (syn_cpw (syn_cpw (.cv z))))
  have p0018 :=
    @g_syl (.classEq (.cv u) (.cv z)) (.classEq (syn_chnord (syn_cpw (syn_cpw (.cv u)))) (syn_chnord (syn_cpw (syn_cpw (.cv z))))) (.classEq (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv u))))) (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv z)))))) p0016 p0017
  have p0019 :=
    @g_eleq1d (.classEq (.cv u) (.cv z)) (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv u))))) (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv z))))) (syn_chwcards (syn_cvv)) p0018
  have p0020 :=
    @g_rspcv (.classMem (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv u))))) (syn_chwcards (syn_cvv))) (.classMem (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv z))))) (syn_chwcards (syn_cvv))) u (.cv z) (syn_cvv) dv_cache_0002 dv_cache_0003 dv_cache_0004 p0019
  have p0021 :=
    @g_mpi (.classMem (.cv z) (syn_cvv)) (syn_wral u (syn_cvv) (.classMem (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv u))))) (syn_chwcards (syn_cvv)))) (.classMem (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv z))))) (syn_chwcards (syn_cvv))) hyp_wppconcrete6rnhwcardsredndv_1 p0020
  have p0022 :=
    Nominal.mp p0011 p0021
  have p0023 :=
    @g_a1i (.classMem (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv z))))) (syn_chwcards (syn_cvv))) (.classEq (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) p0022
  have p0024 :=
    @g_eqeltrd (.classEq (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) (syn_cfv (syn_cwppconcrete6fn) (.cv x)) (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv z))))) (syn_chwcards (syn_cvv)) p0010 p0023
  have p0025 :=
    @g_exlimiv (.classEq (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv x)) (syn_chwcards (syn_cvv))) z dv_cache_0005 p0024
  have p0026 :=
    @g_syl (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn))) (syn_wex z (.classEq (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))) (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv x)) (syn_chwcards (syn_cvv))) p0004 p0025
  have p0027 :=
    @g_syl (.classMem (.cv x) (syn_crn (syn_cwppcardt6fn))) (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv x)) (syn_chwcards (syn_cvv))) p0003 p0026
  have p0028 :=
    @g_rgen (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv x)) (syn_chwcards (syn_cvv))) x (syn_crn (syn_cwppcardt6fn)) p0027
  have p0029 :=
    @g_pm3_2i (syn_wfn (syn_cwppconcrete6fn) (syn_crn (syn_cwppcardt6fn))) (syn_wral x (syn_crn (syn_cwppcardt6fn)) (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv x)) (syn_chwcards (syn_cvv)))) p0000 p0028
  have p0030 :=
    @g_fnfvrnss x (syn_crn (syn_cwppcardt6fn)) (syn_chwcards (syn_cvv)) (syn_cwppconcrete6fn) dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0031 :=
    Nominal.mp p0029 p0030
  exact p0031

noncomputable def g_wppfreceqexndv
    (F : Class) (G : Class) (I : Class) (hyp_wppfreceqexndv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppfreceqexndv_2 : Nominal.NPrf (.classMem G (syn_cfuns))) :
    Nominal.NPrf (.classMem (syn_cwppfreceq F G I) (syn_cvv)) := by
  let proofSupport : Finset Var := F.fv ∪ G.fv ∪ I.fv
  have p0000 :=
    (by simpa [syn_cwppfreceq] using (Nominal.classEqRefl (syn_cwppfreceq F G I)))
  have p0001 :=
    @g_eqid (syn_cfrec F I)
  have p0002 :=
    @g_elex F (syn_cfuns)
  have p0003 :=
    Nominal.mp hyp_wppfreceqexndv_1 p0002
  have p0004 :=
    @g_frecex (syn_cfrec F I) F I p0001 p0003
  have p0005 :=
    @g_cnvexg (syn_cfrec F I) (syn_cvv)
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_eqid (syn_cfrec G I)
  have p0008 :=
    @g_elex G (syn_cfuns)
  have p0009 :=
    Nominal.mp hyp_wppfreceqexndv_2 p0008
  have p0010 :=
    @g_frecex (syn_cfrec G I) G I p0007 p0009
  have p0011 :=
    @g_pm3_2i (.classMem (syn_ccnv (syn_cfrec F I)) (syn_cvv)) (.classMem (syn_cfrec G I) (syn_cvv)) p0006 p0010
  have p0012 :=
    @g_coexg (syn_ccnv (syn_cfrec F I)) (syn_cfrec G I) (syn_cvv) (syn_cvv)
  have p0013 :=
    Nominal.mp p0011 p0012
  have p0014 :=
    @g_fixexg (syn_ccom (syn_ccnv (syn_cfrec F I)) (syn_cfrec G I)) (syn_cvv)
  have p0015 :=
    Nominal.mp p0013 p0014
  have p0016 :=
    @g_eqeltri (syn_cwppfreceq F G I) (syn_cfix (syn_ccom (syn_ccnv (syn_cfrec F I)) (syn_cfrec G I))) (syn_cvv) p0000 p0015
  exact p0016

noncomputable def g_wppfreceqvalndv
    (n : Var) (F : Class) (G : Class) (I : Class) (hyp_wppfreceqvalndv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppfreceqvalndv_2 : Nominal.NPrf (.classMem I (syn_cdm F))) (hyp_wppfreceqvalndv_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) (hyp_wppfreceqvalndv_4 : Nominal.NPrf (.classMem G (syn_cfuns))) (hyp_wppfreceqvalndv_5 : Nominal.NPrf (.classMem I (syn_cdm G))) (hyp_wppfreceqvalndv_6 : Nominal.NPrf (syn_wss (syn_crn G) (syn_cdm G))) :
    Nominal.NPrf (.imp (.classMem (.cv n) (syn_cnnc)) (syn_wb (.classMem (.cv n) (syn_cwppfreceq F G I)) (.classEq (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cfv (syn_cfrec G I) (.cv n))))) := by
  let proofSupport : Finset Var := ({n} : Finset Var) ∪ F.fv ∪ G.fv ∪ I.fv
  have p0000 :=
    (by simpa [syn_cwppfreceq] using (Nominal.classEqRefl (syn_cwppfreceq F G I)))
  have p0001 :=
    @g_eleq2i (syn_cwppfreceq F G I) (syn_cfix (syn_ccom (syn_ccnv (syn_cfrec F I)) (syn_cfrec G I))) (.cv n) p0000
  have p0002 :=
    @g_a1i (syn_wb (.classMem (.cv n) (syn_cwppfreceq F G I)) (.classMem (.cv n) (syn_cfix (syn_ccom (syn_ccnv (syn_cfrec F I)) (syn_cfrec G I))))) (.classMem (.cv n) (syn_cnnc)) p0001
  have p0003 :=
    @g_n_3pm3_2i (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F)) hyp_wppfreceqvalndv_1 hyp_wppfreceqvalndv_2 hyp_wppfreceqvalndv_3
  have p0004 :=
    @g_wpporbitfnndv F I
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_fnfun (syn_cnnc) (syn_cfrec F I)
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_a1i (syn_wfun (syn_cfrec F I)) (.classMem (.cv n) (syn_cnnc)) p0007
  have p0009 :=
    @g_n_3pm3_2i (.classMem G (syn_cfuns)) (.classMem I (syn_cdm G)) (syn_wss (syn_crn G) (syn_cdm G)) hyp_wppfreceqvalndv_4 hyp_wppfreceqvalndv_5 hyp_wppfreceqvalndv_6
  have p0010 :=
    @g_wpporbitfnndv G I
  have p0011 :=
    Nominal.mp p0009 p0010
  have p0012 :=
    @g_fnfun (syn_cnnc) (syn_cfrec G I)
  have p0013 :=
    Nominal.mp p0011 p0012
  have p0014 :=
    @g_a1i (syn_wfun (syn_cfrec G I)) (.classMem (.cv n) (syn_cnnc)) p0013
  have p0015 :=
    @g_n_3pm3_2i (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F)) hyp_wppfreceqvalndv_1 hyp_wppfreceqvalndv_2 hyp_wppfreceqvalndv_3
  have p0016 :=
    @g_wpporbitfnndv F I
  have p0017 :=
    Nominal.mp p0015 p0016
  have p0018 :=
    @g_fndm (syn_cnnc) (syn_cfrec F I)
  have p0019 :=
    Nominal.mp p0017 p0018
  have p0020 :=
    @g_eleq2i (syn_cdm (syn_cfrec F I)) (syn_cnnc) (.cv n) p0019
  have p0021 :=
    @g_biimpri (.classMem (.cv n) (syn_cdm (syn_cfrec F I))) (.classMem (.cv n) (syn_cnnc)) p0020
  have p0022 :=
    @g_n_3pm3_2i (.classMem G (syn_cfuns)) (.classMem I (syn_cdm G)) (syn_wss (syn_crn G) (syn_cdm G)) hyp_wppfreceqvalndv_4 hyp_wppfreceqvalndv_5 hyp_wppfreceqvalndv_6
  have p0023 :=
    @g_wpporbitfnndv G I
  have p0024 :=
    Nominal.mp p0022 p0023
  have p0025 :=
    @g_fndm (syn_cnnc) (syn_cfrec G I)
  have p0026 :=
    Nominal.mp p0024 p0025
  have p0027 :=
    @g_eleq2i (syn_cdm (syn_cfrec G I)) (syn_cnnc) (.cv n) p0026
  have p0028 :=
    @g_biimpri (.classMem (.cv n) (syn_cdm (syn_cfrec G I))) (.classMem (.cv n) (syn_cnnc)) p0027
  have p0029 :=
    @g_jca (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cdm (syn_cfrec F I))) (.classMem (.cv n) (syn_cdm (syn_cfrec G I))) p0021 p0028
  have p0030 :=
    @g_n_3jca (.classMem (.cv n) (syn_cnnc)) (syn_wfun (syn_cfrec F I)) (syn_wfun (syn_cfrec G I)) (syn_wa (.classMem (.cv n) (syn_cdm (syn_cfrec F I))) (.classMem (.cv n) (syn_cdm (syn_cfrec G I)))) p0008 p0014 p0029
  have p0031 :=
    @g_funeqfix (.cv n) (syn_cfrec F I) (syn_cfrec G I)
  have p0032 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) (syn_w3a (syn_wfun (syn_cfrec F I)) (syn_wfun (syn_cfrec G I)) (syn_wa (.classMem (.cv n) (syn_cdm (syn_cfrec F I))) (.classMem (.cv n) (syn_cdm (syn_cfrec G I))))) (syn_wb (.classMem (.cv n) (syn_cfix (syn_ccom (syn_ccnv (syn_cfrec F I)) (syn_cfrec G I)))) (.classEq (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cfv (syn_cfrec G I) (.cv n)))) p0030 p0031
  have p0033 :=
    @g_bitrd (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwppfreceq F G I)) (.classMem (.cv n) (syn_cfix (syn_ccom (syn_ccnv (syn_cfrec F I)) (syn_cfrec G I)))) (.classEq (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cfv (syn_cfrec G I) (.cv n))) p0002 p0032
  exact p0033

noncomputable def g_wppfreceqvalclndv
    (B : Class) (F : Class) (G : Class) (I : Class) (hyp_wppfreceqvalclndv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppfreceqvalclndv_2 : Nominal.NPrf (.classMem I (syn_cdm F))) (hyp_wppfreceqvalclndv_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) (hyp_wppfreceqvalclndv_4 : Nominal.NPrf (.classMem G (syn_cfuns))) (hyp_wppfreceqvalclndv_5 : Nominal.NPrf (.classMem I (syn_cdm G))) (hyp_wppfreceqvalclndv_6 : Nominal.NPrf (syn_wss (syn_crn G) (syn_cdm G))) :
    Nominal.NPrf (.imp (.classMem B (syn_cnnc)) (syn_wb (.classMem B (syn_cwppfreceq F G I)) (.classEq (syn_cfv (syn_cfrec F I) B) (syn_cfv (syn_cfrec G I) B)))) := by
  let proofSupport : Finset Var := B.fv ∪ F.fv ∪ G.fv ∪ I.fv
  let n : Var := freshVar proofSupport 0
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_B : n ∉ B.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_n_not_F : n ∉ F.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_n_not_G : n ∉ G.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_not_I : n ∉ I.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have dv_cache_0001 : n ∉ (B).fv := by
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : n ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : n ∉ ((syn_wb (.classMem B (syn_cwppfreceq F G I)) (.classEq (syn_cfv (syn_cfrec F I) B) (syn_cfv (syn_cfrec G I) B)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfreceq, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_B, fresh_n_not_F, fresh_n_not_G, fresh_n_not_I, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_wppfreceqvalndv n F G I hyp_wppfreceqvalclndv_1 hyp_wppfreceqvalclndv_2 hyp_wppfreceqvalclndv_3 hyp_wppfreceqvalclndv_4 hyp_wppfreceqvalclndv_5 hyp_wppfreceqvalclndv_6
  have p0001 :=
    @g_rgen (syn_wb (.classMem (.cv n) (syn_cwppfreceq F G I)) (.classEq (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cfv (syn_cfrec G I) (.cv n)))) n (syn_cnnc) p0000
  have p0002 :=
    @g_id (.classEq (.cv n) B)
  have p0003 :=
    @g_eleq1d (.classEq (.cv n) B) (.cv n) B (syn_cwppfreceq F G I) p0002
  have p0004 :=
    @g_id (.classEq (.cv n) B)
  have p0005 :=
    @g_fveq2d (.classEq (.cv n) B) (.cv n) B (syn_cfrec F I) p0004
  have p0006 :=
    @g_id (.classEq (.cv n) B)
  have p0007 :=
    @g_fveq2d (.classEq (.cv n) B) (.cv n) B (syn_cfrec G I) p0006
  have p0008 :=
    @g_eqeq12d (.classEq (.cv n) B) (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cfv (syn_cfrec F I) B) (syn_cfv (syn_cfrec G I) (.cv n)) (syn_cfv (syn_cfrec G I) B) p0005 p0007
  have p0009 :=
    @g_bibi12d (.classEq (.cv n) B) (.classMem (.cv n) (syn_cwppfreceq F G I)) (.classMem B (syn_cwppfreceq F G I)) (.classEq (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cfv (syn_cfrec G I) (.cv n))) (.classEq (syn_cfv (syn_cfrec F I) B) (syn_cfv (syn_cfrec G I) B)) p0003 p0008
  have p0010 :=
    @g_rspcv (syn_wb (.classMem (.cv n) (syn_cwppfreceq F G I)) (.classEq (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cfv (syn_cfrec G I) (.cv n)))) (syn_wb (.classMem B (syn_cwppfreceq F G I)) (.classEq (syn_cfv (syn_cfrec F I) B) (syn_cfv (syn_cfrec G I) B))) n B (syn_cnnc) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0009
  have p0011 :=
    @g_mpi (.classMem B (syn_cnnc)) (syn_wral n (syn_cnnc) (syn_wb (.classMem (.cv n) (syn_cwppfreceq F G I)) (.classEq (syn_cfv (syn_cfrec F I) (.cv n)) (syn_cfv (syn_cfrec G I) (.cv n))))) (syn_wb (.classMem B (syn_cwppfreceq F G I)) (.classEq (syn_cfv (syn_cfrec F I) B) (syn_cfv (syn_cfrec G I) B))) p0001 p0010
  exact p0011

noncomputable def g_wppfrecprefixeqexndv
    (k : Var) (F : Class) (G : Class) (I : Class) (hyp_wppfrecprefixeqexndv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppfrecprefixeqexndv_2 : Nominal.NPrf (.classMem G (syn_cfuns))) :
    Nominal.NPrf (.classMem (syn_cwppfrecprefixeq F G I k) (syn_cvv)) := by
  let proofSupport : Finset Var := ({k} : Finset Var) ∪ F.fv ∪ G.fv ∪ I.fv
  have p0000 :=
    (by simpa [syn_cwppfrecprefixeq] using (Nominal.classEqRefl (syn_cwppfrecprefixeq F G I k)))
  have p0001 :=
    @g_nncex
  have p0002 :=
    @g_lefinex
  have p0003 :=
    @g_kqrelex (syn_clefin) p0002
  have p0004 :=
    @g_cnvexg (syn_ckqrel (syn_clefin)) (syn_cvv)
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_snex (.cv k)
  have p0007 :=
    @g_imaex (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k)) p0005 p0006
  have p0008 :=
    @g_difex (syn_cnnc) (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k))) p0001 p0007
  have p0009 :=
    @g_wppfreceqexndv F G I hyp_wppfrecprefixeqexndv_1 hyp_wppfrecprefixeqexndv_2
  have p0010 :=
    @g_unex (syn_cdif (syn_cnnc) (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k)))) (syn_cwppfreceq F G I) p0008 p0009
  have p0011 :=
    @g_eqeltri (syn_cwppfrecprefixeq F G I k) (syn_cun (syn_cdif (syn_cnnc) (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k)))) (syn_cwppfreceq F G I)) (syn_cvv) p0000 p0010
  exact p0011

noncomputable def g_wppfrecprefixeqvalndv
    (B : Class) (k : Var) (F : Class) (G : Class) (I : Class) (hyp_wppfrecprefixeqvalndv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppfrecprefixeqvalndv_2 : Nominal.NPrf (.classMem I (syn_cdm F))) (hyp_wppfrecprefixeqvalndv_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) (hyp_wppfrecprefixeqvalndv_4 : Nominal.NPrf (.classMem G (syn_cfuns))) (hyp_wppfrecprefixeqvalndv_5 : Nominal.NPrf (.classMem I (syn_cdm G))) (hyp_wppfrecprefixeqvalndv_6 : Nominal.NPrf (syn_wss (syn_crn G) (syn_cdm G))) :
    Nominal.NPrf (.imp (.classMem B (syn_cnnc)) (syn_wb (.classMem B (syn_cwppfrecprefixeq F G I k)) (.imp (syn_wbr B (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec F I) B) (syn_cfv (syn_cfrec G I) B))))) := by
  let proofSupport : Finset Var := B.fv ∪ ({k} : Finset Var) ∪ F.fv ∪ G.fv ∪ I.fv
  have p0000 :=
    (by simpa [syn_cwppfrecprefixeq] using (Nominal.classEqRefl (syn_cwppfrecprefixeq F G I k)))
  have p0001 :=
    @g_eleq2i (syn_cwppfrecprefixeq F G I k) (syn_cun (syn_cdif (syn_cnnc) (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k)))) (syn_cwppfreceq F G I)) B p0000
  have p0002 :=
    @g_a1i (syn_wb (.classMem B (syn_cwppfrecprefixeq F G I k)) (.classMem B (syn_cun (syn_cdif (syn_cnnc) (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k)))) (syn_cwppfreceq F G I)))) (.classMem B (syn_cnnc)) p0001
  have p0003 :=
    @g_elun B (syn_cdif (syn_cnnc) (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k)))) (syn_cwppfreceq F G I)
  have p0004 :=
    @g_a1i (syn_wb (.classMem B (syn_cun (syn_cdif (syn_cnnc) (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k)))) (syn_cwppfreceq F G I))) (syn_wo (.classMem B (syn_cdif (syn_cnnc) (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k))))) (.classMem B (syn_cwppfreceq F G I)))) (.classMem B (syn_cnnc)) p0003
  have p0005 :=
    @g_eldif B (syn_cnnc) (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k)))
  have p0006 :=
    @g_a1i (syn_wb (.classMem B (syn_cdif (syn_cnnc) (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k))))) (syn_wa (.classMem B (syn_cnnc)) (.neg (.classMem B (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k))))))) (.classMem B (syn_cnnc)) p0005
  have p0007 :=
    @g_id (.classMem B (syn_cnnc))
  have p0008 :=
    @g_biantrurd (.classMem B (syn_cnnc)) (.classMem B (syn_cnnc)) (.neg (.classMem B (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k))))) p0007
  have p0009 :=
    @g_bitr4d (.classMem B (syn_cnnc)) (.classMem B (syn_cdif (syn_cnnc) (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k))))) (syn_wa (.classMem B (syn_cnnc)) (.neg (.classMem B (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k)))))) (.neg (.classMem B (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k))))) p0006 p0008
  have p0010 :=
    @g_elimasn (syn_ccnv (syn_ckqrel (syn_clefin))) (.cv k) B
  have p0011 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv k) (syn_ccnv (syn_ckqrel (syn_clefin))) B)))
  have p0012 :=
    @g_bitr4i (.classMem B (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k)))) (.classMem (syn_cop (.cv k) B) (syn_ccnv (syn_ckqrel (syn_clefin)))) (syn_wbr (.cv k) (syn_ccnv (syn_ckqrel (syn_clefin))) B) p0010 p0011
  have p0013 :=
    @g_brcnv (.cv k) B (syn_ckqrel (syn_clefin))
  have p0014 :=
    @g_bitri (.classMem B (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k)))) (syn_wbr (.cv k) (syn_ccnv (syn_ckqrel (syn_clefin))) B) (syn_wbr B (syn_ckqrel (syn_clefin)) (.cv k)) p0012 p0013
  have p0015 :=
    @g_notbi (.classMem B (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k)))) (syn_wbr B (syn_ckqrel (syn_clefin)) (.cv k))
  have p0016 :=
    @g_mpbi (syn_wb (.classMem B (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k)))) (syn_wbr B (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wb (.neg (.classMem B (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k))))) (.neg (syn_wbr B (syn_ckqrel (syn_clefin)) (.cv k)))) p0014 p0015
  have p0017 :=
    @g_a1i (syn_wb (.neg (.classMem B (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k))))) (.neg (syn_wbr B (syn_ckqrel (syn_clefin)) (.cv k)))) (.classMem B (syn_cnnc)) p0016
  have p0018 :=
    @g_bitrd (.classMem B (syn_cnnc)) (.classMem B (syn_cdif (syn_cnnc) (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k))))) (.neg (.classMem B (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k))))) (.neg (syn_wbr B (syn_ckqrel (syn_clefin)) (.cv k))) p0009 p0017
  have p0019 :=
    @g_wppfreceqvalclndv B F G I hyp_wppfrecprefixeqvalndv_1 hyp_wppfrecprefixeqvalndv_2 hyp_wppfrecprefixeqvalndv_3 hyp_wppfrecprefixeqvalndv_4 hyp_wppfrecprefixeqvalndv_5 hyp_wppfrecprefixeqvalndv_6
  have p0020 :=
    @g_orbi12d (.classMem B (syn_cnnc)) (.classMem B (syn_cdif (syn_cnnc) (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k))))) (.neg (syn_wbr B (syn_ckqrel (syn_clefin)) (.cv k))) (.classMem B (syn_cwppfreceq F G I)) (.classEq (syn_cfv (syn_cfrec F I) B) (syn_cfv (syn_cfrec G I) B)) p0018 p0019
  have p0021 :=
    @g_bitrd (.classMem B (syn_cnnc)) (.classMem B (syn_cun (syn_cdif (syn_cnnc) (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k)))) (syn_cwppfreceq F G I))) (syn_wo (.classMem B (syn_cdif (syn_cnnc) (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k))))) (.classMem B (syn_cwppfreceq F G I))) (syn_wo (.neg (syn_wbr B (syn_ckqrel (syn_clefin)) (.cv k))) (.classEq (syn_cfv (syn_cfrec F I) B) (syn_cfv (syn_cfrec G I) B))) p0004 p0020
  have p0022 :=
    @g_imor (syn_wbr B (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec F I) B) (syn_cfv (syn_cfrec G I) B))
  have p0023 :=
    @g_a1i (syn_wb (.imp (syn_wbr B (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec F I) B) (syn_cfv (syn_cfrec G I) B))) (syn_wo (.neg (syn_wbr B (syn_ckqrel (syn_clefin)) (.cv k))) (.classEq (syn_cfv (syn_cfrec F I) B) (syn_cfv (syn_cfrec G I) B)))) (.classMem B (syn_cnnc)) p0022
  have p0024 :=
    @g_bitr4d (.classMem B (syn_cnnc)) (.classMem B (syn_cun (syn_cdif (syn_cnnc) (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k)))) (syn_cwppfreceq F G I))) (syn_wo (.neg (syn_wbr B (syn_ckqrel (syn_clefin)) (.cv k))) (.classEq (syn_cfv (syn_cfrec F I) B) (syn_cfv (syn_cfrec G I) B))) (.imp (syn_wbr B (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec F I) B) (syn_cfv (syn_cfrec G I) B))) p0021 p0023
  have p0025 :=
    @g_bitrd (.classMem B (syn_cnnc)) (.classMem B (syn_cwppfrecprefixeq F G I k)) (.classMem B (syn_cun (syn_cdif (syn_cnnc) (syn_cima (syn_ccnv (syn_ckqrel (syn_clefin))) (syn_csn (.cv k)))) (syn_cwppfreceq F G I))) (.imp (syn_wbr B (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec F I) B) (syn_cfv (syn_cfrec G I) B))) p0002 p0024
  exact p0025

noncomputable def g_wppstopstepsamebelowdndv
    (y : Var) (C : Class) (F : Class) (p : Var) (dv_C_p : p ∉ C.fv) (dv_F_p : p ∉ F.fv) (dv_p_y : p ≠ y) (hyp_wppstopstepsamebelowdndv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppstopstepsamebelowdndv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_chwcards (syn_cvv)))) (hyp_wppstopstepsamebelowdndv_3 : Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv)))) (hyp_wppstopstepsamebelowdndv_4 : Nominal.NPrf (syn_wbr (syn_ctc C) (syn_clec) C)) (hyp_wppstopstepsamebelowdndv_5 : Nominal.NPrf (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm F))))) :
    Nominal.NPrf (.imp (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc C)) (.classEq (syn_cfv (syn_cwppstopstep F C) (.cv y)) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (.cv y))))) := by
  let proofSupport : Finset Var := ({y} : Finset Var) ∪ C.fv ∪ F.fv ∪ ({p} : Finset Var)
  have dv_cache_0001 : p ∉ ((Class.cv y)).fv := by
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_p_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((syn_chwcards (syn_cvv))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : p ∉ ((Wff.imp (syn_wbr (.cv y) (syn_clec) C) (.classMem (.cv y) (syn_cdm F)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_p_y, dv_C_p, dv_F_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpr (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))
  have p0001 :=
    @g_a1i (syn_wbr (syn_ctc C) (syn_clec) C) (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))) hyp_wppstopstepsamebelowdndv_4
  have p0002 :=
    @g_jca (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C)) (syn_wbr (syn_ctc C) (syn_clec) C) p0000 p0001
  have p0003 :=
    @g_simpl (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))
  have p0004 :=
    @g_hwcardssnc (syn_cvv)
  have p0005 :=
    @g_ssel (syn_chwcards (syn_cvv)) (syn_cncs) (.cv y)
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_syl (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.classMem (.cv y) (syn_cncs)) p0003 p0006
  have p0008 :=
    @g_hwcardssnc (syn_cvv)
  have p0009 :=
    @g_sselii (syn_chwcards (syn_cvv)) (syn_cncs) C p0008 hyp_wppstopstepsamebelowdndv_3
  have p0010 :=
    @g_tccl C
  have p0011 :=
    Nominal.mp p0009 p0010
  have p0012 :=
    @g_a1i (.classMem (syn_ctc C) (syn_cncs)) (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))) p0011
  have p0013 :=
    @g_hwcardssnc (syn_cvv)
  have p0014 :=
    @g_sselii (syn_chwcards (syn_cvv)) (syn_cncs) C p0013 hyp_wppstopstepsamebelowdndv_3
  have p0015 :=
    @g_a1i (.classMem C (syn_cncs)) (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))) p0014
  have p0016 :=
    @g_n_3jca (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))) (.classMem (.cv y) (syn_cncs)) (.classMem (syn_ctc C) (syn_cncs)) (.classMem C (syn_cncs)) p0007 p0012 p0015
  have p0017 :=
    @g_lectr (.cv y) (syn_ctc C) C
  have p0018 :=
    @g_syl (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))) (syn_w3a (.classMem (.cv y) (syn_cncs)) (.classMem (syn_ctc C) (syn_cncs)) (.classMem C (syn_cncs))) (.imp (syn_wa (syn_wbr (.cv y) (syn_clec) (syn_ctc C)) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_wbr (.cv y) (syn_clec) C)) p0016 p0017
  have p0019 :=
    @g_mpd (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))) (syn_wa (syn_wbr (.cv y) (syn_clec) (syn_ctc C)) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_wbr (.cv y) (syn_clec) C) p0002 p0018
  have p0020 :=
    @g_simpl (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))
  have p0021 :=
    @g_simpl (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))
  have p0022 :=
    @g_id (.classEq (.cv p) (.cv y))
  have p0023 :=
    @g_breq1d (.classEq (.cv p) (.cv y)) (.cv p) (.cv y) C (syn_clec) p0022
  have p0024 :=
    @g_id (.classEq (.cv p) (.cv y))
  have p0025 :=
    @g_eleq1d (.classEq (.cv p) (.cv y)) (.cv p) (.cv y) (syn_cdm F) p0024
  have p0026 :=
    @g_imbi12d (.classEq (.cv p) (.cv y)) (syn_wbr (.cv p) (syn_clec) C) (syn_wbr (.cv y) (syn_clec) C) (.classMem (.cv p) (syn_cdm F)) (.classMem (.cv y) (syn_cdm F)) p0023 p0025
  have p0027 :=
    @g_rspcv (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm F))) (.imp (syn_wbr (.cv y) (syn_clec) C) (.classMem (.cv y) (syn_cdm F))) p (.cv y) (syn_chwcards (syn_cvv)) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0026
  have p0028 :=
    @g_mpi (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm F)))) (.imp (syn_wbr (.cv y) (syn_clec) C) (.classMem (.cv y) (syn_cdm F))) hyp_wppstopstepsamebelowdndv_5 p0027
  have p0029 :=
    @g_syl (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv y) (syn_clec) C) (.classMem (.cv y) (syn_cdm F))) p0021 p0028
  have p0030 :=
    @g_jca (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv y) (syn_clec) C) (.classMem (.cv y) (syn_cdm F))) p0020 p0029
  have p0031 :=
    @g_wppstopstepfvlecdndv (.cv y) C F hyp_wppstopstepsamebelowdndv_1 hyp_wppstopstepsamebelowdndv_2
  have p0032 :=
    @g_syl (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))) (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv y) (syn_clec) C) (.classMem (.cv y) (syn_cdm F)))) (.imp (syn_wbr (.cv y) (syn_clec) C) (.classEq (syn_cfv (syn_cwppstopstep F C) (.cv y)) (syn_cfv F (.cv y)))) p0030 p0031
  have p0033 :=
    @g_mpd (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))) (syn_wbr (.cv y) (syn_clec) C) (.classEq (syn_cfv (syn_cwppstopstep F C) (.cv y)) (syn_cfv F (.cv y))) p0019 p0032
  have p0034 :=
    @g_simpr (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))
  have p0035 :=
    @g_simpl (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))
  have p0036 :=
    @g_simpl (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))
  have p0037 :=
    @g_simpr (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))
  have p0038 :=
    @g_a1i (syn_wbr (syn_ctc C) (syn_clec) C) (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))) hyp_wppstopstepsamebelowdndv_4
  have p0039 :=
    @g_jca (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C)) (syn_wbr (syn_ctc C) (syn_clec) C) p0037 p0038
  have p0040 :=
    @g_simpl (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))
  have p0041 :=
    @g_hwcardssnc (syn_cvv)
  have p0042 :=
    @g_ssel (syn_chwcards (syn_cvv)) (syn_cncs) (.cv y)
  have p0043 :=
    Nominal.mp p0041 p0042
  have p0044 :=
    @g_syl (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.classMem (.cv y) (syn_cncs)) p0040 p0043
  have p0045 :=
    @g_hwcardssnc (syn_cvv)
  have p0046 :=
    @g_sselii (syn_chwcards (syn_cvv)) (syn_cncs) C p0045 hyp_wppstopstepsamebelowdndv_3
  have p0047 :=
    @g_tccl C
  have p0048 :=
    Nominal.mp p0046 p0047
  have p0049 :=
    @g_a1i (.classMem (syn_ctc C) (syn_cncs)) (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))) p0048
  have p0050 :=
    @g_hwcardssnc (syn_cvv)
  have p0051 :=
    @g_sselii (syn_chwcards (syn_cvv)) (syn_cncs) C p0050 hyp_wppstopstepsamebelowdndv_3
  have p0052 :=
    @g_a1i (.classMem C (syn_cncs)) (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))) p0051
  have p0053 :=
    @g_n_3jca (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))) (.classMem (.cv y) (syn_cncs)) (.classMem (syn_ctc C) (syn_cncs)) (.classMem C (syn_cncs)) p0044 p0049 p0052
  have p0054 :=
    @g_lectr (.cv y) (syn_ctc C) C
  have p0055 :=
    @g_syl (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))) (syn_w3a (.classMem (.cv y) (syn_cncs)) (.classMem (syn_ctc C) (syn_cncs)) (.classMem C (syn_cncs))) (.imp (syn_wa (syn_wbr (.cv y) (syn_clec) (syn_ctc C)) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_wbr (.cv y) (syn_clec) C)) p0053 p0054
  have p0056 :=
    @g_mpd (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))) (syn_wa (syn_wbr (.cv y) (syn_clec) (syn_ctc C)) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_wbr (.cv y) (syn_clec) C) p0039 p0055
  have p0057 :=
    @g_simpl (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))
  have p0058 :=
    @g_id (.classEq (.cv p) (.cv y))
  have p0059 :=
    @g_breq1d (.classEq (.cv p) (.cv y)) (.cv p) (.cv y) C (syn_clec) p0058
  have p0060 :=
    @g_id (.classEq (.cv p) (.cv y))
  have p0061 :=
    @g_eleq1d (.classEq (.cv p) (.cv y)) (.cv p) (.cv y) (syn_cdm F) p0060
  have p0062 :=
    @g_imbi12d (.classEq (.cv p) (.cv y)) (syn_wbr (.cv p) (syn_clec) C) (syn_wbr (.cv y) (syn_clec) C) (.classMem (.cv p) (syn_cdm F)) (.classMem (.cv y) (syn_cdm F)) p0059 p0061
  have p0063 :=
    @g_rspcv (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm F))) (.imp (syn_wbr (.cv y) (syn_clec) C) (.classMem (.cv y) (syn_cdm F))) p (.cv y) (syn_chwcards (syn_cvv)) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0062
  have p0064 :=
    @g_mpi (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm F)))) (.imp (syn_wbr (.cv y) (syn_clec) C) (.classMem (.cv y) (syn_cdm F))) hyp_wppstopstepsamebelowdndv_5 p0063
  have p0065 :=
    @g_syl (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv y) (syn_clec) C) (.classMem (.cv y) (syn_cdm F))) p0057 p0064
  have p0066 :=
    @g_mpd (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))) (syn_wbr (.cv y) (syn_clec) C) (.classMem (.cv y) (syn_cdm F)) p0056 p0065
  have p0067 :=
    @g_ex (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C)) (.classMem (.cv y) (syn_cdm F)) p0066
  have p0068 :=
    @g_syl (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc C)) (.classMem (.cv y) (syn_cdm F))) p0036 p0067
  have p0069 :=
    @g_jca (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc C)) (.classMem (.cv y) (syn_cdm F))) p0035 p0068
  have p0070 :=
    @g_wppstopstepfvlecdndv (.cv y) (syn_ctc C) F hyp_wppstopstepsamebelowdndv_1 hyp_wppstopstepsamebelowdndv_2
  have p0071 :=
    @g_syl (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))) (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc C)) (.classMem (.cv y) (syn_cdm F)))) (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc C)) (.classEq (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (.cv y)) (syn_cfv F (.cv y)))) p0069 p0070
  have p0072 :=
    @g_mpd (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C)) (.classEq (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (.cv y)) (syn_cfv F (.cv y))) p0034 p0071
  have p0073 :=
    @g_eqcomd (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (.cv y)) (syn_cfv F (.cv y)) p0072
  have p0074 :=
    @g_eqtrd (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C))) (syn_cfv (syn_cwppstopstep F C) (.cv y)) (syn_cfv F (.cv y)) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (.cv y)) p0033 p0073
  have p0075 :=
    @g_ex (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C)) (.classEq (syn_cfv (syn_cwppstopstep F C) (.cv y)) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (.cv y))) p0074
  exact p0075

#print axioms g_wppstopstepsamebelowdndv

end NFChoice.DirectNominalPrf.WPPReplay
