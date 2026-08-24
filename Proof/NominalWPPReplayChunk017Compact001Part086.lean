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
import NominalWPPReplayChunk017Compact001Part085

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

noncomputable def g_wppconcrete6stoppedgrowthfrompointndv
    (y : Var) (hyp_wppconcrete6stoppedgrowthfrompointndv_1 : Nominal.NPrf (.imp (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))))) :
    Nominal.NPrf (.imp (syn_wwpp) (syn_wral y (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (.imp (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y)) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.cv y)))))) := by
  let proofSupport : Finset Var := ({y} : Finset Var)
  let p : Var := freshVar proofSupport 0
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_ne_y : p ≠ y := by
    intro h
    exact fresh_p (Finset.mem_singleton.mpr h)
  have fresh_y_ne_p : y ≠ p :=
    Ne.symm fresh_p_ne_y
  have dv_cache_0001 : p ∉ ((Class.cv y)).fv := by
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((syn_chwcards (syn_cvv))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : p ∉ ((Wff.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.classMem (.cv y) (syn_cdm (syn_cwppconcrete6fn))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppconcrete6fn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_wwpp)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wwpp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_n_3simpc (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))
  have p0001 :=
    @g_simpr (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))
  have p0002 :=
    @g_syl (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wa (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y)) p0000 p0001
  have p0003 :=
    @g_n_3simpa (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))
  have p0004 :=
    @g_simpl (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
  have p0005 :=
    @g_syl (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wa (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))) (syn_wwpp) p0003 p0004
  have p0006 :=
    @g_n_3simpa (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))
  have p0007 :=
    @g_simpr (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
  have p0008 :=
    @g_syl (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wa (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) p0006 p0007
  have p0009 :=
    @g_wppconcrete6fnfunsndv
  have p0010 :=
    @g_wppconcrete6rnhwcardsndv
  have p0011 :=
    @g_wppstopstepdmndv (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_cwppconcrete6fn) p0009 p0010
  have p0012 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_chwcards (syn_cvv)) (.cv y) p0011
  have p0013 :=
    @g_biimpi (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) p0012
  have p0014 :=
    @g_syl (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) p0008 p0013
  have p0015 :=
    @g_wppconcrete6tcbandgrowthfrompointhwclecdndv y hyp_wppconcrete6stoppedgrowthfrompointndv_1
  have p0016 :=
    @g_syl (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.imp (syn_wwpp) (.imp (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y)) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))))) p0014 p0015
  have p0017 :=
    @g_mpid (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wwpp) (.imp (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y)) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))) p0005 p0016
  have p0018 :=
    @g_mpid (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y)) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))) p0002 p0017
  have p0019 :=
    @g_imp (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))) p0018
  have p0020 :=
    @g_n_3simpa (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))
  have p0021 :=
    @g_simpr (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
  have p0022 :=
    @g_syl (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wa (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) p0020 p0021
  have p0023 :=
    @g_wppconcrete6fnfunsndv
  have p0024 :=
    @g_wppconcrete6rnhwcardsndv
  have p0025 :=
    @g_wppstopstepdmndv (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_cwppconcrete6fn) p0023 p0024
  have p0026 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_chwcards (syn_cvv)) (.cv y) p0025
  have p0027 :=
    @g_biimpi (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) p0026
  have p0028 :=
    @g_syl (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) p0022 p0027
  have p0029 :=
    @g_n_3simpa (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))
  have p0030 :=
    @g_simpr (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
  have p0031 :=
    @g_syl (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wa (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) p0029 p0030
  have p0032 :=
    @g_wppconcrete6fnfunsndv
  have p0033 :=
    @g_wppconcrete6rnhwcardsndv
  have p0034 :=
    @g_wppstopstepdmndv (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_cwppconcrete6fn) p0032 p0033
  have p0035 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_chwcards (syn_cvv)) (.cv y) p0034
  have p0036 :=
    @g_biimpi (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) p0035
  have p0037 :=
    @g_syl (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) p0031 p0036
  have p0038 :=
    @g_wppconcrete6hncard1dmcovndv p
  have p0039 :=
    @g_id (.classEq (.cv p) (.cv y))
  have p0040 :=
    @g_breq1d (.classEq (.cv p) (.cv y)) (.cv p) (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) p0039
  have p0041 :=
    @g_id (.classEq (.cv p) (.cv y))
  have p0042 :=
    @g_eleq1d (.classEq (.cv p) (.cv y)) (.cv p) (.cv y) (syn_cdm (syn_cwppconcrete6fn)) p0041
  have p0043 :=
    @g_imbi12d (.classEq (.cv p) (.cv y)) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (.cv y) (syn_cdm (syn_cwppconcrete6fn))) p0040 p0042
  have p0044 :=
    @g_rspcv (.imp (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn)))) (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.classMem (.cv y) (syn_cdm (syn_cwppconcrete6fn)))) p (.cv y) (syn_chwcards (syn_cvv)) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0043
  have p0045 :=
    @g_mpi (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))))) (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.classMem (.cv y) (syn_cdm (syn_cwppconcrete6fn)))) p0038 p0044
  have p0046 :=
    @g_syl (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.classMem (.cv y) (syn_cdm (syn_cwppconcrete6fn)))) p0037 p0045
  have p0047 :=
    @g_jca (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.classMem (.cv y) (syn_cdm (syn_cwppconcrete6fn)))) p0028 p0046
  have p0048 :=
    @g_wppconcrete6fnfunsndv
  have p0049 :=
    @g_wppconcrete6rnhwcardsndv
  have p0050 :=
    @g_wppstopstepfvlecdndv (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_cwppconcrete6fn) p0048 p0049
  have p0051 :=
    @g_syl (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.classMem (.cv y) (syn_cdm (syn_cwppconcrete6fn))))) (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.classEq (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.cv y)) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))) p0047 p0050
  have p0052 :=
    @g_imp (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.classEq (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.cv y)) (syn_cfv (syn_cwppconcrete6fn) (.cv y))) p0051
  have p0053 :=
    @g_breq2d (syn_wa (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.cv y)) (syn_cfv (syn_cwppconcrete6fn) (.cv y)) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) p0052
  have p0054 :=
    @g_biimprd (syn_wa (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.cv y))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))) p0053
  have p0055 :=
    @g_mpd (syn_wa (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.cv y))) p0019 p0054
  have p0056 :=
    @g_ex (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.cv y))) p0055
  have p0057 :=
    @g_n_3simpa (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))
  have p0058 :=
    @g_simpr (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
  have p0059 :=
    @g_syl (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wa (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) p0057 p0058
  have p0060 :=
    @g_wppconcrete6fnfunsndv
  have p0061 :=
    @g_wppconcrete6rnhwcardsndv
  have p0062 :=
    @g_wppstopstepdmndv (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_cwppconcrete6fn) p0060 p0061
  have p0063 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_chwcards (syn_cvv)) (.cv y) p0062
  have p0064 :=
    @g_biimpi (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) p0063
  have p0065 :=
    @g_syl (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) p0059 p0064
  have p0066 :=
    @g_wppconcrete6thresholdhwcardsndv
  have p0067 :=
    @g_a1i (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_chwcards (syn_cvv))) (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) p0066
  have p0068 :=
    @g_jca (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_chwcards (syn_cvv))) p0065 p0067
  have p0069 :=
    @g_hwcardslecconnexndv (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
  have p0070 :=
    @g_syl (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_chwcards (syn_cvv)))) (syn_wo (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) p0068 p0069
  have p0071 :=
    @g_ord (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y)) p0070
  have p0072 :=
    @g_imp (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (.neg (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y)) p0071
  have p0073 :=
    @g_n_3simpa (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))
  have p0074 :=
    @g_simpr (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
  have p0075 :=
    @g_syl (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wa (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) p0073 p0074
  have p0076 :=
    @g_wppconcrete6fnfunsndv
  have p0077 :=
    @g_wppconcrete6rnhwcardsndv
  have p0078 :=
    @g_wppstopstepdmndv (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_cwppconcrete6fn) p0076 p0077
  have p0079 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_chwcards (syn_cvv)) (.cv y) p0078
  have p0080 :=
    @g_biimpi (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) p0079
  have p0081 :=
    @g_syl (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) p0075 p0080
  have p0082 :=
    @g_n_3simpa (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))
  have p0083 :=
    @g_simpr (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
  have p0084 :=
    @g_syl (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wa (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) p0082 p0083
  have p0085 :=
    @g_wppconcrete6fnfunsndv
  have p0086 :=
    @g_wppconcrete6rnhwcardsndv
  have p0087 :=
    @g_wppstopstepdmndv (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_cwppconcrete6fn) p0085 p0086
  have p0088 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_chwcards (syn_cvv)) (.cv y) p0087
  have p0089 :=
    @g_biimpi (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) p0088
  have p0090 :=
    @g_syl (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) p0084 p0089
  have p0091 :=
    @g_wppconcrete6hncard1dmcovndv p
  have p0092 :=
    @g_id (.classEq (.cv p) (.cv y))
  have p0093 :=
    @g_breq1d (.classEq (.cv p) (.cv y)) (.cv p) (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) p0092
  have p0094 :=
    @g_id (.classEq (.cv p) (.cv y))
  have p0095 :=
    @g_eleq1d (.classEq (.cv p) (.cv y)) (.cv p) (.cv y) (syn_cdm (syn_cwppconcrete6fn)) p0094
  have p0096 :=
    @g_imbi12d (.classEq (.cv p) (.cv y)) (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))) (.classMem (.cv y) (syn_cdm (syn_cwppconcrete6fn))) p0093 p0095
  have p0097 :=
    @g_rspcv (.imp (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn)))) (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.classMem (.cv y) (syn_cdm (syn_cwppconcrete6fn)))) p (.cv y) (syn_chwcards (syn_cvv)) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0096
  have p0098 :=
    @g_mpi (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))))) (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.classMem (.cv y) (syn_cdm (syn_cwppconcrete6fn)))) p0091 p0097
  have p0099 :=
    @g_syl (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.classMem (.cv y) (syn_cdm (syn_cwppconcrete6fn)))) p0090 p0098
  have p0100 :=
    @g_jca (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.classMem (.cv y) (syn_cdm (syn_cwppconcrete6fn)))) p0081 p0099
  have p0101 :=
    @g_wppconcrete6fnfunsndv
  have p0102 :=
    @g_wppconcrete6rnhwcardsndv
  have p0103 :=
    @g_wppstopstepfvnlecdndv (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_cwppconcrete6fn) p0101 p0102
  have p0104 :=
    @g_syl (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.classMem (.cv y) (syn_cdm (syn_cwppconcrete6fn))))) (.imp (.neg (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (.classEq (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.cv y)) (.cv y))) p0100 p0103
  have p0105 :=
    @g_imp (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (.neg (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (.classEq (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.cv y)) (.cv y)) p0104
  have p0106 :=
    @g_breq2d (syn_wa (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (.neg (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.cv y)) (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) p0105
  have p0107 :=
    @g_biimprd (syn_wa (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (.neg (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.cv y))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y)) p0106
  have p0108 :=
    @g_mpd (syn_wa (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (.neg (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y)) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.cv y))) p0072 p0107
  have p0109 :=
    @g_ex (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (.neg (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.cv y))) p0108
  have p0110 :=
    @g_pm2_61d (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.cv y))) p0056 p0109
  have p0111 :=
    @g_n_3exp (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y)) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.cv y))) p0110
  have p0112 :=
    @g_ralrimiv (syn_wwpp) (.imp (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y)) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.cv y)))) y (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) dv_cache_0004 p0111
  exact p0112

noncomputable def g_wppconcrete6notwppfrompointndv
    (hyp_wppconcrete6notwppfrompointndv_1 : Nominal.NPrf (.imp (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))))) :
    Nominal.NPrf (.neg (syn_wwpp)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have p0000 :=
    @g_eqid (syn_c0c)
  have p0001 :=
    @g_notnoti (.classEq (syn_c0c) (syn_c0c)) p0000
  have p0002 :=
    @g_wppconcrete6stoppedgrowthfrompointndv y hyp_wppconcrete6notwppfrompointndv_1
  have p0003 :=
    @g_n_1cex
  have p0004 :=
    @g_pw1ex (syn_c1c) p0003
  have p0005 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0004
  have p0006 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0005
  have p0007 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0006
  have p0008 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0007
  have p0009 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0008
  have p0010 :=
    @g_hncardtc2nodomndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) p0009
  have p0011 :=
    @g_wppconcrete6stoppedgammacontrgrowthstagedndv y p0010
  have p0012 :=
    @g_syl (syn_wwpp) (syn_wral y (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (.imp (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y)) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.cv y))))) (.neg (.classEq (syn_c0c) (syn_c0c))) p0002 p0011
  have p0013 :=
    @g_mto (syn_wwpp) (.neg (.classEq (syn_c0c) (syn_c0c))) p0001 p0012
  exact p0013

noncomputable def g_hwcnselfbasendv
    (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf (.imp (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))) := by
  let proofSupport : Finset Var := ({u} : Finset Var) ∪ A.fv
  have dv_cache_0001 : u ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_hwcnwendv u A dv_cache_0001
  have p0001 :=
    @g_ssid (syn_cfv (syn_c2nd) (.cv u))
  have p0002 :=
    @g_a1i (syn_wss (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (.classMem (.cv u) (syn_chwcn A)) p0001
  have p0003 :=
    @g_jca (.classMem (.cv u) (syn_chwcn A)) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) p0000 p0002
  have p0004 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0005 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0006 :=
    @g_elhwcodesclndv (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) p0004 p0005
  have p0007 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn A)) (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_chwcodes (syn_cfv (syn_c2nd) (.cv u)))) p0003 p0006
  have p0008 :=
    @g_hwcnpair u A
  have p0009 :=
    @g_eleq1d (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_chwcodes (syn_cfv (syn_c2nd) (.cv u))) p0008
  have p0010 :=
    @g_mpbird (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcodes (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_chwcodes (syn_cfv (syn_c2nd) (.cv u)))) p0007 p0009
  have p0011 :=
    @g_hwcnsupp u A
  have p0012 :=
    @g_jca (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcodes (syn_cfv (syn_c2nd) (.cv u)))) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) p0010 p0011
  have p0013 :=
    @g_elex (.cv u) (syn_chwcn A)
  have p0014 :=
    @g_elhwcncl (syn_cfv (syn_c2nd) (.cv u)) (.cv u)
  have p0015 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_cvv)) (syn_wb (.classMem (.cv u) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classMem (.cv u) (syn_chwcodes (syn_cfv (syn_c2nd) (.cv u)))) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))) p0013 p0014
  have p0016 :=
    @g_mpbird (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classMem (.cv u) (syn_chwcodes (syn_cfv (syn_c2nd) (.cv u)))) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) p0012 p0015
  exact p0016

noncomputable def g_hnpw13quoshiftf1ondv
    (A : Class) (hyp_hnpw13quoshiftf1ondv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wf1o (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 A))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 A))) (syn_csi (syn_csi (syn_chnsiquomap A))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord A)))) (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 A))))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_pw1ex A hyp_hnpw13quoshiftf1ondv_1
  have p0001 :=
    @g_pw1ex (syn_cpw1 A) p0000
  have p0002 :=
    @g_hnsiquomapf1ondv (syn_cpw1 (syn_cpw1 A)) p0001
  have p0003 :=
    @g_pw1ex A hyp_hnpw13quoshiftf1ondv_1
  have p0004 :=
    @g_hnsiquomapf1ondv (syn_cpw1 A) p0003
  have p0005 :=
    @g_pw1sif1omapndv (syn_cpw1 (syn_chnord (syn_cpw1 A))) (syn_chnord (syn_cpw1 (syn_cpw1 A))) (syn_chnsiquomap (syn_cpw1 A))
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_hnsiquomapf1ondv A hyp_hnpw13quoshiftf1ondv_1
  have p0008 :=
    @g_pw1sif1omapndv (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A)) (syn_chnsiquomap A)
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_pw1sif1omapndv (syn_cpw1 (syn_cpw1 (syn_chnord A))) (syn_cpw1 (syn_chnord (syn_cpw1 A))) (syn_csi (syn_chnsiquomap A))
  have p0011 :=
    Nominal.mp p0009 p0010
  have p0012 :=
    @g_pm3_2i (syn_wf1o (syn_csi (syn_chnsiquomap (syn_cpw1 A))) (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw1 A))))) (syn_wf1o (syn_csi (syn_csi (syn_chnsiquomap A))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord A)))) (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw1 A))))) p0006 p0011
  have p0013 :=
    @g_f1oco (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord A)))) (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw1 A)))) (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw1 A)))) (syn_csi (syn_chnsiquomap (syn_cpw1 A))) (syn_csi (syn_csi (syn_chnsiquomap A)))
  have p0014 :=
    Nominal.mp p0012 p0013
  have p0015 :=
    @g_pm3_2i (syn_wf1o (syn_chnsiquomap (syn_cpw1 (syn_cpw1 A))) (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw1 A)))) (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 A))))) (syn_wf1o (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 A))) (syn_csi (syn_csi (syn_chnsiquomap A)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord A)))) (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw1 A))))) p0002 p0014
  have p0016 :=
    @g_f1oco (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord A)))) (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw1 A)))) (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 A)))) (syn_chnsiquomap (syn_cpw1 (syn_cpw1 A))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 A))) (syn_csi (syn_csi (syn_chnsiquomap A))))
  have p0017 :=
    Nominal.mp p0015 p0016
  exact p0017

noncomputable def g_hnqcommonprecoverinjndv
    (D : Class) (S : Class) (E : Class) (J : Class) (hyp_hnqcommonprecoverinjndv_1 : Nominal.NPrf (.classMem D (syn_cvv))) (hyp_hnqcommonprecoverinjndv_2 : Nominal.NPrf (.classMem E (syn_cvv))) (hyp_hnqcommonprecoverinjndv_3 : Nominal.NPrf (syn_wf1 J S (syn_chnord D))) :
    Nominal.NPrf (.imp (syn_wss (syn_cima (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S) (syn_crn (syn_chnqinc E (syn_cun D E)))) (syn_wf1 (syn_cres (syn_ccom (syn_ccnv (syn_chnqinc E (syn_cun D E))) (syn_ccom (syn_chnqinc D (syn_cun D E)) J)) S) S (syn_chnord E))) := by
  let proofSupport : Finset Var := D.fv ∪ S.fv ∪ E.fv ∪ J.fv
  have p0000 :=
    @g_ssun2 E D
  have p0001 :=
    @g_unex D E hyp_hnqcommonprecoverinjndv_1 hyp_hnqcommonprecoverinjndv_2
  have p0002 :=
    @g_hnqincf1 (syn_cun D E) E p0000 hyp_hnqcommonprecoverinjndv_2 p0001
  have p0003 :=
    @g_f1cnv (syn_chnord E) (syn_chnord (syn_cun D E)) (syn_chnqinc E (syn_cun D E))
  have p0004 :=
    Nominal.mp p0002 p0003
  have p0005 :=
    @g_f1of1 (syn_crn (syn_chnqinc E (syn_cun D E))) (syn_chnord E) (syn_ccnv (syn_chnqinc E (syn_cun D E)))
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_a1i (syn_wf1 (syn_ccnv (syn_chnqinc E (syn_cun D E))) (syn_crn (syn_chnqinc E (syn_cun D E))) (syn_chnord E)) (syn_wss (syn_cima (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S) (syn_crn (syn_chnqinc E (syn_cun D E)))) p0006
  have p0008 :=
    @g_ssun1 D E
  have p0009 :=
    @g_unex D E hyp_hnqcommonprecoverinjndv_1 hyp_hnqcommonprecoverinjndv_2
  have p0010 :=
    @g_hnqincf1 (syn_cun D E) D p0008 hyp_hnqcommonprecoverinjndv_1 p0009
  have p0011 :=
    @g_pm3_2i (syn_wf1 (syn_chnqinc D (syn_cun D E)) (syn_chnord D) (syn_chnord (syn_cun D E))) (syn_wf1 J S (syn_chnord D)) p0010 hyp_hnqcommonprecoverinjndv_3
  have p0012 :=
    @g_f1co S (syn_chnord D) (syn_chnord (syn_cun D E)) (syn_chnqinc D (syn_cun D E)) J
  have p0013 :=
    Nominal.mp p0011 p0012
  have p0014 :=
    @g_ssid S
  have p0015 :=
    @g_pm3_2i (syn_wf1 (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S (syn_chnord (syn_cun D E))) (syn_wss S S) p0013 p0014
  have p0016 :=
    @g_f1ores S (syn_chnord (syn_cun D E)) S (syn_ccom (syn_chnqinc D (syn_cun D E)) J)
  have p0017 :=
    Nominal.mp p0015 p0016
  have p0018 :=
    @g_f1of1 S (syn_cima (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S) (syn_cres (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S)
  have p0019 :=
    Nominal.mp p0017 p0018
  have p0020 :=
    @g_a1i (syn_wf1 (syn_cres (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S) S (syn_cima (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S)) (syn_wss (syn_cima (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S) (syn_crn (syn_chnqinc E (syn_cun D E)))) p0019
  have p0021 :=
    @g_id (syn_wss (syn_cima (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S) (syn_crn (syn_chnqinc E (syn_cun D E))))
  have p0022 :=
    @g_jca (syn_wss (syn_cima (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S) (syn_crn (syn_chnqinc E (syn_cun D E)))) (syn_wf1 (syn_cres (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S) S (syn_cima (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S)) (syn_wss (syn_cima (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S) (syn_crn (syn_chnqinc E (syn_cun D E)))) p0020 p0021
  have p0023 :=
    @g_f1ss S (syn_cima (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S) (syn_crn (syn_chnqinc E (syn_cun D E))) (syn_cres (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S)
  have p0024 :=
    @g_syl (syn_wss (syn_cima (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S) (syn_crn (syn_chnqinc E (syn_cun D E)))) (syn_wa (syn_wf1 (syn_cres (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S) S (syn_cima (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S)) (syn_wss (syn_cima (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S) (syn_crn (syn_chnqinc E (syn_cun D E))))) (syn_wf1 (syn_cres (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S) S (syn_crn (syn_chnqinc E (syn_cun D E)))) p0022 p0023
  have p0025 :=
    @g_jca (syn_wss (syn_cima (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S) (syn_crn (syn_chnqinc E (syn_cun D E)))) (syn_wf1 (syn_ccnv (syn_chnqinc E (syn_cun D E))) (syn_crn (syn_chnqinc E (syn_cun D E))) (syn_chnord E)) (syn_wf1 (syn_cres (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S) S (syn_crn (syn_chnqinc E (syn_cun D E)))) p0007 p0024
  have p0026 :=
    @g_f1co S (syn_crn (syn_chnqinc E (syn_cun D E))) (syn_chnord E) (syn_ccnv (syn_chnqinc E (syn_cun D E))) (syn_cres (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S)
  have p0027 :=
    @g_syl (syn_wss (syn_cima (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S) (syn_crn (syn_chnqinc E (syn_cun D E)))) (syn_wa (syn_wf1 (syn_ccnv (syn_chnqinc E (syn_cun D E))) (syn_crn (syn_chnqinc E (syn_cun D E))) (syn_chnord E)) (syn_wf1 (syn_cres (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S) S (syn_crn (syn_chnqinc E (syn_cun D E))))) (syn_wf1 (syn_ccom (syn_ccnv (syn_chnqinc E (syn_cun D E))) (syn_cres (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S)) S (syn_chnord E)) p0025 p0026
  have p0028 :=
    @g_resco (syn_ccnv (syn_chnqinc E (syn_cun D E))) (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S
  have p0029 :=
    @g_f1eq1 S (syn_chnord E) (syn_cres (syn_ccom (syn_ccnv (syn_chnqinc E (syn_cun D E))) (syn_ccom (syn_chnqinc D (syn_cun D E)) J)) S) (syn_ccom (syn_ccnv (syn_chnqinc E (syn_cun D E))) (syn_cres (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S))
  have p0030 :=
    Nominal.mp p0028 p0029
  have p0031 :=
    @g_sylibr (syn_wss (syn_cima (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S) (syn_crn (syn_chnqinc E (syn_cun D E)))) (syn_wf1 (syn_ccom (syn_ccnv (syn_chnqinc E (syn_cun D E))) (syn_cres (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S)) S (syn_chnord E)) (syn_wf1 (syn_cres (syn_ccom (syn_ccnv (syn_chnqinc E (syn_cun D E))) (syn_ccom (syn_chnqinc D (syn_cun D E)) J)) S) S (syn_chnord E)) p0027 p0030
  exact p0031

#print axioms g_hnqcommonprecoverinjndv

end NFChoice.DirectNominalPrf.WPPReplay
