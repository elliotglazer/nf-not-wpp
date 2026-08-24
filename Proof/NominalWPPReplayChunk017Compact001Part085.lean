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
import NominalWPPReplayChunk017Compact001Part084

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

noncomputable def g_wppconcrete6tcbandgrowthfrompointhwclecdndv
    (y : Var) (hyp_wppconcrete6tcbandgrowthfrompointhwclecdndv_1 : Nominal.NPrf (.imp (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))))) :
    Nominal.NPrf (.imp (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.imp (syn_wwpp) (.imp (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y)) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))))))) := by
  let proofSupport : Finset Var := ({y} : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_singleton.mpr h)
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have dv_cache_0001 : z ∉ ((Class.cv y)).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((syn_chncard (syn_c1c))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppconcrete6fn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((Wff.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv y)) (syn_cncs))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppconcrete6fn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y)))
  have p0001 :=
    @g_a1i (.imp (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y)))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) p0000
  have p0002 :=
    @g_simpl (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))
  have p0003 :=
    @g_syl (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) p0002 hyp_wppconcrete6tcbandgrowthfrompointhwclecdndv_1
  have p0004 :=
    @g_simpr (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))
  have p0005 :=
    @g_id (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
  have p0006 :=
    @g_hwcardssnc (syn_cvv)
  have p0007 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (.cv y) p0006
  have p0008 :=
    @g_id (.classMem (.cv y) (syn_chwcards (syn_cvv)))
  have p0009 :=
    @g_a1ii (.imp (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.classMem (.cv y) (syn_cncs))) (.imp (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.classMem (.cv y) (syn_chwcards (syn_cvv)))) p0007 p0008
  have p0010 :=
    @g_hncardnc1ndv
  have p0011 :=
    @g_jctir (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.classMem (.cv y) (syn_cncs)) (.classMem (syn_chncard (syn_c1c)) (syn_cncs)) p0009 p0010
  have p0012 :=
    @g_biantrurd (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wa (.classMem (.cv y) (syn_cncs)) (.classMem (syn_chncard (syn_c1c)) (syn_cncs))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) p0011
  have p0013 :=
    (by simpa [syn_wb, syn_w3a] using (Nominal.biimpRefl (syn_w3a (.classMem (.cv y) (syn_cncs)) (.classMem (syn_chncard (syn_c1c)) (syn_cncs)) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))))
  have p0014 :=
    @g_syl6rbbr (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cncs)) (.classMem (syn_chncard (syn_c1c)) (syn_cncs))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_w3a (.classMem (.cv y) (syn_cncs)) (.classMem (syn_chncard (syn_c1c)) (syn_cncs)) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) p0012 p0013
  have p0015 :=
    @g_syl5ibr (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_w3a (.classMem (.cv y) (syn_cncs)) (.classMem (syn_chncard (syn_c1c)) (syn_cncs)) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) p0005 p0014
  have p0016 :=
    @g_letc6ncrepdv z (.cv y) (syn_chncard (syn_c1c)) dv_cache_0001 dv_cache_0002
  have p0017 :=
    @g_syl6 (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_w3a (.classMem (.cv y) (syn_cncs)) (.classMem (syn_chncard (syn_c1c)) (syn_cncs)) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_wex z (.classEq (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))) p0015 p0016
  have p0018 :=
    @g_a1dd (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wex z (.classEq (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y)) p0017
  have p0019 :=
    @g_nfv (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y)) z dv_cache_0003
  have p0020 :=
    @g_nfv (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))) z dv_cache_0004
  have p0021 :=
    @g_simpl (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y)) (.classEq (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
  have p0022 :=
    (by simpa [syn_chncard] using (Nominal.classEqRefl (syn_chncard (syn_c1c))))
  have p0023 :=
    @g_tceq (syn_chncard (syn_c1c)) (syn_cnc (syn_chnord (syn_c1c)))
  have p0024 :=
    Nominal.mp p0022 p0023
  have p0025 :=
    @g_n_1cex
  have p0026 :=
    @g_hnordex (syn_c1c) p0025
  have p0027 :=
    @g_tcnc (syn_chnord (syn_c1c)) p0026
  have p0028 :=
    @g_eqtri (syn_ctc (syn_chncard (syn_c1c))) (syn_ctc (syn_cnc (syn_chnord (syn_c1c)))) (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c)))) p0024 p0027
  have p0029 :=
    @g_tceq (syn_ctc (syn_chncard (syn_c1c))) (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c))))
  have p0030 :=
    Nominal.mp p0028 p0029
  have p0031 :=
    @g_tceq (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))) (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c)))))
  have p0032 :=
    Nominal.mp p0030 p0031
  have p0033 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))) (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c))))))
  have p0034 :=
    Nominal.mp p0032 p0033
  have p0035 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))) (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c)))))))
  have p0036 :=
    Nominal.mp p0034 p0035
  have p0037 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c))))))))
  have p0038 :=
    Nominal.mp p0036 p0037
  have p0039 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c)))))))))
  have p0040 :=
    Nominal.mp p0038 p0039
  have p0041 :=
    @g_a1i (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c))))))))))) (syn_wa (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y)) (.classEq (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))) p0040
  have p0042 :=
    @g_simpr (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y)) (.classEq (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
  have p0043 :=
    @g_breq12d (syn_wa (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y)) (.classEq (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c)))))))))) (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))) (syn_clec) p0041 p0042
  have p0044 :=
    @g_mpbid (syn_wa (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y)) (.classEq (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y)) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c)))))))))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) p0021 p0043
  have p0045 :=
    @g_n_1cex
  have p0046 :=
    @g_hnordex (syn_c1c) p0045
  have p0047 :=
    @g_pw1ex (syn_chnord (syn_c1c)) p0046
  have p0048 :=
    @g_vex z
  have p0049 :=
    @g_wppconcrete6representedmonondv (syn_cpw1 (syn_chnord (syn_c1c))) (.cv z) p0047 p0048
  have p0050 :=
    @g_syl (syn_wa (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y)) (.classEq (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c)))))))))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c))))))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))) p0044 p0049
  have p0051 :=
    (by simpa [syn_chncard] using (Nominal.classEqRefl (syn_chncard (syn_c1c))))
  have p0052 :=
    @g_tceq (syn_chncard (syn_c1c)) (syn_cnc (syn_chnord (syn_c1c)))
  have p0053 :=
    Nominal.mp p0051 p0052
  have p0054 :=
    @g_n_1cex
  have p0055 :=
    @g_hnordex (syn_c1c) p0054
  have p0056 :=
    @g_tcnc (syn_chnord (syn_c1c)) p0055
  have p0057 :=
    @g_eqtri (syn_ctc (syn_chncard (syn_c1c))) (syn_ctc (syn_cnc (syn_chnord (syn_c1c)))) (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c)))) p0053 p0056
  have p0058 :=
    @g_tceq (syn_ctc (syn_chncard (syn_c1c))) (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c))))
  have p0059 :=
    Nominal.mp p0057 p0058
  have p0060 :=
    @g_tceq (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))) (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c)))))
  have p0061 :=
    Nominal.mp p0059 p0060
  have p0062 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))) (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c))))))
  have p0063 :=
    Nominal.mp p0061 p0062
  have p0064 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))) (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c)))))))
  have p0065 :=
    Nominal.mp p0063 p0064
  have p0066 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c))))))))
  have p0067 :=
    Nominal.mp p0065 p0066
  have p0068 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c)))))))))
  have p0069 :=
    Nominal.mp p0067 p0068
  have p0070 :=
    @g_fveq2i (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c)))))))))) (syn_cwppconcrete6fn) p0069
  have p0071 :=
    @g_a1i (.classEq (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c)))))))))))) (syn_wa (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y)) (.classEq (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))) p0070
  have p0072 :=
    @g_simpr (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y)) (.classEq (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
  have p0073 :=
    @g_fveq2d (syn_wa (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y)) (.classEq (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))) (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))) (syn_cwppconcrete6fn) p0072
  have p0074 :=
    @g_breq12d (syn_wa (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y)) (.classEq (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c))))))))))) (syn_cfv (syn_cwppconcrete6fn) (.cv y)) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) (syn_clec) p0071 p0073
  have p0075 :=
    @g_mpbird (syn_wa (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y)) (.classEq (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))) (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))) (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c))))))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))) p0050 p0074
  have p0076 :=
    @g_ex (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y)) (.classEq (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))) p0075
  have p0077 :=
    @g_exlimd (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y)) (.classEq (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))) z p0019 p0020 p0076
  have p0078 :=
    @g_a2i (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y)) (syn_wex z (.classEq (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))) (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))) p0077
  have p0079 :=
    @g_syl6 (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.imp (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y)) (syn_wex z (.classEq (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))) (.imp (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y)) (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))) p0018 p0078
  have p0080 :=
    @g_syl7 (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y)) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))) p0004 p0079
  have p0081 :=
    @g_a1dd (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.imp (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) p0080
  have p0082 :=
    @g_pm3_2 (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))
  have p0083 :=
    @g_a1i (.imp (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (.imp (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))) (syn_wa (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) p0082
  have p0084 :=
    @g_imim2 (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))) (syn_wa (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))) (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y)))
  have p0085 :=
    @g_syl6 (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (.imp (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))) (syn_wa (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))))) (.imp (.imp (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))) (.imp (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wa (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))))) p0083 p0084
  have p0086 :=
    @g_a2d (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (.imp (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))) (.imp (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wa (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))))) p0085
  have p0087 :=
    @g_sylcom (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.imp (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (.imp (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))))) (.imp (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (.imp (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wa (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))))) p0081 p0086
  have p0088 :=
    @g_syl7 (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.imp (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wa (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))))) p0003 p0087
  have p0089 :=
    Nominal.ax2 (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wa (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))))
  have p0090 :=
    @g_syl6 (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.imp (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (.imp (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wa (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))))) (.imp (.imp (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y)))) (.imp (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wa (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))))) p0088 p0089
  have p0091 :=
    @g_mpdi (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.imp (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y)))) (.imp (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wa (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))))) p0001 p0090
  have p0092 :=
    @g_id (.classEq (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
  have p0093 :=
    @g_fveq2d (.classEq (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))) (syn_cwppconcrete6fn) p0092
  have p0094 :=
    @g_vex z
  have p0095 :=
    @g_wppconcrete6fnvalndv (.cv z) p0094
  have p0096 :=
    @g_vex z
  have p0097 :=
    @g_pwex (.cv z) p0096
  have p0098 :=
    @g_pwex (syn_cpw (.cv z)) p0097
  have p0099 :=
    @g_hnordex (syn_cpw (syn_cpw (.cv z))) p0098
  have p0100 :=
    @g_hncardnc (syn_chnord (syn_cpw (syn_cpw (.cv z))))
  have p0101 :=
    Nominal.mp p0099 p0100
  have p0102 :=
    @g_eqeltri (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv z))))) (syn_cncs) p0095 p0101
  have p0103 :=
    @g_a1i (.classMem (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) (syn_cncs)) (.classEq (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) p0102
  have p0104 :=
    @g_eqeltrd (.classEq (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) (syn_cfv (syn_cwppconcrete6fn) (.cv y)) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) (syn_cncs) p0093 p0103
  have p0105 :=
    @g_exlimiv (.classEq (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv y)) (syn_cncs)) z dv_cache_0005 p0104
  have p0106 :=
    @g_syl6 (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wex z (.classEq (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))) (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv y)) (syn_cncs)) p0017 p0105
  have p0107 :=
    (by simpa [syn_wb, syn_w3a] using (Nominal.biimpRefl (syn_w3a (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_cncs)) (.classMem (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_cncs)) (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv y)) (syn_cncs)))))
  have p0108 :=
    @g_hncardnc1ndv
  have p0109 :=
    @g_tccl (syn_chncard (syn_c1c))
  have p0110 :=
    Nominal.mp p0108 p0109
  have p0111 :=
    @g_tccl (syn_ctc (syn_chncard (syn_c1c)))
  have p0112 :=
    Nominal.mp p0110 p0111
  have p0113 :=
    @g_tccl (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))
  have p0114 :=
    Nominal.mp p0112 p0113
  have p0115 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))
  have p0116 :=
    Nominal.mp p0114 p0115
  have p0117 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))
  have p0118 :=
    Nominal.mp p0116 p0117
  have p0119 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))
  have p0120 :=
    Nominal.mp p0118 p0119
  have p0121 :=
    @g_wppconcrete6tcvalncndv
  have p0122 :=
    @g_pm3_2i (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_cncs)) (.classMem (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_cncs)) p0120 p0121
  have p0123 :=
    @g_biantrur (syn_wa (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_cncs)) (.classMem (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_cncs))) (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv y)) (syn_cncs)) p0122
  have p0124 :=
    @g_bitr4i (syn_w3a (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_cncs)) (.classMem (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_cncs)) (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv y)) (syn_cncs))) (syn_wa (syn_wa (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_cncs)) (.classMem (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_cncs))) (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv y)) (syn_cncs))) (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv y)) (syn_cncs)) p0107 p0123
  have p0125 :=
    @g_a1i (syn_wb (syn_w3a (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_cncs)) (.classMem (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_cncs)) (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv y)) (syn_cncs))) (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv y)) (syn_cncs))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) p0124
  have p0126 :=
    @g_biimprd (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_w3a (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_cncs)) (.classMem (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_cncs)) (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv y)) (syn_cncs))) (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv y)) (syn_cncs)) p0125
  have p0127 :=
    @g_sylcom (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv y)) (syn_cncs)) (syn_w3a (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_cncs)) (.classMem (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_cncs)) (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv y)) (syn_cncs))) p0106 p0126
  have p0128 :=
    @g_lectr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_cfv (syn_cwppconcrete6fn) (.cv y))
  have p0129 :=
    @g_syl6 (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_w3a (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_cncs)) (.classMem (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_cncs)) (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv y)) (syn_cncs))) (.imp (syn_wa (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))) p0127 p0128
  have p0130 :=
    @g_syldd (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y))) (syn_wa (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))) p0091 p0129
  have p0131 :=
    @g_exp4a (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_clec) (.cv y)) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))) p0130
  exact p0131

#print axioms g_wppconcrete6tcbandgrowthfrompointhwclecdndv

end NFChoice.DirectNominalPrf.WPPReplay
