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
import NominalWPPReplayChunk017Compact001Part094

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

noncomputable def g_cfbwppfixedblockhnqimagecoverndv
    (X : Class) (hyp_cfbwppfixedblockhnqimagecoverndv_1 : Nominal.NPrf (.classMem X (syn_cvv))) (hyp_cfbwppfixedblockhnqimagecoverndv_2 : Nominal.NPrf (syn_wbr (syn_chncard (syn_cxp (syn_cxpk X X) (syn_cnnc))) (syn_clec) (syn_ctc (syn_ctc (syn_chncard X))))) :
    Nominal.NPrf (.imp (syn_wwpp) (syn_wss (syn_cima (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (syn_crn (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X)))))))) := by
  let proofSupport : Finset Var := X.fv
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_X : q ∉ X.fv := by
    intro h
    exact fresh_q (h)
  have dv_cache_0001 : q ∉ ((syn_wwpp)).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wwpp, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((syn_crn (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_cfbhnpw13pointcoverndv X q hyp_cfbwppfixedblockhnqimagecoverndv_1 hyp_cfbwppfixedblockhnqimagecoverndv_2
  have p0001 :=
    @g_com12 (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (syn_wwpp) (.classMem (syn_cfv (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) (.cv q)) (syn_crn (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))))) p0000
  have p0002 :=
    @g_ralrimiv (syn_wwpp) (.classMem (syn_cfv (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) (.cv q)) (syn_crn (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))))) q (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) dv_cache_0001 p0001
  have p0003 :=
    @g_ssun1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X)))
  have p0004 :=
    @g_pwexg X (syn_cvv)
  have p0005 :=
    Nominal.mp hyp_cfbwppfixedblockhnqimagecoverndv_1 p0004
  have p0006 :=
    @g_pw1exg (syn_cpw X) (syn_cvv)
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_pw1exg (syn_cpw1 (syn_cpw X)) (syn_cvv)
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_pw1exg (syn_cpw1 (syn_cpw1 (syn_cpw X))) (syn_cvv)
  have p0011 :=
    Nominal.mp p0009 p0010
  have p0012 :=
    @g_pwexg X (syn_cvv)
  have p0013 :=
    Nominal.mp hyp_cfbwppfixedblockhnqimagecoverndv_1 p0012
  have p0014 :=
    @g_pw1exg (syn_cpw X) (syn_cvv)
  have p0015 :=
    Nominal.mp p0013 p0014
  have p0016 :=
    @g_pw1exg (syn_cpw1 (syn_cpw X)) (syn_cvv)
  have p0017 :=
    Nominal.mp p0015 p0016
  have p0018 :=
    @g_pw1exg (syn_cpw1 (syn_cpw1 (syn_cpw X))) (syn_cvv)
  have p0019 :=
    Nominal.mp p0017 p0018
  have p0020 :=
    @g_hnordexg X
  have p0021 :=
    Nominal.mp hyp_cfbwppfixedblockhnqimagecoverndv_1 p0020
  have p0022 :=
    @g_pwexg (syn_chnord X) (syn_cvv)
  have p0023 :=
    Nominal.mp p0021 p0022
  have p0024 :=
    @g_pwexg (syn_cpw (syn_chnord X)) (syn_cvv)
  have p0025 :=
    Nominal.mp p0023 p0024
  have p0026 :=
    @g_pm3_2i (.classMem (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cvv)) (.classMem (syn_cpw (syn_cpw (syn_chnord X))) (syn_cvv)) p0019 p0025
  have p0027 :=
    @g_unexg (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))) (syn_cvv) (syn_cvv)
  have p0028 :=
    Nominal.mp p0026 p0027
  have p0029 :=
    @g_hnqincfn (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) p0003 p0011 p0028
  have p0030 :=
    @g_pwexg X (syn_cvv)
  have p0031 :=
    Nominal.mp hyp_cfbwppfixedblockhnqimagecoverndv_1 p0030
  have p0032 :=
    @g_hnpw13quoshiftf1ondv (syn_cpw X) p0031
  have p0033 :=
    @g_f1of (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))
  have p0034 :=
    Nominal.mp p0032 p0033
  have p0035 :=
    @g_pm3_2i (syn_wfn (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))))) (syn_wf (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))))) p0029 p0034
  have p0036 :=
    @g_fnfco (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))
  have p0037 :=
    Nominal.mp p0035 p0036
  have p0038 :=
    @g_fnfun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))))
  have p0039 :=
    Nominal.mp p0037 p0038
  have p0040 :=
    @g_ssun1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X)))
  have p0041 :=
    @g_pwexg X (syn_cvv)
  have p0042 :=
    Nominal.mp hyp_cfbwppfixedblockhnqimagecoverndv_1 p0041
  have p0043 :=
    @g_pw1exg (syn_cpw X) (syn_cvv)
  have p0044 :=
    Nominal.mp p0042 p0043
  have p0045 :=
    @g_pw1exg (syn_cpw1 (syn_cpw X)) (syn_cvv)
  have p0046 :=
    Nominal.mp p0044 p0045
  have p0047 :=
    @g_pw1exg (syn_cpw1 (syn_cpw1 (syn_cpw X))) (syn_cvv)
  have p0048 :=
    Nominal.mp p0046 p0047
  have p0049 :=
    @g_pwexg X (syn_cvv)
  have p0050 :=
    Nominal.mp hyp_cfbwppfixedblockhnqimagecoverndv_1 p0049
  have p0051 :=
    @g_pw1exg (syn_cpw X) (syn_cvv)
  have p0052 :=
    Nominal.mp p0050 p0051
  have p0053 :=
    @g_pw1exg (syn_cpw1 (syn_cpw X)) (syn_cvv)
  have p0054 :=
    Nominal.mp p0052 p0053
  have p0055 :=
    @g_pw1exg (syn_cpw1 (syn_cpw1 (syn_cpw X))) (syn_cvv)
  have p0056 :=
    Nominal.mp p0054 p0055
  have p0057 :=
    @g_hnordexg X
  have p0058 :=
    Nominal.mp hyp_cfbwppfixedblockhnqimagecoverndv_1 p0057
  have p0059 :=
    @g_pwexg (syn_chnord X) (syn_cvv)
  have p0060 :=
    Nominal.mp p0058 p0059
  have p0061 :=
    @g_pwexg (syn_cpw (syn_chnord X)) (syn_cvv)
  have p0062 :=
    Nominal.mp p0060 p0061
  have p0063 :=
    @g_pm3_2i (.classMem (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cvv)) (.classMem (syn_cpw (syn_cpw (syn_chnord X))) (syn_cvv)) p0056 p0062
  have p0064 :=
    @g_unexg (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))) (syn_cvv) (syn_cvv)
  have p0065 :=
    Nominal.mp p0063 p0064
  have p0066 :=
    @g_hnqincfn (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) p0040 p0048 p0065
  have p0067 :=
    @g_pwexg X (syn_cvv)
  have p0068 :=
    Nominal.mp hyp_cfbwppfixedblockhnqimagecoverndv_1 p0067
  have p0069 :=
    @g_hnpw13quoshiftf1ondv (syn_cpw X) p0068
  have p0070 :=
    @g_f1of (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))
  have p0071 :=
    Nominal.mp p0069 p0070
  have p0072 :=
    @g_pm3_2i (syn_wfn (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))))) (syn_wf (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))))) p0066 p0071
  have p0073 :=
    @g_fnfco (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))
  have p0074 :=
    Nominal.mp p0072 p0073
  have p0075 :=
    @g_fndm (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))))
  have p0076 :=
    Nominal.mp p0074 p0075
  have p0077 :=
    @g_eqcomi (syn_cdm (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) p0076
  have p0078 :=
    @g_ssid (syn_cdm (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))))
  have p0079 :=
    @g_eqsstri (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (syn_cdm (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))))) (syn_cdm (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))))) p0077 p0078
  have p0080 :=
    @g_pm3_2i (syn_wfun (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))))) (syn_wss (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (syn_cdm (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))))) p0039 p0079
  have p0081 :=
    @g_funimass4 q (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (syn_crn (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X)))))) (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0082 :=
    Nominal.mp p0080 p0081
  have p0083 :=
    @g_sylibr (syn_wwpp) (syn_wral q (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (.classMem (syn_cfv (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) (.cv q)) (syn_crn (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X)))))))) (syn_wss (syn_cima (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (syn_crn (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))))) p0002 p0082
  exact p0083

noncomputable def g_cfbwppfixedblockhnqgraphinjndv
    (X : Class) (hyp_cfbwppfixedblockhnqgraphinjndv_1 : Nominal.NPrf (.classMem X (syn_cvv))) (hyp_cfbwppfixedblockhnqgraphinjndv_2 : Nominal.NPrf (syn_wbr (syn_chncard (syn_cxp (syn_cxpk X X) (syn_cnnc))) (syn_clec) (syn_ctc (syn_ctc (syn_chncard X))))) :
    Nominal.NPrf (.imp (syn_wwpp) (syn_wf1 (syn_cres (syn_ccom (syn_ccnv (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X)))))) (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (syn_chnord (syn_cpw (syn_cpw (syn_chnord X)))))) := by
  let proofSupport : Finset Var := X.fv
  have p0000 :=
    @g_cfbwppfixedblockhnqimagecoverndv X hyp_cfbwppfixedblockhnqgraphinjndv_1 hyp_cfbwppfixedblockhnqgraphinjndv_2
  have p0001 :=
    @g_pwexg X (syn_cvv)
  have p0002 :=
    Nominal.mp hyp_cfbwppfixedblockhnqgraphinjndv_1 p0001
  have p0003 :=
    @g_pw1exg (syn_cpw X) (syn_cvv)
  have p0004 :=
    Nominal.mp p0002 p0003
  have p0005 :=
    @g_pw1exg (syn_cpw1 (syn_cpw X)) (syn_cvv)
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_pw1exg (syn_cpw1 (syn_cpw1 (syn_cpw X))) (syn_cvv)
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_hnordexg X
  have p0010 :=
    Nominal.mp hyp_cfbwppfixedblockhnqgraphinjndv_1 p0009
  have p0011 :=
    @g_pwexg (syn_chnord X) (syn_cvv)
  have p0012 :=
    Nominal.mp p0010 p0011
  have p0013 :=
    @g_pwexg (syn_cpw (syn_chnord X)) (syn_cvv)
  have p0014 :=
    Nominal.mp p0012 p0013
  have p0015 :=
    @g_pwexg X (syn_cvv)
  have p0016 :=
    Nominal.mp hyp_cfbwppfixedblockhnqgraphinjndv_1 p0015
  have p0017 :=
    @g_hnpw13quoshiftf1ondv (syn_cpw X) p0016
  have p0018 :=
    @g_f1of1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))
  have p0019 :=
    Nominal.mp p0017 p0018
  have p0020 :=
    @g_hnqcommonprecoverinjndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (syn_cpw (syn_cpw (syn_chnord X))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))) p0008 p0014 p0019
  have p0021 :=
    @g_syl (syn_wwpp) (syn_wss (syn_cima (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (syn_crn (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))))) (syn_wf1 (syn_cres (syn_ccom (syn_ccnv (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X)))))) (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (syn_chnord (syn_cpw (syn_cpw (syn_chnord X))))) p0000 p0020
  exact p0021

#print axioms g_cfbwppfixedblockhnqgraphinjndv

end NFChoice.DirectNominalPrf.WPPReplay
