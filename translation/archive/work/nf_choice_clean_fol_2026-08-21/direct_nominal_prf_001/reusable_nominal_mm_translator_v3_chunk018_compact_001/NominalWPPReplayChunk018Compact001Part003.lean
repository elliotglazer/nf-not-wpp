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
import NominalWPPReplayChunk018Compact001Part002

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

noncomputable def g_cfbliteralp17hncardboundndv
     :
    Nominal.NPrf (syn_wbr (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))) (syn_cnnc))) (syn_clec) (syn_ctc (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_cfbliteralunivhncardboundndv
  have p0001 :=
    @g_vvex
  have p0002 :=
    @g_vvex
  have p0003 :=
    @g_xpkex (syn_cvv) (syn_cvv) p0001 p0002
  have p0004 :=
    @g_nncex
  have p0005 :=
    @g_xpex (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc) p0003 p0004
  have p0006 :=
    @g_hncardnc (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc))
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_vvex
  have p0009 :=
    @g_pw1ex (syn_cvv) p0008
  have p0010 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0009
  have p0011 :=
    @g_hncardnc (syn_cpw1 (syn_cpw1 (syn_cvv)))
  have p0012 :=
    Nominal.mp p0010 p0011
  have p0013 :=
    @g_pm3_2i (.classMem (syn_chncard (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc))) (syn_cncs)) (.classMem (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cncs)) p0007 p0012
  have p0014 :=
    @g_tlecg (syn_chncard (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cvv))))
  have p0015 :=
    Nominal.mp p0013 p0014
  have p0016 :=
    @g_mpbi (syn_wbr (syn_chncard (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc))) (syn_clec) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_wbr (syn_ctc (syn_chncard (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc)))) (syn_clec) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0000 p0015
  have p0017 :=
    @g_vvex
  have p0018 :=
    @g_vvex
  have p0019 :=
    @g_xpkex (syn_cvv) (syn_cvv) p0017 p0018
  have p0020 :=
    @g_nncex
  have p0021 :=
    @g_xpex (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc) p0019 p0020
  have p0022 :=
    @g_hncardtcshiftndv (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc)) p0021
  have p0023 :=
    @g_vvex
  have p0024 :=
    @g_vvex
  have p0025 :=
    @g_xpkex (syn_cvv) (syn_cvv) p0023 p0024
  have p0026 :=
    @g_nncex
  have p0027 :=
    @g_xpex (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc) p0025 p0026
  have p0028 :=
    @g_pw1ex (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc)) p0027
  have p0029 :=
    @g_vvex
  have p0030 :=
    @g_pw1ex (syn_cvv) p0029
  have p0031 :=
    @g_vvex
  have p0032 :=
    @g_pw1ex (syn_cvv) p0031
  have p0033 :=
    @g_xpkex (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)) p0030 p0032
  have p0034 :=
    @g_nncex
  have p0035 :=
    @g_xpex (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc) p0033 p0034
  have p0036 :=
    @g_vvex
  have p0037 :=
    @g_wpplitshiftenndv (syn_cvv) p0036
  have p0038 :=
    @g_vvex
  have p0039 :=
    @g_vvex
  have p0040 :=
    @g_xpkex (syn_cvv) (syn_cvv) p0038 p0039
  have p0041 :=
    @g_nncex
  have p0042 :=
    @g_xpex (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc) p0040 p0041
  have p0043 :=
    @g_pw1ex (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc)) p0042
  have p0044 :=
    @g_eqnc (syn_cpw1 (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc))) (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc)) p0043
  have p0045 :=
    @g_mpbir (.classEq (syn_cnc (syn_cpw1 (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc)))) (syn_cnc (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc)))) (syn_wbr (syn_cpw1 (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc))) (syn_cen) (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc))) p0037 p0044
  have p0046 :=
    @g_hncardnceqndv (syn_cpw1 (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc))) (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc)) p0028 p0035 p0045
  have p0047 :=
    @g_eqtri (syn_ctc (syn_chncard (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc)))) (syn_chncard (syn_cpw1 (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc)))) (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc))) p0022 p0046
  have p0048 :=
    @g_vvex
  have p0049 :=
    @g_pw1ex (syn_cvv) p0048
  have p0050 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0049
  have p0051 :=
    @g_hncardtcshiftndv (syn_cpw1 (syn_cpw1 (syn_cvv))) p0050
  have p0052 :=
    @g_breq12i (syn_ctc (syn_chncard (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc)))) (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc))) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_clec) p0047 p0051
  have p0053 :=
    @g_mpbi (syn_wbr (syn_ctc (syn_chncard (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc)))) (syn_clec) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_wbr (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc))) (syn_clec) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0016 p0052
  have p0054 :=
    @g_vvex
  have p0055 :=
    @g_pw1ex (syn_cvv) p0054
  have p0056 :=
    @g_vvex
  have p0057 :=
    @g_pw1ex (syn_cvv) p0056
  have p0058 :=
    @g_xpkex (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)) p0055 p0057
  have p0059 :=
    @g_nncex
  have p0060 :=
    @g_xpex (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc) p0058 p0059
  have p0061 :=
    @g_hncardnc (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc))
  have p0062 :=
    Nominal.mp p0060 p0061
  have p0063 :=
    @g_vvex
  have p0064 :=
    @g_pw1ex (syn_cvv) p0063
  have p0065 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0064
  have p0066 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0065
  have p0067 :=
    @g_hncardnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
  have p0068 :=
    Nominal.mp p0066 p0067
  have p0069 :=
    @g_pm3_2i (.classMem (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc))) (syn_cncs)) (.classMem (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cncs)) p0062 p0068
  have p0070 :=
    @g_tlecg (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
  have p0071 :=
    Nominal.mp p0069 p0070
  have p0072 :=
    @g_mpbi (syn_wbr (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc))) (syn_clec) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_wbr (syn_ctc (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc)))) (syn_clec) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) p0053 p0071
  have p0073 :=
    @g_vvex
  have p0074 :=
    @g_pw1ex (syn_cvv) p0073
  have p0075 :=
    @g_vvex
  have p0076 :=
    @g_pw1ex (syn_cvv) p0075
  have p0077 :=
    @g_xpkex (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)) p0074 p0076
  have p0078 :=
    @g_nncex
  have p0079 :=
    @g_xpex (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc) p0077 p0078
  have p0080 :=
    @g_hncardtcshiftndv (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc)) p0079
  have p0081 :=
    @g_vvex
  have p0082 :=
    @g_pw1ex (syn_cvv) p0081
  have p0083 :=
    @g_vvex
  have p0084 :=
    @g_pw1ex (syn_cvv) p0083
  have p0085 :=
    @g_xpkex (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)) p0082 p0084
  have p0086 :=
    @g_nncex
  have p0087 :=
    @g_xpex (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc) p0085 p0086
  have p0088 :=
    @g_pw1ex (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc)) p0087
  have p0089 :=
    @g_vvex
  have p0090 :=
    @g_pw1ex (syn_cvv) p0089
  have p0091 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0090
  have p0092 :=
    @g_vvex
  have p0093 :=
    @g_pw1ex (syn_cvv) p0092
  have p0094 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0093
  have p0095 :=
    @g_xpkex (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))) p0091 p0094
  have p0096 :=
    @g_nncex
  have p0097 :=
    @g_xpex (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cnnc) p0095 p0096
  have p0098 :=
    @g_vvex
  have p0099 :=
    @g_pw1ex (syn_cvv) p0098
  have p0100 :=
    @g_wpplitshiftenndv (syn_cpw1 (syn_cvv)) p0099
  have p0101 :=
    @g_vvex
  have p0102 :=
    @g_pw1ex (syn_cvv) p0101
  have p0103 :=
    @g_vvex
  have p0104 :=
    @g_pw1ex (syn_cvv) p0103
  have p0105 :=
    @g_xpkex (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)) p0102 p0104
  have p0106 :=
    @g_nncex
  have p0107 :=
    @g_xpex (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc) p0105 p0106
  have p0108 :=
    @g_pw1ex (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc)) p0107
  have p0109 :=
    @g_eqnc (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc))) (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cnnc)) p0108
  have p0110 :=
    @g_mpbir (.classEq (syn_cnc (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc)))) (syn_cnc (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cnnc)))) (syn_wbr (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc))) (syn_cen) (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cnnc))) p0100 p0109
  have p0111 :=
    @g_hncardnceqndv (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc))) (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cnnc)) p0088 p0097 p0110
  have p0112 :=
    @g_eqtri (syn_ctc (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc)))) (syn_chncard (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc)))) (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cnnc))) p0080 p0111
  have p0113 :=
    @g_vvex
  have p0114 :=
    @g_pw1ex (syn_cvv) p0113
  have p0115 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0114
  have p0116 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0115
  have p0117 :=
    @g_hncardtcshiftndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0116
  have p0118 :=
    @g_breq12i (syn_ctc (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc)))) (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cnnc))) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_clec) p0112 p0117
  have p0119 :=
    @g_mpbi (syn_wbr (syn_ctc (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_cnnc)))) (syn_clec) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_wbr (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cnnc))) (syn_clec) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) p0072 p0118
  have p0120 :=
    @g_vvex
  have p0121 :=
    @g_pw1ex (syn_cvv) p0120
  have p0122 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0121
  have p0123 :=
    @g_vvex
  have p0124 :=
    @g_pw1ex (syn_cvv) p0123
  have p0125 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0124
  have p0126 :=
    @g_xpkex (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))) p0122 p0125
  have p0127 :=
    @g_nncex
  have p0128 :=
    @g_xpex (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cnnc) p0126 p0127
  have p0129 :=
    @g_hncardnc (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cnnc))
  have p0130 :=
    Nominal.mp p0128 p0129
  have p0131 :=
    @g_vvex
  have p0132 :=
    @g_pw1ex (syn_cvv) p0131
  have p0133 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0132
  have p0134 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0133
  have p0135 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0134
  have p0136 :=
    @g_hncardnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
  have p0137 :=
    Nominal.mp p0135 p0136
  have p0138 :=
    @g_pm3_2i (.classMem (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cnnc))) (syn_cncs)) (.classMem (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cncs)) p0130 p0137
  have p0139 :=
    @g_tlecg (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cnnc))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
  have p0140 :=
    Nominal.mp p0138 p0139
  have p0141 :=
    @g_mpbi (syn_wbr (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cnnc))) (syn_clec) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_wbr (syn_ctc (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cnnc)))) (syn_clec) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) p0119 p0140
  have p0142 :=
    @g_vvex
  have p0143 :=
    @g_pw1ex (syn_cvv) p0142
  have p0144 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0143
  have p0145 :=
    @g_vvex
  have p0146 :=
    @g_pw1ex (syn_cvv) p0145
  have p0147 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0146
  have p0148 :=
    @g_xpkex (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))) p0144 p0147
  have p0149 :=
    @g_nncex
  have p0150 :=
    @g_xpex (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cnnc) p0148 p0149
  have p0151 :=
    @g_hncardtcshiftndv (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cnnc)) p0150
  have p0152 :=
    @g_vvex
  have p0153 :=
    @g_pw1ex (syn_cvv) p0152
  have p0154 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0153
  have p0155 :=
    @g_vvex
  have p0156 :=
    @g_pw1ex (syn_cvv) p0155
  have p0157 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0156
  have p0158 :=
    @g_xpkex (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))) p0154 p0157
  have p0159 :=
    @g_nncex
  have p0160 :=
    @g_xpex (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cnnc) p0158 p0159
  have p0161 :=
    @g_pw1ex (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cnnc)) p0160
  have p0162 :=
    @g_vvex
  have p0163 :=
    @g_pw1ex (syn_cvv) p0162
  have p0164 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0163
  have p0165 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0164
  have p0166 :=
    @g_vvex
  have p0167 :=
    @g_pw1ex (syn_cvv) p0166
  have p0168 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0167
  have p0169 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0168
  have p0170 :=
    @g_xpkex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0165 p0169
  have p0171 :=
    @g_nncex
  have p0172 :=
    @g_xpex (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc) p0170 p0171
  have p0173 :=
    @g_vvex
  have p0174 :=
    @g_pw1ex (syn_cvv) p0173
  have p0175 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0174
  have p0176 :=
    @g_wpplitshiftenndv (syn_cpw1 (syn_cpw1 (syn_cvv))) p0175
  have p0177 :=
    @g_vvex
  have p0178 :=
    @g_pw1ex (syn_cvv) p0177
  have p0179 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0178
  have p0180 :=
    @g_vvex
  have p0181 :=
    @g_pw1ex (syn_cvv) p0180
  have p0182 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0181
  have p0183 :=
    @g_xpkex (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))) p0179 p0182
  have p0184 :=
    @g_nncex
  have p0185 :=
    @g_xpex (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cnnc) p0183 p0184
  have p0186 :=
    @g_pw1ex (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cnnc)) p0185
  have p0187 :=
    @g_eqnc (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cnnc))) (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc)) p0186
  have p0188 :=
    @g_mpbir (.classEq (syn_cnc (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cnnc)))) (syn_cnc (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc)))) (syn_wbr (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cnnc))) (syn_cen) (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc))) p0176 p0187
  have p0189 :=
    @g_hncardnceqndv (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cnnc))) (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc)) p0161 p0172 p0188
  have p0190 :=
    @g_eqtri (syn_ctc (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cnnc)))) (syn_chncard (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cnnc)))) (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc))) p0151 p0189
  have p0191 :=
    @g_vvex
  have p0192 :=
    @g_pw1ex (syn_cvv) p0191
  have p0193 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0192
  have p0194 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0193
  have p0195 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0194
  have p0196 :=
    @g_hncardtcshiftndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0195
  have p0197 :=
    @g_breq12i (syn_ctc (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cnnc)))) (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc))) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_clec) p0190 p0196
  have p0198 :=
    @g_mpbi (syn_wbr (syn_ctc (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cnnc)))) (syn_clec) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_wbr (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc))) (syn_clec) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) p0141 p0197
  have p0199 :=
    @g_vvex
  have p0200 :=
    @g_pw1ex (syn_cvv) p0199
  have p0201 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0200
  have p0202 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0201
  have p0203 :=
    @g_vvex
  have p0204 :=
    @g_pw1ex (syn_cvv) p0203
  have p0205 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0204
  have p0206 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0205
  have p0207 :=
    @g_xpkex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0202 p0206
  have p0208 :=
    @g_nncex
  have p0209 :=
    @g_xpex (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc) p0207 p0208
  have p0210 :=
    @g_hncardnc (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc))
  have p0211 :=
    Nominal.mp p0209 p0210
  have p0212 :=
    @g_vvex
  have p0213 :=
    @g_pw1ex (syn_cvv) p0212
  have p0214 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0213
  have p0215 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0214
  have p0216 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0215
  have p0217 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0216
  have p0218 :=
    @g_hncardnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
  have p0219 :=
    Nominal.mp p0217 p0218
  have p0220 :=
    @g_pm3_2i (.classMem (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc))) (syn_cncs)) (.classMem (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cncs)) p0211 p0219
  have p0221 :=
    @g_tlecg (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
  have p0222 :=
    Nominal.mp p0220 p0221
  have p0223 :=
    @g_mpbi (syn_wbr (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc))) (syn_clec) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_wbr (syn_ctc (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc)))) (syn_clec) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))) p0198 p0222
  have p0224 :=
    @g_vvex
  have p0225 :=
    @g_pw1ex (syn_cvv) p0224
  have p0226 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0225
  have p0227 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0226
  have p0228 :=
    @g_vvex
  have p0229 :=
    @g_pw1ex (syn_cvv) p0228
  have p0230 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0229
  have p0231 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0230
  have p0232 :=
    @g_xpkex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0227 p0231
  have p0233 :=
    @g_nncex
  have p0234 :=
    @g_xpex (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc) p0232 p0233
  have p0235 :=
    @g_hncardtcshiftndv (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc)) p0234
  have p0236 :=
    @g_vvex
  have p0237 :=
    @g_pw1ex (syn_cvv) p0236
  have p0238 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0237
  have p0239 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0238
  have p0240 :=
    @g_vvex
  have p0241 :=
    @g_pw1ex (syn_cvv) p0240
  have p0242 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0241
  have p0243 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0242
  have p0244 :=
    @g_xpkex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0239 p0243
  have p0245 :=
    @g_nncex
  have p0246 :=
    @g_xpex (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc) p0244 p0245
  have p0247 :=
    @g_pw1ex (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc)) p0246
  have p0248 :=
    @g_vvex
  have p0249 :=
    @g_pw1ex (syn_cvv) p0248
  have p0250 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0249
  have p0251 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0250
  have p0252 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0251
  have p0253 :=
    @g_vvex
  have p0254 :=
    @g_pw1ex (syn_cvv) p0253
  have p0255 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0254
  have p0256 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0255
  have p0257 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0256
  have p0258 :=
    @g_xpkex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0252 p0257
  have p0259 :=
    @g_nncex
  have p0260 :=
    @g_xpex (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc) p0258 p0259
  have p0261 :=
    @g_vvex
  have p0262 :=
    @g_pw1ex (syn_cvv) p0261
  have p0263 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0262
  have p0264 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0263
  have p0265 :=
    @g_wpplitshiftenndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0264
  have p0266 :=
    @g_vvex
  have p0267 :=
    @g_pw1ex (syn_cvv) p0266
  have p0268 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0267
  have p0269 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0268
  have p0270 :=
    @g_vvex
  have p0271 :=
    @g_pw1ex (syn_cvv) p0270
  have p0272 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0271
  have p0273 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0272
  have p0274 :=
    @g_xpkex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0269 p0273
  have p0275 :=
    @g_nncex
  have p0276 :=
    @g_xpex (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc) p0274 p0275
  have p0277 :=
    @g_pw1ex (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc)) p0276
  have p0278 :=
    @g_eqnc (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc))) (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc)) p0277
  have p0279 :=
    @g_mpbir (.classEq (syn_cnc (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc)))) (syn_cnc (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc)))) (syn_wbr (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc))) (syn_cen) (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc))) p0265 p0278
  have p0280 :=
    @g_hncardnceqndv (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc))) (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc)) p0247 p0260 p0279
  have p0281 :=
    @g_eqtri (syn_ctc (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc)))) (syn_chncard (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc)))) (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc))) p0235 p0280
  have p0282 :=
    @g_vvex
  have p0283 :=
    @g_pw1ex (syn_cvv) p0282
  have p0284 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0283
  have p0285 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0284
  have p0286 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0285
  have p0287 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0286
  have p0288 :=
    @g_hncardtcshiftndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0287
  have p0289 :=
    @g_breq12i (syn_ctc (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc)))) (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc))) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_clec) p0281 p0288
  have p0290 :=
    @g_mpbi (syn_wbr (syn_ctc (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnnc)))) (syn_clec) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))) (syn_wbr (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc))) (syn_clec) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))) p0223 p0289
  have p0291 :=
    @g_vvex
  have p0292 :=
    @g_pw1ex (syn_cvv) p0291
  have p0293 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0292
  have p0294 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0293
  have p0295 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0294
  have p0296 :=
    @g_vvex
  have p0297 :=
    @g_pw1ex (syn_cvv) p0296
  have p0298 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0297
  have p0299 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0298
  have p0300 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0299
  have p0301 :=
    @g_xpkex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0295 p0300
  have p0302 :=
    @g_nncex
  have p0303 :=
    @g_xpex (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc) p0301 p0302
  have p0304 :=
    @g_hncardnc (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc))
  have p0305 :=
    Nominal.mp p0303 p0304
  have p0306 :=
    @g_vvex
  have p0307 :=
    @g_pw1ex (syn_cvv) p0306
  have p0308 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0307
  have p0309 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0308
  have p0310 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0309
  have p0311 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0310
  have p0312 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0311
  have p0313 :=
    @g_hncardnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
  have p0314 :=
    Nominal.mp p0312 p0313
  have p0315 :=
    @g_pm3_2i (.classMem (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc))) (syn_cncs)) (.classMem (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cncs)) p0305 p0314
  have p0316 :=
    @g_tlecg (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
  have p0317 :=
    Nominal.mp p0315 p0316
  have p0318 :=
    @g_mpbi (syn_wbr (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc))) (syn_clec) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))) (syn_wbr (syn_ctc (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc)))) (syn_clec) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))) p0290 p0317
  have p0319 :=
    @g_vvex
  have p0320 :=
    @g_pw1ex (syn_cvv) p0319
  have p0321 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0320
  have p0322 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0321
  have p0323 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0322
  have p0324 :=
    @g_vvex
  have p0325 :=
    @g_pw1ex (syn_cvv) p0324
  have p0326 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0325
  have p0327 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0326
  have p0328 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0327
  have p0329 :=
    @g_xpkex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0323 p0328
  have p0330 :=
    @g_nncex
  have p0331 :=
    @g_xpex (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc) p0329 p0330
  have p0332 :=
    @g_hncardtcshiftndv (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc)) p0331
  have p0333 :=
    @g_vvex
  have p0334 :=
    @g_pw1ex (syn_cvv) p0333
  have p0335 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0334
  have p0336 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0335
  have p0337 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0336
  have p0338 :=
    @g_vvex
  have p0339 :=
    @g_pw1ex (syn_cvv) p0338
  have p0340 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0339
  have p0341 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0340
  have p0342 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0341
  have p0343 :=
    @g_xpkex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0337 p0342
  have p0344 :=
    @g_nncex
  have p0345 :=
    @g_xpex (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc) p0343 p0344
  have p0346 :=
    @g_pw1ex (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc)) p0345
  have p0347 :=
    @g_vvex
  have p0348 :=
    @g_pw1ex (syn_cvv) p0347
  have p0349 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0348
  have p0350 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0349
  have p0351 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0350
  have p0352 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0351
  have p0353 :=
    @g_vvex
  have p0354 :=
    @g_pw1ex (syn_cvv) p0353
  have p0355 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0354
  have p0356 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0355
  have p0357 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0356
  have p0358 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0357
  have p0359 :=
    @g_xpkex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0352 p0358
  have p0360 :=
    @g_nncex
  have p0361 :=
    @g_xpex (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc) p0359 p0360
  have p0362 :=
    @g_vvex
  have p0363 :=
    @g_pw1ex (syn_cvv) p0362
  have p0364 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0363
  have p0365 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0364
  have p0366 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0365
  have p0367 :=
    @g_wpplitshiftenndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0366
  have p0368 :=
    @g_vvex
  have p0369 :=
    @g_pw1ex (syn_cvv) p0368
  have p0370 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0369
  have p0371 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0370
  have p0372 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0371
  have p0373 :=
    @g_vvex
  have p0374 :=
    @g_pw1ex (syn_cvv) p0373
  have p0375 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0374
  have p0376 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0375
  have p0377 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0376
  have p0378 :=
    @g_xpkex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0372 p0377
  have p0379 :=
    @g_nncex
  have p0380 :=
    @g_xpex (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc) p0378 p0379
  have p0381 :=
    @g_pw1ex (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc)) p0380
  have p0382 :=
    @g_eqnc (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc))) (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc)) p0381
  have p0383 :=
    @g_mpbir (.classEq (syn_cnc (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc)))) (syn_cnc (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc)))) (syn_wbr (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc))) (syn_cen) (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc))) p0367 p0382
  have p0384 :=
    @g_hncardnceqndv (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc))) (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc)) p0346 p0361 p0383
  have p0385 :=
    @g_eqtri (syn_ctc (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc)))) (syn_chncard (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc)))) (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc))) p0332 p0384
  have p0386 :=
    @g_vvex
  have p0387 :=
    @g_pw1ex (syn_cvv) p0386
  have p0388 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0387
  have p0389 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0388
  have p0390 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0389
  have p0391 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0390
  have p0392 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0391
  have p0393 :=
    @g_hncardtcshiftndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) p0392
  have p0394 :=
    @g_breq12i (syn_ctc (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc)))) (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc))) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))) (syn_clec) p0385 p0393
  have p0395 :=
    @g_mpbi (syn_wbr (syn_ctc (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cnnc)))) (syn_clec) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))) (syn_wbr (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc))) (syn_clec) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))) p0318 p0394
  have p0396 :=
    @g_vvex
  have p0397 :=
    @g_pw1ex (syn_cvv) p0396
  have p0398 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0397
  have p0399 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0398
  have p0400 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0399
  have p0401 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0400
  have p0402 :=
    @g_vvex
  have p0403 :=
    @g_pw1ex (syn_cvv) p0402
  have p0404 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0403
  have p0405 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0404
  have p0406 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0405
  have p0407 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0406
  have p0408 :=
    @g_xpkex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0401 p0407
  have p0409 :=
    @g_nncex
  have p0410 :=
    @g_xpex (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc) p0408 p0409
  have p0411 :=
    @g_hncardnc (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc))
  have p0412 :=
    Nominal.mp p0410 p0411
  have p0413 :=
    @g_vvex
  have p0414 :=
    @g_pw1ex (syn_cvv) p0413
  have p0415 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0414
  have p0416 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0415
  have p0417 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0416
  have p0418 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0417
  have p0419 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0418
  have p0420 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) p0419
  have p0421 :=
    @g_hncardnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
  have p0422 :=
    Nominal.mp p0420 p0421
  have p0423 :=
    @g_pm3_2i (.classMem (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc))) (syn_cncs)) (.classMem (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))) (syn_cncs)) p0412 p0422
  have p0424 :=
    @g_tlecg (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))
  have p0425 :=
    Nominal.mp p0423 p0424
  have p0426 :=
    @g_mpbi (syn_wbr (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc))) (syn_clec) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))) (syn_wbr (syn_ctc (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc)))) (syn_clec) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))))) p0395 p0425
  have p0427 :=
    @g_vvex
  have p0428 :=
    @g_pw1ex (syn_cvv) p0427
  have p0429 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0428
  have p0430 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0429
  have p0431 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0430
  have p0432 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0431
  have p0433 :=
    @g_vvex
  have p0434 :=
    @g_pw1ex (syn_cvv) p0433
  have p0435 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0434
  have p0436 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0435
  have p0437 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0436
  have p0438 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0437
  have p0439 :=
    @g_xpkex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0432 p0438
  have p0440 :=
    @g_nncex
  have p0441 :=
    @g_xpex (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc) p0439 p0440
  have p0442 :=
    @g_hncardtcshiftndv (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc)) p0441
  have p0443 :=
    @g_vvex
  have p0444 :=
    @g_pw1ex (syn_cvv) p0443
  have p0445 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0444
  have p0446 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0445
  have p0447 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0446
  have p0448 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0447
  have p0449 :=
    @g_vvex
  have p0450 :=
    @g_pw1ex (syn_cvv) p0449
  have p0451 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0450
  have p0452 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0451
  have p0453 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0452
  have p0454 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0453
  have p0455 :=
    @g_xpkex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0448 p0454
  have p0456 :=
    @g_nncex
  have p0457 :=
    @g_xpex (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc) p0455 p0456
  have p0458 :=
    @g_pw1ex (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc)) p0457
  have p0459 :=
    @g_vvex
  have p0460 :=
    @g_pw1ex (syn_cvv) p0459
  have p0461 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0460
  have p0462 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0461
  have p0463 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0462
  have p0464 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0463
  have p0465 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0464
  have p0466 :=
    @g_vvex
  have p0467 :=
    @g_pw1ex (syn_cvv) p0466
  have p0468 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0467
  have p0469 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0468
  have p0470 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0469
  have p0471 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0470
  have p0472 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0471
  have p0473 :=
    @g_xpkex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) p0465 p0472
  have p0474 :=
    @g_nncex
  have p0475 :=
    @g_xpex (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cnnc) p0473 p0474
  have p0476 :=
    @g_vvex
  have p0477 :=
    @g_pw1ex (syn_cvv) p0476
  have p0478 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0477
  have p0479 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0478
  have p0480 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0479
  have p0481 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0480
  have p0482 :=
    @g_wpplitshiftenndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0481
  have p0483 :=
    @g_vvex
  have p0484 :=
    @g_pw1ex (syn_cvv) p0483
  have p0485 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0484
  have p0486 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0485
  have p0487 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0486
  have p0488 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0487
  have p0489 :=
    @g_vvex
  have p0490 :=
    @g_pw1ex (syn_cvv) p0489
  have p0491 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0490
  have p0492 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0491
  have p0493 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0492
  have p0494 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0493
  have p0495 :=
    @g_xpkex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0488 p0494
  have p0496 :=
    @g_nncex
  have p0497 :=
    @g_xpex (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc) p0495 p0496
  have p0498 :=
    @g_pw1ex (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc)) p0497
  have p0499 :=
    @g_eqnc (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc))) (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cnnc)) p0498
  have p0500 :=
    @g_mpbir (.classEq (syn_cnc (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc)))) (syn_cnc (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cnnc)))) (syn_wbr (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc))) (syn_cen) (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cnnc))) p0482 p0499
  have p0501 :=
    @g_hncardnceqndv (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc))) (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cnnc)) p0458 p0475 p0500
  have p0502 :=
    @g_eqtri (syn_ctc (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc)))) (syn_chncard (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc)))) (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cnnc))) p0442 p0501
  have p0503 :=
    @g_breq1i (syn_ctc (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc)))) (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cnnc))) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))) (syn_clec) p0502
  have p0504 :=
    @g_mpbi (syn_wbr (syn_ctc (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cnnc)))) (syn_clec) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))))) (syn_wbr (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cnnc))) (syn_clec) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))))) p0426 p0503
  have p0505 :=
    @g_vvex
  have p0506 :=
    @g_pw1ex (syn_cvv) p0505
  have p0507 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0506
  have p0508 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0507
  have p0509 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0508
  have p0510 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0509
  have p0511 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0510
  have p0512 :=
    @g_vvex
  have p0513 :=
    @g_pw1ex (syn_cvv) p0512
  have p0514 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0513
  have p0515 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0514
  have p0516 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0515
  have p0517 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0516
  have p0518 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0517
  have p0519 :=
    @g_xpkex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) p0511 p0518
  have p0520 :=
    @g_nncex
  have p0521 :=
    @g_xpex (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cnnc) p0519 p0520
  have p0522 :=
    @g_hncardnc (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cnnc))
  have p0523 :=
    Nominal.mp p0521 p0522
  have p0524 :=
    @g_vvex
  have p0525 :=
    @g_pw1ex (syn_cvv) p0524
  have p0526 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0525
  have p0527 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0526
  have p0528 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0527
  have p0529 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0528
  have p0530 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0529
  have p0531 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) p0530
  have p0532 :=
    @g_hncardnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))
  have p0533 :=
    Nominal.mp p0531 p0532
  have p0534 :=
    @g_tccl (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))
  have p0535 :=
    Nominal.mp p0533 p0534
  have p0536 :=
    @g_pm3_2i (.classMem (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cnnc))) (syn_cncs)) (.classMem (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))) (syn_cncs)) p0523 p0535
  have p0537 :=
    @g_tlecg (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cnnc))) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))))
  have p0538 :=
    Nominal.mp p0536 p0537
  have p0539 :=
    @g_mpbi (syn_wbr (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cnnc))) (syn_clec) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))))) (syn_wbr (syn_ctc (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cnnc)))) (syn_clec) (syn_ctc (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))))) p0504 p0538
  have p0540 :=
    @g_vvex
  have p0541 :=
    @g_pw1ex (syn_cvv) p0540
  have p0542 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0541
  have p0543 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0542
  have p0544 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0543
  have p0545 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0544
  have p0546 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0545
  have p0547 :=
    @g_vvex
  have p0548 :=
    @g_pw1ex (syn_cvv) p0547
  have p0549 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0548
  have p0550 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0549
  have p0551 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0550
  have p0552 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0551
  have p0553 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0552
  have p0554 :=
    @g_xpkex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) p0546 p0553
  have p0555 :=
    @g_nncex
  have p0556 :=
    @g_xpex (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cnnc) p0554 p0555
  have p0557 :=
    @g_hncardtcshiftndv (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cnnc)) p0556
  have p0558 :=
    @g_vvex
  have p0559 :=
    @g_pw1ex (syn_cvv) p0558
  have p0560 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0559
  have p0561 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0560
  have p0562 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0561
  have p0563 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0562
  have p0564 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0563
  have p0565 :=
    @g_vvex
  have p0566 :=
    @g_pw1ex (syn_cvv) p0565
  have p0567 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0566
  have p0568 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0567
  have p0569 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0568
  have p0570 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0569
  have p0571 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0570
  have p0572 :=
    @g_xpkex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) p0564 p0571
  have p0573 :=
    @g_nncex
  have p0574 :=
    @g_xpex (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cnnc) p0572 p0573
  have p0575 :=
    @g_pw1ex (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cnnc)) p0574
  have p0576 :=
    @g_vvex
  have p0577 :=
    @g_pw1ex (syn_cvv) p0576
  have p0578 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0577
  have p0579 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0578
  have p0580 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0579
  have p0581 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0580
  have p0582 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0581
  have p0583 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) p0582
  have p0584 :=
    @g_vvex
  have p0585 :=
    @g_pw1ex (syn_cvv) p0584
  have p0586 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0585
  have p0587 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0586
  have p0588 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0587
  have p0589 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0588
  have p0590 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0589
  have p0591 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) p0590
  have p0592 :=
    @g_xpkex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) p0583 p0591
  have p0593 :=
    @g_nncex
  have p0594 :=
    @g_xpex (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))) (syn_cnnc) p0592 p0593
  have p0595 :=
    @g_vvex
  have p0596 :=
    @g_pw1ex (syn_cvv) p0595
  have p0597 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0596
  have p0598 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0597
  have p0599 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0598
  have p0600 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0599
  have p0601 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0600
  have p0602 :=
    @g_wpplitshiftenndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) p0601
  have p0603 :=
    @g_vvex
  have p0604 :=
    @g_pw1ex (syn_cvv) p0603
  have p0605 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0604
  have p0606 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0605
  have p0607 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0606
  have p0608 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0607
  have p0609 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0608
  have p0610 :=
    @g_vvex
  have p0611 :=
    @g_pw1ex (syn_cvv) p0610
  have p0612 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0611
  have p0613 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0612
  have p0614 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0613
  have p0615 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0614
  have p0616 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0615
  have p0617 :=
    @g_xpkex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) p0609 p0616
  have p0618 :=
    @g_nncex
  have p0619 :=
    @g_xpex (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cnnc) p0617 p0618
  have p0620 :=
    @g_pw1ex (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cnnc)) p0619
  have p0621 :=
    @g_eqnc (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cnnc))) (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))) (syn_cnnc)) p0620
  have p0622 :=
    @g_mpbir (.classEq (syn_cnc (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cnnc)))) (syn_cnc (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))) (syn_cnnc)))) (syn_wbr (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cnnc))) (syn_cen) (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))) (syn_cnnc))) p0602 p0621
  have p0623 :=
    @g_hncardnceqndv (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cnnc))) (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))) (syn_cnnc)) p0575 p0594 p0622
  have p0624 :=
    @g_eqtri (syn_ctc (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cnnc)))) (syn_chncard (syn_cpw1 (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cnnc)))) (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))) (syn_cnnc))) p0557 p0623
  have p0625 :=
    @g_breq1i (syn_ctc (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cnnc)))) (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))) (syn_cnnc))) (syn_ctc (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))))) (syn_clec) p0624
  have p0626 :=
    @g_mpbi (syn_wbr (syn_ctc (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cnnc)))) (syn_clec) (syn_ctc (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))))) (syn_wbr (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))) (syn_cnnc))) (syn_clec) (syn_ctc (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))))) p0539 p0625
  exact p0626

#print axioms g_cfbliteralp17hncardboundndv

end NFChoice.DirectNominalPrf.WPPReplay
