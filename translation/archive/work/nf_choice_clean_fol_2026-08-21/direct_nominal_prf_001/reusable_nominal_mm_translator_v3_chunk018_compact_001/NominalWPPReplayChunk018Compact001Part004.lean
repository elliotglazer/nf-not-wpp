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
import NominalWPPReplayChunk018Compact001Part003

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

noncomputable def g_cfbliteralp16onehncardboundndv
     :
    Nominal.NPrf (syn_wbr (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cnnc))) (syn_clec) (syn_ctc (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_cfbliteralp17hncardboundndv
  have p0001 :=
    @g_n_1cex
  have p0002 :=
    @g_pw1ex (syn_c1c) p0001
  have p0003 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0002
  have p0004 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0003
  have p0005 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0004
  have p0006 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0005
  have p0007 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0006
  have p0008 :=
    @g_n_1cex
  have p0009 :=
    @g_pw1ex (syn_c1c) p0008
  have p0010 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0009
  have p0011 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0010
  have p0012 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0011
  have p0013 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0012
  have p0014 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0013
  have p0015 :=
    @g_xpkex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) p0007 p0014
  have p0016 :=
    @g_nncex
  have p0017 :=
    @g_xpex (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cnnc) p0015 p0016
  have p0018 :=
    @g_vvex
  have p0019 :=
    @g_pw1ex (syn_cvv) p0018
  have p0020 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0019
  have p0021 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0020
  have p0022 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0021
  have p0023 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0022
  have p0024 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0023
  have p0025 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) p0024
  have p0026 :=
    @g_vvex
  have p0027 :=
    @g_pw1ex (syn_cvv) p0026
  have p0028 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0027
  have p0029 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0028
  have p0030 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0029
  have p0031 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0030
  have p0032 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0031
  have p0033 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) p0032
  have p0034 :=
    @g_xpkex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) p0025 p0033
  have p0035 :=
    @g_nncex
  have p0036 :=
    @g_xpex (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))) (syn_cnnc) p0034 p0035
  have p0037 :=
    @g_df1c2
  have p0038 :=
    @g_pw1eq (syn_c1c) (syn_cpw1 (syn_cvv))
  have p0039 :=
    Nominal.mp p0037 p0038
  have p0040 :=
    @g_pw1eq (syn_cpw1 (syn_c1c)) (syn_cpw1 (syn_cpw1 (syn_cvv)))
  have p0041 :=
    Nominal.mp p0039 p0040
  have p0042 :=
    @g_pw1eq (syn_cpw1 (syn_cpw1 (syn_c1c))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
  have p0043 :=
    Nominal.mp p0041 p0042
  have p0044 :=
    @g_pw1eq (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
  have p0045 :=
    Nominal.mp p0043 p0044
  have p0046 :=
    @g_pw1eq (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
  have p0047 :=
    Nominal.mp p0045 p0046
  have p0048 :=
    @g_pw1eq (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
  have p0049 :=
    Nominal.mp p0047 p0048
  have p0050 :=
    @g_df1c2
  have p0051 :=
    @g_pw1eq (syn_c1c) (syn_cpw1 (syn_cvv))
  have p0052 :=
    Nominal.mp p0050 p0051
  have p0053 :=
    @g_pw1eq (syn_cpw1 (syn_c1c)) (syn_cpw1 (syn_cpw1 (syn_cvv)))
  have p0054 :=
    Nominal.mp p0052 p0053
  have p0055 :=
    @g_pw1eq (syn_cpw1 (syn_cpw1 (syn_c1c))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
  have p0056 :=
    Nominal.mp p0054 p0055
  have p0057 :=
    @g_pw1eq (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
  have p0058 :=
    Nominal.mp p0056 p0057
  have p0059 :=
    @g_pw1eq (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
  have p0060 :=
    Nominal.mp p0058 p0059
  have p0061 :=
    @g_pw1eq (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
  have p0062 :=
    Nominal.mp p0060 p0061
  have p0063 :=
    @g_xpkeq12i (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) p0049 p0062
  have p0064 :=
    @g_xpeq1i (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))) (syn_cnnc) p0063
  have p0065 :=
    @g_nceqi (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cnnc)) (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))) (syn_cnnc)) p0064
  have p0066 :=
    @g_hncardnceqndv (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cnnc)) (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))) (syn_cnnc)) p0017 p0036 p0065
  have p0067 :=
    @g_eqcomi (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cnnc))) (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))) (syn_cnnc))) p0066
  have p0068 :=
    @g_n_1cex
  have p0069 :=
    @g_pw1ex (syn_c1c) p0068
  have p0070 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0069
  have p0071 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0070
  have p0072 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0071
  have p0073 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0072
  have p0074 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0073
  have p0075 :=
    @g_vvex
  have p0076 :=
    @g_pw1ex (syn_cvv) p0075
  have p0077 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0076
  have p0078 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cvv))) p0077
  have p0079 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0078
  have p0080 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0079
  have p0081 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0080
  have p0082 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))) p0081
  have p0083 :=
    @g_df1c2
  have p0084 :=
    @g_pw1eq (syn_c1c) (syn_cpw1 (syn_cvv))
  have p0085 :=
    Nominal.mp p0083 p0084
  have p0086 :=
    @g_pw1eq (syn_cpw1 (syn_c1c)) (syn_cpw1 (syn_cpw1 (syn_cvv)))
  have p0087 :=
    Nominal.mp p0085 p0086
  have p0088 :=
    @g_pw1eq (syn_cpw1 (syn_cpw1 (syn_c1c))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))
  have p0089 :=
    Nominal.mp p0087 p0088
  have p0090 :=
    @g_pw1eq (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))
  have p0091 :=
    Nominal.mp p0089 p0090
  have p0092 :=
    @g_pw1eq (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))
  have p0093 :=
    Nominal.mp p0091 p0092
  have p0094 :=
    @g_pw1eq (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))
  have p0095 :=
    Nominal.mp p0093 p0094
  have p0096 :=
    @g_nceqi (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) p0095
  have p0097 :=
    @g_hncardnceqndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) p0074 p0082 p0096
  have p0098 :=
    @g_tceq (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))
  have p0099 :=
    Nominal.mp p0097 p0098
  have p0100 :=
    @g_tceq (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))))
  have p0101 :=
    Nominal.mp p0099 p0100
  have p0102 :=
    @g_eqcomi (syn_ctc (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_ctc (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))))) p0101
  have p0103 :=
    @g_breq12i (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))) (syn_cnnc))) (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cnnc))) (syn_ctc (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))))) (syn_ctc (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_clec) p0067 p0102
  have p0104 :=
    @g_mpbi (syn_wbr (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv))))))))) (syn_cnnc))) (syn_clec) (syn_ctc (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cvv)))))))))))) (syn_wbr (syn_chncard (syn_cxp (syn_cxpk (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cnnc))) (syn_clec) (syn_ctc (syn_ctc (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) p0000 p0103
  exact p0104

noncomputable def g_cfbfixedblockhnqgraphexndv
    (X : Class) (hyp_cfbfixedblockhnqgraphexndv_1 : Nominal.NPrf (.classMem X (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cres (syn_ccom (syn_ccnv (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X)))))) (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (syn_cvv)) := by
  let proofSupport : Finset Var := X.fv
  have p0000 :=
    @g_hnordex X hyp_cfbfixedblockhnqgraphexndv_1
  have p0001 :=
    @g_pwex (syn_chnord X) p0000
  have p0002 :=
    @g_pwex (syn_cpw (syn_chnord X)) p0001
  have p0003 :=
    @g_pwex X hyp_cfbfixedblockhnqgraphexndv_1
  have p0004 :=
    @g_pw1ex (syn_cpw X) p0003
  have p0005 :=
    @g_pw1ex (syn_cpw1 (syn_cpw X)) p0004
  have p0006 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw X))) p0005
  have p0007 :=
    @g_hnordex X hyp_cfbfixedblockhnqgraphexndv_1
  have p0008 :=
    @g_pwex (syn_chnord X) p0007
  have p0009 :=
    @g_pwex (syn_cpw (syn_chnord X)) p0008
  have p0010 :=
    @g_unex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))) p0006 p0009
  have p0011 :=
    @g_pm3_2i (.classMem (syn_cpw (syn_cpw (syn_chnord X))) (syn_cvv)) (.classMem (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X)))) (syn_cvv)) p0002 p0010
  have p0012 :=
    @g_hnqincexg (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X)))) (syn_cpw (syn_cpw (syn_chnord X)))
  have p0013 :=
    Nominal.mp p0011 p0012
  have p0014 :=
    @g_cnvex (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) p0013
  have p0015 :=
    @g_pwex X hyp_cfbfixedblockhnqgraphexndv_1
  have p0016 :=
    @g_pw1ex (syn_cpw X) p0015
  have p0017 :=
    @g_pw1ex (syn_cpw1 (syn_cpw X)) p0016
  have p0018 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw X))) p0017
  have p0019 :=
    @g_pwex X hyp_cfbfixedblockhnqgraphexndv_1
  have p0020 :=
    @g_pw1ex (syn_cpw X) p0019
  have p0021 :=
    @g_pw1ex (syn_cpw1 (syn_cpw X)) p0020
  have p0022 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw X))) p0021
  have p0023 :=
    @g_hnordex X hyp_cfbfixedblockhnqgraphexndv_1
  have p0024 :=
    @g_pwex (syn_chnord X) p0023
  have p0025 :=
    @g_pwex (syn_cpw (syn_chnord X)) p0024
  have p0026 :=
    @g_unex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))) p0022 p0025
  have p0027 :=
    @g_pm3_2i (.classMem (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cvv)) (.classMem (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X)))) (syn_cvv)) p0018 p0026
  have p0028 :=
    @g_hnqincexg (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))
  have p0029 :=
    Nominal.mp p0027 p0028
  have p0030 :=
    @g_pwex X hyp_cfbfixedblockhnqgraphexndv_1
  have p0031 :=
    @g_pw1ex (syn_cpw X) p0030
  have p0032 :=
    @g_pw1ex (syn_cpw1 (syn_cpw X)) p0031
  have p0033 :=
    @g_hnsiquomapexgndv (syn_cpw1 (syn_cpw1 (syn_cpw X)))
  have p0034 :=
    Nominal.mp p0032 p0033
  have p0035 :=
    @g_pwex X hyp_cfbfixedblockhnqgraphexndv_1
  have p0036 :=
    @g_pw1ex (syn_cpw X) p0035
  have p0037 :=
    @g_hnsiquomapexgndv (syn_cpw1 (syn_cpw X))
  have p0038 :=
    Nominal.mp p0036 p0037
  have p0039 :=
    @g_siex (syn_chnsiquomap (syn_cpw1 (syn_cpw X))) p0038
  have p0040 :=
    @g_pwex X hyp_cfbfixedblockhnqgraphexndv_1
  have p0041 :=
    @g_hnsiquomapexgndv (syn_cpw X)
  have p0042 :=
    Nominal.mp p0040 p0041
  have p0043 :=
    @g_siex (syn_chnsiquomap (syn_cpw X)) p0042
  have p0044 :=
    @g_siex (syn_csi (syn_chnsiquomap (syn_cpw X))) p0043
  have p0045 :=
    @g_coex (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))) p0039 p0044
  have p0046 :=
    @g_coex (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))) p0034 p0045
  have p0047 :=
    @g_coex (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))) p0029 p0046
  have p0048 :=
    @g_coex (syn_ccnv (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X)))))) (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))))) p0014 p0047
  have p0049 :=
    @g_pwex X hyp_cfbfixedblockhnqgraphexndv_1
  have p0050 :=
    @g_hnordex (syn_cpw X) p0049
  have p0051 :=
    @g_pw1ex (syn_chnord (syn_cpw X)) p0050
  have p0052 :=
    @g_pw1ex (syn_cpw1 (syn_chnord (syn_cpw X))) p0051
  have p0053 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))) p0052
  have p0054 :=
    @g_resex (syn_ccom (syn_ccnv (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X)))))) (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) p0048 p0053
  exact p0054

noncomputable def g_cfbwppfixedblockhnqinjexndv
    (f : Var) (X : Class) (dv_X_f : f ∉ X.fv) (hyp_cfbwppfixedblockhnqinjexndv_1 : Nominal.NPrf (.classMem X (syn_cvv))) (hyp_cfbwppfixedblockhnqinjexndv_2 : Nominal.NPrf (syn_wbr (syn_chncard (syn_cxp (syn_cxpk X X) (syn_cnnc))) (syn_clec) (syn_ctc (syn_ctc (syn_chncard X))))) :
    Nominal.NPrf (.imp (syn_wwpp) (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (syn_chnord (syn_cpw (syn_cpw (syn_chnord X))))))) := by
  let proofSupport : Finset Var := ({f} : Finset Var) ∪ X.fv
  have dv_cache_0001 : f ∉ ((syn_cres (syn_ccom (syn_ccnv (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X)))))) (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))).fv := by
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_X_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : f ∉ ((syn_wf1 (syn_cres (syn_ccom (syn_ccnv (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X)))))) (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (syn_chnord (syn_cpw (syn_cpw (syn_chnord X)))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqinc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_X_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_cfbwppfixedblockhnqgraphinjndv X hyp_cfbwppfixedblockhnqinjexndv_1 hyp_cfbwppfixedblockhnqinjexndv_2
  have p0001 :=
    @g_cfbfixedblockhnqgraphexndv X hyp_cfbwppfixedblockhnqinjexndv_1
  have p0002 :=
    @g_f1eq1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (syn_chnord (syn_cpw (syn_cpw (syn_chnord X)))) (.cv f) (syn_cres (syn_ccom (syn_ccnv (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X)))))) (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))
  have p0003 :=
    @g_spcegv (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (syn_chnord (syn_cpw (syn_cpw (syn_chnord X))))) (syn_wf1 (syn_cres (syn_ccom (syn_ccnv (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X)))))) (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (syn_chnord (syn_cpw (syn_cpw (syn_chnord X))))) f (syn_cres (syn_ccom (syn_ccnv (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X)))))) (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (syn_cvv) dv_cache_0001 dv_cache_0002 p0002
  have p0004 :=
    Nominal.mp p0001 p0003
  have p0005 :=
    @g_syl (syn_wwpp) (syn_wf1 (syn_cres (syn_ccom (syn_ccnv (syn_chnqinc (syn_cpw (syn_cpw (syn_chnord X))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X)))))) (syn_ccom (syn_chnqinc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cun (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cpw (syn_cpw (syn_chnord X))))) (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (syn_chnord (syn_cpw (syn_cpw (syn_chnord X))))) (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (syn_chnord (syn_cpw (syn_cpw (syn_chnord X)))))) p0000 p0004
  exact p0005

noncomputable def g_wppfiniteblocknotwppndv
     :
    Nominal.NPrf (.neg (syn_wwpp)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let f : Var := freshVar proofSupport 0
  have fresh_f : f ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have dv_cache_0001 : f ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv := by
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_cfbpw16oneexndv
  have p0001 :=
    @g_cfbliteralp16onehncardboundndv
  have p0002 :=
    @g_cfbwppfixedblockhnqinjexndv f (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) dv_cache_0001 p0000 p0001
  have p0003 :=
    @g_cfbfixedblocknotwppfrominjndv f p0002
  exact p0003

#print axioms g_wppfiniteblocknotwppndv

end NFChoice.DirectNominalPrf.WPPReplay
