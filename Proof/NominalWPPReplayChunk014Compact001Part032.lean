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
import NominalWPPReplayChunk014Compact001Part031

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

noncomputable def g_elhwrrels
    (u : Var) :
    Nominal.NPrf (syn_wb (.classMem (.cv u) (syn_chwrels)) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) := by
  let proofSupport : Finset Var := ({u} : Finset Var)
  have p0000 :=
    (by simpa [syn_chwrels] using (Nominal.classEqRefl (syn_chwrels)))
  have p0001 :=
    @g_eleq2i (syn_chwrels) (syn_cima (syn_ccnv (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))) (syn_csset)) (.cv u) p0000
  have p0002 :=
    @g_n_1stfo
  have p0003 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0004 :=
    Nominal.mp p0002 p0003
  have p0005 :=
    @g_fncross
  have p0006 :=
    @g_n_2ndfo
  have p0007 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_n_2ndfo
  have p0010 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0011 :=
    Nominal.mp p0009 p0010
  have p0012 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0008 p0011
  have p0013 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c2nd) (syn_c2nd)
  have p0014 :=
    Nominal.mp p0012 p0013
  have p0015 :=
    @g_inidm (syn_cvv)
  have p0016 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c2nd) (syn_c2nd)) p0015
  have p0017 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cvv)) p0014 p0016
  have p0018 :=
    @g_ssv (syn_crn (syn_ctxp (syn_c2nd) (syn_c2nd)))
  have p0019 :=
    @g_n_3pm3_2i (syn_wfn (syn_ccross) (syn_cvv)) (syn_wfn (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cvv)) (syn_wss (syn_crn (syn_ctxp (syn_c2nd) (syn_c2nd))) (syn_cvv)) p0005 p0017 p0018
  have p0020 :=
    @g_fnco (syn_cvv) (syn_cvv) (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))
  have p0021 :=
    Nominal.mp p0019 p0020
  have p0022 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfn (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (syn_cvv)) p0004 p0021
  have p0023 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))
  have p0024 :=
    Nominal.mp p0022 p0023
  have p0025 :=
    @g_inidm (syn_cvv)
  have p0026 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))) p0025
  have p0027 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))) (syn_cvv)) p0024 p0026
  have p0028 :=
    @g_elpreima (syn_cvv) (.cv u) (syn_csset) (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))
  have p0029 :=
    Nominal.mp p0027 p0028
  have p0030 :=
    @g_vex u
  have p0031 :=
    @g_biantrur (.classMem (.cv u) (syn_cvv)) (.classMem (syn_cfv (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))) (.cv u)) (syn_csset)) p0030
  have p0032 :=
    @g_bicomi (.classMem (syn_cfv (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))) (.cv u)) (syn_csset)) (syn_wa (.classMem (.cv u) (syn_cvv)) (.classMem (syn_cfv (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))) (.cv u)) (syn_csset))) p0031
  have p0033 :=
    @g_bitri (.classMem (.cv u) (syn_cima (syn_ccnv (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))) (syn_csset))) (syn_wa (.classMem (.cv u) (syn_cvv)) (.classMem (syn_cfv (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))) (.cv u)) (syn_csset))) (.classMem (syn_cfv (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))) (.cv u)) (syn_csset)) p0029 p0032
  have p0034 :=
    @g_eqid (syn_cfv (syn_c1st) (.cv u))
  have p0035 :=
    @g_n_1stfo
  have p0036 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0037 :=
    Nominal.mp p0035 p0036
  have p0038 :=
    @g_vex u
  have p0039 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (.classMem (.cv u) (syn_cvv)) p0037 p0038
  have p0040 :=
    @g_fnbrfvb (syn_cvv) (.cv u) (syn_cfv (syn_c1st) (.cv u)) (syn_c1st)
  have p0041 :=
    Nominal.mp p0039 p0040
  have p0042 :=
    @g_mpbi (.classEq (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv u))) (syn_wbr (.cv u) (syn_c1st) (syn_cfv (syn_c1st) (.cv u))) p0034 p0041
  have p0043 :=
    @g_eqid (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u))
  have p0044 :=
    @g_fncross
  have p0045 :=
    @g_n_2ndfo
  have p0046 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0047 :=
    Nominal.mp p0045 p0046
  have p0048 :=
    @g_n_2ndfo
  have p0049 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0050 :=
    Nominal.mp p0048 p0049
  have p0051 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0047 p0050
  have p0052 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c2nd) (syn_c2nd)
  have p0053 :=
    Nominal.mp p0051 p0052
  have p0054 :=
    @g_inidm (syn_cvv)
  have p0055 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c2nd) (syn_c2nd)) p0054
  have p0056 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cvv)) p0053 p0055
  have p0057 :=
    @g_ssv (syn_crn (syn_ctxp (syn_c2nd) (syn_c2nd)))
  have p0058 :=
    @g_n_3pm3_2i (syn_wfn (syn_ccross) (syn_cvv)) (syn_wfn (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cvv)) (syn_wss (syn_crn (syn_ctxp (syn_c2nd) (syn_c2nd))) (syn_cvv)) p0044 p0056 p0057
  have p0059 :=
    @g_fnco (syn_cvv) (syn_cvv) (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))
  have p0060 :=
    Nominal.mp p0058 p0059
  have p0061 :=
    @g_vex u
  have p0062 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (syn_cvv)) (.classMem (.cv u) (syn_cvv)) p0060 p0061
  have p0063 :=
    @g_fnbrfvb (syn_cvv) (.cv u) (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u)) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))
  have p0064 :=
    Nominal.mp p0062 p0063
  have p0065 :=
    @g_mpbi (.classEq (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u)) (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u))) (syn_wbr (.cv u) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u))) p0043 p0064
  have p0066 :=
    @g_pm3_2i (syn_wbr (.cv u) (syn_c1st) (syn_cfv (syn_c1st) (.cv u))) (syn_wbr (.cv u) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u))) p0042 p0065
  have p0067 :=
    @g_trtxp (.cv u) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u)) (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))
  have p0068 :=
    @g_mpbir (syn_wbr (.cv u) (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u)))) (syn_wa (syn_wbr (.cv u) (syn_c1st) (syn_cfv (syn_c1st) (.cv u))) (syn_wbr (.cv u) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u)))) p0066 p0067
  have p0069 :=
    @g_n_1stfo
  have p0070 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0071 :=
    Nominal.mp p0069 p0070
  have p0072 :=
    @g_fncross
  have p0073 :=
    @g_n_2ndfo
  have p0074 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0075 :=
    Nominal.mp p0073 p0074
  have p0076 :=
    @g_n_2ndfo
  have p0077 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0078 :=
    Nominal.mp p0076 p0077
  have p0079 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0075 p0078
  have p0080 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c2nd) (syn_c2nd)
  have p0081 :=
    Nominal.mp p0079 p0080
  have p0082 :=
    @g_inidm (syn_cvv)
  have p0083 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c2nd) (syn_c2nd)) p0082
  have p0084 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cvv)) p0081 p0083
  have p0085 :=
    @g_ssv (syn_crn (syn_ctxp (syn_c2nd) (syn_c2nd)))
  have p0086 :=
    @g_n_3pm3_2i (syn_wfn (syn_ccross) (syn_cvv)) (syn_wfn (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cvv)) (syn_wss (syn_crn (syn_ctxp (syn_c2nd) (syn_c2nd))) (syn_cvv)) p0072 p0084 p0085
  have p0087 :=
    @g_fnco (syn_cvv) (syn_cvv) (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))
  have p0088 :=
    Nominal.mp p0086 p0087
  have p0089 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfn (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (syn_cvv)) p0071 p0088
  have p0090 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))
  have p0091 :=
    Nominal.mp p0089 p0090
  have p0092 :=
    @g_inidm (syn_cvv)
  have p0093 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))) p0092
  have p0094 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))) (syn_cvv)) p0091 p0093
  have p0095 :=
    @g_fnfun (syn_cvv) (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))
  have p0096 :=
    Nominal.mp p0094 p0095
  have p0097 :=
    @g_funbrfv (.cv u) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u))) (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))
  have p0098 :=
    Nominal.mp p0096 p0097
  have p0099 :=
    Nominal.mp p0068 p0098
  have p0100 :=
    @g_n_2ndfo
  have p0101 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0102 :=
    Nominal.mp p0100 p0101
  have p0103 :=
    @g_n_2ndfo
  have p0104 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0105 :=
    Nominal.mp p0103 p0104
  have p0106 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0102 p0105
  have p0107 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c2nd) (syn_c2nd)
  have p0108 :=
    Nominal.mp p0106 p0107
  have p0109 :=
    @g_inidm (syn_cvv)
  have p0110 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c2nd) (syn_c2nd)) p0109
  have p0111 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cvv)) p0108 p0110
  have p0112 :=
    @g_vex u
  have p0113 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cvv)) (.classMem (.cv u) (syn_cvv)) p0111 p0112
  have p0114 :=
    @g_fvco2 (syn_cvv) (.cv u) (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))
  have p0115 :=
    Nominal.mp p0113 p0114
  have p0116 :=
    @g_eqid (syn_cfv (syn_c2nd) (.cv u))
  have p0117 :=
    @g_n_2ndfo
  have p0118 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0119 :=
    Nominal.mp p0117 p0118
  have p0120 :=
    @g_vex u
  have p0121 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (.classMem (.cv u) (syn_cvv)) p0119 p0120
  have p0122 :=
    @g_fnbrfvb (syn_cvv) (.cv u) (syn_cfv (syn_c2nd) (.cv u)) (syn_c2nd)
  have p0123 :=
    Nominal.mp p0121 p0122
  have p0124 :=
    @g_mpbi (.classEq (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv u) (syn_c2nd) (syn_cfv (syn_c2nd) (.cv u))) p0116 p0123
  have p0125 :=
    @g_eqid (syn_cfv (syn_c2nd) (.cv u))
  have p0126 :=
    @g_n_2ndfo
  have p0127 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0128 :=
    Nominal.mp p0126 p0127
  have p0129 :=
    @g_vex u
  have p0130 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (.classMem (.cv u) (syn_cvv)) p0128 p0129
  have p0131 :=
    @g_fnbrfvb (syn_cvv) (.cv u) (syn_cfv (syn_c2nd) (.cv u)) (syn_c2nd)
  have p0132 :=
    Nominal.mp p0130 p0131
  have p0133 :=
    @g_mpbi (.classEq (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv u) (syn_c2nd) (syn_cfv (syn_c2nd) (.cv u))) p0125 p0132
  have p0134 :=
    @g_pm3_2i (syn_wbr (.cv u) (syn_c2nd) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv u) (syn_c2nd) (syn_cfv (syn_c2nd) (.cv u))) p0124 p0133
  have p0135 :=
    @g_trtxp (.cv u) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_c2nd) (syn_c2nd)
  have p0136 :=
    @g_mpbir (syn_wbr (.cv u) (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cop (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (syn_wbr (.cv u) (syn_c2nd) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv u) (syn_c2nd) (syn_cfv (syn_c2nd) (.cv u)))) p0134 p0135
  have p0137 :=
    @g_n_2ndfo
  have p0138 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0139 :=
    Nominal.mp p0137 p0138
  have p0140 :=
    @g_n_2ndfo
  have p0141 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0142 :=
    Nominal.mp p0140 p0141
  have p0143 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0139 p0142
  have p0144 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c2nd) (syn_c2nd)
  have p0145 :=
    Nominal.mp p0143 p0144
  have p0146 :=
    @g_inidm (syn_cvv)
  have p0147 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c2nd) (syn_c2nd)) p0146
  have p0148 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cvv)) p0145 p0147
  have p0149 :=
    @g_fnfun (syn_cvv) (syn_ctxp (syn_c2nd) (syn_c2nd))
  have p0150 :=
    Nominal.mp p0148 p0149
  have p0151 :=
    @g_funbrfv (.cv u) (syn_cop (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_ctxp (syn_c2nd) (syn_c2nd))
  have p0152 :=
    Nominal.mp p0150 p0151
  have p0153 :=
    Nominal.mp p0136 p0152
  have p0154 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_c2nd) (syn_c2nd)) (.cv u)) (syn_cop (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_ccross) p0153
  have p0155 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u)) (syn_cfv (syn_ccross) (syn_cfv (syn_ctxp (syn_c2nd) (syn_c2nd)) (.cv u))) (syn_cfv (syn_ccross) (syn_cop (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) p0115 p0154
  have p0156 :=
    (by simpa [syn_co] using (Nominal.classEqRefl (syn_co (syn_cfv (syn_c2nd) (.cv u)) (syn_ccross) (syn_cfv (syn_c2nd) (.cv u)))))
  have p0157 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0158 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0159 :=
    @g_pm3_2i (.classMem (syn_cfv (syn_c2nd) (.cv u)) (syn_cvv)) (.classMem (syn_cfv (syn_c2nd) (.cv u)) (syn_cvv)) p0157 p0158
  have p0160 :=
    @g_ovcross (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cvv) (syn_cvv)
  have p0161 :=
    Nominal.mp p0159 p0160
  have p0162 :=
    @g_eqtr3i (syn_co (syn_cfv (syn_c2nd) (.cv u)) (syn_ccross) (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_ccross) (syn_cop (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) p0156 p0161
  have p0163 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u)) (syn_cfv (syn_ccross) (syn_cop (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) p0155 p0162
  have p0164 :=
    @g_opeq2i (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)) p0163
  have p0165 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))) (.cv u)) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u))) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) p0099 p0164
  have p0166 :=
    @g_eleq1i (syn_cfv (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))) (.cv u)) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (syn_csset) p0165
  have p0167 :=
    @g_bitri (.classMem (.cv u) (syn_cima (syn_ccnv (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))) (syn_csset))) (.classMem (syn_cfv (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))) (.cv u)) (syn_csset)) (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (syn_csset)) p0033 p0166
  have p0168 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_csset) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))))
  have p0169 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0170 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0171 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0172 :=
    @g_xpex (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) p0170 p0171
  have p0173 :=
    @g_brsset (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) p0169 p0172
  have p0174 :=
    @g_bitr3i (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (syn_csset)) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_csset) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) p0168 p0173
  have p0175 :=
    @g_bitri (.classMem (.cv u) (syn_cima (syn_ccnv (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))) (syn_csset))) (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (syn_csset)) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) p0167 p0174
  have p0176 :=
    @g_bitri (.classMem (.cv u) (syn_chwrels)) (.classMem (.cv u) (syn_cima (syn_ccnv (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))) (syn_csset))) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) p0001 p0175
  exact p0176

noncomputable def g_elhwcn
    (u : Var) (A : Class) :
    Nominal.NPrf (syn_wb (.classMem (.cv u) (syn_chwcn A)) (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))) := by
  let proofSupport : Finset Var := ({u} : Finset Var) ∪ A.fv
  have p0000 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn A)))
  have p0001 :=
    @g_eleq2i (syn_chwcn A) (syn_cin (syn_chwcodes A) (syn_chwrels)) (.cv u) p0000
  have p0002 :=
    @g_elin (.cv u) (syn_chwcodes A) (syn_chwrels)
  have p0003 :=
    (by simpa [syn_chwrels] using (Nominal.classEqRefl (syn_chwrels)))
  have p0004 :=
    @g_eleq2i (syn_chwrels) (syn_cima (syn_ccnv (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))) (syn_csset)) (.cv u) p0003
  have p0005 :=
    @g_n_1stfo
  have p0006 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_fncross
  have p0009 :=
    @g_n_2ndfo
  have p0010 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0011 :=
    Nominal.mp p0009 p0010
  have p0012 :=
    @g_n_2ndfo
  have p0013 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0014 :=
    Nominal.mp p0012 p0013
  have p0015 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0011 p0014
  have p0016 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c2nd) (syn_c2nd)
  have p0017 :=
    Nominal.mp p0015 p0016
  have p0018 :=
    @g_inidm (syn_cvv)
  have p0019 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c2nd) (syn_c2nd)) p0018
  have p0020 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cvv)) p0017 p0019
  have p0021 :=
    @g_ssv (syn_crn (syn_ctxp (syn_c2nd) (syn_c2nd)))
  have p0022 :=
    @g_n_3pm3_2i (syn_wfn (syn_ccross) (syn_cvv)) (syn_wfn (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cvv)) (syn_wss (syn_crn (syn_ctxp (syn_c2nd) (syn_c2nd))) (syn_cvv)) p0008 p0020 p0021
  have p0023 :=
    @g_fnco (syn_cvv) (syn_cvv) (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))
  have p0024 :=
    Nominal.mp p0022 p0023
  have p0025 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfn (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (syn_cvv)) p0007 p0024
  have p0026 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))
  have p0027 :=
    Nominal.mp p0025 p0026
  have p0028 :=
    @g_inidm (syn_cvv)
  have p0029 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))) p0028
  have p0030 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))) (syn_cvv)) p0027 p0029
  have p0031 :=
    @g_elpreima (syn_cvv) (.cv u) (syn_csset) (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))
  have p0032 :=
    Nominal.mp p0030 p0031
  have p0033 :=
    @g_vex u
  have p0034 :=
    @g_biantrur (.classMem (.cv u) (syn_cvv)) (.classMem (syn_cfv (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))) (.cv u)) (syn_csset)) p0033
  have p0035 :=
    @g_bicomi (.classMem (syn_cfv (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))) (.cv u)) (syn_csset)) (syn_wa (.classMem (.cv u) (syn_cvv)) (.classMem (syn_cfv (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))) (.cv u)) (syn_csset))) p0034
  have p0036 :=
    @g_bitri (.classMem (.cv u) (syn_cima (syn_ccnv (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))) (syn_csset))) (syn_wa (.classMem (.cv u) (syn_cvv)) (.classMem (syn_cfv (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))) (.cv u)) (syn_csset))) (.classMem (syn_cfv (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))) (.cv u)) (syn_csset)) p0032 p0035
  have p0037 :=
    @g_eqid (syn_cfv (syn_c1st) (.cv u))
  have p0038 :=
    @g_n_1stfo
  have p0039 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0040 :=
    Nominal.mp p0038 p0039
  have p0041 :=
    @g_vex u
  have p0042 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (.classMem (.cv u) (syn_cvv)) p0040 p0041
  have p0043 :=
    @g_fnbrfvb (syn_cvv) (.cv u) (syn_cfv (syn_c1st) (.cv u)) (syn_c1st)
  have p0044 :=
    Nominal.mp p0042 p0043
  have p0045 :=
    @g_mpbi (.classEq (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv u))) (syn_wbr (.cv u) (syn_c1st) (syn_cfv (syn_c1st) (.cv u))) p0037 p0044
  have p0046 :=
    @g_eqid (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u))
  have p0047 :=
    @g_fncross
  have p0048 :=
    @g_n_2ndfo
  have p0049 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0050 :=
    Nominal.mp p0048 p0049
  have p0051 :=
    @g_n_2ndfo
  have p0052 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0053 :=
    Nominal.mp p0051 p0052
  have p0054 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0050 p0053
  have p0055 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c2nd) (syn_c2nd)
  have p0056 :=
    Nominal.mp p0054 p0055
  have p0057 :=
    @g_inidm (syn_cvv)
  have p0058 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c2nd) (syn_c2nd)) p0057
  have p0059 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cvv)) p0056 p0058
  have p0060 :=
    @g_ssv (syn_crn (syn_ctxp (syn_c2nd) (syn_c2nd)))
  have p0061 :=
    @g_n_3pm3_2i (syn_wfn (syn_ccross) (syn_cvv)) (syn_wfn (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cvv)) (syn_wss (syn_crn (syn_ctxp (syn_c2nd) (syn_c2nd))) (syn_cvv)) p0047 p0059 p0060
  have p0062 :=
    @g_fnco (syn_cvv) (syn_cvv) (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))
  have p0063 :=
    Nominal.mp p0061 p0062
  have p0064 :=
    @g_vex u
  have p0065 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (syn_cvv)) (.classMem (.cv u) (syn_cvv)) p0063 p0064
  have p0066 :=
    @g_fnbrfvb (syn_cvv) (.cv u) (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u)) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))
  have p0067 :=
    Nominal.mp p0065 p0066
  have p0068 :=
    @g_mpbi (.classEq (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u)) (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u))) (syn_wbr (.cv u) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u))) p0046 p0067
  have p0069 :=
    @g_pm3_2i (syn_wbr (.cv u) (syn_c1st) (syn_cfv (syn_c1st) (.cv u))) (syn_wbr (.cv u) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u))) p0045 p0068
  have p0070 :=
    @g_trtxp (.cv u) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u)) (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))
  have p0071 :=
    @g_mpbir (syn_wbr (.cv u) (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u)))) (syn_wa (syn_wbr (.cv u) (syn_c1st) (syn_cfv (syn_c1st) (.cv u))) (syn_wbr (.cv u) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u)))) p0069 p0070
  have p0072 :=
    @g_n_1stfo
  have p0073 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0074 :=
    Nominal.mp p0072 p0073
  have p0075 :=
    @g_fncross
  have p0076 :=
    @g_n_2ndfo
  have p0077 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0078 :=
    Nominal.mp p0076 p0077
  have p0079 :=
    @g_n_2ndfo
  have p0080 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0081 :=
    Nominal.mp p0079 p0080
  have p0082 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0078 p0081
  have p0083 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c2nd) (syn_c2nd)
  have p0084 :=
    Nominal.mp p0082 p0083
  have p0085 :=
    @g_inidm (syn_cvv)
  have p0086 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c2nd) (syn_c2nd)) p0085
  have p0087 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cvv)) p0084 p0086
  have p0088 :=
    @g_ssv (syn_crn (syn_ctxp (syn_c2nd) (syn_c2nd)))
  have p0089 :=
    @g_n_3pm3_2i (syn_wfn (syn_ccross) (syn_cvv)) (syn_wfn (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cvv)) (syn_wss (syn_crn (syn_ctxp (syn_c2nd) (syn_c2nd))) (syn_cvv)) p0075 p0087 p0088
  have p0090 :=
    @g_fnco (syn_cvv) (syn_cvv) (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))
  have p0091 :=
    Nominal.mp p0089 p0090
  have p0092 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfn (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (syn_cvv)) p0074 p0091
  have p0093 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))
  have p0094 :=
    Nominal.mp p0092 p0093
  have p0095 :=
    @g_inidm (syn_cvv)
  have p0096 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))) p0095
  have p0097 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))) (syn_cvv)) p0094 p0096
  have p0098 :=
    @g_fnfun (syn_cvv) (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))
  have p0099 :=
    Nominal.mp p0097 p0098
  have p0100 :=
    @g_funbrfv (.cv u) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u))) (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))
  have p0101 :=
    Nominal.mp p0099 p0100
  have p0102 :=
    Nominal.mp p0071 p0101
  have p0103 :=
    @g_n_2ndfo
  have p0104 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0105 :=
    Nominal.mp p0103 p0104
  have p0106 :=
    @g_n_2ndfo
  have p0107 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0108 :=
    Nominal.mp p0106 p0107
  have p0109 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0105 p0108
  have p0110 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c2nd) (syn_c2nd)
  have p0111 :=
    Nominal.mp p0109 p0110
  have p0112 :=
    @g_inidm (syn_cvv)
  have p0113 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c2nd) (syn_c2nd)) p0112
  have p0114 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cvv)) p0111 p0113
  have p0115 :=
    @g_vex u
  have p0116 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cvv)) (.classMem (.cv u) (syn_cvv)) p0114 p0115
  have p0117 :=
    @g_fvco2 (syn_cvv) (.cv u) (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))
  have p0118 :=
    Nominal.mp p0116 p0117
  have p0119 :=
    @g_eqid (syn_cfv (syn_c2nd) (.cv u))
  have p0120 :=
    @g_n_2ndfo
  have p0121 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0122 :=
    Nominal.mp p0120 p0121
  have p0123 :=
    @g_vex u
  have p0124 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (.classMem (.cv u) (syn_cvv)) p0122 p0123
  have p0125 :=
    @g_fnbrfvb (syn_cvv) (.cv u) (syn_cfv (syn_c2nd) (.cv u)) (syn_c2nd)
  have p0126 :=
    Nominal.mp p0124 p0125
  have p0127 :=
    @g_mpbi (.classEq (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv u) (syn_c2nd) (syn_cfv (syn_c2nd) (.cv u))) p0119 p0126
  have p0128 :=
    @g_eqid (syn_cfv (syn_c2nd) (.cv u))
  have p0129 :=
    @g_n_2ndfo
  have p0130 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0131 :=
    Nominal.mp p0129 p0130
  have p0132 :=
    @g_vex u
  have p0133 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (.classMem (.cv u) (syn_cvv)) p0131 p0132
  have p0134 :=
    @g_fnbrfvb (syn_cvv) (.cv u) (syn_cfv (syn_c2nd) (.cv u)) (syn_c2nd)
  have p0135 :=
    Nominal.mp p0133 p0134
  have p0136 :=
    @g_mpbi (.classEq (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv u) (syn_c2nd) (syn_cfv (syn_c2nd) (.cv u))) p0128 p0135
  have p0137 :=
    @g_pm3_2i (syn_wbr (.cv u) (syn_c2nd) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv u) (syn_c2nd) (syn_cfv (syn_c2nd) (.cv u))) p0127 p0136
  have p0138 :=
    @g_trtxp (.cv u) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_c2nd) (syn_c2nd)
  have p0139 :=
    @g_mpbir (syn_wbr (.cv u) (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cop (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (syn_wbr (.cv u) (syn_c2nd) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv u) (syn_c2nd) (syn_cfv (syn_c2nd) (.cv u)))) p0137 p0138
  have p0140 :=
    @g_n_2ndfo
  have p0141 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0142 :=
    Nominal.mp p0140 p0141
  have p0143 :=
    @g_n_2ndfo
  have p0144 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0145 :=
    Nominal.mp p0143 p0144
  have p0146 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0142 p0145
  have p0147 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c2nd) (syn_c2nd)
  have p0148 :=
    Nominal.mp p0146 p0147
  have p0149 :=
    @g_inidm (syn_cvv)
  have p0150 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c2nd) (syn_c2nd)) p0149
  have p0151 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c2nd) (syn_c2nd)) (syn_cvv)) p0148 p0150
  have p0152 :=
    @g_fnfun (syn_cvv) (syn_ctxp (syn_c2nd) (syn_c2nd))
  have p0153 :=
    Nominal.mp p0151 p0152
  have p0154 :=
    @g_funbrfv (.cv u) (syn_cop (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_ctxp (syn_c2nd) (syn_c2nd))
  have p0155 :=
    Nominal.mp p0153 p0154
  have p0156 :=
    Nominal.mp p0139 p0155
  have p0157 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_c2nd) (syn_c2nd)) (.cv u)) (syn_cop (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_ccross) p0156
  have p0158 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u)) (syn_cfv (syn_ccross) (syn_cfv (syn_ctxp (syn_c2nd) (syn_c2nd)) (.cv u))) (syn_cfv (syn_ccross) (syn_cop (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) p0118 p0157
  have p0159 :=
    (by simpa [syn_co] using (Nominal.classEqRefl (syn_co (syn_cfv (syn_c2nd) (.cv u)) (syn_ccross) (syn_cfv (syn_c2nd) (.cv u)))))
  have p0160 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0161 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0162 :=
    @g_pm3_2i (.classMem (syn_cfv (syn_c2nd) (.cv u)) (syn_cvv)) (.classMem (syn_cfv (syn_c2nd) (.cv u)) (syn_cvv)) p0160 p0161
  have p0163 :=
    @g_ovcross (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cvv) (syn_cvv)
  have p0164 :=
    Nominal.mp p0162 p0163
  have p0165 :=
    @g_eqtr3i (syn_co (syn_cfv (syn_c2nd) (.cv u)) (syn_ccross) (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_ccross) (syn_cop (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) p0159 p0164
  have p0166 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u)) (syn_cfv (syn_ccross) (syn_cop (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) p0158 p0165
  have p0167 :=
    @g_opeq2i (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)) p0166
  have p0168 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))) (.cv u)) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))) (.cv u))) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) p0102 p0167
  have p0169 :=
    @g_eleq1i (syn_cfv (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))) (.cv u)) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (syn_csset) p0168
  have p0170 :=
    @g_bitri (.classMem (.cv u) (syn_cima (syn_ccnv (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))) (syn_csset))) (.classMem (syn_cfv (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd)))) (.cv u)) (syn_csset)) (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (syn_csset)) p0036 p0169
  have p0171 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_csset) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))))
  have p0172 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0173 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0174 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0175 :=
    @g_xpex (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) p0173 p0174
  have p0176 :=
    @g_brsset (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) p0172 p0175
  have p0177 :=
    @g_bitr3i (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (syn_csset)) (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_csset) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) p0171 p0176
  have p0178 :=
    @g_bitri (.classMem (.cv u) (syn_cima (syn_ccnv (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))) (syn_csset))) (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (syn_csset)) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) p0170 p0177
  have p0179 :=
    @g_bitri (.classMem (.cv u) (syn_chwrels)) (.classMem (.cv u) (syn_cima (syn_ccnv (syn_ctxp (syn_c1st) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c2nd))))) (syn_csset))) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) p0004 p0178
  have p0180 :=
    @g_anbi2i (.classMem (.cv u) (syn_chwrels)) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem (.cv u) (syn_chwcodes A)) p0179
  have p0181 :=
    @g_bitri (.classMem (.cv u) (syn_cin (syn_chwcodes A) (syn_chwrels))) (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv u) (syn_chwrels))) (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) p0002 p0180
  have p0182 :=
    @g_bitri (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_cin (syn_chwcodes A) (syn_chwrels))) (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (syn_wss (syn_cfv (syn_c1st) (.cv u)) (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) p0001 p0181
  exact p0182

noncomputable def g_elhwbij
    (f : Var) :
    Nominal.NPrf (syn_wb (.classMem (.cv f) (syn_chwbij)) (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f))))) := by
  let proofSupport : Finset Var := ({f} : Finset Var)
  let g : Var := freshVar proofSupport 0
  have fresh_g : g ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_g_ne_f : g ≠ f := by
    intro h
    exact fresh_g (Finset.mem_singleton.mpr h)
  have fresh_f_ne_g : f ≠ g :=
    Ne.symm fresh_g_ne_f
  have dv_cache_0001 : g ∉ ((Class.cv f)).fv := by
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : g ∉ ((syn_ccnv (syn_cimage (syn_cswap)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : g ∉ ((syn_cfuns)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfuns, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : g ∉ ((syn_ccnv (.cv f))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    (by simpa [syn_chwbij] using (Nominal.classEqRefl (syn_chwbij)))
  have p0001 :=
    @g_eleq2i (syn_chwbij) (syn_cin (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfuns))) (.cv f) p0000
  have p0002 :=
    @g_elin (.cv f) (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfuns))
  have p0003 :=
    @g_elima g (.cv f) (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfuns) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0004 :=
    @g_brcnv (.cv g) (.cv f) (syn_cimage (syn_cswap))
  have p0005 :=
    @g_vex f
  have p0006 :=
    @g_vex g
  have p0007 :=
    @g_brimage (.cv f) (.cv g) (syn_cswap) p0005 p0006
  have p0008 :=
    @g_bitri (syn_wbr (.cv g) (syn_ccnv (syn_cimage (syn_cswap))) (.cv f)) (syn_wbr (.cv f) (syn_cimage (syn_cswap)) (.cv g)) (.classEq (.cv g) (syn_cima (syn_cswap) (.cv f))) p0004 p0007
  have p0009 :=
    @g_dfcnv2 (.cv f)
  have p0010 :=
    @g_eqeq2i (syn_ccnv (.cv f)) (syn_cima (syn_cswap) (.cv f)) (.cv g) p0009
  have p0011 :=
    @g_bicomi (.classEq (.cv g) (syn_ccnv (.cv f))) (.classEq (.cv g) (syn_cima (syn_cswap) (.cv f))) p0010
  have p0012 :=
    @g_bitri (syn_wbr (.cv g) (syn_ccnv (syn_cimage (syn_cswap))) (.cv f)) (.classEq (.cv g) (syn_cima (syn_cswap) (.cv f))) (.classEq (.cv g) (syn_ccnv (.cv f))) p0008 p0011
  have p0013 :=
    @g_rexbii (syn_wbr (.cv g) (syn_ccnv (syn_cimage (syn_cswap))) (.cv f)) (.classEq (.cv g) (syn_ccnv (.cv f))) g (syn_cfuns) p0012
  have p0014 :=
    @g_bitri (.classMem (.cv f) (syn_cima (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfuns))) (syn_wrex g (syn_cfuns) (syn_wbr (.cv g) (syn_ccnv (syn_cimage (syn_cswap))) (.cv f))) (syn_wrex g (syn_cfuns) (.classEq (.cv g) (syn_ccnv (.cv f)))) p0003 p0013
  have p0015 :=
    @g_risset g (syn_ccnv (.cv f)) (syn_cfuns) dv_cache_0004 dv_cache_0003
  have p0016 :=
    @g_bicomi (.classMem (syn_ccnv (.cv f)) (syn_cfuns)) (syn_wrex g (syn_cfuns) (.classEq (.cv g) (syn_ccnv (.cv f)))) p0015
  have p0017 :=
    @g_bitri (.classMem (.cv f) (syn_cima (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfuns))) (syn_wrex g (syn_cfuns) (.classEq (.cv g) (syn_ccnv (.cv f)))) (.classMem (syn_ccnv (.cv f)) (syn_cfuns)) p0014 p0016
  have p0018 :=
    @g_anbi2i (.classMem (.cv f) (syn_cima (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfuns))) (.classMem (syn_ccnv (.cv f)) (syn_cfuns)) (.classMem (.cv f) (syn_cfuns)) p0017
  have p0019 :=
    @g_bitri (.classMem (.cv f) (syn_cin (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfuns)))) (syn_wa (.classMem (.cv f) (syn_cfuns)) (.classMem (.cv f) (syn_cima (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfuns)))) (syn_wa (.classMem (.cv f) (syn_cfuns)) (.classMem (syn_ccnv (.cv f)) (syn_cfuns))) p0002 p0018
  have p0020 :=
    @g_vex f
  have p0021 :=
    @g_elfuns (.cv f) p0020
  have p0022 :=
    @g_vex f
  have p0023 :=
    @g_cnvex (.cv f) p0022
  have p0024 :=
    @g_elfuns (syn_ccnv (.cv f)) p0023
  have p0025 :=
    @g_anbi12i (.classMem (.cv f) (syn_cfuns)) (syn_wfun (.cv f)) (.classMem (syn_ccnv (.cv f)) (syn_cfuns)) (syn_wfun (syn_ccnv (.cv f))) p0021 p0024
  have p0026 :=
    @g_bitri (.classMem (.cv f) (syn_cin (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfuns)))) (syn_wa (.classMem (.cv f) (syn_cfuns)) (.classMem (syn_ccnv (.cv f)) (syn_cfuns))) (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f)))) p0019 p0025
  have p0027 :=
    @g_bitri (.classMem (.cv f) (syn_chwbij)) (.classMem (.cv f) (syn_cin (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfuns)))) (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f)))) p0001 p0026
  exact p0027

noncomputable def g_elhnord
    (x : Var) (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_u_x : u ≠ x) (hyp_elhnord_1 : Nominal.NPrf (.classMem (.cv x) (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem (.cv x) (syn_chnord A)) (syn_wrex u (syn_chwcn A) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso A))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv
  have dv_cache_0001 : u ∉ ((syn_chwcn A)).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_u_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : u ∉ ((syn_chwniso A)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    (by simpa [syn_chnord] using (Nominal.classEqRefl (syn_chnord A)))
  have p0001 :=
    @g_eleq2i (syn_chnord A) (syn_cqs (syn_chwcn A) (syn_chwniso A)) (.cv x) p0000
  have p0002 :=
    @g_elqs u (syn_chwcn A) (.cv x) (syn_chwniso A) dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_elhnord_1
  have p0003 :=
    @g_bitri (.classMem (.cv x) (syn_chnord A)) (.classMem (.cv x) (syn_cqs (syn_chwcn A) (syn_chwniso A))) (syn_wrex u (syn_chwcn A) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso A)))) p0001 p0002
  exact p0003

noncomputable def g_hwnisoclasselhnord
    (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) (hyp_hwnisoclasselhnord_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem (.cv u) (syn_chwcn A)) (.classMem (syn_cec (.cv u) (syn_chwniso A)) (syn_chnord A))) := by
  let proofSupport : Finset Var := ({u} : Finset Var) ∪ A.fv
  have p0000 :=
    @g_hwnisoex A hyp_hwnisoclasselhnord_1
  have p0001 :=
    @g_ecelqsi (syn_chwcn A) (.cv u) (syn_chwniso A) p0000
  have p0002 :=
    (by simpa [syn_chnord] using (Nominal.classEqRefl (syn_chnord A)))
  have p0003 :=
    @g_eleq2i (syn_chnord A) (syn_cqs (syn_chwcn A) (syn_chwniso A)) (syn_cec (.cv u) (syn_chwniso A)) p0002
  have p0004 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn A)) (.classMem (syn_cec (.cv u) (syn_chwniso A)) (syn_cqs (syn_chwcn A) (syn_chwniso A))) (.classMem (syn_cec (.cv u) (syn_chwniso A)) (syn_chnord A)) p0001 p0003
  exact p0004

noncomputable def g_imageswapfn
     :
    Nominal.NPrf (syn_wfn (syn_cimage (syn_cswap)) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let a : Var := freshVar proofSupport 1
  let b : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_ne_a : x ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_x : a ≠ x :=
    Ne.symm fresh_x_ne_a
  have fresh_x_ne_b : x ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_b_ne_x : b ≠ x :=
    Ne.symm fresh_x_ne_b
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have dv_cache_0001 : x ∉ ((syn_cvv)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cima (syn_cswap) (.cv a))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : a ∉ ((syn_cimage (syn_cswap))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : b ∉ ((syn_cimage (syn_cswap))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : a ∉ ((syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : b ∉ ((syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : a ≠ b := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have p0000 :=
    @g_swapex
  have p0001 :=
    @g_vex x
  have p0002 :=
    @g_imaex (syn_cswap) (.cv x) p0000 p0001
  have p0003 :=
    @g_eqid (syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x)))
  have p0004 :=
    @g_fnmpti x (syn_cvv) (syn_cima (syn_cswap) (.cv x)) (syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x))) dv_cache_0001 p0002 p0003
  have p0005 :=
    @g_vex a
  have p0006 :=
    @g_vex b
  have p0007 :=
    @g_brimage (.cv a) (.cv b) (syn_cswap) p0005 p0006
  have p0008 :=
    @g_swapex
  have p0009 :=
    @g_vex x
  have p0010 :=
    @g_imaex (syn_cswap) (.cv x) p0008 p0009
  have p0011 :=
    @g_eqid (syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x)))
  have p0012 :=
    @g_fnmpti x (syn_cvv) (syn_cima (syn_cswap) (.cv x)) (syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x))) dv_cache_0001 p0010 p0011
  have p0013 :=
    @g_vex a
  have p0014 :=
    @g_pm3_2i (syn_wfn (syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x))) (syn_cvv)) (.classMem (.cv a) (syn_cvv)) p0012 p0013
  have p0015 :=
    @g_fnbrfvb (syn_cvv) (.cv a) (.cv b) (syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x)))
  have p0016 :=
    Nominal.mp p0014 p0015
  have p0017 :=
    @g_bicomi (.classEq (syn_cfv (syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x))) (.cv a)) (.cv b)) (syn_wbr (.cv a) (syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x))) (.cv b)) p0016
  have p0018 :=
    @g_vex a
  have p0019 :=
    @g_imaeq2 (.cv x) (.cv a) (syn_cswap)
  have p0020 :=
    @g_eqid (syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x)))
  have p0021 :=
    @g_swapex
  have p0022 :=
    @g_vex a
  have p0023 :=
    @g_imaex (syn_cswap) (.cv a) p0021 p0022
  have p0024 :=
    @g_fvmpt x (.cv a) (syn_cima (syn_cswap) (.cv x)) (syn_cima (syn_cswap) (.cv a)) (syn_cvv) (syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x))) dv_cache_0002 dv_cache_0003 dv_cache_0001 p0019 p0020 p0023
  have p0025 :=
    Nominal.mp p0018 p0024
  have p0026 :=
    @g_eqeq1i (syn_cfv (syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x))) (.cv a)) (syn_cima (syn_cswap) (.cv a)) (.cv b) p0025
  have p0027 :=
    @g_bitri (syn_wbr (.cv a) (syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x))) (.cv b)) (.classEq (syn_cfv (syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x))) (.cv a)) (.cv b)) (.classEq (syn_cima (syn_cswap) (.cv a)) (.cv b)) p0017 p0026
  have p0028 :=
    @g_eqcom (syn_cima (syn_cswap) (.cv a)) (.cv b)
  have p0029 :=
    @g_bitri (syn_wbr (.cv a) (syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x))) (.cv b)) (.classEq (syn_cima (syn_cswap) (.cv a)) (.cv b)) (.classEq (.cv b) (syn_cima (syn_cswap) (.cv a))) p0027 p0028
  have p0030 :=
    @g_bitr4i (syn_wbr (.cv a) (syn_cimage (syn_cswap)) (.cv b)) (.classEq (.cv b) (syn_cima (syn_cswap) (.cv a))) (syn_wbr (.cv a) (syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x))) (.cv b)) p0007 p0029
  have p0031 :=
    @g_eqbrriv a b (syn_cimage (syn_cswap)) (syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x))) dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 p0030
  have p0032 :=
    @g_fneq1i (syn_cvv) (syn_cimage (syn_cswap)) (syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x))) p0031
  have p0033 :=
    @g_mpbir (syn_wfn (syn_cimage (syn_cswap)) (syn_cvv)) (syn_wfn (syn_cmpt x (syn_cvv) (syn_cima (syn_cswap) (.cv x))) (syn_cvv)) p0004 p0032
  exact p0033

noncomputable def g_imageswapval
    (f : Var) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cimage (syn_cswap)) (.cv f)) (syn_ccnv (.cv f))) := by
  let proofSupport : Finset Var := ({f} : Finset Var)
  have p0000 :=
    @g_eqid (syn_cima (syn_cswap) (.cv f))
  have p0001 :=
    @g_vex f
  have p0002 :=
    @g_swapex
  have p0003 :=
    @g_vex f
  have p0004 :=
    @g_imaex (syn_cswap) (.cv f) p0002 p0003
  have p0005 :=
    @g_brimage (.cv f) (syn_cima (syn_cswap) (.cv f)) (syn_cswap) p0001 p0004
  have p0006 :=
    @g_mpbir (syn_wbr (.cv f) (syn_cimage (syn_cswap)) (syn_cima (syn_cswap) (.cv f))) (.classEq (syn_cima (syn_cswap) (.cv f)) (syn_cima (syn_cswap) (.cv f))) p0000 p0005
  have p0007 :=
    @g_imageswapfn
  have p0008 :=
    @g_vex f
  have p0009 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_cswap)) (syn_cvv)) (.classMem (.cv f) (syn_cvv)) p0007 p0008
  have p0010 :=
    @g_fnbrfvb (syn_cvv) (.cv f) (syn_cima (syn_cswap) (.cv f)) (syn_cimage (syn_cswap))
  have p0011 :=
    Nominal.mp p0009 p0010
  have p0012 :=
    @g_mpbir (.classEq (syn_cfv (syn_cimage (syn_cswap)) (.cv f)) (syn_cima (syn_cswap) (.cv f))) (syn_wbr (.cv f) (syn_cimage (syn_cswap)) (syn_cima (syn_cswap) (.cv f))) p0006 p0011
  have p0013 :=
    @g_dfcnv2 (.cv f)
  have p0014 :=
    @g_eqtr4i (syn_cfv (syn_cimage (syn_cswap)) (.cv f)) (syn_cima (syn_cswap) (.cv f)) (syn_ccnv (.cv f)) p0012 p0013
  exact p0014

#print axioms g_imageswapval

end NFChoice.DirectNominalPrf.WPPReplay
