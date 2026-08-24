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
import NominalWPPReplayChunk017Compact001Part016

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

noncomputable def g_hncodecutpairfnfn
     :
    Nominal.NPrf (syn_wfn (syn_chncodecutpairfn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_lninteropfn
  have p0001 :=
    @g_ln1stfn
  have p0002 :=
    @g_ln1stfn
  have p0003 :=
    @g_fncovv (syn_c1st) (syn_c1st) p0001 p0002
  have p0004 :=
    @g_fncross
  have p0005 :=
    @g_lninteropfn
  have p0006 :=
    @g_ln2ndfn
  have p0007 :=
    @g_ln1stfn
  have p0008 :=
    @g_fncovv (syn_c2nd) (syn_c1st) p0006 p0007
  have p0009 :=
    @g_lnimageopfn
  have p0010 :=
    @g_imageswapfn
  have p0011 :=
    @g_fnlndifop
  have p0012 :=
    @g_ln1stfn
  have p0013 :=
    @g_ln1stfn
  have p0014 :=
    @g_fncovv (syn_c1st) (syn_c1st) p0012 p0013
  have p0015 :=
    @g_idex
  have p0016 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p0017 :=
    Nominal.mp p0015 p0016
  have p0018 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p0014 p0017
  have p0019 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p0020 :=
    Nominal.mp p0018 p0019
  have p0021 :=
    @g_inidm (syn_cvv)
  have p0022 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0021
  have p0023 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) p0020 p0022
  have p0024 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0011 p0023
  have p0025 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p0026 :=
    @g_fneq1i (syn_cvv) (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) p0025
  have p0027 :=
    @g_mpbir (syn_wfn (syn_chncodestrictfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv)) p0024 p0026
  have p0028 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p0010 p0027
  have p0029 :=
    @g_ln2ndfn
  have p0030 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0028 p0029
  have p0031 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)
  have p0032 :=
    Nominal.mp p0030 p0031
  have p0033 :=
    @g_inidm (syn_cvv)
  have p0034 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0033
  have p0035 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cvv)) p0032 p0034
  have p0036 :=
    @g_fncovv (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0009 p0035
  have p0037 :=
    (by simpa [syn_chncodepredfn] using (Nominal.classEqRefl (syn_chncodepredfn)))
  have p0038 :=
    @g_fneq1i (syn_cvv) (syn_chncodepredfn) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) p0037
  have p0039 :=
    @g_mpbir (syn_wfn (syn_chncodepredfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) (syn_cvv)) p0036 p0038
  have p0040 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c2nd) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_chncodepredfn) (syn_cvv)) p0008 p0039
  have p0041 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)
  have p0042 :=
    Nominal.mp p0040 p0041
  have p0043 :=
    @g_inidm (syn_cvv)
  have p0044 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0043
  have p0045 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cvv)) p0042 p0044
  have p0046 :=
    @g_fncovv (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0005 p0045
  have p0047 :=
    (by simpa [syn_chncodecarrierfn] using (Nominal.classEqRefl (syn_chncodecarrierfn)))
  have p0048 :=
    @g_fneq1i (syn_cvv) (syn_chncodecarrierfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) p0047
  have p0049 :=
    @g_mpbir (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) (syn_cvv)) p0046 p0048
  have p0050 :=
    @g_lninteropfn
  have p0051 :=
    @g_ln2ndfn
  have p0052 :=
    @g_ln1stfn
  have p0053 :=
    @g_fncovv (syn_c2nd) (syn_c1st) p0051 p0052
  have p0054 :=
    @g_lnimageopfn
  have p0055 :=
    @g_imageswapfn
  have p0056 :=
    @g_fnlndifop
  have p0057 :=
    @g_ln1stfn
  have p0058 :=
    @g_ln1stfn
  have p0059 :=
    @g_fncovv (syn_c1st) (syn_c1st) p0057 p0058
  have p0060 :=
    @g_idex
  have p0061 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p0062 :=
    Nominal.mp p0060 p0061
  have p0063 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p0059 p0062
  have p0064 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p0065 :=
    Nominal.mp p0063 p0064
  have p0066 :=
    @g_inidm (syn_cvv)
  have p0067 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0066
  have p0068 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) p0065 p0067
  have p0069 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0056 p0068
  have p0070 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p0071 :=
    @g_fneq1i (syn_cvv) (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) p0070
  have p0072 :=
    @g_mpbir (syn_wfn (syn_chncodestrictfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv)) p0069 p0071
  have p0073 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p0055 p0072
  have p0074 :=
    @g_ln2ndfn
  have p0075 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0073 p0074
  have p0076 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)
  have p0077 :=
    Nominal.mp p0075 p0076
  have p0078 :=
    @g_inidm (syn_cvv)
  have p0079 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0078
  have p0080 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cvv)) p0077 p0079
  have p0081 :=
    @g_fncovv (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0054 p0080
  have p0082 :=
    (by simpa [syn_chncodepredfn] using (Nominal.classEqRefl (syn_chncodepredfn)))
  have p0083 :=
    @g_fneq1i (syn_cvv) (syn_chncodepredfn) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) p0082
  have p0084 :=
    @g_mpbir (syn_wfn (syn_chncodepredfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) (syn_cvv)) p0081 p0083
  have p0085 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c2nd) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_chncodepredfn) (syn_cvv)) p0053 p0084
  have p0086 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)
  have p0087 :=
    Nominal.mp p0085 p0086
  have p0088 :=
    @g_inidm (syn_cvv)
  have p0089 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0088
  have p0090 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cvv)) p0087 p0089
  have p0091 :=
    @g_fncovv (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0050 p0090
  have p0092 :=
    (by simpa [syn_chncodecarrierfn] using (Nominal.classEqRefl (syn_chncodecarrierfn)))
  have p0093 :=
    @g_fneq1i (syn_cvv) (syn_chncodecarrierfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) p0092
  have p0094 :=
    @g_mpbir (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) (syn_cvv)) p0091 p0093
  have p0095 :=
    @g_pm3_2i (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) p0049 p0094
  have p0096 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_chncodecarrierfn) (syn_chncodecarrierfn)
  have p0097 :=
    Nominal.mp p0095 p0096
  have p0098 :=
    @g_inidm (syn_cvv)
  have p0099 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) p0098
  have p0100 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) (syn_cvv)) p0097 p0099
  have p0101 :=
    @g_fncovv (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) p0004 p0100
  have p0102 :=
    (by simpa [syn_chncodesquarefn] using (Nominal.classEqRefl (syn_chncodesquarefn)))
  have p0103 :=
    @g_fneq1i (syn_cvv) (syn_chncodesquarefn) (syn_ccom (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn))) p0102
  have p0104 :=
    @g_mpbir (syn_wfn (syn_chncodesquarefn) (syn_cvv)) (syn_wfn (syn_ccom (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn))) (syn_cvv)) p0101 p0103
  have p0105 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_chncodesquarefn) (syn_cvv)) p0003 p0104
  have p0106 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)
  have p0107 :=
    Nominal.mp p0105 p0106
  have p0108 :=
    @g_inidm (syn_cvv)
  have p0109 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) p0108
  have p0110 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) (syn_cvv)) p0107 p0109
  have p0111 :=
    @g_fncovv (syn_clninterop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) p0000 p0110
  have p0112 :=
    (by simpa [syn_chncoderelfn] using (Nominal.classEqRefl (syn_chncoderelfn)))
  have p0113 :=
    @g_fneq1i (syn_cvv) (syn_chncoderelfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn))) p0112
  have p0114 :=
    @g_mpbir (syn_wfn (syn_chncoderelfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn))) (syn_cvv)) p0111 p0113
  have p0115 :=
    @g_lninteropfn
  have p0116 :=
    @g_ln2ndfn
  have p0117 :=
    @g_ln1stfn
  have p0118 :=
    @g_fncovv (syn_c2nd) (syn_c1st) p0116 p0117
  have p0119 :=
    @g_lnimageopfn
  have p0120 :=
    @g_imageswapfn
  have p0121 :=
    @g_fnlndifop
  have p0122 :=
    @g_ln1stfn
  have p0123 :=
    @g_ln1stfn
  have p0124 :=
    @g_fncovv (syn_c1st) (syn_c1st) p0122 p0123
  have p0125 :=
    @g_idex
  have p0126 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p0127 :=
    Nominal.mp p0125 p0126
  have p0128 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p0124 p0127
  have p0129 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p0130 :=
    Nominal.mp p0128 p0129
  have p0131 :=
    @g_inidm (syn_cvv)
  have p0132 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0131
  have p0133 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) p0130 p0132
  have p0134 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0121 p0133
  have p0135 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p0136 :=
    @g_fneq1i (syn_cvv) (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) p0135
  have p0137 :=
    @g_mpbir (syn_wfn (syn_chncodestrictfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv)) p0134 p0136
  have p0138 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p0120 p0137
  have p0139 :=
    @g_ln2ndfn
  have p0140 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0138 p0139
  have p0141 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)
  have p0142 :=
    Nominal.mp p0140 p0141
  have p0143 :=
    @g_inidm (syn_cvv)
  have p0144 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0143
  have p0145 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cvv)) p0142 p0144
  have p0146 :=
    @g_fncovv (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0119 p0145
  have p0147 :=
    (by simpa [syn_chncodepredfn] using (Nominal.classEqRefl (syn_chncodepredfn)))
  have p0148 :=
    @g_fneq1i (syn_cvv) (syn_chncodepredfn) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) p0147
  have p0149 :=
    @g_mpbir (syn_wfn (syn_chncodepredfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) (syn_cvv)) p0146 p0148
  have p0150 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c2nd) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_chncodepredfn) (syn_cvv)) p0118 p0149
  have p0151 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)
  have p0152 :=
    Nominal.mp p0150 p0151
  have p0153 :=
    @g_inidm (syn_cvv)
  have p0154 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0153
  have p0155 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cvv)) p0152 p0154
  have p0156 :=
    @g_fncovv (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0115 p0155
  have p0157 :=
    (by simpa [syn_chncodecarrierfn] using (Nominal.classEqRefl (syn_chncodecarrierfn)))
  have p0158 :=
    @g_fneq1i (syn_cvv) (syn_chncodecarrierfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) p0157
  have p0159 :=
    @g_mpbir (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) (syn_cvv)) p0156 p0158
  have p0160 :=
    @g_pm3_2i (syn_wfn (syn_chncoderelfn) (syn_cvv)) (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) p0114 p0159
  have p0161 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_chncoderelfn) (syn_chncodecarrierfn)
  have p0162 :=
    Nominal.mp p0160 p0161
  have p0163 :=
    @g_inidm (syn_cvv)
  have p0164 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn)) p0163
  have p0165 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn)) (syn_cvv)) p0162 p0164
  have p0166 :=
    (by simpa [syn_chncodecutfn] using (Nominal.classEqRefl (syn_chncodecutfn)))
  have p0167 :=
    @g_fneq1i (syn_cvv) (syn_chncodecutfn) (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn)) p0166
  have p0168 :=
    @g_mpbir (syn_wfn (syn_chncodecutfn) (syn_cvv)) (syn_wfn (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn)) (syn_cvv)) p0165 p0167
  have p0169 :=
    @g_ln1stfn
  have p0170 :=
    @g_pm3_2i (syn_wfn (syn_chncodecutfn) (syn_cvv)) (syn_wfn (syn_c1st) (syn_cvv)) p0168 p0169
  have p0171 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_chncodecutfn) (syn_c1st)
  have p0172 :=
    Nominal.mp p0170 p0171
  have p0173 :=
    @g_inidm (syn_cvv)
  have p0174 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_chncodecutfn) (syn_c1st)) p0173
  have p0175 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_chncodecutfn) (syn_c1st)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_chncodecutfn) (syn_c1st)) (syn_cvv)) p0172 p0174
  have p0176 :=
    (by simpa [syn_chncodecutpairfn] using (Nominal.classEqRefl (syn_chncodecutpairfn)))
  have p0177 :=
    @g_fneq1i (syn_cvv) (syn_chncodecutpairfn) (syn_ctxp (syn_chncodecutfn) (syn_c1st)) p0176
  have p0178 :=
    @g_mpbir (syn_wfn (syn_chncodecutpairfn) (syn_cvv)) (syn_wfn (syn_ctxp (syn_chncodecutfn) (syn_c1st)) (syn_cvv)) p0175 p0177
  exact p0178

noncomputable def g_hncodecutpairfnex
     :
    Nominal.NPrf (.classMem (syn_chncodecutpairfn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_chncodecutpairfn] using (Nominal.classEqRefl (syn_chncodecutpairfn)))
  have p0001 :=
    (by simpa [syn_chncodecutfn] using (Nominal.classEqRefl (syn_chncodecutfn)))
  have p0002 :=
    (by simpa [syn_chncoderelfn] using (Nominal.classEqRefl (syn_chncoderelfn)))
  have p0003 :=
    @g_lninteropex
  have p0004 :=
    @g_n_1stex
  have p0005 :=
    @g_n_1stex
  have p0006 :=
    @g_coex (syn_c1st) (syn_c1st) p0004 p0005
  have p0007 :=
    (by simpa [syn_chncodesquarefn] using (Nominal.classEqRefl (syn_chncodesquarefn)))
  have p0008 :=
    @g_crossex
  have p0009 :=
    (by simpa [syn_chncodecarrierfn] using (Nominal.classEqRefl (syn_chncodecarrierfn)))
  have p0010 :=
    @g_lninteropex
  have p0011 :=
    @g_n_2ndex
  have p0012 :=
    @g_n_1stex
  have p0013 :=
    @g_coex (syn_c2nd) (syn_c1st) p0011 p0012
  have p0014 :=
    (by simpa [syn_chncodepredfn] using (Nominal.classEqRefl (syn_chncodepredfn)))
  have p0015 :=
    @g_lnimageopex
  have p0016 :=
    @g_swapex
  have p0017 :=
    @g_imageex (syn_cswap) p0016
  have p0018 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p0019 :=
    @g_lndifopex
  have p0020 :=
    @g_n_1stex
  have p0021 :=
    @g_n_1stex
  have p0022 :=
    @g_coex (syn_c1st) (syn_c1st) p0020 p0021
  have p0023 :=
    @g_vvex
  have p0024 :=
    @g_snex (syn_cid)
  have p0025 :=
    @g_xpex (syn_cvv) (syn_csn (syn_cid)) p0023 p0024
  have p0026 :=
    @g_txpex (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))) p0022 p0025
  have p0027 :=
    @g_coex (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0019 p0026
  have p0028 :=
    @g_eqeltri (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv) p0018 p0027
  have p0029 :=
    @g_coex (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p0017 p0028
  have p0030 :=
    @g_n_2ndex
  have p0031 :=
    @g_txpex (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd) p0029 p0030
  have p0032 :=
    @g_coex (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0015 p0031
  have p0033 :=
    @g_eqeltri (syn_chncodepredfn) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) (syn_cvv) p0014 p0032
  have p0034 :=
    @g_txpex (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn) p0013 p0033
  have p0035 :=
    @g_coex (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0010 p0034
  have p0036 :=
    @g_eqeltri (syn_chncodecarrierfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) (syn_cvv) p0009 p0035
  have p0037 :=
    (by simpa [syn_chncodecarrierfn] using (Nominal.classEqRefl (syn_chncodecarrierfn)))
  have p0038 :=
    @g_lninteropex
  have p0039 :=
    @g_n_2ndex
  have p0040 :=
    @g_n_1stex
  have p0041 :=
    @g_coex (syn_c2nd) (syn_c1st) p0039 p0040
  have p0042 :=
    (by simpa [syn_chncodepredfn] using (Nominal.classEqRefl (syn_chncodepredfn)))
  have p0043 :=
    @g_lnimageopex
  have p0044 :=
    @g_swapex
  have p0045 :=
    @g_imageex (syn_cswap) p0044
  have p0046 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p0047 :=
    @g_lndifopex
  have p0048 :=
    @g_n_1stex
  have p0049 :=
    @g_n_1stex
  have p0050 :=
    @g_coex (syn_c1st) (syn_c1st) p0048 p0049
  have p0051 :=
    @g_vvex
  have p0052 :=
    @g_snex (syn_cid)
  have p0053 :=
    @g_xpex (syn_cvv) (syn_csn (syn_cid)) p0051 p0052
  have p0054 :=
    @g_txpex (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))) p0050 p0053
  have p0055 :=
    @g_coex (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0047 p0054
  have p0056 :=
    @g_eqeltri (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv) p0046 p0055
  have p0057 :=
    @g_coex (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p0045 p0056
  have p0058 :=
    @g_n_2ndex
  have p0059 :=
    @g_txpex (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd) p0057 p0058
  have p0060 :=
    @g_coex (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0043 p0059
  have p0061 :=
    @g_eqeltri (syn_chncodepredfn) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) (syn_cvv) p0042 p0060
  have p0062 :=
    @g_txpex (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn) p0041 p0061
  have p0063 :=
    @g_coex (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0038 p0062
  have p0064 :=
    @g_eqeltri (syn_chncodecarrierfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) (syn_cvv) p0037 p0063
  have p0065 :=
    @g_txpex (syn_chncodecarrierfn) (syn_chncodecarrierfn) p0036 p0064
  have p0066 :=
    @g_coex (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) p0008 p0065
  have p0067 :=
    @g_eqeltri (syn_chncodesquarefn) (syn_ccom (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn))) (syn_cvv) p0007 p0066
  have p0068 :=
    @g_txpex (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn) p0006 p0067
  have p0069 :=
    @g_coex (syn_clninterop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) p0003 p0068
  have p0070 :=
    @g_eqeltri (syn_chncoderelfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn))) (syn_cvv) p0002 p0069
  have p0071 :=
    (by simpa [syn_chncodecarrierfn] using (Nominal.classEqRefl (syn_chncodecarrierfn)))
  have p0072 :=
    @g_lninteropex
  have p0073 :=
    @g_n_2ndex
  have p0074 :=
    @g_n_1stex
  have p0075 :=
    @g_coex (syn_c2nd) (syn_c1st) p0073 p0074
  have p0076 :=
    (by simpa [syn_chncodepredfn] using (Nominal.classEqRefl (syn_chncodepredfn)))
  have p0077 :=
    @g_lnimageopex
  have p0078 :=
    @g_swapex
  have p0079 :=
    @g_imageex (syn_cswap) p0078
  have p0080 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p0081 :=
    @g_lndifopex
  have p0082 :=
    @g_n_1stex
  have p0083 :=
    @g_n_1stex
  have p0084 :=
    @g_coex (syn_c1st) (syn_c1st) p0082 p0083
  have p0085 :=
    @g_vvex
  have p0086 :=
    @g_snex (syn_cid)
  have p0087 :=
    @g_xpex (syn_cvv) (syn_csn (syn_cid)) p0085 p0086
  have p0088 :=
    @g_txpex (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))) p0084 p0087
  have p0089 :=
    @g_coex (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0081 p0088
  have p0090 :=
    @g_eqeltri (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv) p0080 p0089
  have p0091 :=
    @g_coex (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p0079 p0090
  have p0092 :=
    @g_n_2ndex
  have p0093 :=
    @g_txpex (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd) p0091 p0092
  have p0094 :=
    @g_coex (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0077 p0093
  have p0095 :=
    @g_eqeltri (syn_chncodepredfn) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) (syn_cvv) p0076 p0094
  have p0096 :=
    @g_txpex (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn) p0075 p0095
  have p0097 :=
    @g_coex (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0072 p0096
  have p0098 :=
    @g_eqeltri (syn_chncodecarrierfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) (syn_cvv) p0071 p0097
  have p0099 :=
    @g_txpex (syn_chncoderelfn) (syn_chncodecarrierfn) p0070 p0098
  have p0100 :=
    @g_eqeltri (syn_chncodecutfn) (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn)) (syn_cvv) p0001 p0099
  have p0101 :=
    @g_n_1stex
  have p0102 :=
    @g_txpex (syn_chncodecutfn) (syn_c1st) p0100 p0101
  have p0103 :=
    @g_eqeltri (syn_chncodecutpairfn) (syn_ctxp (syn_chncodecutfn) (syn_c1st)) (syn_cvv) p0000 p0102
  exact p0103

#print axioms g_hncodecutpairfnex

end NFChoice.DirectNominalPrf.WPPReplay
