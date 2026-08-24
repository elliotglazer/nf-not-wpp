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
import NominalWPPReplayChunk017Compact001Part017

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

noncomputable def g_hncodecutfnval
    (x : Var) (D : Class) (R : Class) (hyp_hncodecutfnval_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_hncodecutfnval_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_chncodecutfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_chnwcutcode R D (.cv x))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ D.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_chncodecutfn] using (Nominal.classEqRefl (syn_chncodecutfn)))
  have p0001 :=
    @g_fveq1i (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_chncodecutfn) (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn)) p0000
  have p0002 :=
    @g_lninteropfn
  have p0003 :=
    @g_ln1stfn
  have p0004 :=
    @g_ln1stfn
  have p0005 :=
    @g_fncovv (syn_c1st) (syn_c1st) p0003 p0004
  have p0006 :=
    @g_fncross
  have p0007 :=
    @g_lninteropfn
  have p0008 :=
    @g_ln2ndfn
  have p0009 :=
    @g_ln1stfn
  have p0010 :=
    @g_fncovv (syn_c2nd) (syn_c1st) p0008 p0009
  have p0011 :=
    @g_lnimageopfn
  have p0012 :=
    @g_imageswapfn
  have p0013 :=
    @g_fnlndifop
  have p0014 :=
    @g_ln1stfn
  have p0015 :=
    @g_ln1stfn
  have p0016 :=
    @g_fncovv (syn_c1st) (syn_c1st) p0014 p0015
  have p0017 :=
    @g_idex
  have p0018 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p0019 :=
    Nominal.mp p0017 p0018
  have p0020 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p0016 p0019
  have p0021 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p0022 :=
    Nominal.mp p0020 p0021
  have p0023 :=
    @g_inidm (syn_cvv)
  have p0024 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0023
  have p0025 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) p0022 p0024
  have p0026 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0013 p0025
  have p0027 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p0028 :=
    @g_fneq1i (syn_cvv) (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) p0027
  have p0029 :=
    @g_mpbir (syn_wfn (syn_chncodestrictfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv)) p0026 p0028
  have p0030 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p0012 p0029
  have p0031 :=
    @g_ln2ndfn
  have p0032 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0030 p0031
  have p0033 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)
  have p0034 :=
    Nominal.mp p0032 p0033
  have p0035 :=
    @g_inidm (syn_cvv)
  have p0036 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0035
  have p0037 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cvv)) p0034 p0036
  have p0038 :=
    @g_fncovv (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0011 p0037
  have p0039 :=
    (by simpa [syn_chncodepredfn] using (Nominal.classEqRefl (syn_chncodepredfn)))
  have p0040 :=
    @g_fneq1i (syn_cvv) (syn_chncodepredfn) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) p0039
  have p0041 :=
    @g_mpbir (syn_wfn (syn_chncodepredfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) (syn_cvv)) p0038 p0040
  have p0042 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c2nd) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_chncodepredfn) (syn_cvv)) p0010 p0041
  have p0043 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)
  have p0044 :=
    Nominal.mp p0042 p0043
  have p0045 :=
    @g_inidm (syn_cvv)
  have p0046 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0045
  have p0047 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cvv)) p0044 p0046
  have p0048 :=
    @g_fncovv (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0007 p0047
  have p0049 :=
    (by simpa [syn_chncodecarrierfn] using (Nominal.classEqRefl (syn_chncodecarrierfn)))
  have p0050 :=
    @g_fneq1i (syn_cvv) (syn_chncodecarrierfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) p0049
  have p0051 :=
    @g_mpbir (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) (syn_cvv)) p0048 p0050
  have p0052 :=
    @g_lninteropfn
  have p0053 :=
    @g_ln2ndfn
  have p0054 :=
    @g_ln1stfn
  have p0055 :=
    @g_fncovv (syn_c2nd) (syn_c1st) p0053 p0054
  have p0056 :=
    @g_lnimageopfn
  have p0057 :=
    @g_imageswapfn
  have p0058 :=
    @g_fnlndifop
  have p0059 :=
    @g_ln1stfn
  have p0060 :=
    @g_ln1stfn
  have p0061 :=
    @g_fncovv (syn_c1st) (syn_c1st) p0059 p0060
  have p0062 :=
    @g_idex
  have p0063 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p0064 :=
    Nominal.mp p0062 p0063
  have p0065 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p0061 p0064
  have p0066 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p0067 :=
    Nominal.mp p0065 p0066
  have p0068 :=
    @g_inidm (syn_cvv)
  have p0069 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0068
  have p0070 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) p0067 p0069
  have p0071 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0058 p0070
  have p0072 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p0073 :=
    @g_fneq1i (syn_cvv) (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) p0072
  have p0074 :=
    @g_mpbir (syn_wfn (syn_chncodestrictfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv)) p0071 p0073
  have p0075 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p0057 p0074
  have p0076 :=
    @g_ln2ndfn
  have p0077 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0075 p0076
  have p0078 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)
  have p0079 :=
    Nominal.mp p0077 p0078
  have p0080 :=
    @g_inidm (syn_cvv)
  have p0081 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0080
  have p0082 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cvv)) p0079 p0081
  have p0083 :=
    @g_fncovv (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0056 p0082
  have p0084 :=
    (by simpa [syn_chncodepredfn] using (Nominal.classEqRefl (syn_chncodepredfn)))
  have p0085 :=
    @g_fneq1i (syn_cvv) (syn_chncodepredfn) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) p0084
  have p0086 :=
    @g_mpbir (syn_wfn (syn_chncodepredfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) (syn_cvv)) p0083 p0085
  have p0087 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c2nd) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_chncodepredfn) (syn_cvv)) p0055 p0086
  have p0088 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)
  have p0089 :=
    Nominal.mp p0087 p0088
  have p0090 :=
    @g_inidm (syn_cvv)
  have p0091 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0090
  have p0092 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cvv)) p0089 p0091
  have p0093 :=
    @g_fncovv (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0052 p0092
  have p0094 :=
    (by simpa [syn_chncodecarrierfn] using (Nominal.classEqRefl (syn_chncodecarrierfn)))
  have p0095 :=
    @g_fneq1i (syn_cvv) (syn_chncodecarrierfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) p0094
  have p0096 :=
    @g_mpbir (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) (syn_cvv)) p0093 p0095
  have p0097 :=
    @g_pm3_2i (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) p0051 p0096
  have p0098 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_chncodecarrierfn) (syn_chncodecarrierfn)
  have p0099 :=
    Nominal.mp p0097 p0098
  have p0100 :=
    @g_inidm (syn_cvv)
  have p0101 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) p0100
  have p0102 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) (syn_cvv)) p0099 p0101
  have p0103 :=
    @g_fncovv (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) p0006 p0102
  have p0104 :=
    (by simpa [syn_chncodesquarefn] using (Nominal.classEqRefl (syn_chncodesquarefn)))
  have p0105 :=
    @g_fneq1i (syn_cvv) (syn_chncodesquarefn) (syn_ccom (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn))) p0104
  have p0106 :=
    @g_mpbir (syn_wfn (syn_chncodesquarefn) (syn_cvv)) (syn_wfn (syn_ccom (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn))) (syn_cvv)) p0103 p0105
  have p0107 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_chncodesquarefn) (syn_cvv)) p0005 p0106
  have p0108 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)
  have p0109 :=
    Nominal.mp p0107 p0108
  have p0110 :=
    @g_inidm (syn_cvv)
  have p0111 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) p0110
  have p0112 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) (syn_cvv)) p0109 p0111
  have p0113 :=
    @g_fncovv (syn_clninterop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) p0002 p0112
  have p0114 :=
    (by simpa [syn_chncoderelfn] using (Nominal.classEqRefl (syn_chncoderelfn)))
  have p0115 :=
    @g_fneq1i (syn_cvv) (syn_chncoderelfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn))) p0114
  have p0116 :=
    @g_mpbir (syn_wfn (syn_chncoderelfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn))) (syn_cvv)) p0113 p0115
  have p0117 :=
    @g_lninteropfn
  have p0118 :=
    @g_ln2ndfn
  have p0119 :=
    @g_ln1stfn
  have p0120 :=
    @g_fncovv (syn_c2nd) (syn_c1st) p0118 p0119
  have p0121 :=
    @g_lnimageopfn
  have p0122 :=
    @g_imageswapfn
  have p0123 :=
    @g_fnlndifop
  have p0124 :=
    @g_ln1stfn
  have p0125 :=
    @g_ln1stfn
  have p0126 :=
    @g_fncovv (syn_c1st) (syn_c1st) p0124 p0125
  have p0127 :=
    @g_idex
  have p0128 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p0129 :=
    Nominal.mp p0127 p0128
  have p0130 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p0126 p0129
  have p0131 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p0132 :=
    Nominal.mp p0130 p0131
  have p0133 :=
    @g_inidm (syn_cvv)
  have p0134 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0133
  have p0135 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) p0132 p0134
  have p0136 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0123 p0135
  have p0137 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p0138 :=
    @g_fneq1i (syn_cvv) (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) p0137
  have p0139 :=
    @g_mpbir (syn_wfn (syn_chncodestrictfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv)) p0136 p0138
  have p0140 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p0122 p0139
  have p0141 :=
    @g_ln2ndfn
  have p0142 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0140 p0141
  have p0143 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)
  have p0144 :=
    Nominal.mp p0142 p0143
  have p0145 :=
    @g_inidm (syn_cvv)
  have p0146 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0145
  have p0147 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cvv)) p0144 p0146
  have p0148 :=
    @g_fncovv (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0121 p0147
  have p0149 :=
    (by simpa [syn_chncodepredfn] using (Nominal.classEqRefl (syn_chncodepredfn)))
  have p0150 :=
    @g_fneq1i (syn_cvv) (syn_chncodepredfn) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) p0149
  have p0151 :=
    @g_mpbir (syn_wfn (syn_chncodepredfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) (syn_cvv)) p0148 p0150
  have p0152 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c2nd) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_chncodepredfn) (syn_cvv)) p0120 p0151
  have p0153 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)
  have p0154 :=
    Nominal.mp p0152 p0153
  have p0155 :=
    @g_inidm (syn_cvv)
  have p0156 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0155
  have p0157 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cvv)) p0154 p0156
  have p0158 :=
    @g_fncovv (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0117 p0157
  have p0159 :=
    (by simpa [syn_chncodecarrierfn] using (Nominal.classEqRefl (syn_chncodecarrierfn)))
  have p0160 :=
    @g_fneq1i (syn_cvv) (syn_chncodecarrierfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) p0159
  have p0161 :=
    @g_mpbir (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) (syn_cvv)) p0158 p0160
  have p0162 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p0163 :=
    @g_snex (.cv x)
  have p0164 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p0162 p0163
  have p0165 :=
    @g_fvtxpvv (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_chncoderelfn) (syn_chncodecarrierfn) p0116 p0161 p0164
  have p0166 :=
    (by simpa [syn_chncoderelfn] using (Nominal.classEqRefl (syn_chncoderelfn)))
  have p0167 :=
    @g_fveq1i (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_chncoderelfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn))) p0166
  have p0168 :=
    @g_ln1stfn
  have p0169 :=
    @g_ln1stfn
  have p0170 :=
    @g_fncovv (syn_c1st) (syn_c1st) p0168 p0169
  have p0171 :=
    @g_fncross
  have p0172 :=
    @g_lninteropfn
  have p0173 :=
    @g_ln2ndfn
  have p0174 :=
    @g_ln1stfn
  have p0175 :=
    @g_fncovv (syn_c2nd) (syn_c1st) p0173 p0174
  have p0176 :=
    @g_lnimageopfn
  have p0177 :=
    @g_imageswapfn
  have p0178 :=
    @g_fnlndifop
  have p0179 :=
    @g_ln1stfn
  have p0180 :=
    @g_ln1stfn
  have p0181 :=
    @g_fncovv (syn_c1st) (syn_c1st) p0179 p0180
  have p0182 :=
    @g_idex
  have p0183 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p0184 :=
    Nominal.mp p0182 p0183
  have p0185 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p0181 p0184
  have p0186 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p0187 :=
    Nominal.mp p0185 p0186
  have p0188 :=
    @g_inidm (syn_cvv)
  have p0189 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0188
  have p0190 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) p0187 p0189
  have p0191 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0178 p0190
  have p0192 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p0193 :=
    @g_fneq1i (syn_cvv) (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) p0192
  have p0194 :=
    @g_mpbir (syn_wfn (syn_chncodestrictfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv)) p0191 p0193
  have p0195 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p0177 p0194
  have p0196 :=
    @g_ln2ndfn
  have p0197 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0195 p0196
  have p0198 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)
  have p0199 :=
    Nominal.mp p0197 p0198
  have p0200 :=
    @g_inidm (syn_cvv)
  have p0201 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0200
  have p0202 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cvv)) p0199 p0201
  have p0203 :=
    @g_fncovv (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0176 p0202
  have p0204 :=
    (by simpa [syn_chncodepredfn] using (Nominal.classEqRefl (syn_chncodepredfn)))
  have p0205 :=
    @g_fneq1i (syn_cvv) (syn_chncodepredfn) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) p0204
  have p0206 :=
    @g_mpbir (syn_wfn (syn_chncodepredfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) (syn_cvv)) p0203 p0205
  have p0207 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c2nd) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_chncodepredfn) (syn_cvv)) p0175 p0206
  have p0208 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)
  have p0209 :=
    Nominal.mp p0207 p0208
  have p0210 :=
    @g_inidm (syn_cvv)
  have p0211 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0210
  have p0212 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cvv)) p0209 p0211
  have p0213 :=
    @g_fncovv (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0172 p0212
  have p0214 :=
    (by simpa [syn_chncodecarrierfn] using (Nominal.classEqRefl (syn_chncodecarrierfn)))
  have p0215 :=
    @g_fneq1i (syn_cvv) (syn_chncodecarrierfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) p0214
  have p0216 :=
    @g_mpbir (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) (syn_cvv)) p0213 p0215
  have p0217 :=
    @g_lninteropfn
  have p0218 :=
    @g_ln2ndfn
  have p0219 :=
    @g_ln1stfn
  have p0220 :=
    @g_fncovv (syn_c2nd) (syn_c1st) p0218 p0219
  have p0221 :=
    @g_lnimageopfn
  have p0222 :=
    @g_imageswapfn
  have p0223 :=
    @g_fnlndifop
  have p0224 :=
    @g_ln1stfn
  have p0225 :=
    @g_ln1stfn
  have p0226 :=
    @g_fncovv (syn_c1st) (syn_c1st) p0224 p0225
  have p0227 :=
    @g_idex
  have p0228 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p0229 :=
    Nominal.mp p0227 p0228
  have p0230 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p0226 p0229
  have p0231 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p0232 :=
    Nominal.mp p0230 p0231
  have p0233 :=
    @g_inidm (syn_cvv)
  have p0234 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0233
  have p0235 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) p0232 p0234
  have p0236 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0223 p0235
  have p0237 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p0238 :=
    @g_fneq1i (syn_cvv) (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) p0237
  have p0239 :=
    @g_mpbir (syn_wfn (syn_chncodestrictfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv)) p0236 p0238
  have p0240 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p0222 p0239
  have p0241 :=
    @g_ln2ndfn
  have p0242 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0240 p0241
  have p0243 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)
  have p0244 :=
    Nominal.mp p0242 p0243
  have p0245 :=
    @g_inidm (syn_cvv)
  have p0246 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0245
  have p0247 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cvv)) p0244 p0246
  have p0248 :=
    @g_fncovv (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0221 p0247
  have p0249 :=
    (by simpa [syn_chncodepredfn] using (Nominal.classEqRefl (syn_chncodepredfn)))
  have p0250 :=
    @g_fneq1i (syn_cvv) (syn_chncodepredfn) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) p0249
  have p0251 :=
    @g_mpbir (syn_wfn (syn_chncodepredfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) (syn_cvv)) p0248 p0250
  have p0252 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c2nd) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_chncodepredfn) (syn_cvv)) p0220 p0251
  have p0253 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)
  have p0254 :=
    Nominal.mp p0252 p0253
  have p0255 :=
    @g_inidm (syn_cvv)
  have p0256 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0255
  have p0257 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cvv)) p0254 p0256
  have p0258 :=
    @g_fncovv (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0217 p0257
  have p0259 :=
    (by simpa [syn_chncodecarrierfn] using (Nominal.classEqRefl (syn_chncodecarrierfn)))
  have p0260 :=
    @g_fneq1i (syn_cvv) (syn_chncodecarrierfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) p0259
  have p0261 :=
    @g_mpbir (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) (syn_cvv)) p0258 p0260
  have p0262 :=
    @g_pm3_2i (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) p0216 p0261
  have p0263 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_chncodecarrierfn) (syn_chncodecarrierfn)
  have p0264 :=
    Nominal.mp p0262 p0263
  have p0265 :=
    @g_inidm (syn_cvv)
  have p0266 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) p0265
  have p0267 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) (syn_cvv)) p0264 p0266
  have p0268 :=
    @g_fncovv (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) p0171 p0267
  have p0269 :=
    (by simpa [syn_chncodesquarefn] using (Nominal.classEqRefl (syn_chncodesquarefn)))
  have p0270 :=
    @g_fneq1i (syn_cvv) (syn_chncodesquarefn) (syn_ccom (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn))) p0269
  have p0271 :=
    @g_mpbir (syn_wfn (syn_chncodesquarefn) (syn_cvv)) (syn_wfn (syn_ccom (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn))) (syn_cvv)) p0268 p0270
  have p0272 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_chncodesquarefn) (syn_cvv)) p0170 p0271
  have p0273 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)
  have p0274 :=
    Nominal.mp p0272 p0273
  have p0275 :=
    @g_inidm (syn_cvv)
  have p0276 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) p0275
  have p0277 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) (syn_cvv)) p0274 p0276
  have p0278 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p0279 :=
    @g_snex (.cv x)
  have p0280 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p0278 p0279
  have p0281 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) (syn_cvv)) (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cvv)) p0277 p0280
  have p0282 :=
    @g_fvco2 (syn_cvv) (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_clninterop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn))
  have p0283 :=
    Nominal.mp p0281 p0282
  have p0284 :=
    @g_ln1stfn
  have p0285 :=
    @g_ln1stfn
  have p0286 :=
    @g_fncovv (syn_c1st) (syn_c1st) p0284 p0285
  have p0287 :=
    @g_fncross
  have p0288 :=
    @g_lninteropfn
  have p0289 :=
    @g_ln2ndfn
  have p0290 :=
    @g_ln1stfn
  have p0291 :=
    @g_fncovv (syn_c2nd) (syn_c1st) p0289 p0290
  have p0292 :=
    @g_lnimageopfn
  have p0293 :=
    @g_imageswapfn
  have p0294 :=
    @g_fnlndifop
  have p0295 :=
    @g_ln1stfn
  have p0296 :=
    @g_ln1stfn
  have p0297 :=
    @g_fncovv (syn_c1st) (syn_c1st) p0295 p0296
  have p0298 :=
    @g_idex
  have p0299 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p0300 :=
    Nominal.mp p0298 p0299
  have p0301 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p0297 p0300
  have p0302 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p0303 :=
    Nominal.mp p0301 p0302
  have p0304 :=
    @g_inidm (syn_cvv)
  have p0305 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0304
  have p0306 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) p0303 p0305
  have p0307 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0294 p0306
  have p0308 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p0309 :=
    @g_fneq1i (syn_cvv) (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) p0308
  have p0310 :=
    @g_mpbir (syn_wfn (syn_chncodestrictfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv)) p0307 p0309
  have p0311 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p0293 p0310
  have p0312 :=
    @g_ln2ndfn
  have p0313 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0311 p0312
  have p0314 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)
  have p0315 :=
    Nominal.mp p0313 p0314
  have p0316 :=
    @g_inidm (syn_cvv)
  have p0317 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0316
  have p0318 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cvv)) p0315 p0317
  have p0319 :=
    @g_fncovv (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0292 p0318
  have p0320 :=
    (by simpa [syn_chncodepredfn] using (Nominal.classEqRefl (syn_chncodepredfn)))
  have p0321 :=
    @g_fneq1i (syn_cvv) (syn_chncodepredfn) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) p0320
  have p0322 :=
    @g_mpbir (syn_wfn (syn_chncodepredfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) (syn_cvv)) p0319 p0321
  have p0323 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c2nd) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_chncodepredfn) (syn_cvv)) p0291 p0322
  have p0324 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)
  have p0325 :=
    Nominal.mp p0323 p0324
  have p0326 :=
    @g_inidm (syn_cvv)
  have p0327 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0326
  have p0328 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cvv)) p0325 p0327
  have p0329 :=
    @g_fncovv (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0288 p0328
  have p0330 :=
    (by simpa [syn_chncodecarrierfn] using (Nominal.classEqRefl (syn_chncodecarrierfn)))
  have p0331 :=
    @g_fneq1i (syn_cvv) (syn_chncodecarrierfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) p0330
  have p0332 :=
    @g_mpbir (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) (syn_cvv)) p0329 p0331
  have p0333 :=
    @g_lninteropfn
  have p0334 :=
    @g_ln2ndfn
  have p0335 :=
    @g_ln1stfn
  have p0336 :=
    @g_fncovv (syn_c2nd) (syn_c1st) p0334 p0335
  have p0337 :=
    @g_lnimageopfn
  have p0338 :=
    @g_imageswapfn
  have p0339 :=
    @g_fnlndifop
  have p0340 :=
    @g_ln1stfn
  have p0341 :=
    @g_ln1stfn
  have p0342 :=
    @g_fncovv (syn_c1st) (syn_c1st) p0340 p0341
  have p0343 :=
    @g_idex
  have p0344 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p0345 :=
    Nominal.mp p0343 p0344
  have p0346 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p0342 p0345
  have p0347 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p0348 :=
    Nominal.mp p0346 p0347
  have p0349 :=
    @g_inidm (syn_cvv)
  have p0350 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0349
  have p0351 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) p0348 p0350
  have p0352 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0339 p0351
  have p0353 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p0354 :=
    @g_fneq1i (syn_cvv) (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) p0353
  have p0355 :=
    @g_mpbir (syn_wfn (syn_chncodestrictfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv)) p0352 p0354
  have p0356 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p0338 p0355
  have p0357 :=
    @g_ln2ndfn
  have p0358 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0356 p0357
  have p0359 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)
  have p0360 :=
    Nominal.mp p0358 p0359
  have p0361 :=
    @g_inidm (syn_cvv)
  have p0362 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0361
  have p0363 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cvv)) p0360 p0362
  have p0364 :=
    @g_fncovv (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0337 p0363
  have p0365 :=
    (by simpa [syn_chncodepredfn] using (Nominal.classEqRefl (syn_chncodepredfn)))
  have p0366 :=
    @g_fneq1i (syn_cvv) (syn_chncodepredfn) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) p0365
  have p0367 :=
    @g_mpbir (syn_wfn (syn_chncodepredfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) (syn_cvv)) p0364 p0366
  have p0368 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c2nd) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_chncodepredfn) (syn_cvv)) p0336 p0367
  have p0369 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)
  have p0370 :=
    Nominal.mp p0368 p0369
  have p0371 :=
    @g_inidm (syn_cvv)
  have p0372 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0371
  have p0373 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cvv)) p0370 p0372
  have p0374 :=
    @g_fncovv (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0333 p0373
  have p0375 :=
    (by simpa [syn_chncodecarrierfn] using (Nominal.classEqRefl (syn_chncodecarrierfn)))
  have p0376 :=
    @g_fneq1i (syn_cvv) (syn_chncodecarrierfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) p0375
  have p0377 :=
    @g_mpbir (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) (syn_cvv)) p0374 p0376
  have p0378 :=
    @g_pm3_2i (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) p0332 p0377
  have p0379 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_chncodecarrierfn) (syn_chncodecarrierfn)
  have p0380 :=
    Nominal.mp p0378 p0379
  have p0381 :=
    @g_inidm (syn_cvv)
  have p0382 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) p0381
  have p0383 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) (syn_cvv)) p0380 p0382
  have p0384 :=
    @g_fncovv (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) p0287 p0383
  have p0385 :=
    (by simpa [syn_chncodesquarefn] using (Nominal.classEqRefl (syn_chncodesquarefn)))
  have p0386 :=
    @g_fneq1i (syn_cvv) (syn_chncodesquarefn) (syn_ccom (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn))) p0385
  have p0387 :=
    @g_mpbir (syn_wfn (syn_chncodesquarefn) (syn_cvv)) (syn_wfn (syn_ccom (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn))) (syn_cvv)) p0384 p0386
  have p0388 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p0389 :=
    @g_snex (.cv x)
  have p0390 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p0388 p0389
  have p0391 :=
    @g_fvtxpvv (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn) p0286 p0387 p0390
  have p0392 :=
    @g_ln1stfn
  have p0393 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p0394 :=
    @g_snex (.cv x)
  have p0395 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p0393 p0394
  have p0396 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cvv)) p0392 p0395
  have p0397 :=
    @g_fvco2 (syn_cvv) (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_c1st) (syn_c1st)
  have p0398 :=
    Nominal.mp p0396 p0397
  have p0399 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p0400 :=
    @g_snex (.cv x)
  have p0401 :=
    @g_opfv1st (syn_cop R D) (syn_csn (.cv x)) p0399 p0400
  have p0402 :=
    @g_fveq2i (syn_cfv (syn_c1st) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop R D) (syn_c1st) p0401
  have p0403 :=
    @g_opfv1st R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p0404 :=
    @g_eqtri (syn_cfv (syn_c1st) (syn_cfv (syn_c1st) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cfv (syn_c1st) (syn_cop R D)) R p0402 p0403
  have p0405 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_c1st) (syn_c1st)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_c1st) (syn_cfv (syn_c1st) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) R p0398 p0404
  have p0406 :=
    (by simpa [syn_chncodesquarefn] using (Nominal.classEqRefl (syn_chncodesquarefn)))
  have p0407 :=
    @g_fveq1i (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_chncodesquarefn) (syn_ccom (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn))) p0406
  have p0408 :=
    @g_lninteropfn
  have p0409 :=
    @g_ln2ndfn
  have p0410 :=
    @g_ln1stfn
  have p0411 :=
    @g_fncovv (syn_c2nd) (syn_c1st) p0409 p0410
  have p0412 :=
    @g_lnimageopfn
  have p0413 :=
    @g_imageswapfn
  have p0414 :=
    @g_fnlndifop
  have p0415 :=
    @g_ln1stfn
  have p0416 :=
    @g_ln1stfn
  have p0417 :=
    @g_fncovv (syn_c1st) (syn_c1st) p0415 p0416
  have p0418 :=
    @g_idex
  have p0419 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p0420 :=
    Nominal.mp p0418 p0419
  have p0421 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p0417 p0420
  have p0422 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p0423 :=
    Nominal.mp p0421 p0422
  have p0424 :=
    @g_inidm (syn_cvv)
  have p0425 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0424
  have p0426 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) p0423 p0425
  have p0427 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0414 p0426
  have p0428 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p0429 :=
    @g_fneq1i (syn_cvv) (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) p0428
  have p0430 :=
    @g_mpbir (syn_wfn (syn_chncodestrictfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv)) p0427 p0429
  have p0431 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p0413 p0430
  have p0432 :=
    @g_ln2ndfn
  have p0433 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0431 p0432
  have p0434 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)
  have p0435 :=
    Nominal.mp p0433 p0434
  have p0436 :=
    @g_inidm (syn_cvv)
  have p0437 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0436
  have p0438 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cvv)) p0435 p0437
  have p0439 :=
    @g_fncovv (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0412 p0438
  have p0440 :=
    (by simpa [syn_chncodepredfn] using (Nominal.classEqRefl (syn_chncodepredfn)))
  have p0441 :=
    @g_fneq1i (syn_cvv) (syn_chncodepredfn) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) p0440
  have p0442 :=
    @g_mpbir (syn_wfn (syn_chncodepredfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) (syn_cvv)) p0439 p0441
  have p0443 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c2nd) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_chncodepredfn) (syn_cvv)) p0411 p0442
  have p0444 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)
  have p0445 :=
    Nominal.mp p0443 p0444
  have p0446 :=
    @g_inidm (syn_cvv)
  have p0447 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0446
  have p0448 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cvv)) p0445 p0447
  have p0449 :=
    @g_fncovv (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0408 p0448
  have p0450 :=
    (by simpa [syn_chncodecarrierfn] using (Nominal.classEqRefl (syn_chncodecarrierfn)))
  have p0451 :=
    @g_fneq1i (syn_cvv) (syn_chncodecarrierfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) p0450
  have p0452 :=
    @g_mpbir (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) (syn_cvv)) p0449 p0451
  have p0453 :=
    @g_lninteropfn
  have p0454 :=
    @g_ln2ndfn
  have p0455 :=
    @g_ln1stfn
  have p0456 :=
    @g_fncovv (syn_c2nd) (syn_c1st) p0454 p0455
  have p0457 :=
    @g_lnimageopfn
  have p0458 :=
    @g_imageswapfn
  have p0459 :=
    @g_fnlndifop
  have p0460 :=
    @g_ln1stfn
  have p0461 :=
    @g_ln1stfn
  have p0462 :=
    @g_fncovv (syn_c1st) (syn_c1st) p0460 p0461
  have p0463 :=
    @g_idex
  have p0464 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p0465 :=
    Nominal.mp p0463 p0464
  have p0466 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p0462 p0465
  have p0467 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p0468 :=
    Nominal.mp p0466 p0467
  have p0469 :=
    @g_inidm (syn_cvv)
  have p0470 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0469
  have p0471 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) p0468 p0470
  have p0472 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0459 p0471
  have p0473 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p0474 :=
    @g_fneq1i (syn_cvv) (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) p0473
  have p0475 :=
    @g_mpbir (syn_wfn (syn_chncodestrictfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv)) p0472 p0474
  have p0476 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p0458 p0475
  have p0477 :=
    @g_ln2ndfn
  have p0478 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0476 p0477
  have p0479 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)
  have p0480 :=
    Nominal.mp p0478 p0479
  have p0481 :=
    @g_inidm (syn_cvv)
  have p0482 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0481
  have p0483 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cvv)) p0480 p0482
  have p0484 :=
    @g_fncovv (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0457 p0483
  have p0485 :=
    (by simpa [syn_chncodepredfn] using (Nominal.classEqRefl (syn_chncodepredfn)))
  have p0486 :=
    @g_fneq1i (syn_cvv) (syn_chncodepredfn) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) p0485
  have p0487 :=
    @g_mpbir (syn_wfn (syn_chncodepredfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) (syn_cvv)) p0484 p0486
  have p0488 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c2nd) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_chncodepredfn) (syn_cvv)) p0456 p0487
  have p0489 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)
  have p0490 :=
    Nominal.mp p0488 p0489
  have p0491 :=
    @g_inidm (syn_cvv)
  have p0492 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0491
  have p0493 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cvv)) p0490 p0492
  have p0494 :=
    @g_fncovv (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0453 p0493
  have p0495 :=
    (by simpa [syn_chncodecarrierfn] using (Nominal.classEqRefl (syn_chncodecarrierfn)))
  have p0496 :=
    @g_fneq1i (syn_cvv) (syn_chncodecarrierfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) p0495
  have p0497 :=
    @g_mpbir (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) (syn_cvv)) p0494 p0496
  have p0498 :=
    @g_pm3_2i (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) p0452 p0497
  have p0499 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_chncodecarrierfn) (syn_chncodecarrierfn)
  have p0500 :=
    Nominal.mp p0498 p0499
  have p0501 :=
    @g_inidm (syn_cvv)
  have p0502 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) p0501
  have p0503 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) (syn_cvv)) p0500 p0502
  have p0504 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p0505 :=
    @g_snex (.cv x)
  have p0506 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p0504 p0505
  have p0507 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) (syn_cvv)) (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cvv)) p0503 p0506
  have p0508 :=
    @g_fvco2 (syn_cvv) (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn))
  have p0509 :=
    Nominal.mp p0507 p0508
  have p0510 :=
    @g_lninteropfn
  have p0511 :=
    @g_ln2ndfn
  have p0512 :=
    @g_ln1stfn
  have p0513 :=
    @g_fncovv (syn_c2nd) (syn_c1st) p0511 p0512
  have p0514 :=
    @g_lnimageopfn
  have p0515 :=
    @g_imageswapfn
  have p0516 :=
    @g_fnlndifop
  have p0517 :=
    @g_ln1stfn
  have p0518 :=
    @g_ln1stfn
  have p0519 :=
    @g_fncovv (syn_c1st) (syn_c1st) p0517 p0518
  have p0520 :=
    @g_idex
  have p0521 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p0522 :=
    Nominal.mp p0520 p0521
  have p0523 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p0519 p0522
  have p0524 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p0525 :=
    Nominal.mp p0523 p0524
  have p0526 :=
    @g_inidm (syn_cvv)
  have p0527 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0526
  have p0528 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) p0525 p0527
  have p0529 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0516 p0528
  have p0530 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p0531 :=
    @g_fneq1i (syn_cvv) (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) p0530
  have p0532 :=
    @g_mpbir (syn_wfn (syn_chncodestrictfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv)) p0529 p0531
  have p0533 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p0515 p0532
  have p0534 :=
    @g_ln2ndfn
  have p0535 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0533 p0534
  have p0536 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)
  have p0537 :=
    Nominal.mp p0535 p0536
  have p0538 :=
    @g_inidm (syn_cvv)
  have p0539 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0538
  have p0540 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cvv)) p0537 p0539
  have p0541 :=
    @g_fncovv (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0514 p0540
  have p0542 :=
    (by simpa [syn_chncodepredfn] using (Nominal.classEqRefl (syn_chncodepredfn)))
  have p0543 :=
    @g_fneq1i (syn_cvv) (syn_chncodepredfn) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) p0542
  have p0544 :=
    @g_mpbir (syn_wfn (syn_chncodepredfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) (syn_cvv)) p0541 p0543
  have p0545 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c2nd) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_chncodepredfn) (syn_cvv)) p0513 p0544
  have p0546 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)
  have p0547 :=
    Nominal.mp p0545 p0546
  have p0548 :=
    @g_inidm (syn_cvv)
  have p0549 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0548
  have p0550 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cvv)) p0547 p0549
  have p0551 :=
    @g_fncovv (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0510 p0550
  have p0552 :=
    (by simpa [syn_chncodecarrierfn] using (Nominal.classEqRefl (syn_chncodecarrierfn)))
  have p0553 :=
    @g_fneq1i (syn_cvv) (syn_chncodecarrierfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) p0552
  have p0554 :=
    @g_mpbir (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) (syn_cvv)) p0551 p0553
  have p0555 :=
    @g_lninteropfn
  have p0556 :=
    @g_ln2ndfn
  have p0557 :=
    @g_ln1stfn
  have p0558 :=
    @g_fncovv (syn_c2nd) (syn_c1st) p0556 p0557
  have p0559 :=
    @g_lnimageopfn
  have p0560 :=
    @g_imageswapfn
  have p0561 :=
    @g_fnlndifop
  have p0562 :=
    @g_ln1stfn
  have p0563 :=
    @g_ln1stfn
  have p0564 :=
    @g_fncovv (syn_c1st) (syn_c1st) p0562 p0563
  have p0565 :=
    @g_idex
  have p0566 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p0567 :=
    Nominal.mp p0565 p0566
  have p0568 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p0564 p0567
  have p0569 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p0570 :=
    Nominal.mp p0568 p0569
  have p0571 :=
    @g_inidm (syn_cvv)
  have p0572 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0571
  have p0573 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) p0570 p0572
  have p0574 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0561 p0573
  have p0575 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p0576 :=
    @g_fneq1i (syn_cvv) (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) p0575
  have p0577 :=
    @g_mpbir (syn_wfn (syn_chncodestrictfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv)) p0574 p0576
  have p0578 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p0560 p0577
  have p0579 :=
    @g_ln2ndfn
  have p0580 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0578 p0579
  have p0581 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)
  have p0582 :=
    Nominal.mp p0580 p0581
  have p0583 :=
    @g_inidm (syn_cvv)
  have p0584 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0583
  have p0585 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cvv)) p0582 p0584
  have p0586 :=
    @g_fncovv (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0559 p0585
  have p0587 :=
    (by simpa [syn_chncodepredfn] using (Nominal.classEqRefl (syn_chncodepredfn)))
  have p0588 :=
    @g_fneq1i (syn_cvv) (syn_chncodepredfn) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) p0587
  have p0589 :=
    @g_mpbir (syn_wfn (syn_chncodepredfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) (syn_cvv)) p0586 p0588
  have p0590 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c2nd) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_chncodepredfn) (syn_cvv)) p0558 p0589
  have p0591 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)
  have p0592 :=
    Nominal.mp p0590 p0591
  have p0593 :=
    @g_inidm (syn_cvv)
  have p0594 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0593
  have p0595 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cvv)) p0592 p0594
  have p0596 :=
    @g_fncovv (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0555 p0595
  have p0597 :=
    (by simpa [syn_chncodecarrierfn] using (Nominal.classEqRefl (syn_chncodecarrierfn)))
  have p0598 :=
    @g_fneq1i (syn_cvv) (syn_chncodecarrierfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) p0597
  have p0599 :=
    @g_mpbir (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) (syn_cvv)) p0596 p0598
  have p0600 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p0601 :=
    @g_snex (.cv x)
  have p0602 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p0600 p0601
  have p0603 :=
    @g_fvtxpvv (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_chncodecarrierfn) (syn_chncodecarrierfn) p0554 p0599 p0602
  have p0604 :=
    (by simpa [syn_chncodecarrierfn] using (Nominal.classEqRefl (syn_chncodecarrierfn)))
  have p0605 :=
    @g_fveq1i (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_chncodecarrierfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) p0604
  have p0606 :=
    @g_ln2ndfn
  have p0607 :=
    @g_ln1stfn
  have p0608 :=
    @g_fncovv (syn_c2nd) (syn_c1st) p0606 p0607
  have p0609 :=
    @g_lnimageopfn
  have p0610 :=
    @g_imageswapfn
  have p0611 :=
    @g_fnlndifop
  have p0612 :=
    @g_ln1stfn
  have p0613 :=
    @g_ln1stfn
  have p0614 :=
    @g_fncovv (syn_c1st) (syn_c1st) p0612 p0613
  have p0615 :=
    @g_idex
  have p0616 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p0617 :=
    Nominal.mp p0615 p0616
  have p0618 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p0614 p0617
  have p0619 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p0620 :=
    Nominal.mp p0618 p0619
  have p0621 :=
    @g_inidm (syn_cvv)
  have p0622 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0621
  have p0623 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) p0620 p0622
  have p0624 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0611 p0623
  have p0625 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p0626 :=
    @g_fneq1i (syn_cvv) (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) p0625
  have p0627 :=
    @g_mpbir (syn_wfn (syn_chncodestrictfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv)) p0624 p0626
  have p0628 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p0610 p0627
  have p0629 :=
    @g_ln2ndfn
  have p0630 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0628 p0629
  have p0631 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)
  have p0632 :=
    Nominal.mp p0630 p0631
  have p0633 :=
    @g_inidm (syn_cvv)
  have p0634 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0633
  have p0635 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cvv)) p0632 p0634
  have p0636 :=
    @g_fncovv (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0609 p0635
  have p0637 :=
    (by simpa [syn_chncodepredfn] using (Nominal.classEqRefl (syn_chncodepredfn)))
  have p0638 :=
    @g_fneq1i (syn_cvv) (syn_chncodepredfn) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) p0637
  have p0639 :=
    @g_mpbir (syn_wfn (syn_chncodepredfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) (syn_cvv)) p0636 p0638
  have p0640 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c2nd) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_chncodepredfn) (syn_cvv)) p0608 p0639
  have p0641 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)
  have p0642 :=
    Nominal.mp p0640 p0641
  have p0643 :=
    @g_inidm (syn_cvv)
  have p0644 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0643
  have p0645 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cvv)) p0642 p0644
  have p0646 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p0647 :=
    @g_snex (.cv x)
  have p0648 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p0646 p0647
  have p0649 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cvv)) (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cvv)) p0645 p0648
  have p0650 :=
    @g_fvco2 (syn_cvv) (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))
  have p0651 :=
    Nominal.mp p0649 p0650
  have p0652 :=
    @g_ln2ndfn
  have p0653 :=
    @g_ln1stfn
  have p0654 :=
    @g_fncovv (syn_c2nd) (syn_c1st) p0652 p0653
  have p0655 :=
    @g_lnimageopfn
  have p0656 :=
    @g_imageswapfn
  have p0657 :=
    @g_fnlndifop
  have p0658 :=
    @g_ln1stfn
  have p0659 :=
    @g_ln1stfn
  have p0660 :=
    @g_fncovv (syn_c1st) (syn_c1st) p0658 p0659
  have p0661 :=
    @g_idex
  have p0662 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p0663 :=
    Nominal.mp p0661 p0662
  have p0664 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p0660 p0663
  have p0665 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p0666 :=
    Nominal.mp p0664 p0665
  have p0667 :=
    @g_inidm (syn_cvv)
  have p0668 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0667
  have p0669 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) p0666 p0668
  have p0670 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0657 p0669
  have p0671 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p0672 :=
    @g_fneq1i (syn_cvv) (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) p0671
  have p0673 :=
    @g_mpbir (syn_wfn (syn_chncodestrictfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv)) p0670 p0672
  have p0674 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p0656 p0673
  have p0675 :=
    @g_ln2ndfn
  have p0676 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0674 p0675
  have p0677 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)
  have p0678 :=
    Nominal.mp p0676 p0677
  have p0679 :=
    @g_inidm (syn_cvv)
  have p0680 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0679
  have p0681 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cvv)) p0678 p0680
  have p0682 :=
    @g_fncovv (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0655 p0681
  have p0683 :=
    (by simpa [syn_chncodepredfn] using (Nominal.classEqRefl (syn_chncodepredfn)))
  have p0684 :=
    @g_fneq1i (syn_cvv) (syn_chncodepredfn) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) p0683
  have p0685 :=
    @g_mpbir (syn_wfn (syn_chncodepredfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) (syn_cvv)) p0682 p0684
  have p0686 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p0687 :=
    @g_snex (.cv x)
  have p0688 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p0686 p0687
  have p0689 :=
    @g_fvtxpvv (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn) p0654 p0685 p0688
  have p0690 :=
    @g_ln1stfn
  have p0691 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p0692 :=
    @g_snex (.cv x)
  have p0693 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p0691 p0692
  have p0694 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cvv)) p0690 p0693
  have p0695 :=
    @g_fvco2 (syn_cvv) (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_c2nd) (syn_c1st)
  have p0696 :=
    Nominal.mp p0694 p0695
  have p0697 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p0698 :=
    @g_snex (.cv x)
  have p0699 :=
    @g_opfv1st (syn_cop R D) (syn_csn (.cv x)) p0697 p0698
  have p0700 :=
    @g_fveq2i (syn_cfv (syn_c1st) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop R D) (syn_c2nd) p0699
  have p0701 :=
    @g_opfv2nd R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p0702 :=
    @g_eqtri (syn_cfv (syn_c2nd) (syn_cfv (syn_c1st) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cfv (syn_c2nd) (syn_cop R D)) D p0700 p0701
  have p0703 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_c2nd) (syn_c1st)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_c2nd) (syn_cfv (syn_c1st) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) D p0696 p0702
  have p0704 :=
    (by simpa [syn_chncodepredfn] using (Nominal.classEqRefl (syn_chncodepredfn)))
  have p0705 :=
    @g_fveq1i (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_chncodepredfn) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) p0704
  have p0706 :=
    @g_imageswapfn
  have p0707 :=
    @g_fnlndifop
  have p0708 :=
    @g_ln1stfn
  have p0709 :=
    @g_ln1stfn
  have p0710 :=
    @g_fncovv (syn_c1st) (syn_c1st) p0708 p0709
  have p0711 :=
    @g_idex
  have p0712 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p0713 :=
    Nominal.mp p0711 p0712
  have p0714 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p0710 p0713
  have p0715 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p0716 :=
    Nominal.mp p0714 p0715
  have p0717 :=
    @g_inidm (syn_cvv)
  have p0718 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0717
  have p0719 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) p0716 p0718
  have p0720 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0707 p0719
  have p0721 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p0722 :=
    @g_fneq1i (syn_cvv) (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) p0721
  have p0723 :=
    @g_mpbir (syn_wfn (syn_chncodestrictfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv)) p0720 p0722
  have p0724 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p0706 p0723
  have p0725 :=
    @g_ln2ndfn
  have p0726 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0724 p0725
  have p0727 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)
  have p0728 :=
    Nominal.mp p0726 p0727
  have p0729 :=
    @g_inidm (syn_cvv)
  have p0730 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0729
  have p0731 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cvv)) p0728 p0730
  have p0732 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p0733 :=
    @g_snex (.cv x)
  have p0734 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p0732 p0733
  have p0735 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cvv)) (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cvv)) p0731 p0734
  have p0736 :=
    @g_fvco2 (syn_cvv) (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))
  have p0737 :=
    Nominal.mp p0735 p0736
  have p0738 :=
    @g_imageswapfn
  have p0739 :=
    @g_fnlndifop
  have p0740 :=
    @g_ln1stfn
  have p0741 :=
    @g_ln1stfn
  have p0742 :=
    @g_fncovv (syn_c1st) (syn_c1st) p0740 p0741
  have p0743 :=
    @g_idex
  have p0744 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p0745 :=
    Nominal.mp p0743 p0744
  have p0746 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p0742 p0745
  have p0747 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p0748 :=
    Nominal.mp p0746 p0747
  have p0749 :=
    @g_inidm (syn_cvv)
  have p0750 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0749
  have p0751 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) p0748 p0750
  have p0752 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0739 p0751
  have p0753 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p0754 :=
    @g_fneq1i (syn_cvv) (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) p0753
  have p0755 :=
    @g_mpbir (syn_wfn (syn_chncodestrictfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv)) p0752 p0754
  have p0756 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p0738 p0755
  have p0757 :=
    @g_ln2ndfn
  have p0758 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p0759 :=
    @g_snex (.cv x)
  have p0760 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p0758 p0759
  have p0761 :=
    @g_fvtxpvv (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd) p0756 p0757 p0760
  have p0762 :=
    @g_fnlndifop
  have p0763 :=
    @g_ln1stfn
  have p0764 :=
    @g_ln1stfn
  have p0765 :=
    @g_fncovv (syn_c1st) (syn_c1st) p0763 p0764
  have p0766 :=
    @g_idex
  have p0767 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p0768 :=
    Nominal.mp p0766 p0767
  have p0769 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p0765 p0768
  have p0770 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p0771 :=
    Nominal.mp p0769 p0770
  have p0772 :=
    @g_inidm (syn_cvv)
  have p0773 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0772
  have p0774 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) p0771 p0773
  have p0775 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0762 p0774
  have p0776 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p0777 :=
    @g_fneq1i (syn_cvv) (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) p0776
  have p0778 :=
    @g_mpbir (syn_wfn (syn_chncodestrictfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv)) p0775 p0777
  have p0779 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p0780 :=
    @g_snex (.cv x)
  have p0781 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p0779 p0780
  have p0782 :=
    @g_pm3_2i (syn_wfn (syn_chncodestrictfn) (syn_cvv)) (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cvv)) p0778 p0781
  have p0783 :=
    @g_fvco2 (syn_cvv) (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cimage (syn_cswap)) (syn_chncodestrictfn)
  have p0784 :=
    Nominal.mp p0782 p0783
  have p0785 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p0786 :=
    @g_fveq1i (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) p0785
  have p0787 :=
    @g_ln1stfn
  have p0788 :=
    @g_ln1stfn
  have p0789 :=
    @g_fncovv (syn_c1st) (syn_c1st) p0787 p0788
  have p0790 :=
    @g_idex
  have p0791 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p0792 :=
    Nominal.mp p0790 p0791
  have p0793 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p0789 p0792
  have p0794 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p0795 :=
    Nominal.mp p0793 p0794
  have p0796 :=
    @g_inidm (syn_cvv)
  have p0797 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0796
  have p0798 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) p0795 p0797
  have p0799 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p0800 :=
    @g_snex (.cv x)
  have p0801 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p0799 p0800
  have p0802 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cvv)) p0798 p0801
  have p0803 :=
    @g_fvco2 (syn_cvv) (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))
  have p0804 :=
    Nominal.mp p0802 p0803
  have p0805 :=
    @g_ln1stfn
  have p0806 :=
    @g_ln1stfn
  have p0807 :=
    @g_fncovv (syn_c1st) (syn_c1st) p0805 p0806
  have p0808 :=
    @g_idex
  have p0809 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p0810 :=
    Nominal.mp p0808 p0809
  have p0811 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p0812 :=
    @g_snex (.cv x)
  have p0813 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p0811 p0812
  have p0814 :=
    @g_fvtxpvv (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))) p0807 p0810 p0813
  have p0815 :=
    @g_ln1stfn
  have p0816 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p0817 :=
    @g_snex (.cv x)
  have p0818 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p0816 p0817
  have p0819 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cvv)) p0815 p0818
  have p0820 :=
    @g_fvco2 (syn_cvv) (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_c1st) (syn_c1st)
  have p0821 :=
    Nominal.mp p0819 p0820
  have p0822 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p0823 :=
    @g_snex (.cv x)
  have p0824 :=
    @g_opfv1st (syn_cop R D) (syn_csn (.cv x)) p0822 p0823
  have p0825 :=
    @g_fveq2i (syn_cfv (syn_c1st) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop R D) (syn_c1st) p0824
  have p0826 :=
    @g_opfv1st R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p0827 :=
    @g_eqtri (syn_cfv (syn_c1st) (syn_cfv (syn_c1st) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cfv (syn_c1st) (syn_cop R D)) R p0825 p0826
  have p0828 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_c1st) (syn_c1st)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_c1st) (syn_cfv (syn_c1st) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) R p0821 p0827
  have p0829 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p0830 :=
    @g_snex (.cv x)
  have p0831 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p0829 p0830
  have p0832 :=
    @g_idex
  have p0833 :=
    @g_fvconst2 (syn_cvv) (syn_cid) (syn_cop (syn_cop R D) (syn_csn (.cv x))) p0832
  have p0834 :=
    Nominal.mp p0831 p0833
  have p0835 :=
    @g_opeq12i (syn_cfv (syn_ccom (syn_c1st) (syn_c1st)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) R (syn_cfv (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cid) p0828 p0834
  have p0836 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop (syn_cfv (syn_ccom (syn_c1st) (syn_c1st)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cop R (syn_cid)) p0814 p0835
  have p0837 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop R (syn_cid)) (syn_clndifop) p0836
  have p0838 :=
    (by simpa [syn_co] using (Nominal.classEqRefl (syn_co R (syn_clndifop) (syn_cid))))
  have p0839 :=
    @g_eqcomi (syn_co R (syn_clndifop) (syn_cid)) (syn_cfv (syn_clndifop) (syn_cop R (syn_cid))) p0838
  have p0840 :=
    @g_idex
  have p0841 :=
    @g_pm3_2i (.classMem R (syn_cvv)) (.classMem (syn_cid) (syn_cvv)) hyp_hncodecutfnval_1 p0840
  have p0842 :=
    @g_lndifopvalg R (syn_cid) (syn_cvv) (syn_cvv)
  have p0843 :=
    Nominal.mp p0841 p0842
  have p0844 :=
    @g_eqtri (syn_cfv (syn_clndifop) (syn_cop R (syn_cid))) (syn_co R (syn_clndifop) (syn_cid)) (syn_cdif R (syn_cid)) p0839 p0843
  have p0845 :=
    @g_eqtri (syn_cfv (syn_clndifop) (syn_cfv (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cfv (syn_clndifop) (syn_cop R (syn_cid))) (syn_cdif R (syn_cid)) p0837 p0844
  have p0846 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_clndifop) (syn_cfv (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cdif R (syn_cid)) p0804 p0845
  have p0847 :=
    @g_eqtri (syn_cfv (syn_chncodestrictfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cdif R (syn_cid)) p0786 p0846
  have p0848 :=
    @g_fveq2i (syn_cfv (syn_chncodestrictfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cdif R (syn_cid)) (syn_cimage (syn_cswap)) p0847
  have p0849 :=
    @g_idex
  have p0850 :=
    @g_difex R (syn_cid) hyp_hncodecutfnval_1 p0849
  have p0851 :=
    @g_wppimageswapfv (syn_cdif R (syn_cid)) p0850
  have p0852 :=
    @g_eqtri (syn_cfv (syn_cimage (syn_cswap)) (syn_cfv (syn_chncodestrictfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cfv (syn_cimage (syn_cswap)) (syn_cdif R (syn_cid))) (syn_ccnv (syn_cdif R (syn_cid))) p0848 p0851
  have p0853 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_cimage (syn_cswap)) (syn_cfv (syn_chncodestrictfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_ccnv (syn_cdif R (syn_cid))) p0784 p0852
  have p0854 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p0855 :=
    @g_snex (.cv x)
  have p0856 :=
    @g_opfv2nd (syn_cop R D) (syn_csn (.cv x)) p0854 p0855
  have p0857 :=
    @g_opeq12i (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_ccnv (syn_cdif R (syn_cid))) (syn_cfv (syn_c2nd) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_csn (.cv x)) p0853 p0856
  have p0858 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_c2nd) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cop (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0761 p0857
  have p0859 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_clnimageop) p0858
  have p0860 :=
    @g_idex
  have p0861 :=
    @g_difex R (syn_cid) hyp_hncodecutfnval_1 p0860
  have p0862 :=
    @g_cnvex (syn_cdif R (syn_cid)) p0861
  have p0863 :=
    @g_snex (.cv x)
  have p0864 :=
    @g_lnimageopval (syn_csn (.cv x)) (syn_ccnv (syn_cdif R (syn_cid))) p0862 p0863
  have p0865 :=
    @g_eqtri (syn_cfv (syn_clnimageop) (syn_cfv (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cfv (syn_clnimageop) (syn_cop (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0859 p0864
  have p0866 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_clnimageop) (syn_cfv (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0737 p0865
  have p0867 :=
    @g_eqtri (syn_cfv (syn_chncodepredfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0705 p0866
  have p0868 :=
    @g_opeq12i (syn_cfv (syn_ccom (syn_c2nd) (syn_c1st)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) D (syn_cfv (syn_chncodepredfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0703 p0867
  have p0869 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop (syn_cfv (syn_ccom (syn_c2nd) (syn_c1st)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_chncodepredfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cop D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0689 p0868
  have p0870 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_clninterop) p0869
  have p0871 :=
    @g_idex
  have p0872 :=
    @g_difex R (syn_cid) hyp_hncodecutfnval_1 p0871
  have p0873 :=
    @g_cnvex (syn_cdif R (syn_cid)) p0872
  have p0874 :=
    @g_snex (.cv x)
  have p0875 :=
    @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) p0873 p0874
  have p0876 :=
    @g_lninteropval D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) hyp_hncodecutfnval_2 p0875
  have p0877 :=
    @g_eqtri (syn_cfv (syn_clninterop) (syn_cfv (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cfv (syn_clninterop) (syn_cop D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0870 p0876
  have p0878 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_clninterop) (syn_cfv (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0651 p0877
  have p0879 :=
    @g_eqtri (syn_cfv (syn_chncodecarrierfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0605 p0878
  have p0880 :=
    (by simpa [syn_chncodecarrierfn] using (Nominal.classEqRefl (syn_chncodecarrierfn)))
  have p0881 :=
    @g_fveq1i (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_chncodecarrierfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) p0880
  have p0882 :=
    @g_ln2ndfn
  have p0883 :=
    @g_ln1stfn
  have p0884 :=
    @g_fncovv (syn_c2nd) (syn_c1st) p0882 p0883
  have p0885 :=
    @g_lnimageopfn
  have p0886 :=
    @g_imageswapfn
  have p0887 :=
    @g_fnlndifop
  have p0888 :=
    @g_ln1stfn
  have p0889 :=
    @g_ln1stfn
  have p0890 :=
    @g_fncovv (syn_c1st) (syn_c1st) p0888 p0889
  have p0891 :=
    @g_idex
  have p0892 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p0893 :=
    Nominal.mp p0891 p0892
  have p0894 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p0890 p0893
  have p0895 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p0896 :=
    Nominal.mp p0894 p0895
  have p0897 :=
    @g_inidm (syn_cvv)
  have p0898 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0897
  have p0899 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) p0896 p0898
  have p0900 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0887 p0899
  have p0901 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p0902 :=
    @g_fneq1i (syn_cvv) (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) p0901
  have p0903 :=
    @g_mpbir (syn_wfn (syn_chncodestrictfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv)) p0900 p0902
  have p0904 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p0886 p0903
  have p0905 :=
    @g_ln2ndfn
  have p0906 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0904 p0905
  have p0907 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)
  have p0908 :=
    Nominal.mp p0906 p0907
  have p0909 :=
    @g_inidm (syn_cvv)
  have p0910 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0909
  have p0911 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cvv)) p0908 p0910
  have p0912 :=
    @g_fncovv (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0885 p0911
  have p0913 :=
    (by simpa [syn_chncodepredfn] using (Nominal.classEqRefl (syn_chncodepredfn)))
  have p0914 :=
    @g_fneq1i (syn_cvv) (syn_chncodepredfn) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) p0913
  have p0915 :=
    @g_mpbir (syn_wfn (syn_chncodepredfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) (syn_cvv)) p0912 p0914
  have p0916 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c2nd) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_chncodepredfn) (syn_cvv)) p0884 p0915
  have p0917 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)
  have p0918 :=
    Nominal.mp p0916 p0917
  have p0919 :=
    @g_inidm (syn_cvv)
  have p0920 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p0919
  have p0921 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cvv)) p0918 p0920
  have p0922 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p0923 :=
    @g_snex (.cv x)
  have p0924 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p0922 p0923
  have p0925 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cvv)) (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cvv)) p0921 p0924
  have p0926 :=
    @g_fvco2 (syn_cvv) (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))
  have p0927 :=
    Nominal.mp p0925 p0926
  have p0928 :=
    @g_ln2ndfn
  have p0929 :=
    @g_ln1stfn
  have p0930 :=
    @g_fncovv (syn_c2nd) (syn_c1st) p0928 p0929
  have p0931 :=
    @g_lnimageopfn
  have p0932 :=
    @g_imageswapfn
  have p0933 :=
    @g_fnlndifop
  have p0934 :=
    @g_ln1stfn
  have p0935 :=
    @g_ln1stfn
  have p0936 :=
    @g_fncovv (syn_c1st) (syn_c1st) p0934 p0935
  have p0937 :=
    @g_idex
  have p0938 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p0939 :=
    Nominal.mp p0937 p0938
  have p0940 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p0936 p0939
  have p0941 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p0942 :=
    Nominal.mp p0940 p0941
  have p0943 :=
    @g_inidm (syn_cvv)
  have p0944 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0943
  have p0945 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) p0942 p0944
  have p0946 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0933 p0945
  have p0947 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p0948 :=
    @g_fneq1i (syn_cvv) (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) p0947
  have p0949 :=
    @g_mpbir (syn_wfn (syn_chncodestrictfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv)) p0946 p0948
  have p0950 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p0932 p0949
  have p0951 :=
    @g_ln2ndfn
  have p0952 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0950 p0951
  have p0953 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)
  have p0954 :=
    Nominal.mp p0952 p0953
  have p0955 :=
    @g_inidm (syn_cvv)
  have p0956 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0955
  have p0957 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cvv)) p0954 p0956
  have p0958 :=
    @g_fncovv (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p0931 p0957
  have p0959 :=
    (by simpa [syn_chncodepredfn] using (Nominal.classEqRefl (syn_chncodepredfn)))
  have p0960 :=
    @g_fneq1i (syn_cvv) (syn_chncodepredfn) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) p0959
  have p0961 :=
    @g_mpbir (syn_wfn (syn_chncodepredfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) (syn_cvv)) p0958 p0960
  have p0962 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p0963 :=
    @g_snex (.cv x)
  have p0964 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p0962 p0963
  have p0965 :=
    @g_fvtxpvv (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn) p0930 p0961 p0964
  have p0966 :=
    @g_ln1stfn
  have p0967 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p0968 :=
    @g_snex (.cv x)
  have p0969 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p0967 p0968
  have p0970 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cvv)) p0966 p0969
  have p0971 :=
    @g_fvco2 (syn_cvv) (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_c2nd) (syn_c1st)
  have p0972 :=
    Nominal.mp p0970 p0971
  have p0973 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p0974 :=
    @g_snex (.cv x)
  have p0975 :=
    @g_opfv1st (syn_cop R D) (syn_csn (.cv x)) p0973 p0974
  have p0976 :=
    @g_fveq2i (syn_cfv (syn_c1st) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop R D) (syn_c2nd) p0975
  have p0977 :=
    @g_opfv2nd R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p0978 :=
    @g_eqtri (syn_cfv (syn_c2nd) (syn_cfv (syn_c1st) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cfv (syn_c2nd) (syn_cop R D)) D p0976 p0977
  have p0979 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_c2nd) (syn_c1st)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_c2nd) (syn_cfv (syn_c1st) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) D p0972 p0978
  have p0980 :=
    (by simpa [syn_chncodepredfn] using (Nominal.classEqRefl (syn_chncodepredfn)))
  have p0981 :=
    @g_fveq1i (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_chncodepredfn) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) p0980
  have p0982 :=
    @g_imageswapfn
  have p0983 :=
    @g_fnlndifop
  have p0984 :=
    @g_ln1stfn
  have p0985 :=
    @g_ln1stfn
  have p0986 :=
    @g_fncovv (syn_c1st) (syn_c1st) p0984 p0985
  have p0987 :=
    @g_idex
  have p0988 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p0989 :=
    Nominal.mp p0987 p0988
  have p0990 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p0986 p0989
  have p0991 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p0992 :=
    Nominal.mp p0990 p0991
  have p0993 :=
    @g_inidm (syn_cvv)
  have p0994 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0993
  have p0995 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) p0992 p0994
  have p0996 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p0983 p0995
  have p0997 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p0998 :=
    @g_fneq1i (syn_cvv) (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) p0997
  have p0999 :=
    @g_mpbir (syn_wfn (syn_chncodestrictfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv)) p0996 p0998
  have p1000 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p0982 p0999
  have p1001 :=
    @g_ln2ndfn
  have p1002 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p1000 p1001
  have p1003 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)
  have p1004 :=
    Nominal.mp p1002 p1003
  have p1005 :=
    @g_inidm (syn_cvv)
  have p1006 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p1005
  have p1007 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cvv)) p1004 p1006
  have p1008 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p1009 :=
    @g_snex (.cv x)
  have p1010 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p1008 p1009
  have p1011 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cvv)) (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cvv)) p1007 p1010
  have p1012 :=
    @g_fvco2 (syn_cvv) (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))
  have p1013 :=
    Nominal.mp p1011 p1012
  have p1014 :=
    @g_imageswapfn
  have p1015 :=
    @g_fnlndifop
  have p1016 :=
    @g_ln1stfn
  have p1017 :=
    @g_ln1stfn
  have p1018 :=
    @g_fncovv (syn_c1st) (syn_c1st) p1016 p1017
  have p1019 :=
    @g_idex
  have p1020 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p1021 :=
    Nominal.mp p1019 p1020
  have p1022 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p1018 p1021
  have p1023 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p1024 :=
    Nominal.mp p1022 p1023
  have p1025 :=
    @g_inidm (syn_cvv)
  have p1026 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p1025
  have p1027 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) p1024 p1026
  have p1028 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p1015 p1027
  have p1029 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p1030 :=
    @g_fneq1i (syn_cvv) (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) p1029
  have p1031 :=
    @g_mpbir (syn_wfn (syn_chncodestrictfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv)) p1028 p1030
  have p1032 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p1014 p1031
  have p1033 :=
    @g_ln2ndfn
  have p1034 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p1035 :=
    @g_snex (.cv x)
  have p1036 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p1034 p1035
  have p1037 :=
    @g_fvtxpvv (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd) p1032 p1033 p1036
  have p1038 :=
    @g_fnlndifop
  have p1039 :=
    @g_ln1stfn
  have p1040 :=
    @g_ln1stfn
  have p1041 :=
    @g_fncovv (syn_c1st) (syn_c1st) p1039 p1040
  have p1042 :=
    @g_idex
  have p1043 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p1044 :=
    Nominal.mp p1042 p1043
  have p1045 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p1041 p1044
  have p1046 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p1047 :=
    Nominal.mp p1045 p1046
  have p1048 :=
    @g_inidm (syn_cvv)
  have p1049 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p1048
  have p1050 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) p1047 p1049
  have p1051 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p1038 p1050
  have p1052 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p1053 :=
    @g_fneq1i (syn_cvv) (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) p1052
  have p1054 :=
    @g_mpbir (syn_wfn (syn_chncodestrictfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv)) p1051 p1053
  have p1055 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p1056 :=
    @g_snex (.cv x)
  have p1057 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p1055 p1056
  have p1058 :=
    @g_pm3_2i (syn_wfn (syn_chncodestrictfn) (syn_cvv)) (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cvv)) p1054 p1057
  have p1059 :=
    @g_fvco2 (syn_cvv) (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cimage (syn_cswap)) (syn_chncodestrictfn)
  have p1060 :=
    Nominal.mp p1058 p1059
  have p1061 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p1062 :=
    @g_fveq1i (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) p1061
  have p1063 :=
    @g_ln1stfn
  have p1064 :=
    @g_ln1stfn
  have p1065 :=
    @g_fncovv (syn_c1st) (syn_c1st) p1063 p1064
  have p1066 :=
    @g_idex
  have p1067 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p1068 :=
    Nominal.mp p1066 p1067
  have p1069 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p1065 p1068
  have p1070 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p1071 :=
    Nominal.mp p1069 p1070
  have p1072 :=
    @g_inidm (syn_cvv)
  have p1073 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p1072
  have p1074 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) p1071 p1073
  have p1075 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p1076 :=
    @g_snex (.cv x)
  have p1077 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p1075 p1076
  have p1078 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cvv)) p1074 p1077
  have p1079 :=
    @g_fvco2 (syn_cvv) (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))
  have p1080 :=
    Nominal.mp p1078 p1079
  have p1081 :=
    @g_ln1stfn
  have p1082 :=
    @g_ln1stfn
  have p1083 :=
    @g_fncovv (syn_c1st) (syn_c1st) p1081 p1082
  have p1084 :=
    @g_idex
  have p1085 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p1086 :=
    Nominal.mp p1084 p1085
  have p1087 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p1088 :=
    @g_snex (.cv x)
  have p1089 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p1087 p1088
  have p1090 :=
    @g_fvtxpvv (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))) p1083 p1086 p1089
  have p1091 :=
    @g_ln1stfn
  have p1092 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p1093 :=
    @g_snex (.cv x)
  have p1094 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p1092 p1093
  have p1095 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cvv)) p1091 p1094
  have p1096 :=
    @g_fvco2 (syn_cvv) (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_c1st) (syn_c1st)
  have p1097 :=
    Nominal.mp p1095 p1096
  have p1098 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p1099 :=
    @g_snex (.cv x)
  have p1100 :=
    @g_opfv1st (syn_cop R D) (syn_csn (.cv x)) p1098 p1099
  have p1101 :=
    @g_fveq2i (syn_cfv (syn_c1st) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop R D) (syn_c1st) p1100
  have p1102 :=
    @g_opfv1st R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p1103 :=
    @g_eqtri (syn_cfv (syn_c1st) (syn_cfv (syn_c1st) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cfv (syn_c1st) (syn_cop R D)) R p1101 p1102
  have p1104 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_c1st) (syn_c1st)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_c1st) (syn_cfv (syn_c1st) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) R p1097 p1103
  have p1105 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p1106 :=
    @g_snex (.cv x)
  have p1107 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p1105 p1106
  have p1108 :=
    @g_idex
  have p1109 :=
    @g_fvconst2 (syn_cvv) (syn_cid) (syn_cop (syn_cop R D) (syn_csn (.cv x))) p1108
  have p1110 :=
    Nominal.mp p1107 p1109
  have p1111 :=
    @g_opeq12i (syn_cfv (syn_ccom (syn_c1st) (syn_c1st)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) R (syn_cfv (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cid) p1104 p1110
  have p1112 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop (syn_cfv (syn_ccom (syn_c1st) (syn_c1st)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cop R (syn_cid)) p1090 p1111
  have p1113 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop R (syn_cid)) (syn_clndifop) p1112
  have p1114 :=
    (by simpa [syn_co] using (Nominal.classEqRefl (syn_co R (syn_clndifop) (syn_cid))))
  have p1115 :=
    @g_eqcomi (syn_co R (syn_clndifop) (syn_cid)) (syn_cfv (syn_clndifop) (syn_cop R (syn_cid))) p1114
  have p1116 :=
    @g_idex
  have p1117 :=
    @g_pm3_2i (.classMem R (syn_cvv)) (.classMem (syn_cid) (syn_cvv)) hyp_hncodecutfnval_1 p1116
  have p1118 :=
    @g_lndifopvalg R (syn_cid) (syn_cvv) (syn_cvv)
  have p1119 :=
    Nominal.mp p1117 p1118
  have p1120 :=
    @g_eqtri (syn_cfv (syn_clndifop) (syn_cop R (syn_cid))) (syn_co R (syn_clndifop) (syn_cid)) (syn_cdif R (syn_cid)) p1115 p1119
  have p1121 :=
    @g_eqtri (syn_cfv (syn_clndifop) (syn_cfv (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cfv (syn_clndifop) (syn_cop R (syn_cid))) (syn_cdif R (syn_cid)) p1113 p1120
  have p1122 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_clndifop) (syn_cfv (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cdif R (syn_cid)) p1080 p1121
  have p1123 :=
    @g_eqtri (syn_cfv (syn_chncodestrictfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cdif R (syn_cid)) p1062 p1122
  have p1124 :=
    @g_fveq2i (syn_cfv (syn_chncodestrictfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cdif R (syn_cid)) (syn_cimage (syn_cswap)) p1123
  have p1125 :=
    @g_idex
  have p1126 :=
    @g_difex R (syn_cid) hyp_hncodecutfnval_1 p1125
  have p1127 :=
    @g_wppimageswapfv (syn_cdif R (syn_cid)) p1126
  have p1128 :=
    @g_eqtri (syn_cfv (syn_cimage (syn_cswap)) (syn_cfv (syn_chncodestrictfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cfv (syn_cimage (syn_cswap)) (syn_cdif R (syn_cid))) (syn_ccnv (syn_cdif R (syn_cid))) p1124 p1127
  have p1129 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_cimage (syn_cswap)) (syn_cfv (syn_chncodestrictfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_ccnv (syn_cdif R (syn_cid))) p1060 p1128
  have p1130 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p1131 :=
    @g_snex (.cv x)
  have p1132 :=
    @g_opfv2nd (syn_cop R D) (syn_csn (.cv x)) p1130 p1131
  have p1133 :=
    @g_opeq12i (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_ccnv (syn_cdif R (syn_cid))) (syn_cfv (syn_c2nd) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_csn (.cv x)) p1129 p1132
  have p1134 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_c2nd) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cop (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p1037 p1133
  have p1135 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_clnimageop) p1134
  have p1136 :=
    @g_idex
  have p1137 :=
    @g_difex R (syn_cid) hyp_hncodecutfnval_1 p1136
  have p1138 :=
    @g_cnvex (syn_cdif R (syn_cid)) p1137
  have p1139 :=
    @g_snex (.cv x)
  have p1140 :=
    @g_lnimageopval (syn_csn (.cv x)) (syn_ccnv (syn_cdif R (syn_cid))) p1138 p1139
  have p1141 :=
    @g_eqtri (syn_cfv (syn_clnimageop) (syn_cfv (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cfv (syn_clnimageop) (syn_cop (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p1135 p1140
  have p1142 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_clnimageop) (syn_cfv (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p1013 p1141
  have p1143 :=
    @g_eqtri (syn_cfv (syn_chncodepredfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0981 p1142
  have p1144 :=
    @g_opeq12i (syn_cfv (syn_ccom (syn_c2nd) (syn_c1st)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) D (syn_cfv (syn_chncodepredfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0979 p1143
  have p1145 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop (syn_cfv (syn_ccom (syn_c2nd) (syn_c1st)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_chncodepredfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cop D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0965 p1144
  have p1146 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_clninterop) p1145
  have p1147 :=
    @g_idex
  have p1148 :=
    @g_difex R (syn_cid) hyp_hncodecutfnval_1 p1147
  have p1149 :=
    @g_cnvex (syn_cdif R (syn_cid)) p1148
  have p1150 :=
    @g_snex (.cv x)
  have p1151 :=
    @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) p1149 p1150
  have p1152 :=
    @g_lninteropval D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) hyp_hncodecutfnval_2 p1151
  have p1153 :=
    @g_eqtri (syn_cfv (syn_clninterop) (syn_cfv (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cfv (syn_clninterop) (syn_cop D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p1146 p1152
  have p1154 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_clninterop) (syn_cfv (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0927 p1153
  have p1155 :=
    @g_eqtri (syn_cfv (syn_chncodecarrierfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0881 p1154
  have p1156 :=
    @g_opeq12i (syn_cfv (syn_chncodecarrierfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cfv (syn_chncodecarrierfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0879 p1155
  have p1157 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop (syn_cfv (syn_chncodecarrierfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_chncodecarrierfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cop (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0603 p1156
  have p1158 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_ccross) p1157
  have p1159 :=
    (by simpa [syn_co] using (Nominal.classEqRefl (syn_co (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_ccross) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
  have p1160 :=
    @g_eqcomi (syn_co (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_ccross) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cfv (syn_ccross) (syn_cop (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) p1159
  have p1161 :=
    @g_idex
  have p1162 :=
    @g_difex R (syn_cid) hyp_hncodecutfnval_1 p1161
  have p1163 :=
    @g_cnvex (syn_cdif R (syn_cid)) p1162
  have p1164 :=
    @g_snex (.cv x)
  have p1165 :=
    @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) p1163 p1164
  have p1166 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) hyp_hncodecutfnval_2 p1165
  have p1167 :=
    @g_idex
  have p1168 :=
    @g_difex R (syn_cid) hyp_hncodecutfnval_1 p1167
  have p1169 :=
    @g_cnvex (syn_cdif R (syn_cid)) p1168
  have p1170 :=
    @g_snex (.cv x)
  have p1171 :=
    @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) p1169 p1170
  have p1172 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) hyp_hncodecutfnval_2 p1171
  have p1173 :=
    @g_pm3_2i (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv)) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv)) p1166 p1172
  have p1174 :=
    @g_ovcross (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv) (syn_cvv)
  have p1175 :=
    Nominal.mp p1173 p1174
  have p1176 :=
    @g_eqtri (syn_cfv (syn_ccross) (syn_cop (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_co (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_ccross) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p1160 p1175
  have p1177 :=
    @g_eqtri (syn_cfv (syn_ccross) (syn_cfv (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cfv (syn_ccross) (syn_cop (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p1158 p1176
  have p1178 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn))) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_ccross) (syn_cfv (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn)) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0509 p1177
  have p1179 :=
    @g_eqtri (syn_cfv (syn_chncodesquarefn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_chncodecarrierfn) (syn_chncodecarrierfn))) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0407 p1178
  have p1180 :=
    @g_opeq12i (syn_cfv (syn_ccom (syn_c1st) (syn_c1st)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) R (syn_cfv (syn_chncodesquarefn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0405 p1179
  have p1181 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop (syn_cfv (syn_ccom (syn_c1st) (syn_c1st)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_chncodesquarefn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cop R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) p0391 p1180
  have p1182 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_clninterop) p1181
  have p1183 :=
    @g_idex
  have p1184 :=
    @g_difex R (syn_cid) hyp_hncodecutfnval_1 p1183
  have p1185 :=
    @g_cnvex (syn_cdif R (syn_cid)) p1184
  have p1186 :=
    @g_snex (.cv x)
  have p1187 :=
    @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) p1185 p1186
  have p1188 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) hyp_hncodecutfnval_2 p1187
  have p1189 :=
    @g_idex
  have p1190 :=
    @g_difex R (syn_cid) hyp_hncodecutfnval_1 p1189
  have p1191 :=
    @g_cnvex (syn_cdif R (syn_cid)) p1190
  have p1192 :=
    @g_snex (.cv x)
  have p1193 :=
    @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) p1191 p1192
  have p1194 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) hyp_hncodecutfnval_2 p1193
  have p1195 :=
    @g_xpex (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p1188 p1194
  have p1196 :=
    @g_lninteropval R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) hyp_hncodecutfnval_1 p1195
  have p1197 :=
    @g_eqtri (syn_cfv (syn_clninterop) (syn_cfv (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cfv (syn_clninterop) (syn_cop R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) p1182 p1196
  have p1198 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn))) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_clninterop) (syn_cfv (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn)) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) p0283 p1197
  have p1199 :=
    @g_eqtri (syn_cfv (syn_chncoderelfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_chncodesquarefn))) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) p0167 p1198
  have p1200 :=
    (by simpa [syn_chncodecarrierfn] using (Nominal.classEqRefl (syn_chncodecarrierfn)))
  have p1201 :=
    @g_fveq1i (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_chncodecarrierfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) p1200
  have p1202 :=
    @g_ln2ndfn
  have p1203 :=
    @g_ln1stfn
  have p1204 :=
    @g_fncovv (syn_c2nd) (syn_c1st) p1202 p1203
  have p1205 :=
    @g_lnimageopfn
  have p1206 :=
    @g_imageswapfn
  have p1207 :=
    @g_fnlndifop
  have p1208 :=
    @g_ln1stfn
  have p1209 :=
    @g_ln1stfn
  have p1210 :=
    @g_fncovv (syn_c1st) (syn_c1st) p1208 p1209
  have p1211 :=
    @g_idex
  have p1212 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p1213 :=
    Nominal.mp p1211 p1212
  have p1214 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p1210 p1213
  have p1215 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p1216 :=
    Nominal.mp p1214 p1215
  have p1217 :=
    @g_inidm (syn_cvv)
  have p1218 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p1217
  have p1219 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) p1216 p1218
  have p1220 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p1207 p1219
  have p1221 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p1222 :=
    @g_fneq1i (syn_cvv) (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) p1221
  have p1223 :=
    @g_mpbir (syn_wfn (syn_chncodestrictfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv)) p1220 p1222
  have p1224 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p1206 p1223
  have p1225 :=
    @g_ln2ndfn
  have p1226 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p1224 p1225
  have p1227 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)
  have p1228 :=
    Nominal.mp p1226 p1227
  have p1229 :=
    @g_inidm (syn_cvv)
  have p1230 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p1229
  have p1231 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cvv)) p1228 p1230
  have p1232 :=
    @g_fncovv (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p1205 p1231
  have p1233 :=
    (by simpa [syn_chncodepredfn] using (Nominal.classEqRefl (syn_chncodepredfn)))
  have p1234 :=
    @g_fneq1i (syn_cvv) (syn_chncodepredfn) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) p1233
  have p1235 :=
    @g_mpbir (syn_wfn (syn_chncodepredfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) (syn_cvv)) p1232 p1234
  have p1236 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c2nd) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_chncodepredfn) (syn_cvv)) p1204 p1235
  have p1237 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)
  have p1238 :=
    Nominal.mp p1236 p1237
  have p1239 :=
    @g_inidm (syn_cvv)
  have p1240 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) p1239
  have p1241 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cvv)) p1238 p1240
  have p1242 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p1243 :=
    @g_snex (.cv x)
  have p1244 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p1242 p1243
  have p1245 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cvv)) (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cvv)) p1241 p1244
  have p1246 :=
    @g_fvco2 (syn_cvv) (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))
  have p1247 :=
    Nominal.mp p1245 p1246
  have p1248 :=
    @g_ln2ndfn
  have p1249 :=
    @g_ln1stfn
  have p1250 :=
    @g_fncovv (syn_c2nd) (syn_c1st) p1248 p1249
  have p1251 :=
    @g_lnimageopfn
  have p1252 :=
    @g_imageswapfn
  have p1253 :=
    @g_fnlndifop
  have p1254 :=
    @g_ln1stfn
  have p1255 :=
    @g_ln1stfn
  have p1256 :=
    @g_fncovv (syn_c1st) (syn_c1st) p1254 p1255
  have p1257 :=
    @g_idex
  have p1258 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p1259 :=
    Nominal.mp p1257 p1258
  have p1260 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p1256 p1259
  have p1261 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p1262 :=
    Nominal.mp p1260 p1261
  have p1263 :=
    @g_inidm (syn_cvv)
  have p1264 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p1263
  have p1265 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) p1262 p1264
  have p1266 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p1253 p1265
  have p1267 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p1268 :=
    @g_fneq1i (syn_cvv) (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) p1267
  have p1269 :=
    @g_mpbir (syn_wfn (syn_chncodestrictfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv)) p1266 p1268
  have p1270 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p1252 p1269
  have p1271 :=
    @g_ln2ndfn
  have p1272 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p1270 p1271
  have p1273 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)
  have p1274 :=
    Nominal.mp p1272 p1273
  have p1275 :=
    @g_inidm (syn_cvv)
  have p1276 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p1275
  have p1277 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cvv)) p1274 p1276
  have p1278 :=
    @g_fncovv (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p1251 p1277
  have p1279 :=
    (by simpa [syn_chncodepredfn] using (Nominal.classEqRefl (syn_chncodepredfn)))
  have p1280 :=
    @g_fneq1i (syn_cvv) (syn_chncodepredfn) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) p1279
  have p1281 :=
    @g_mpbir (syn_wfn (syn_chncodepredfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) (syn_cvv)) p1278 p1280
  have p1282 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p1283 :=
    @g_snex (.cv x)
  have p1284 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p1282 p1283
  have p1285 :=
    @g_fvtxpvv (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn) p1250 p1281 p1284
  have p1286 :=
    @g_ln1stfn
  have p1287 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p1288 :=
    @g_snex (.cv x)
  have p1289 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p1287 p1288
  have p1290 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cvv)) p1286 p1289
  have p1291 :=
    @g_fvco2 (syn_cvv) (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_c2nd) (syn_c1st)
  have p1292 :=
    Nominal.mp p1290 p1291
  have p1293 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p1294 :=
    @g_snex (.cv x)
  have p1295 :=
    @g_opfv1st (syn_cop R D) (syn_csn (.cv x)) p1293 p1294
  have p1296 :=
    @g_fveq2i (syn_cfv (syn_c1st) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop R D) (syn_c2nd) p1295
  have p1297 :=
    @g_opfv2nd R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p1298 :=
    @g_eqtri (syn_cfv (syn_c2nd) (syn_cfv (syn_c1st) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cfv (syn_c2nd) (syn_cop R D)) D p1296 p1297
  have p1299 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_c2nd) (syn_c1st)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_c2nd) (syn_cfv (syn_c1st) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) D p1292 p1298
  have p1300 :=
    (by simpa [syn_chncodepredfn] using (Nominal.classEqRefl (syn_chncodepredfn)))
  have p1301 :=
    @g_fveq1i (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_chncodepredfn) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) p1300
  have p1302 :=
    @g_imageswapfn
  have p1303 :=
    @g_fnlndifop
  have p1304 :=
    @g_ln1stfn
  have p1305 :=
    @g_ln1stfn
  have p1306 :=
    @g_fncovv (syn_c1st) (syn_c1st) p1304 p1305
  have p1307 :=
    @g_idex
  have p1308 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p1309 :=
    Nominal.mp p1307 p1308
  have p1310 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p1306 p1309
  have p1311 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p1312 :=
    Nominal.mp p1310 p1311
  have p1313 :=
    @g_inidm (syn_cvv)
  have p1314 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p1313
  have p1315 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) p1312 p1314
  have p1316 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p1303 p1315
  have p1317 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p1318 :=
    @g_fneq1i (syn_cvv) (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) p1317
  have p1319 :=
    @g_mpbir (syn_wfn (syn_chncodestrictfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv)) p1316 p1318
  have p1320 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p1302 p1319
  have p1321 :=
    @g_ln2ndfn
  have p1322 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p1320 p1321
  have p1323 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)
  have p1324 :=
    Nominal.mp p1322 p1323
  have p1325 :=
    @g_inidm (syn_cvv)
  have p1326 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) p1325
  have p1327 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cvv)) p1324 p1326
  have p1328 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p1329 :=
    @g_snex (.cv x)
  have p1330 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p1328 p1329
  have p1331 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cvv)) (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cvv)) p1327 p1330
  have p1332 :=
    @g_fvco2 (syn_cvv) (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))
  have p1333 :=
    Nominal.mp p1331 p1332
  have p1334 :=
    @g_imageswapfn
  have p1335 :=
    @g_fnlndifop
  have p1336 :=
    @g_ln1stfn
  have p1337 :=
    @g_ln1stfn
  have p1338 :=
    @g_fncovv (syn_c1st) (syn_c1st) p1336 p1337
  have p1339 :=
    @g_idex
  have p1340 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p1341 :=
    Nominal.mp p1339 p1340
  have p1342 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p1338 p1341
  have p1343 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p1344 :=
    Nominal.mp p1342 p1343
  have p1345 :=
    @g_inidm (syn_cvv)
  have p1346 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p1345
  have p1347 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) p1344 p1346
  have p1348 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p1335 p1347
  have p1349 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p1350 :=
    @g_fneq1i (syn_cvv) (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) p1349
  have p1351 :=
    @g_mpbir (syn_wfn (syn_chncodestrictfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv)) p1348 p1350
  have p1352 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_chncodestrictfn) p1334 p1351
  have p1353 :=
    @g_ln2ndfn
  have p1354 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p1355 :=
    @g_snex (.cv x)
  have p1356 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p1354 p1355
  have p1357 :=
    @g_fvtxpvv (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd) p1352 p1353 p1356
  have p1358 :=
    @g_fnlndifop
  have p1359 :=
    @g_ln1stfn
  have p1360 :=
    @g_ln1stfn
  have p1361 :=
    @g_fncovv (syn_c1st) (syn_c1st) p1359 p1360
  have p1362 :=
    @g_idex
  have p1363 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p1364 :=
    Nominal.mp p1362 p1363
  have p1365 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p1361 p1364
  have p1366 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p1367 :=
    Nominal.mp p1365 p1366
  have p1368 :=
    @g_inidm (syn_cvv)
  have p1369 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p1368
  have p1370 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) p1367 p1369
  have p1371 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p1358 p1370
  have p1372 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p1373 :=
    @g_fneq1i (syn_cvv) (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) p1372
  have p1374 :=
    @g_mpbir (syn_wfn (syn_chncodestrictfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cvv)) p1371 p1373
  have p1375 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p1376 :=
    @g_snex (.cv x)
  have p1377 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p1375 p1376
  have p1378 :=
    @g_pm3_2i (syn_wfn (syn_chncodestrictfn) (syn_cvv)) (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cvv)) p1374 p1377
  have p1379 :=
    @g_fvco2 (syn_cvv) (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cimage (syn_cswap)) (syn_chncodestrictfn)
  have p1380 :=
    Nominal.mp p1378 p1379
  have p1381 :=
    (by simpa [syn_chncodestrictfn] using (Nominal.classEqRefl (syn_chncodestrictfn)))
  have p1382 :=
    @g_fveq1i (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_chncodestrictfn) (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) p1381
  have p1383 :=
    @g_ln1stfn
  have p1384 :=
    @g_ln1stfn
  have p1385 :=
    @g_fncovv (syn_c1st) (syn_c1st) p1383 p1384
  have p1386 :=
    @g_idex
  have p1387 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p1388 :=
    Nominal.mp p1386 p1387
  have p1389 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_c1st) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cvv)) p1385 p1388
  have p1390 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))
  have p1391 :=
    Nominal.mp p1389 p1390
  have p1392 :=
    @g_inidm (syn_cvv)
  have p1393 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) p1392
  have p1394 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) p1391 p1393
  have p1395 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p1396 :=
    @g_snex (.cv x)
  have p1397 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p1395 p1396
  have p1398 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cvv)) (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cvv)) p1394 p1397
  have p1399 :=
    @g_fvco2 (syn_cvv) (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))
  have p1400 :=
    Nominal.mp p1398 p1399
  have p1401 :=
    @g_ln1stfn
  have p1402 :=
    @g_ln1stfn
  have p1403 :=
    @g_fncovv (syn_c1st) (syn_c1st) p1401 p1402
  have p1404 :=
    @g_idex
  have p1405 :=
    @g_fnconstg (syn_cvv) (syn_cid) (syn_cvv)
  have p1406 :=
    Nominal.mp p1404 p1405
  have p1407 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p1408 :=
    @g_snex (.cv x)
  have p1409 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p1407 p1408
  have p1410 :=
    @g_fvtxpvv (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))) p1403 p1406 p1409
  have p1411 :=
    @g_ln1stfn
  have p1412 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p1413 :=
    @g_snex (.cv x)
  have p1414 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p1412 p1413
  have p1415 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cvv)) p1411 p1414
  have p1416 :=
    @g_fvco2 (syn_cvv) (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_c1st) (syn_c1st)
  have p1417 :=
    Nominal.mp p1415 p1416
  have p1418 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p1419 :=
    @g_snex (.cv x)
  have p1420 :=
    @g_opfv1st (syn_cop R D) (syn_csn (.cv x)) p1418 p1419
  have p1421 :=
    @g_fveq2i (syn_cfv (syn_c1st) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop R D) (syn_c1st) p1420
  have p1422 :=
    @g_opfv1st R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p1423 :=
    @g_eqtri (syn_cfv (syn_c1st) (syn_cfv (syn_c1st) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cfv (syn_c1st) (syn_cop R D)) R p1421 p1422
  have p1424 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_c1st) (syn_c1st)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_c1st) (syn_cfv (syn_c1st) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) R p1417 p1423
  have p1425 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p1426 :=
    @g_snex (.cv x)
  have p1427 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p1425 p1426
  have p1428 :=
    @g_idex
  have p1429 :=
    @g_fvconst2 (syn_cvv) (syn_cid) (syn_cop (syn_cop R D) (syn_csn (.cv x))) p1428
  have p1430 :=
    Nominal.mp p1427 p1429
  have p1431 :=
    @g_opeq12i (syn_cfv (syn_ccom (syn_c1st) (syn_c1st)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) R (syn_cfv (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cid) p1424 p1430
  have p1432 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop (syn_cfv (syn_ccom (syn_c1st) (syn_c1st)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_cxp (syn_cvv) (syn_csn (syn_cid))) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cop R (syn_cid)) p1410 p1431
  have p1433 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop R (syn_cid)) (syn_clndifop) p1432
  have p1434 :=
    (by simpa [syn_co] using (Nominal.classEqRefl (syn_co R (syn_clndifop) (syn_cid))))
  have p1435 :=
    @g_eqcomi (syn_co R (syn_clndifop) (syn_cid)) (syn_cfv (syn_clndifop) (syn_cop R (syn_cid))) p1434
  have p1436 :=
    @g_idex
  have p1437 :=
    @g_pm3_2i (.classMem R (syn_cvv)) (.classMem (syn_cid) (syn_cvv)) hyp_hncodecutfnval_1 p1436
  have p1438 :=
    @g_lndifopvalg R (syn_cid) (syn_cvv) (syn_cvv)
  have p1439 :=
    Nominal.mp p1437 p1438
  have p1440 :=
    @g_eqtri (syn_cfv (syn_clndifop) (syn_cop R (syn_cid))) (syn_co R (syn_clndifop) (syn_cid)) (syn_cdif R (syn_cid)) p1435 p1439
  have p1441 :=
    @g_eqtri (syn_cfv (syn_clndifop) (syn_cfv (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cfv (syn_clndifop) (syn_cop R (syn_cid))) (syn_cdif R (syn_cid)) p1433 p1440
  have p1442 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_clndifop) (syn_cfv (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid)))) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cdif R (syn_cid)) p1400 p1441
  have p1443 :=
    @g_eqtri (syn_cfv (syn_chncodestrictfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_ccom (syn_clndifop) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st)) (syn_cxp (syn_cvv) (syn_csn (syn_cid))))) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cdif R (syn_cid)) p1382 p1442
  have p1444 :=
    @g_fveq2i (syn_cfv (syn_chncodestrictfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cdif R (syn_cid)) (syn_cimage (syn_cswap)) p1443
  have p1445 :=
    @g_idex
  have p1446 :=
    @g_difex R (syn_cid) hyp_hncodecutfnval_1 p1445
  have p1447 :=
    @g_wppimageswapfv (syn_cdif R (syn_cid)) p1446
  have p1448 :=
    @g_eqtri (syn_cfv (syn_cimage (syn_cswap)) (syn_cfv (syn_chncodestrictfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cfv (syn_cimage (syn_cswap)) (syn_cdif R (syn_cid))) (syn_ccnv (syn_cdif R (syn_cid))) p1444 p1447
  have p1449 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_cimage (syn_cswap)) (syn_cfv (syn_chncodestrictfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_ccnv (syn_cdif R (syn_cid))) p1380 p1448
  have p1450 :=
    @g_opex R D hyp_hncodecutfnval_1 hyp_hncodecutfnval_2
  have p1451 :=
    @g_snex (.cv x)
  have p1452 :=
    @g_opfv2nd (syn_cop R D) (syn_csn (.cv x)) p1450 p1451
  have p1453 :=
    @g_opeq12i (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_ccnv (syn_cdif R (syn_cid))) (syn_cfv (syn_c2nd) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_csn (.cv x)) p1449 p1452
  have p1454 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_c2nd) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cop (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p1357 p1453
  have p1455 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_clnimageop) p1454
  have p1456 :=
    @g_idex
  have p1457 :=
    @g_difex R (syn_cid) hyp_hncodecutfnval_1 p1456
  have p1458 :=
    @g_cnvex (syn_cdif R (syn_cid)) p1457
  have p1459 :=
    @g_snex (.cv x)
  have p1460 :=
    @g_lnimageopval (syn_csn (.cv x)) (syn_ccnv (syn_cdif R (syn_cid))) p1458 p1459
  have p1461 :=
    @g_eqtri (syn_cfv (syn_clnimageop) (syn_cfv (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cfv (syn_clnimageop) (syn_cop (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p1455 p1460
  have p1462 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_clnimageop) (syn_cfv (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd)) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p1333 p1461
  have p1463 :=
    @g_eqtri (syn_cfv (syn_chncodepredfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_ccom (syn_clnimageop) (syn_ctxp (syn_ccom (syn_cimage (syn_cswap)) (syn_chncodestrictfn)) (syn_c2nd))) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p1301 p1462
  have p1464 :=
    @g_opeq12i (syn_cfv (syn_ccom (syn_c2nd) (syn_c1st)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) D (syn_cfv (syn_chncodepredfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p1299 p1463
  have p1465 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop (syn_cfv (syn_ccom (syn_c2nd) (syn_c1st)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_chncodepredfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cop D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p1285 p1464
  have p1466 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_clninterop) p1465
  have p1467 :=
    @g_idex
  have p1468 :=
    @g_difex R (syn_cid) hyp_hncodecutfnval_1 p1467
  have p1469 :=
    @g_cnvex (syn_cdif R (syn_cid)) p1468
  have p1470 :=
    @g_snex (.cv x)
  have p1471 :=
    @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) p1469 p1470
  have p1472 :=
    @g_lninteropval D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) hyp_hncodecutfnval_2 p1471
  have p1473 :=
    @g_eqtri (syn_cfv (syn_clninterop) (syn_cfv (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cfv (syn_clninterop) (syn_cop D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p1466 p1472
  have p1474 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_clninterop) (syn_cfv (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn)) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p1247 p1473
  have p1475 :=
    @g_eqtri (syn_cfv (syn_chncodecarrierfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_ccom (syn_clninterop) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_chncodepredfn))) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p1201 p1474
  have p1476 :=
    @g_opeq12i (syn_cfv (syn_chncoderelfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_chncodecarrierfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p1199 p1475
  have p1477 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop (syn_cfv (syn_chncoderelfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_chncodecarrierfn) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0165 p1476
  have p1478 :=
    @g_eqtri (syn_cfv (syn_chncodecutfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0001 p1477
  have p1479 :=
    (by simpa [syn_chnwcutcode] using (Nominal.classEqRefl (syn_chnwcutcode R D (.cv x))))
  have p1480 :=
    @g_eqcomi (syn_chnwcutcode R D (.cv x)) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p1479
  have p1481 :=
    @g_eqtri (syn_cfv (syn_chncodecutfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_chnwcutcode R D (.cv x)) p1478 p1480
  exact p1481

#print axioms g_hncodecutfnval

end NFChoice.DirectNominalPrf.WPPReplay
