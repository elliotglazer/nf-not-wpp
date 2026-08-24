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
import NominalWPPReplayChunk017Compact001Part018

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

noncomputable def g_hncodecutpairfnval
    (x : Var) (D : Class) (R : Class) (hyp_hncodecutpairfnval_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_hncodecutpairfnval_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_chncodecutpairfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop (syn_chnwcutcode R D (.cv x)) (syn_cop R D))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ D.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_chncodecutpairfn] using (Nominal.classEqRefl (syn_chncodecutpairfn)))
  have p0001 :=
    @g_fveq1i (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_chncodecutpairfn) (syn_ctxp (syn_chncodecutfn) (syn_c1st)) p0000
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
    @g_pm3_2i (syn_wfn (syn_chncoderelfn) (syn_cvv)) (syn_wfn (syn_chncodecarrierfn) (syn_cvv)) p0116 p0161
  have p0163 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_chncoderelfn) (syn_chncodecarrierfn)
  have p0164 :=
    Nominal.mp p0162 p0163
  have p0165 :=
    @g_inidm (syn_cvv)
  have p0166 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn)) p0165
  have p0167 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn)) (syn_cvv)) p0164 p0166
  have p0168 :=
    (by simpa [syn_chncodecutfn] using (Nominal.classEqRefl (syn_chncodecutfn)))
  have p0169 :=
    @g_fneq1i (syn_cvv) (syn_chncodecutfn) (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn)) p0168
  have p0170 :=
    @g_mpbir (syn_wfn (syn_chncodecutfn) (syn_cvv)) (syn_wfn (syn_ctxp (syn_chncoderelfn) (syn_chncodecarrierfn)) (syn_cvv)) p0167 p0169
  have p0171 :=
    @g_ln1stfn
  have p0172 :=
    @g_opex R D hyp_hncodecutpairfnval_1 hyp_hncodecutpairfnval_2
  have p0173 :=
    @g_snex (.cv x)
  have p0174 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p0172 p0173
  have p0175 :=
    @g_fvtxpvv (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_chncodecutfn) (syn_c1st) p0170 p0171 p0174
  have p0176 :=
    @g_hncodecutfnval x D R hyp_hncodecutpairfnval_1 hyp_hncodecutpairfnval_2
  have p0177 :=
    @g_opex R D hyp_hncodecutpairfnval_1 hyp_hncodecutpairfnval_2
  have p0178 :=
    @g_snex (.cv x)
  have p0179 :=
    @g_opfv1st (syn_cop R D) (syn_csn (.cv x)) p0177 p0178
  have p0180 :=
    @g_opeq12i (syn_cfv (syn_chncodecutfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_chnwcutcode R D (.cv x)) (syn_cfv (syn_c1st) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop R D) p0176 p0179
  have p0181 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_chncodecutfn) (syn_c1st)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop (syn_cfv (syn_chncodecutfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_c1st) (syn_cop (syn_cop R D) (syn_csn (.cv x))))) (syn_cop (syn_chnwcutcode R D (.cv x)) (syn_cop R D)) p0175 p0180
  have p0182 :=
    @g_eqtri (syn_cfv (syn_chncodecutpairfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cfv (syn_ctxp (syn_chncodecutfn) (syn_c1st)) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop (syn_chnwcutcode R D (.cv x)) (syn_cop R D)) p0001 p0181
  exact p0182

noncomputable def g_hncodecmpsetexg
    (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cvv)) (.classMem (syn_chncodecmpset A) (syn_cvv))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    (by simpa [syn_chncodecmpset] using (Nominal.classEqRefl (syn_chncodecmpset A)))
  have p0001 :=
    @g_hwnisoexg A
  have p0002 :=
    (by simpa [syn_chncodecutrel] using (Nominal.classEqRefl (syn_chncodecutrel A)))
  have p0003 :=
    @g_hncodecutpairfnex
  have p0004 :=
    @g_a1i (.classMem (syn_chncodecutpairfn) (syn_cvv)) (.classMem A (syn_cvv)) p0003
  have p0005 :=
    (by simpa [syn_chncodecutinputs] using (Nominal.classEqRefl (syn_chncodecutinputs A)))
  have p0006 :=
    @g_lnpwquoinputfnex
  have p0007 :=
    @g_a1i (.classMem (syn_clnpwquoinputfn) (syn_cvv)) (.classMem A (syn_cvv)) p0006
  have p0008 :=
    @g_hwcnexg A
  have p0009 :=
    @g_pw1exg (syn_chwcn A) (syn_cvv)
  have p0010 :=
    @g_syl (.classMem A (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)) (.classMem (syn_cpw1 (syn_chwcn A)) (syn_cvv)) p0008 p0009
  have p0011 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_clnpwquoinputfn) (syn_cvv)) (.classMem (syn_cpw1 (syn_chwcn A)) (syn_cvv)) p0007 p0010
  have p0012 :=
    @g_imaexg (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A)) (syn_cvv) (syn_cvv)
  have p0013 :=
    @g_syl (.classMem A (syn_cvv)) (syn_wa (.classMem (syn_clnpwquoinputfn) (syn_cvv)) (.classMem (syn_cpw1 (syn_chwcn A)) (syn_cvv))) (.classMem (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A))) (syn_cvv)) p0011 p0012
  have p0014 :=
    @g_uniexg (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A))) (syn_cvv)
  have p0015 :=
    @g_syl (.classMem A (syn_cvv)) (.classMem (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A))) (syn_cvv)) (.classMem (syn_cuni (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A)))) (syn_cvv)) p0013 p0014
  have p0016 :=
    @g_syl5eqel (.classMem A (syn_cvv)) (syn_chncodecutinputs A) (syn_cuni (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A)))) (syn_cvv) p0005 p0015
  have p0017 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_chncodecutpairfn) (syn_cvv)) (.classMem (syn_chncodecutinputs A) (syn_cvv)) p0004 p0016
  have p0018 :=
    @g_imaexg (syn_chncodecutpairfn) (syn_chncodecutinputs A) (syn_cvv) (syn_cvv)
  have p0019 :=
    @g_syl (.classMem A (syn_cvv)) (syn_wa (.classMem (syn_chncodecutpairfn) (syn_cvv)) (.classMem (syn_chncodecutinputs A) (syn_cvv))) (.classMem (syn_cima (syn_chncodecutpairfn) (syn_chncodecutinputs A)) (syn_cvv)) p0017 p0018
  have p0020 :=
    @g_syl5eqel (.classMem A (syn_cvv)) (syn_chncodecutrel A) (syn_cima (syn_chncodecutpairfn) (syn_chncodecutinputs A)) (syn_cvv) p0002 p0019
  have p0021 :=
    @g_hwnisoexg A
  have p0022 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_chncodecutrel A) (syn_cvv)) (.classMem (syn_chwniso A) (syn_cvv)) p0020 p0021
  have p0023 :=
    @g_coexg (syn_chncodecutrel A) (syn_chwniso A) (syn_cvv) (syn_cvv)
  have p0024 :=
    @g_syl (.classMem A (syn_cvv)) (syn_wa (.classMem (syn_chncodecutrel A) (syn_cvv)) (.classMem (syn_chwniso A) (syn_cvv))) (.classMem (syn_ccom (syn_chncodecutrel A) (syn_chwniso A)) (syn_cvv)) p0022 p0023
  have p0025 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_chwniso A) (syn_cvv)) (.classMem (syn_ccom (syn_chncodecutrel A) (syn_chwniso A)) (syn_cvv)) p0001 p0024
  have p0026 :=
    @g_unexg (syn_chwniso A) (syn_ccom (syn_chncodecutrel A) (syn_chwniso A)) (syn_cvv) (syn_cvv)
  have p0027 :=
    @g_syl (.classMem A (syn_cvv)) (syn_wa (.classMem (syn_chwniso A) (syn_cvv)) (.classMem (syn_ccom (syn_chncodecutrel A) (syn_chwniso A)) (syn_cvv))) (.classMem (syn_cun (syn_chwniso A) (syn_ccom (syn_chncodecutrel A) (syn_chwniso A))) (syn_cvv)) p0025 p0026
  have p0028 :=
    @g_syl5eqel (.classMem A (syn_cvv)) (syn_chncodecmpset A) (syn_cun (syn_chwniso A) (syn_ccom (syn_chncodecutrel A) (syn_chwniso A))) (syn_cvv) p0000 p0027
  exact p0028

noncomputable def g_brhncodecmpset
    (x : Var) (v : Var) (u : Var) (A : Class) (dv_A_x : x ∉ A.fv) (dv_u_x : u ≠ x) (dv_v_x : v ≠ x) :
    Nominal.NPrf (syn_wb (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wex x (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv x)) (syn_wbr (.cv x) (syn_chncodecutrel A) (.cv v)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({v} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv
  have dv_cache_0001 : x ∉ ((Class.cv u)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_u_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Class.cv v)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_v_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_chncodecutrel A)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutrel, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_chwniso A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    (by simpa [syn_chncodecmpset] using (Nominal.classEqRefl (syn_chncodecmpset A)))
  have p0001 :=
    @g_breqi (.cv u) (.cv v) (syn_chncodecmpset A) (syn_cun (syn_chwniso A) (syn_ccom (syn_chncodecutrel A) (syn_chwniso A))) p0000
  have p0002 :=
    @g_brun (.cv u) (.cv v) (syn_chwniso A) (syn_ccom (syn_chncodecutrel A) (syn_chwniso A))
  have p0003 :=
    @g_brco x (.cv u) (.cv v) (syn_chncodecutrel A) (syn_chwniso A) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0004 :=
    @g_orbi2i (syn_wbr (.cv u) (syn_ccom (syn_chncodecutrel A) (syn_chwniso A)) (.cv v)) (syn_wex x (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv x)) (syn_wbr (.cv x) (syn_chncodecutrel A) (.cv v)))) (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0003
  have p0005 :=
    @g_bitri (syn_wbr (.cv u) (syn_cun (syn_chwniso A) (syn_ccom (syn_chncodecutrel A) (syn_chwniso A))) (.cv v)) (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv u) (syn_ccom (syn_chncodecutrel A) (syn_chwniso A)) (.cv v))) (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wex x (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv x)) (syn_wbr (.cv x) (syn_chncodecutrel A) (.cv v))))) p0002 p0004
  have p0006 :=
    @g_bitri (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv u) (syn_cun (syn_chwniso A) (syn_ccom (syn_chncodecutrel A) (syn_chwniso A))) (.cv v)) (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wex x (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv x)) (syn_wbr (.cv x) (syn_chncodecutrel A) (.cv v))))) p0001 p0005
  exact p0006

noncomputable def g_hncodecutinputmemi
    (x : Var) (A : Class) (D : Class) (R : Class) (dv_A_R : Disjoint A.fv R.fv) (hyp_hncodecutinputmemi_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_hncodecutinputmemi_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D)) (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_chncodecutinputs A))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ D.fv ∪ R.fv
  have p0000 :=
    @g_opex R D hyp_hncodecutinputmemi_1 hyp_hncodecutinputmemi_2
  have p0001 :=
    @g_snid (syn_cop R D) p0000
  have p0002 :=
    @g_a1i (.classMem (syn_cop R D) (syn_csn (syn_cop R D))) (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D)) p0001
  have p0003 :=
    @g_simpr (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D)
  have p0004 :=
    @g_snelpw1 (.cv x) D
  have p0005 :=
    @g_sylibr (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D)) (.classMem (.cv x) D) (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) p0003 p0004
  have p0006 :=
    @g_jca (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D)) (.classMem (syn_cop R D) (syn_csn (syn_cop R D))) (.classMem (syn_csn (.cv x)) (syn_cpw1 D)) p0002 p0005
  have p0007 :=
    @g_opelxp (syn_cop R D) (syn_csn (.cv x)) (syn_csn (syn_cop R D)) (syn_cpw1 D)
  have p0008 :=
    @g_sylibr (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D)) (syn_wa (.classMem (syn_cop R D) (syn_csn (syn_cop R D))) (.classMem (syn_csn (.cv x)) (syn_cpw1 D))) (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))) p0006 p0007
  have p0009 :=
    @g_lnpwquoinputfnval D R hyp_hncodecutinputmemi_1 hyp_hncodecutinputmemi_2
  have p0010 :=
    @g_a1i (.classEq (syn_cfv (syn_clnpwquoinputfn) (syn_csn (syn_cop R D))) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))) (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D)) p0009
  have p0011 :=
    @g_simpl (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D)
  have p0012 :=
    @g_snelpw1 (syn_cop R D) (syn_chwcn A)
  have p0013 :=
    @g_sylibr (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D)) (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (syn_csn (syn_cop R D)) (syn_cpw1 (syn_chwcn A))) p0011 p0012
  have p0014 :=
    @g_lnpwquoinputfnfn
  have p0015 :=
    @g_fnfun (syn_cvv) (syn_clnpwquoinputfn)
  have p0016 :=
    Nominal.mp p0014 p0015
  have p0017 :=
    @g_snex (syn_cop R D)
  have p0018 :=
    @g_lnpwquoinputfnfn
  have p0019 :=
    @g_fndm (syn_cvv) (syn_clnpwquoinputfn)
  have p0020 :=
    Nominal.mp p0018 p0019
  have p0021 :=
    @g_eleqtrri (syn_csn (syn_cop R D)) (syn_cvv) (syn_cdm (syn_clnpwquoinputfn)) p0017 p0020
  have p0022 :=
    @g_pm3_2i (syn_wfun (syn_clnpwquoinputfn)) (.classMem (syn_csn (syn_cop R D)) (syn_cdm (syn_clnpwquoinputfn))) p0016 p0021
  have p0023 :=
    @g_funfvima (syn_cpw1 (syn_chwcn A)) (syn_csn (syn_cop R D)) (syn_clnpwquoinputfn)
  have p0024 :=
    Nominal.mp p0022 p0023
  have p0025 :=
    @g_syl (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D)) (.classMem (syn_csn (syn_cop R D)) (syn_cpw1 (syn_chwcn A))) (.classMem (syn_cfv (syn_clnpwquoinputfn) (syn_csn (syn_cop R D))) (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A)))) p0013 p0024
  have p0026 :=
    @g_eqeltrrd (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D)) (syn_cfv (syn_clnpwquoinputfn) (syn_csn (syn_cop R D))) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)) (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A))) p0010 p0025
  have p0027 :=
    @g_jca (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D)) (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))) (.classMem (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)) (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A)))) p0008 p0026
  have p0028 :=
    @g_elunii (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)) (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A)))
  have p0029 :=
    @g_syl (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D)) (syn_wa (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))) (.classMem (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)) (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A))))) (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cuni (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A))))) p0027 p0028
  have p0030 :=
    (by simpa [syn_chncodecutinputs] using (Nominal.classEqRefl (syn_chncodecutinputs A)))
  have p0031 :=
    @g_a1i (.classEq (syn_chncodecutinputs A) (syn_cuni (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A))))) (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D)) p0030
  have p0032 :=
    @g_eleqtrrd (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D)) (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cuni (syn_cima (syn_clnpwquoinputfn) (syn_cpw1 (syn_chwcn A)))) (syn_chncodecutinputs A) p0029 p0031
  exact p0032

noncomputable def g_hncodecutreledgei
    (x : Var) (A : Class) (D : Class) (R : Class) (dv_A_R : Disjoint A.fv R.fv) (hyp_hncodecutreledgei_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_hncodecutreledgei_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D)) (syn_wbr (syn_chnwcutcode R D (.cv x)) (syn_chncodecutrel A) (syn_cop R D))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ A.fv ∪ D.fv ∪ R.fv
  have dv_cache_0001 : Disjoint (A).fv (R).fv := by
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have p0000 :=
    @g_hncodecutpairfnval x D R hyp_hncodecutreledgei_1 hyp_hncodecutreledgei_2
  have p0001 :=
    @g_a1i (.classEq (syn_cfv (syn_chncodecutpairfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop (syn_chnwcutcode R D (.cv x)) (syn_cop R D))) (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D)) p0000
  have p0002 :=
    @g_hncodecutinputmemi x A D R dv_cache_0001 hyp_hncodecutreledgei_1 hyp_hncodecutreledgei_2
  have p0003 :=
    @g_hncodecutpairfnfn
  have p0004 :=
    @g_fnfun (syn_cvv) (syn_chncodecutpairfn)
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_opex R D hyp_hncodecutreledgei_1 hyp_hncodecutreledgei_2
  have p0007 :=
    @g_snex (.cv x)
  have p0008 :=
    @g_opex (syn_cop R D) (syn_csn (.cv x)) p0006 p0007
  have p0009 :=
    @g_hncodecutpairfnfn
  have p0010 :=
    @g_fndm (syn_cvv) (syn_chncodecutpairfn)
  have p0011 :=
    Nominal.mp p0009 p0010
  have p0012 :=
    @g_eleqtrri (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cvv) (syn_cdm (syn_chncodecutpairfn)) p0008 p0011
  have p0013 :=
    @g_pm3_2i (syn_wfun (syn_chncodecutpairfn)) (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_cdm (syn_chncodecutpairfn))) p0005 p0012
  have p0014 :=
    @g_funfvima (syn_chncodecutinputs A) (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_chncodecutpairfn)
  have p0015 :=
    Nominal.mp p0013 p0014
  have p0016 :=
    @g_syl (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D)) (.classMem (syn_cop (syn_cop R D) (syn_csn (.cv x))) (syn_chncodecutinputs A)) (.classMem (syn_cfv (syn_chncodecutpairfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cima (syn_chncodecutpairfn) (syn_chncodecutinputs A))) p0002 p0015
  have p0017 :=
    @g_eqeltrrd (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D)) (syn_cfv (syn_chncodecutpairfn) (syn_cop (syn_cop R D) (syn_csn (.cv x)))) (syn_cop (syn_chnwcutcode R D (.cv x)) (syn_cop R D)) (syn_cima (syn_chncodecutpairfn) (syn_chncodecutinputs A)) p0001 p0016
  have p0018 :=
    (by simpa [syn_chncodecutrel] using (Nominal.classEqRefl (syn_chncodecutrel A)))
  have p0019 :=
    @g_a1i (.classEq (syn_chncodecutrel A) (syn_cima (syn_chncodecutpairfn) (syn_chncodecutinputs A))) (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D)) p0018
  have p0020 :=
    @g_eleqtrrd (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D)) (syn_cop (syn_chnwcutcode R D (.cv x)) (syn_cop R D)) (syn_cima (syn_chncodecutpairfn) (syn_chncodecutinputs A)) (syn_chncodecutrel A) p0017 p0019
  have p0021 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (syn_chnwcutcode R D (.cv x)) (syn_chncodecutrel A) (syn_cop R D))))
  have p0022 :=
    @g_sylibr (syn_wa (.classMem (syn_cop R D) (syn_chwcn A)) (.classMem (.cv x) D)) (.classMem (syn_cop (syn_chnwcutcode R D (.cv x)) (syn_cop R D)) (syn_chncodecutrel A)) (syn_wbr (syn_chnwcutcode R D (.cv x)) (syn_chncodecutrel A) (syn_cop R D)) p0020 p0021
  exact p0022

noncomputable def g_lnpwquoinputfnvalhwcn
    (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf (.imp (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cfv (syn_clnpwquoinputfn) (syn_csn (.cv u))) (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))) := by
  let proofSupport : Finset Var := ({u} : Finset Var) ∪ A.fv
  have p0000 :=
    @g_hwcnpair u A
  have p0001 :=
    @g_sneqd (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) p0000
  have p0002 :=
    @g_fveq2d (.classMem (.cv u) (syn_chwcn A)) (syn_csn (.cv u)) (syn_csn (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (syn_clnpwquoinputfn) p0001
  have p0003 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0004 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0005 :=
    @g_lnpwquoinputfnval (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) p0003 p0004
  have p0006 :=
    @g_a1i (.classEq (syn_cfv (syn_clnpwquoinputfn) (syn_csn (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (syn_cxp (syn_csn (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classMem (.cv u) (syn_chwcn A)) p0005
  have p0007 :=
    @g_hwcnpair u A
  have p0008 :=
    @g_sneqd (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) p0007
  have p0009 :=
    @g_xpeq1d (.classMem (.cv u) (syn_chwcn A)) (syn_csn (.cv u)) (syn_csn (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))) p0008
  have p0010 :=
    @g_eqcomd (.classMem (.cv u) (syn_chwcn A)) (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_cxp (syn_csn (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) p0009
  have p0011 :=
    @g_n_3eqtrd (.classMem (.cv u) (syn_chwcn A)) (syn_cfv (syn_clnpwquoinputfn) (syn_csn (.cv u))) (syn_cfv (syn_clnpwquoinputfn) (syn_csn (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) (syn_cxp (syn_csn (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_cxp (syn_csn (.cv u)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) p0002 p0006 p0010
  exact p0011

noncomputable def g_hncodeinputproductdecode
    (x : Var) (u : Var) (D : Class) (p : Var) (dv_D_x : x ∉ D.fv) (dv_p_x : p ≠ x) (dv_u_x : u ≠ x) :
    Nominal.NPrf (.imp (.classMem (.cv p) (syn_cxp (syn_csn (.cv u)) (syn_cpw1 D))) (syn_wrex x D (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({u} : Finset Var) ∪ D.fv ∪ ({p} : Finset Var)
  let s : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  have fresh_s : s ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_s_ne_x : s ≠ x := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_s : x ≠ s :=
    Ne.symm fresh_s_ne_x
  have fresh_s_ne_u : s ≠ u := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_s : u ≠ s :=
    Ne.symm fresh_s_ne_u
  have fresh_s_not_D : s ∉ D.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_s_ne_p : s ≠ p := by
    intro h
    exact fresh_s (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_s : p ≠ s :=
    Ne.symm fresh_s_ne_p
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_w_ne_u : w ≠ u := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_w : u ≠ w :=
    Ne.symm fresh_w_ne_u
  have fresh_w_not_D : w ∉ D.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_ne_p : w ≠ p := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_w : p ≠ w :=
    Ne.symm fresh_w_ne_p
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y :=
    Ne.symm fresh_y_ne_x
  have fresh_y_ne_u : y ≠ u := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_y : u ≠ y :=
    Ne.symm fresh_y_ne_u
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_p : y ≠ p := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_y : p ≠ y :=
    Ne.symm fresh_y_ne_p
  have fresh_s_ne_w : s ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_w_ne_s : w ≠ s :=
    Ne.symm fresh_s_ne_w
  have fresh_s_ne_y : s ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_s : y ≠ s :=
    Ne.symm fresh_s_ne_y
  have fresh_w_ne_y : w ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_w : y ≠ w :=
    Ne.symm fresh_w_ne_y
  have dv_cache_0001 : w ∉ ((Class.cv p)).fv := by
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : s ∉ ((Class.cv p)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : w ∉ ((syn_csn (.cv u))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : s ∉ ((syn_csn (.cv u))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : w ∉ ((syn_cpw1 D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : s ∉ ((syn_cpw1 D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : w ≠ s := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show w ≠ s from (by exact fresh_w_ne_s))
  have dv_cache_0008 : s ∉ ((Wff.classEq (.cv w) (.cv u))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_ne_w, fresh_s_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : w ∉ ((Class.cv u)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : w ∉ ((syn_wrex s (syn_cpw1 D) (.classEq (.cv p) (syn_cop (.cv u) (.cv s))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_D, fresh_w_ne_p, fresh_w_ne_u, fresh_w_ne_s, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((Class.cv s)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_s, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : x ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ ((Wff.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_p_x), (Ne.symm dv_u_x), fresh_x_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : y ∉ ((Wff.imp (.classEq (.cv p) (syn_cop (.cv u) (.cv s))) (syn_wrex x D (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_p, fresh_y_ne_u, fresh_y_ne_s, fresh_y_not_D, fresh_y_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : s ∉ ((syn_wrex x D (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_D, fresh_s_ne_p, fresh_s_ne_u, fresh_s_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elxp2 w s (.cv p) (syn_csn (.cv u)) (syn_cpw1 D) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 :=
    @g_vex u
  have p0002 :=
    @g_id (.classEq (.cv w) (.cv u))
  have p0003 :=
    @g_opeq1d (.classEq (.cv w) (.cv u)) (.cv w) (.cv u) (.cv s) p0002
  have p0004 :=
    @g_eqeq2d (.classEq (.cv w) (.cv u)) (syn_cop (.cv w) (.cv s)) (syn_cop (.cv u) (.cv s)) (.cv p) p0003
  have p0005 :=
    @g_rexbidv (.classEq (.cv w) (.cv u)) (.classEq (.cv p) (syn_cop (.cv w) (.cv s))) (.classEq (.cv p) (syn_cop (.cv u) (.cv s))) s (syn_cpw1 D) dv_cache_0008 p0004
  have p0006 :=
    @g_rexsn (syn_wrex s (syn_cpw1 D) (.classEq (.cv p) (syn_cop (.cv w) (.cv s)))) (syn_wrex s (syn_cpw1 D) (.classEq (.cv p) (syn_cop (.cv u) (.cv s)))) w (.cv u) dv_cache_0009 dv_cache_0010 p0001 p0005
  have p0007 :=
    @g_biimpi (syn_wrex w (syn_csn (.cv u)) (syn_wrex s (syn_cpw1 D) (.classEq (.cv p) (syn_cop (.cv w) (.cv s))))) (syn_wrex s (syn_cpw1 D) (.classEq (.cv p) (syn_cop (.cv u) (.cv s)))) p0006
  have p0008 :=
    @g_sylbi (.classMem (.cv p) (syn_cxp (syn_csn (.cv u)) (syn_cpw1 D))) (syn_wrex w (syn_csn (.cv u)) (syn_wrex s (syn_cpw1 D) (.classEq (.cv p) (syn_cop (.cv w) (.cv s))))) (syn_wrex s (syn_cpw1 D) (.classEq (.cv p) (syn_cop (.cv u) (.cv s)))) p0000 p0007
  have p0009 :=
    @g_elpw1 y (.cv s) D dv_cache_0011 dv_cache_0012
  have p0010 :=
    @g_n_3simpa (.classMem (.cv y) D) (.classEq (.cv s) (syn_csn (.cv y))) (.classEq (.cv p) (syn_cop (.cv u) (.cv s)))
  have p0011 :=
    @g_simpl (.classMem (.cv y) D) (.classEq (.cv s) (syn_csn (.cv y)))
  have p0012 :=
    @g_syl (syn_w3a (.classMem (.cv y) D) (.classEq (.cv s) (syn_csn (.cv y))) (.classEq (.cv p) (syn_cop (.cv u) (.cv s)))) (syn_wa (.classMem (.cv y) D) (.classEq (.cv s) (syn_csn (.cv y)))) (.classMem (.cv y) D) p0010 p0011
  have p0013 :=
    @g_n_3simpc (.classMem (.cv y) D) (.classEq (.cv s) (syn_csn (.cv y))) (.classEq (.cv p) (syn_cop (.cv u) (.cv s)))
  have p0014 :=
    @g_simpr (.classEq (.cv s) (syn_csn (.cv y))) (.classEq (.cv p) (syn_cop (.cv u) (.cv s)))
  have p0015 :=
    @g_syl (syn_w3a (.classMem (.cv y) D) (.classEq (.cv s) (syn_csn (.cv y))) (.classEq (.cv p) (syn_cop (.cv u) (.cv s)))) (syn_wa (.classEq (.cv s) (syn_csn (.cv y))) (.classEq (.cv p) (syn_cop (.cv u) (.cv s)))) (.classEq (.cv p) (syn_cop (.cv u) (.cv s))) p0013 p0014
  have p0016 :=
    @g_n_3simpc (.classMem (.cv y) D) (.classEq (.cv s) (syn_csn (.cv y))) (.classEq (.cv p) (syn_cop (.cv u) (.cv s)))
  have p0017 :=
    @g_simpl (.classEq (.cv s) (syn_csn (.cv y))) (.classEq (.cv p) (syn_cop (.cv u) (.cv s)))
  have p0018 :=
    @g_syl (syn_w3a (.classMem (.cv y) D) (.classEq (.cv s) (syn_csn (.cv y))) (.classEq (.cv p) (syn_cop (.cv u) (.cv s)))) (syn_wa (.classEq (.cv s) (syn_csn (.cv y))) (.classEq (.cv p) (syn_cop (.cv u) (.cv s)))) (.classEq (.cv s) (syn_csn (.cv y))) p0016 p0017
  have p0019 :=
    @g_opeq2d (syn_w3a (.classMem (.cv y) D) (.classEq (.cv s) (syn_csn (.cv y))) (.classEq (.cv p) (syn_cop (.cv u) (.cv s)))) (.cv s) (syn_csn (.cv y)) (.cv u) p0018
  have p0020 :=
    @g_eqtrd (syn_w3a (.classMem (.cv y) D) (.classEq (.cv s) (syn_csn (.cv y))) (.classEq (.cv p) (syn_cop (.cv u) (.cv s)))) (.cv p) (syn_cop (.cv u) (.cv s)) (syn_cop (.cv u) (syn_csn (.cv y))) p0015 p0019
  have p0021 :=
    @g_jca (syn_w3a (.classMem (.cv y) D) (.classEq (.cv s) (syn_csn (.cv y))) (.classEq (.cv p) (syn_cop (.cv u) (.cv s)))) (.classMem (.cv y) D) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv y)))) p0012 p0020
  have p0022 :=
    @g_id (.classEq (.cv x) (.cv y))
  have p0023 :=
    @g_sneqd (.classEq (.cv x) (.cv y)) (.cv x) (.cv y) p0022
  have p0024 :=
    @g_opeq2d (.classEq (.cv x) (.cv y)) (syn_csn (.cv x)) (syn_csn (.cv y)) (.cv u) p0023
  have p0025 :=
    @g_eqeq2d (.classEq (.cv x) (.cv y)) (syn_cop (.cv u) (syn_csn (.cv x))) (syn_cop (.cv u) (syn_csn (.cv y))) (.cv p) p0024
  have p0026 :=
    @g_rspcev (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x)))) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv y)))) x (.cv y) D dv_cache_0013 dv_cache_0014 dv_cache_0015 p0025
  have p0027 :=
    @g_syl (syn_w3a (.classMem (.cv y) D) (.classEq (.cv s) (syn_csn (.cv y))) (.classEq (.cv p) (syn_cop (.cv u) (.cv s)))) (syn_wa (.classMem (.cv y) D) (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv y))))) (syn_wrex x D (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))) p0021 p0026
  have p0028 :=
    @g_n_3exp (.classMem (.cv y) D) (.classEq (.cv s) (syn_csn (.cv y))) (.classEq (.cv p) (syn_cop (.cv u) (.cv s))) (syn_wrex x D (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))) p0027
  have p0029 :=
    @g_rexlimiv (.classEq (.cv s) (syn_csn (.cv y))) (.imp (.classEq (.cv p) (syn_cop (.cv u) (.cv s))) (syn_wrex x D (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x)))))) y D dv_cache_0016 p0028
  have p0030 :=
    @g_sylbi (.classMem (.cv s) (syn_cpw1 D)) (syn_wrex y D (.classEq (.cv s) (syn_csn (.cv y)))) (.imp (.classEq (.cv p) (syn_cop (.cv u) (.cv s))) (syn_wrex x D (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x)))))) p0009 p0029
  have p0031 :=
    @g_rexlimiv (.classEq (.cv p) (syn_cop (.cv u) (.cv s))) (syn_wrex x D (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))) s (syn_cpw1 D) dv_cache_0017 p0030
  have p0032 :=
    @g_syl (.classMem (.cv p) (syn_cxp (syn_csn (.cv u)) (syn_cpw1 D))) (syn_wrex s (syn_cpw1 D) (.classEq (.cv p) (syn_cop (.cv u) (.cv s)))) (syn_wrex x D (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))) p0008 p0031
  exact p0032

#print axioms g_hncodeinputproductdecode

end NFChoice.DirectNominalPrf.WPPReplay
