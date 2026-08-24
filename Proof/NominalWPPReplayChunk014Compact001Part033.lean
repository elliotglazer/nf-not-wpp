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
import NominalWPPReplayChunk014Compact001Part032

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

noncomputable def g_hwtrnfn
     :
    Nominal.NPrf (syn_wfn (syn_chwtrn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_composefn
  have p0001 :=
    @g_composefn
  have p0002 :=
    @g_n_1stfo
  have p0003 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0004 :=
    Nominal.mp p0002 p0003
  have p0005 :=
    @g_n_2ndfo
  have p0006 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0004 p0007
  have p0009 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_c2nd)
  have p0010 :=
    Nominal.mp p0008 p0009
  have p0011 :=
    @g_inidm (syn_cvv)
  have p0012 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c1st) (syn_c2nd)) p0011
  have p0013 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c1st) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c1st) (syn_c2nd)) (syn_cvv)) p0010 p0012
  have p0014 :=
    @g_ssv (syn_crn (syn_ctxp (syn_c1st) (syn_c2nd)))
  have p0015 :=
    @g_n_3pm3_2i (syn_wfn (syn_ccompose) (syn_cvv)) (syn_wfn (syn_ctxp (syn_c1st) (syn_c2nd)) (syn_cvv)) (syn_wss (syn_crn (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_cvv)) p0001 p0013 p0014
  have p0016 :=
    @g_fnco (syn_cvv) (syn_cvv) (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))
  have p0017 :=
    Nominal.mp p0015 p0016
  have p0018 :=
    @g_imageswapfn
  have p0019 :=
    @g_n_1stfo
  have p0020 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0021 :=
    Nominal.mp p0019 p0020
  have p0022 :=
    @g_ssv (syn_crn (syn_c1st))
  have p0023 :=
    @g_n_3pm3_2i (syn_wfn (syn_cimage (syn_cswap)) (syn_cvv)) (syn_wfn (syn_c1st) (syn_cvv)) (syn_wss (syn_crn (syn_c1st)) (syn_cvv)) p0018 p0021 p0022
  have p0024 :=
    @g_fnco (syn_cvv) (syn_cvv) (syn_cimage (syn_cswap)) (syn_c1st)
  have p0025 :=
    Nominal.mp p0023 p0024
  have p0026 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cvv)) p0017 p0025
  have p0027 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))
  have p0028 :=
    Nominal.mp p0026 p0027
  have p0029 :=
    @g_inidm (syn_cvv)
  have p0030 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) p0029
  have p0031 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) (syn_cvv)) p0028 p0030
  have p0032 :=
    @g_ssv (syn_crn (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))))
  have p0033 :=
    @g_n_3pm3_2i (syn_wfn (syn_ccompose) (syn_cvv)) (syn_wfn (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) (syn_cvv)) (syn_wss (syn_crn (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))) (syn_cvv)) p0000 p0031 p0032
  have p0034 :=
    @g_fnco (syn_cvv) (syn_cvv) (syn_ccompose) (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))
  have p0035 :=
    Nominal.mp p0033 p0034
  have p0036 :=
    (by simpa [syn_chwtrn] using (Nominal.classEqRefl (syn_chwtrn)))
  have p0037 :=
    @g_fneq1i (syn_cvv) (syn_chwtrn) (syn_ccom (syn_ccompose) (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))) p0036
  have p0038 :=
    @g_bicomi (syn_wfn (syn_chwtrn) (syn_cvv)) (syn_wfn (syn_ccom (syn_ccompose) (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))) (syn_cvv)) p0037
  have p0039 :=
    @g_mpbi (syn_wfn (syn_ccom (syn_ccompose) (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))) (syn_cvv)) (syn_wfn (syn_chwtrn) (syn_cvv)) p0035 p0038
  exact p0039

noncomputable def g_hwtrnval
    (R : Class) (f : Var) (hyp_hwtrnval_1 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_chwtrn) (syn_cop (.cv f) R)) (syn_ccom (syn_ccom (.cv f) R) (syn_ccnv (.cv f)))) := by
  let proofSupport : Finset Var := R.fv ∪ ({f} : Finset Var)
  have p0000 :=
    (by simpa [syn_chwtrn] using (Nominal.classEqRefl (syn_chwtrn)))
  have p0001 :=
    @g_fveq1i (syn_cop (.cv f) R) (syn_chwtrn) (syn_ccom (syn_ccompose) (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))) p0000
  have p0002 :=
    @g_composefn
  have p0003 :=
    @g_n_1stfo
  have p0004 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_n_2ndfo
  have p0007 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0005 p0008
  have p0010 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_c2nd)
  have p0011 :=
    Nominal.mp p0009 p0010
  have p0012 :=
    @g_inidm (syn_cvv)
  have p0013 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c1st) (syn_c2nd)) p0012
  have p0014 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c1st) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c1st) (syn_c2nd)) (syn_cvv)) p0011 p0013
  have p0015 :=
    @g_ssv (syn_crn (syn_ctxp (syn_c1st) (syn_c2nd)))
  have p0016 :=
    @g_n_3pm3_2i (syn_wfn (syn_ccompose) (syn_cvv)) (syn_wfn (syn_ctxp (syn_c1st) (syn_c2nd)) (syn_cvv)) (syn_wss (syn_crn (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_cvv)) p0002 p0014 p0015
  have p0017 :=
    @g_fnco (syn_cvv) (syn_cvv) (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))
  have p0018 :=
    Nominal.mp p0016 p0017
  have p0019 :=
    @g_imageswapfn
  have p0020 :=
    @g_n_1stfo
  have p0021 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0022 :=
    Nominal.mp p0020 p0021
  have p0023 :=
    @g_ssv (syn_crn (syn_c1st))
  have p0024 :=
    @g_n_3pm3_2i (syn_wfn (syn_cimage (syn_cswap)) (syn_cvv)) (syn_wfn (syn_c1st) (syn_cvv)) (syn_wss (syn_crn (syn_c1st)) (syn_cvv)) p0019 p0022 p0023
  have p0025 :=
    @g_fnco (syn_cvv) (syn_cvv) (syn_cimage (syn_cswap)) (syn_c1st)
  have p0026 :=
    Nominal.mp p0024 p0025
  have p0027 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cvv)) p0018 p0026
  have p0028 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))
  have p0029 :=
    Nominal.mp p0027 p0028
  have p0030 :=
    @g_inidm (syn_cvv)
  have p0031 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) p0030
  have p0032 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) (syn_cvv)) p0029 p0031
  have p0033 :=
    @g_vex f
  have p0034 :=
    @g_opex (.cv f) R p0033 hyp_hwtrnval_1
  have p0035 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) (syn_cvv)) (.classMem (syn_cop (.cv f) R) (syn_cvv)) p0032 p0034
  have p0036 :=
    @g_fvco2 (syn_cvv) (syn_cop (.cv f) R) (syn_ccompose) (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))
  have p0037 :=
    Nominal.mp p0035 p0036
  have p0038 :=
    @g_eqid (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_cop (.cv f) R))
  have p0039 :=
    @g_composefn
  have p0040 :=
    @g_n_1stfo
  have p0041 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0042 :=
    Nominal.mp p0040 p0041
  have p0043 :=
    @g_n_2ndfo
  have p0044 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0045 :=
    Nominal.mp p0043 p0044
  have p0046 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0042 p0045
  have p0047 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_c2nd)
  have p0048 :=
    Nominal.mp p0046 p0047
  have p0049 :=
    @g_inidm (syn_cvv)
  have p0050 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c1st) (syn_c2nd)) p0049
  have p0051 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c1st) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c1st) (syn_c2nd)) (syn_cvv)) p0048 p0050
  have p0052 :=
    @g_ssv (syn_crn (syn_ctxp (syn_c1st) (syn_c2nd)))
  have p0053 :=
    @g_n_3pm3_2i (syn_wfn (syn_ccompose) (syn_cvv)) (syn_wfn (syn_ctxp (syn_c1st) (syn_c2nd)) (syn_cvv)) (syn_wss (syn_crn (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_cvv)) p0039 p0051 p0052
  have p0054 :=
    @g_fnco (syn_cvv) (syn_cvv) (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))
  have p0055 :=
    Nominal.mp p0053 p0054
  have p0056 :=
    @g_vex f
  have p0057 :=
    @g_opex (.cv f) R p0056 hyp_hwtrnval_1
  have p0058 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_cvv)) (.classMem (syn_cop (.cv f) R) (syn_cvv)) p0055 p0057
  have p0059 :=
    @g_fnbrfvb (syn_cvv) (syn_cop (.cv f) R) (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_cop (.cv f) R)) (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd)))
  have p0060 :=
    Nominal.mp p0058 p0059
  have p0061 :=
    @g_mpbi (.classEq (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_cop (.cv f) R)) (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_cop (.cv f) R))) (syn_wbr (syn_cop (.cv f) R) (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_cop (.cv f) R))) p0038 p0060
  have p0062 :=
    @g_eqid (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cop (.cv f) R))
  have p0063 :=
    @g_imageswapfn
  have p0064 :=
    @g_n_1stfo
  have p0065 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0066 :=
    Nominal.mp p0064 p0065
  have p0067 :=
    @g_ssv (syn_crn (syn_c1st))
  have p0068 :=
    @g_n_3pm3_2i (syn_wfn (syn_cimage (syn_cswap)) (syn_cvv)) (syn_wfn (syn_c1st) (syn_cvv)) (syn_wss (syn_crn (syn_c1st)) (syn_cvv)) p0063 p0066 p0067
  have p0069 :=
    @g_fnco (syn_cvv) (syn_cvv) (syn_cimage (syn_cswap)) (syn_c1st)
  have p0070 :=
    Nominal.mp p0068 p0069
  have p0071 :=
    @g_vex f
  have p0072 :=
    @g_opex (.cv f) R p0071 hyp_hwtrnval_1
  have p0073 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cvv)) (.classMem (syn_cop (.cv f) R) (syn_cvv)) p0070 p0072
  have p0074 :=
    @g_fnbrfvb (syn_cvv) (syn_cop (.cv f) R) (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cop (.cv f) R)) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))
  have p0075 :=
    Nominal.mp p0073 p0074
  have p0076 :=
    @g_mpbi (.classEq (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cop (.cv f) R)) (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cop (.cv f) R))) (syn_wbr (syn_cop (.cv f) R) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cop (.cv f) R))) p0062 p0075
  have p0077 :=
    @g_pm3_2i (syn_wbr (syn_cop (.cv f) R) (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_cop (.cv f) R))) (syn_wbr (syn_cop (.cv f) R) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cop (.cv f) R))) p0061 p0076
  have p0078 :=
    @g_trtxp (syn_cop (.cv f) R) (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_cop (.cv f) R)) (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cop (.cv f) R)) (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))
  have p0079 :=
    @g_mpbir (syn_wbr (syn_cop (.cv f) R) (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) (syn_cop (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_cop (.cv f) R)) (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cop (.cv f) R)))) (syn_wa (syn_wbr (syn_cop (.cv f) R) (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_cop (.cv f) R))) (syn_wbr (syn_cop (.cv f) R) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cop (.cv f) R)))) p0077 p0078
  have p0080 :=
    @g_composefn
  have p0081 :=
    @g_n_1stfo
  have p0082 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0083 :=
    Nominal.mp p0081 p0082
  have p0084 :=
    @g_n_2ndfo
  have p0085 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0086 :=
    Nominal.mp p0084 p0085
  have p0087 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0083 p0086
  have p0088 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_c2nd)
  have p0089 :=
    Nominal.mp p0087 p0088
  have p0090 :=
    @g_inidm (syn_cvv)
  have p0091 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c1st) (syn_c2nd)) p0090
  have p0092 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c1st) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c1st) (syn_c2nd)) (syn_cvv)) p0089 p0091
  have p0093 :=
    @g_ssv (syn_crn (syn_ctxp (syn_c1st) (syn_c2nd)))
  have p0094 :=
    @g_n_3pm3_2i (syn_wfn (syn_ccompose) (syn_cvv)) (syn_wfn (syn_ctxp (syn_c1st) (syn_c2nd)) (syn_cvv)) (syn_wss (syn_crn (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_cvv)) p0080 p0092 p0093
  have p0095 :=
    @g_fnco (syn_cvv) (syn_cvv) (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))
  have p0096 :=
    Nominal.mp p0094 p0095
  have p0097 :=
    @g_imageswapfn
  have p0098 :=
    @g_n_1stfo
  have p0099 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0100 :=
    Nominal.mp p0098 p0099
  have p0101 :=
    @g_ssv (syn_crn (syn_c1st))
  have p0102 :=
    @g_n_3pm3_2i (syn_wfn (syn_cimage (syn_cswap)) (syn_cvv)) (syn_wfn (syn_c1st) (syn_cvv)) (syn_wss (syn_crn (syn_c1st)) (syn_cvv)) p0097 p0100 p0101
  have p0103 :=
    @g_fnco (syn_cvv) (syn_cvv) (syn_cimage (syn_cswap)) (syn_c1st)
  have p0104 :=
    Nominal.mp p0102 p0103
  have p0105 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cvv)) p0096 p0104
  have p0106 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))
  have p0107 :=
    Nominal.mp p0105 p0106
  have p0108 :=
    @g_inidm (syn_cvv)
  have p0109 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) p0108
  have p0110 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) (syn_cvv)) p0107 p0109
  have p0111 :=
    @g_fnfun (syn_cvv) (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))
  have p0112 :=
    Nominal.mp p0110 p0111
  have p0113 :=
    @g_funbrfv (syn_cop (.cv f) R) (syn_cop (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_cop (.cv f) R)) (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cop (.cv f) R))) (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))
  have p0114 :=
    Nominal.mp p0112 p0113
  have p0115 :=
    Nominal.mp p0079 p0114
  have p0116 :=
    @g_n_1stfo
  have p0117 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0118 :=
    Nominal.mp p0116 p0117
  have p0119 :=
    @g_n_2ndfo
  have p0120 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0121 :=
    Nominal.mp p0119 p0120
  have p0122 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0118 p0121
  have p0123 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_c2nd)
  have p0124 :=
    Nominal.mp p0122 p0123
  have p0125 :=
    @g_inidm (syn_cvv)
  have p0126 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c1st) (syn_c2nd)) p0125
  have p0127 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c1st) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c1st) (syn_c2nd)) (syn_cvv)) p0124 p0126
  have p0128 :=
    @g_vex f
  have p0129 :=
    @g_opex (.cv f) R p0128 hyp_hwtrnval_1
  have p0130 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_c1st) (syn_c2nd)) (syn_cvv)) (.classMem (syn_cop (.cv f) R) (syn_cvv)) p0127 p0129
  have p0131 :=
    @g_fvco2 (syn_cvv) (syn_cop (.cv f) R) (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))
  have p0132 :=
    Nominal.mp p0130 p0131
  have p0133 :=
    @g_eqid (syn_cfv (syn_c1st) (syn_cop (.cv f) R))
  have p0134 :=
    @g_n_1stfo
  have p0135 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0136 :=
    Nominal.mp p0134 p0135
  have p0137 :=
    @g_vex f
  have p0138 :=
    @g_opex (.cv f) R p0137 hyp_hwtrnval_1
  have p0139 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (.classMem (syn_cop (.cv f) R) (syn_cvv)) p0136 p0138
  have p0140 :=
    @g_fnbrfvb (syn_cvv) (syn_cop (.cv f) R) (syn_cfv (syn_c1st) (syn_cop (.cv f) R)) (syn_c1st)
  have p0141 :=
    Nominal.mp p0139 p0140
  have p0142 :=
    @g_mpbi (.classEq (syn_cfv (syn_c1st) (syn_cop (.cv f) R)) (syn_cfv (syn_c1st) (syn_cop (.cv f) R))) (syn_wbr (syn_cop (.cv f) R) (syn_c1st) (syn_cfv (syn_c1st) (syn_cop (.cv f) R))) p0133 p0141
  have p0143 :=
    @g_eqid (syn_cfv (syn_c2nd) (syn_cop (.cv f) R))
  have p0144 :=
    @g_n_2ndfo
  have p0145 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0146 :=
    Nominal.mp p0144 p0145
  have p0147 :=
    @g_vex f
  have p0148 :=
    @g_opex (.cv f) R p0147 hyp_hwtrnval_1
  have p0149 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (.classMem (syn_cop (.cv f) R) (syn_cvv)) p0146 p0148
  have p0150 :=
    @g_fnbrfvb (syn_cvv) (syn_cop (.cv f) R) (syn_cfv (syn_c2nd) (syn_cop (.cv f) R)) (syn_c2nd)
  have p0151 :=
    Nominal.mp p0149 p0150
  have p0152 :=
    @g_mpbi (.classEq (syn_cfv (syn_c2nd) (syn_cop (.cv f) R)) (syn_cfv (syn_c2nd) (syn_cop (.cv f) R))) (syn_wbr (syn_cop (.cv f) R) (syn_c2nd) (syn_cfv (syn_c2nd) (syn_cop (.cv f) R))) p0143 p0151
  have p0153 :=
    @g_pm3_2i (syn_wbr (syn_cop (.cv f) R) (syn_c1st) (syn_cfv (syn_c1st) (syn_cop (.cv f) R))) (syn_wbr (syn_cop (.cv f) R) (syn_c2nd) (syn_cfv (syn_c2nd) (syn_cop (.cv f) R))) p0142 p0152
  have p0154 :=
    @g_trtxp (syn_cop (.cv f) R) (syn_cfv (syn_c1st) (syn_cop (.cv f) R)) (syn_cfv (syn_c2nd) (syn_cop (.cv f) R)) (syn_c1st) (syn_c2nd)
  have p0155 :=
    @g_mpbir (syn_wbr (syn_cop (.cv f) R) (syn_ctxp (syn_c1st) (syn_c2nd)) (syn_cop (syn_cfv (syn_c1st) (syn_cop (.cv f) R)) (syn_cfv (syn_c2nd) (syn_cop (.cv f) R)))) (syn_wa (syn_wbr (syn_cop (.cv f) R) (syn_c1st) (syn_cfv (syn_c1st) (syn_cop (.cv f) R))) (syn_wbr (syn_cop (.cv f) R) (syn_c2nd) (syn_cfv (syn_c2nd) (syn_cop (.cv f) R)))) p0153 p0154
  have p0156 :=
    @g_n_1stfo
  have p0157 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0158 :=
    Nominal.mp p0156 p0157
  have p0159 :=
    @g_n_2ndfo
  have p0160 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0161 :=
    Nominal.mp p0159 p0160
  have p0162 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0158 p0161
  have p0163 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_c2nd)
  have p0164 :=
    Nominal.mp p0162 p0163
  have p0165 :=
    @g_inidm (syn_cvv)
  have p0166 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c1st) (syn_c2nd)) p0165
  have p0167 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c1st) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c1st) (syn_c2nd)) (syn_cvv)) p0164 p0166
  have p0168 :=
    @g_fnfun (syn_cvv) (syn_ctxp (syn_c1st) (syn_c2nd))
  have p0169 :=
    Nominal.mp p0167 p0168
  have p0170 :=
    @g_funbrfv (syn_cop (.cv f) R) (syn_cop (syn_cfv (syn_c1st) (syn_cop (.cv f) R)) (syn_cfv (syn_c2nd) (syn_cop (.cv f) R))) (syn_ctxp (syn_c1st) (syn_c2nd))
  have p0171 :=
    Nominal.mp p0169 p0170
  have p0172 :=
    Nominal.mp p0155 p0171
  have p0173 :=
    @g_vex f
  have p0174 :=
    @g_opfv1st (.cv f) R p0173 hyp_hwtrnval_1
  have p0175 :=
    @g_vex f
  have p0176 :=
    @g_opfv2nd (.cv f) R p0175 hyp_hwtrnval_1
  have p0177 :=
    @g_opeq12i (syn_cfv (syn_c1st) (syn_cop (.cv f) R)) (.cv f) (syn_cfv (syn_c2nd) (syn_cop (.cv f) R)) R p0174 p0176
  have p0178 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_c1st) (syn_c2nd)) (syn_cop (.cv f) R)) (syn_cop (syn_cfv (syn_c1st) (syn_cop (.cv f) R)) (syn_cfv (syn_c2nd) (syn_cop (.cv f) R))) (syn_cop (.cv f) R) p0172 p0177
  have p0179 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_c1st) (syn_c2nd)) (syn_cop (.cv f) R)) (syn_cop (.cv f) R) (syn_ccompose) p0178
  have p0180 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_cop (.cv f) R)) (syn_cfv (syn_ccompose) (syn_cfv (syn_ctxp (syn_c1st) (syn_c2nd)) (syn_cop (.cv f) R))) (syn_cfv (syn_ccompose) (syn_cop (.cv f) R)) p0132 p0179
  have p0181 :=
    (by simpa [syn_co] using (Nominal.classEqRefl (syn_co (.cv f) (syn_ccompose) R)))
  have p0182 :=
    @g_vex f
  have p0183 :=
    @g_pm3_2i (.classMem (.cv f) (syn_cvv)) (.classMem R (syn_cvv)) p0182 hyp_hwtrnval_1
  have p0184 :=
    @g_composevalg (.cv f) R (syn_cvv) (syn_cvv)
  have p0185 :=
    Nominal.mp p0183 p0184
  have p0186 :=
    @g_eqtr3i (syn_co (.cv f) (syn_ccompose) R) (syn_cfv (syn_ccompose) (syn_cop (.cv f) R)) (syn_ccom (.cv f) R) p0181 p0185
  have p0187 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_cop (.cv f) R)) (syn_cfv (syn_ccompose) (syn_cop (.cv f) R)) (syn_ccom (.cv f) R) p0180 p0186
  have p0188 :=
    @g_n_1stfo
  have p0189 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0190 :=
    Nominal.mp p0188 p0189
  have p0191 :=
    @g_vex f
  have p0192 :=
    @g_opex (.cv f) R p0191 hyp_hwtrnval_1
  have p0193 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (.classMem (syn_cop (.cv f) R) (syn_cvv)) p0190 p0192
  have p0194 :=
    @g_fvco2 (syn_cvv) (syn_cop (.cv f) R) (syn_cimage (syn_cswap)) (syn_c1st)
  have p0195 :=
    Nominal.mp p0193 p0194
  have p0196 :=
    @g_vex f
  have p0197 :=
    @g_opfv1st (.cv f) R p0196 hyp_hwtrnval_1
  have p0198 :=
    @g_fveq2i (syn_cfv (syn_c1st) (syn_cop (.cv f) R)) (.cv f) (syn_cimage (syn_cswap)) p0197
  have p0199 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cop (.cv f) R)) (syn_cfv (syn_cimage (syn_cswap)) (syn_cfv (syn_c1st) (syn_cop (.cv f) R))) (syn_cfv (syn_cimage (syn_cswap)) (.cv f)) p0195 p0198
  have p0200 :=
    @g_imageswapval f
  have p0201 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cop (.cv f) R)) (syn_cfv (syn_cimage (syn_cswap)) (.cv f)) (syn_ccnv (.cv f)) p0199 p0200
  have p0202 :=
    @g_opeq12i (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_cop (.cv f) R)) (syn_ccom (.cv f) R) (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cop (.cv f) R)) (syn_ccnv (.cv f)) p0187 p0201
  have p0203 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) (syn_cop (.cv f) R)) (syn_cop (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_cop (.cv f) R)) (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)) (syn_cop (.cv f) R))) (syn_cop (syn_ccom (.cv f) R) (syn_ccnv (.cv f))) p0115 p0202
  have p0204 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) (syn_cop (.cv f) R)) (syn_cop (syn_ccom (.cv f) R) (syn_ccnv (.cv f))) (syn_ccompose) p0203
  have p0205 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))) (syn_cop (.cv f) R)) (syn_cfv (syn_ccompose) (syn_cfv (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st))) (syn_cop (.cv f) R))) (syn_cfv (syn_ccompose) (syn_cop (syn_ccom (.cv f) R) (syn_ccnv (.cv f)))) p0037 p0204
  have p0206 :=
    (by simpa [syn_co] using (Nominal.classEqRefl (syn_co (syn_ccom (.cv f) R) (syn_ccompose) (syn_ccnv (.cv f)))))
  have p0207 :=
    @g_vex f
  have p0208 :=
    @g_coex (.cv f) R p0207 hyp_hwtrnval_1
  have p0209 :=
    @g_vex f
  have p0210 :=
    @g_cnvex (.cv f) p0209
  have p0211 :=
    @g_pm3_2i (.classMem (syn_ccom (.cv f) R) (syn_cvv)) (.classMem (syn_ccnv (.cv f)) (syn_cvv)) p0208 p0210
  have p0212 :=
    @g_composevalg (syn_ccom (.cv f) R) (syn_ccnv (.cv f)) (syn_cvv) (syn_cvv)
  have p0213 :=
    Nominal.mp p0211 p0212
  have p0214 :=
    @g_eqtr3i (syn_co (syn_ccom (.cv f) R) (syn_ccompose) (syn_ccnv (.cv f))) (syn_cfv (syn_ccompose) (syn_cop (syn_ccom (.cv f) R) (syn_ccnv (.cv f)))) (syn_ccom (syn_ccom (.cv f) R) (syn_ccnv (.cv f))) p0206 p0213
  have p0215 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))) (syn_cop (.cv f) R)) (syn_cfv (syn_ccompose) (syn_cop (syn_ccom (.cv f) R) (syn_ccnv (.cv f)))) (syn_ccom (syn_ccom (.cv f) R) (syn_ccnv (.cv f))) p0205 p0214
  have p0216 :=
    @g_eqtri (syn_cfv (syn_chwtrn) (syn_cop (.cv f) R)) (syn_cfv (syn_ccom (syn_ccompose) (syn_ctxp (syn_ccom (syn_ccompose) (syn_ctxp (syn_c1st) (syn_c2nd))) (syn_ccom (syn_cimage (syn_cswap)) (syn_c1st)))) (syn_cop (.cv f) R)) (syn_ccom (syn_ccom (.cv f) R) (syn_ccnv (.cv f))) p0001 p0215
  exact p0216

noncomputable def g_ranfnfn
     :
    Nominal.NPrf (syn_wfn (syn_cranfn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have dv_cache_0001 : x ∉ ((syn_cvv)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_vex x
  have p0001 :=
    @g_rnex (.cv x) p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ranfn x
  have p0003 :=
    @g_fnmpti x (syn_cvv) (syn_crn (.cv x)) (syn_cranfn) dv_cache_0001 p0001 p0002
  exact p0003

noncomputable def g_hwgenfn
     :
    Nominal.NPrf (syn_wfn (syn_chwgen) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have dv_cache_0001 : x ∉ ((syn_cvv)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_n_2ndfo
  have p0001 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_vex x
  have p0004 :=
    @g_dmex (.cv x) p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_domfn x
  have p0006 :=
    @g_fnmpti x (syn_cvv) (syn_cdm (.cv x)) (syn_cdomfn) dv_cache_0001 p0004 p0005
  have p0007 :=
    @g_n_1stfo
  have p0008 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_ssv (syn_crn (syn_c1st))
  have p0011 :=
    @g_n_3pm3_2i (syn_wfn (syn_cdomfn) (syn_cvv)) (syn_wfn (syn_c1st) (syn_cvv)) (syn_wss (syn_crn (syn_c1st)) (syn_cvv)) p0006 p0009 p0010
  have p0012 :=
    @g_fnco (syn_cvv) (syn_cvv) (syn_cdomfn) (syn_c1st)
  have p0013 :=
    Nominal.mp p0011 p0012
  have p0014 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (syn_wfn (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cvv)) p0002 p0013
  have p0015 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))
  have p0016 :=
    Nominal.mp p0014 p0015
  have p0017 :=
    @g_inidm (syn_cvv)
  have p0018 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) p0017
  have p0019 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cvv)) p0016 p0018
  have p0020 :=
    @g_hwtrnfn
  have p0021 :=
    @g_vex x
  have p0022 :=
    @g_rnex (.cv x) p0021
  have p0023 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ranfn x
  have p0024 :=
    @g_fnmpti x (syn_cvv) (syn_crn (.cv x)) (syn_cranfn) dv_cache_0001 p0022 p0023
  have p0025 :=
    @g_n_1stfo
  have p0026 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0027 :=
    Nominal.mp p0025 p0026
  have p0028 :=
    @g_ssv (syn_crn (syn_c1st))
  have p0029 :=
    @g_n_3pm3_2i (syn_wfn (syn_cranfn) (syn_cvv)) (syn_wfn (syn_c1st) (syn_cvv)) (syn_wss (syn_crn (syn_c1st)) (syn_cvv)) p0024 p0027 p0028
  have p0030 :=
    @g_fnco (syn_cvv) (syn_cvv) (syn_cranfn) (syn_c1st)
  have p0031 :=
    Nominal.mp p0029 p0030
  have p0032 :=
    @g_pm3_2i (syn_wfn (syn_chwtrn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cvv)) p0020 p0031
  have p0033 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))
  have p0034 :=
    Nominal.mp p0032 p0033
  have p0035 :=
    @g_inidm (syn_cvv)
  have p0036 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) p0035
  have p0037 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cvv)) p0034 p0036
  have p0038 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cvv)) (syn_wfn (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cvv)) p0019 p0037
  have p0039 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))
  have p0040 :=
    Nominal.mp p0038 p0039
  have p0041 :=
    @g_inidm (syn_cvv)
  have p0042 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))) p0041
  have p0043 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))) (syn_cvv)) p0040 p0042
  have p0044 :=
    (by simpa [syn_chwgen] using (Nominal.classEqRefl (syn_chwgen)))
  have p0045 :=
    @g_fneq1i (syn_cvv) (syn_chwgen) (syn_ctxp (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))) p0044
  have p0046 :=
    @g_bicomi (syn_wfn (syn_chwgen) (syn_cvv)) (syn_wfn (syn_ctxp (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))) (syn_cvv)) p0045
  have p0047 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))) (syn_cvv)) (syn_wfn (syn_chwgen) (syn_cvv)) p0043 p0046
  exact p0047

#print axioms g_hwgenfn

end NFChoice.DirectNominalPrf.WPPReplay
