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
import NominalWPPReplayChunk016Compact001Part049

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

noncomputable def g_hncodetrnfnvalndv
    (u : Var) (F : Class) (hyp_hncodetrnfnvalndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) (hyp_hncodetrnfnvalndv_2 : Nominal.NPrf (.classMem (.cv u) (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) := by
  let proofSupport : Finset Var := ({u} : Finset Var) ∪ F.fv
  have p0000 :=
    (by simpa [syn_chncodetrnfn] using (Nominal.classEqRefl (syn_chncodetrnfn F)))
  have p0001 :=
    @g_fveq1i (.cv u) (syn_chncodetrnfn F) (syn_ccom (syn_c2nd) (syn_ccom (syn_chwgen) (syn_ctxp (syn_chnbaseresfn F) (syn_c1st)))) p0000
  have p0002 :=
    @g_hwgenfn
  have p0003 :=
    @g_lnimageresfnfn
  have p0004 :=
    @g_fnconstg (syn_cvv) F (syn_cvv)
  have p0005 :=
    Nominal.mp hyp_hncodetrnfnvalndv_1 p0004
  have p0006 :=
    @g_ln2ndfn
  have p0007 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn F)) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0005 p0006
  have p0008 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd)
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_inidm (syn_cvv)
  have p0011 :=
    @g_eqcomi (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) p0010
  have p0012 :=
    @g_fneq2i (syn_cvv) (syn_cin (syn_cvv) (syn_cvv)) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd)) p0011
  have p0013 :=
    @g_mpbir (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd)) (syn_cvv)) (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) p0009 p0012
  have p0014 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd)) p0003 p0013
  have p0015 :=
    (by simpa [syn_chnbaseresfn] using (Nominal.classEqRefl (syn_chnbaseresfn F)))
  have p0016 :=
    @g_fneq1i (syn_cvv) (syn_chnbaseresfn F) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd))) p0015
  have p0017 :=
    @g_mpbir (syn_wfn (syn_chnbaseresfn F) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd))) (syn_cvv)) p0014 p0016
  have p0018 :=
    @g_ln1stfn
  have p0019 :=
    @g_pm3_2i (syn_wfn (syn_chnbaseresfn F) (syn_cvv)) (syn_wfn (syn_c1st) (syn_cvv)) p0017 p0018
  have p0020 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_chnbaseresfn F) (syn_c1st)
  have p0021 :=
    Nominal.mp p0019 p0020
  have p0022 :=
    @g_inidm (syn_cvv)
  have p0023 :=
    @g_eqcomi (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) p0022
  have p0024 :=
    @g_fneq2i (syn_cvv) (syn_cin (syn_cvv) (syn_cvv)) (syn_ctxp (syn_chnbaseresfn F) (syn_c1st)) p0023
  have p0025 :=
    @g_mpbir (syn_wfn (syn_ctxp (syn_chnbaseresfn F) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_ctxp (syn_chnbaseresfn F) (syn_c1st)) (syn_cin (syn_cvv) (syn_cvv))) p0021 p0024
  have p0026 :=
    @g_fncovv (syn_chwgen) (syn_ctxp (syn_chnbaseresfn F) (syn_c1st)) p0002 p0025
  have p0027 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_chwgen) (syn_ctxp (syn_chnbaseresfn F) (syn_c1st))) (syn_cvv)) (.classMem (.cv u) (syn_cvv)) p0026 hyp_hncodetrnfnvalndv_2
  have p0028 :=
    @g_fvco2 (syn_cvv) (.cv u) (syn_c2nd) (syn_ccom (syn_chwgen) (syn_ctxp (syn_chnbaseresfn F) (syn_c1st)))
  have p0029 :=
    Nominal.mp p0027 p0028
  have p0030 :=
    @g_lnimageresfnfn
  have p0031 :=
    @g_fnconstg (syn_cvv) F (syn_cvv)
  have p0032 :=
    Nominal.mp hyp_hncodetrnfnvalndv_1 p0031
  have p0033 :=
    @g_ln2ndfn
  have p0034 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn F)) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0032 p0033
  have p0035 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd)
  have p0036 :=
    Nominal.mp p0034 p0035
  have p0037 :=
    @g_inidm (syn_cvv)
  have p0038 :=
    @g_eqcomi (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) p0037
  have p0039 :=
    @g_fneq2i (syn_cvv) (syn_cin (syn_cvv) (syn_cvv)) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd)) p0038
  have p0040 :=
    @g_mpbir (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd)) (syn_cvv)) (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) p0036 p0039
  have p0041 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd)) p0030 p0040
  have p0042 :=
    (by simpa [syn_chnbaseresfn] using (Nominal.classEqRefl (syn_chnbaseresfn F)))
  have p0043 :=
    @g_fneq1i (syn_cvv) (syn_chnbaseresfn F) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd))) p0042
  have p0044 :=
    @g_mpbir (syn_wfn (syn_chnbaseresfn F) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd))) (syn_cvv)) p0041 p0043
  have p0045 :=
    @g_ln1stfn
  have p0046 :=
    @g_pm3_2i (syn_wfn (syn_chnbaseresfn F) (syn_cvv)) (syn_wfn (syn_c1st) (syn_cvv)) p0044 p0045
  have p0047 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_chnbaseresfn F) (syn_c1st)
  have p0048 :=
    Nominal.mp p0046 p0047
  have p0049 :=
    @g_inidm (syn_cvv)
  have p0050 :=
    @g_eqcomi (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) p0049
  have p0051 :=
    @g_fneq2i (syn_cvv) (syn_cin (syn_cvv) (syn_cvv)) (syn_ctxp (syn_chnbaseresfn F) (syn_c1st)) p0050
  have p0052 :=
    @g_mpbir (syn_wfn (syn_ctxp (syn_chnbaseresfn F) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_ctxp (syn_chnbaseresfn F) (syn_c1st)) (syn_cin (syn_cvv) (syn_cvv))) p0048 p0051
  have p0053 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_chnbaseresfn F) (syn_c1st)) (syn_cvv)) (.classMem (.cv u) (syn_cvv)) p0052 hyp_hncodetrnfnvalndv_2
  have p0054 :=
    @g_fvco2 (syn_cvv) (.cv u) (syn_chwgen) (syn_ctxp (syn_chnbaseresfn F) (syn_c1st))
  have p0055 :=
    Nominal.mp p0053 p0054
  have p0056 :=
    @g_lnimageresfnfn
  have p0057 :=
    @g_fnconstg (syn_cvv) F (syn_cvv)
  have p0058 :=
    Nominal.mp hyp_hncodetrnfnvalndv_1 p0057
  have p0059 :=
    @g_ln2ndfn
  have p0060 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn F)) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0058 p0059
  have p0061 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd)
  have p0062 :=
    Nominal.mp p0060 p0061
  have p0063 :=
    @g_inidm (syn_cvv)
  have p0064 :=
    @g_eqcomi (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) p0063
  have p0065 :=
    @g_fneq2i (syn_cvv) (syn_cin (syn_cvv) (syn_cvv)) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd)) p0064
  have p0066 :=
    @g_mpbir (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd)) (syn_cvv)) (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) p0062 p0065
  have p0067 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd)) p0056 p0066
  have p0068 :=
    (by simpa [syn_chnbaseresfn] using (Nominal.classEqRefl (syn_chnbaseresfn F)))
  have p0069 :=
    @g_fneq1i (syn_cvv) (syn_chnbaseresfn F) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd))) p0068
  have p0070 :=
    @g_mpbir (syn_wfn (syn_chnbaseresfn F) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_c2nd))) (syn_cvv)) p0067 p0069
  have p0071 :=
    @g_ln1stfn
  have p0072 :=
    @g_fvtxpvv (.cv u) (syn_chnbaseresfn F) (syn_c1st) p0070 p0071 hyp_hncodetrnfnvalndv_2
  have p0073 :=
    @g_hnbaseresfnvalndv u F hyp_hncodetrnfnvalndv_1 hyp_hncodetrnfnvalndv_2
  have p0074 :=
    @g_eqid (syn_cfv (syn_c1st) (.cv u))
  have p0075 :=
    @g_opeq12i (syn_cfv (syn_chnbaseresfn F) (.cv u)) (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) p0073 p0074
  have p0076 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_chnbaseresfn F) (syn_c1st)) (.cv u)) (syn_cop (syn_cfv (syn_chnbaseresfn F) (.cv u)) (syn_cfv (syn_c1st) (.cv u))) (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) p0072 p0075
  have p0077 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_chnbaseresfn F) (syn_c1st)) (.cv u)) (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_chwgen) p0076
  have p0078 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_chwgen) (syn_ctxp (syn_chnbaseresfn F) (syn_c1st))) (.cv u)) (syn_cfv (syn_chwgen) (syn_cfv (syn_ctxp (syn_chnbaseresfn F) (syn_c1st)) (.cv u))) (syn_cfv (syn_chwgen) (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))) p0055 p0077
  have p0079 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0080 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hncodetrnfnvalndv_1 p0079
  have p0081 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0082 :=
    @g_hwgenvalclndv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)) p0080 p0081
  have p0083 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_chwgen) (syn_ctxp (syn_chnbaseresfn F) (syn_c1st))) (.cv u)) (syn_cfv (syn_chwgen) (syn_cop (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))) (syn_cop (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) p0078 p0082
  have p0084 :=
    @g_fveq2i (syn_cfv (syn_ccom (syn_chwgen) (syn_ctxp (syn_chnbaseresfn F) (syn_c1st))) (.cv u)) (syn_cop (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))))) (syn_c2nd) p0083
  have p0085 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_c2nd) (syn_ccom (syn_chwgen) (syn_ctxp (syn_chnbaseresfn F) (syn_c1st)))) (.cv u)) (syn_cfv (syn_c2nd) (syn_cfv (syn_ccom (syn_chwgen) (syn_ctxp (syn_chnbaseresfn F) (syn_c1st))) (.cv u))) (syn_cfv (syn_c2nd) (syn_cop (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))) p0029 p0084
  have p0086 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0087 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0088 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hncodetrnfnvalndv_1 p0087
  have p0089 :=
    @g_dmex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0088
  have p0090 :=
    @g_opex (syn_cfv (syn_c1st) (.cv u)) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0086 p0089
  have p0091 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0092 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hncodetrnfnvalndv_1 p0091
  have p0093 :=
    @g_fvex (.cv u) (syn_c1st)
  have p0094 :=
    @g_coex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)) p0092 p0093
  have p0095 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0096 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hncodetrnfnvalndv_1 p0095
  have p0097 :=
    @g_cnvex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0096
  have p0098 :=
    @g_coex (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0094 p0097
  have p0099 :=
    @g_fvex (.cv u) (syn_c2nd)
  have p0100 :=
    @g_resex F (syn_cfv (syn_c2nd) (.cv u)) hyp_hncodetrnfnvalndv_1 p0099
  have p0101 :=
    @g_rnex (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) p0100
  have p0102 :=
    @g_opex (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u)))) p0098 p0101
  have p0103 :=
    @g_opfv2nd (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0090 p0102
  have p0104 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_c2nd) (syn_ccom (syn_chwgen) (syn_ctxp (syn_chnbaseresfn F) (syn_c1st)))) (.cv u)) (syn_cfv (syn_c2nd) (syn_cop (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cdm (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))))) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0085 p0103
  have p0105 :=
    @g_eqtri (syn_cfv (syn_chncodetrnfn F) (.cv u)) (syn_cfv (syn_ccom (syn_c2nd) (syn_ccom (syn_chwgen) (syn_ctxp (syn_chnbaseresfn F) (syn_c1st)))) (.cv u)) (syn_cop (syn_ccom (syn_ccom (syn_cres F (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))) (syn_ccnv (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) (syn_crn (syn_cres F (syn_cfv (syn_c2nd) (.cv u))))) p0001 p0104
  exact p0105

#print axioms g_hncodetrnfnvalndv

end NFChoice.DirectNominalPrf.WPPReplay
