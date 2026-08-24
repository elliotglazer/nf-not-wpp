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
import NominalWPPReplayChunk016Compact001Part056

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

noncomputable def g_wpphwgencnvfnvalndv
    (A : Class) (hyp_wpphwgencnvfnvalndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cwpphwgencnvfn) (syn_csn A)) (syn_ccnv (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A)))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    (by simpa [syn_cwpphwgencnvfn] using (Nominal.classEqRefl (syn_cwpphwgencnvfn)))
  have p0001 :=
    @g_fveq1i (syn_csn A) (syn_cwpphwgencnvfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn)) p0000
  have p0002 :=
    @g_lnimageresfnfn
  have p0003 :=
    @g_hwgenex
  have p0004 :=
    @g_hwbijex
  have p0005 :=
    @g_vvex
  have p0006 :=
    @g_xpex (syn_chwbij) (syn_cvv) p0004 p0005
  have p0007 :=
    @g_imaex (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)) p0003 p0006
  have p0008 :=
    @g_fnconstg (syn_cvv) (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cvv)
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_imageswapfn
  have p0011 :=
    @g_lnimageresfnfn
  have p0012 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn (syn_cvv))))
  have p0013 :=
    @g_hwcodesunivndv
  have p0014 :=
    @g_weex
  have p0015 :=
    @g_eqeltri (syn_chwcodes (syn_cvv)) (syn_cwe) (syn_cvv) p0013 p0014
  have p0016 :=
    @g_hwrelsex
  have p0017 :=
    @g_inex (syn_chwcodes (syn_cvv)) (syn_chwrels) p0015 p0016
  have p0018 :=
    @g_eqeltri (syn_chwcn (syn_cvv)) (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels)) (syn_cvv) p0012 p0017
  have p0019 :=
    @g_cnvex (syn_chwcn (syn_cvv)) p0018
  have p0020 :=
    @g_fnconstg (syn_cvv) (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cvv)
  have p0021 :=
    Nominal.mp p0019 p0020
  have p0022 :=
    @g_ssetex
  have p0023 :=
    @g_cnvex (syn_csset) p0022
  have p0024 :=
    @g_wppimagefn (syn_ccnv (syn_csset)) p0023
  have p0025 :=
    (by simpa [syn_cwpppowsetfn] using (Nominal.classEqRefl (syn_cwpppowsetfn)))
  have p0026 :=
    @g_fneq1i (syn_cvv) (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) p0025
  have p0027 :=
    @g_mpbir (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) (syn_wfn (syn_cimage (syn_ccnv (syn_csset))) (syn_cvv)) p0024 p0026
  have p0028 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cvv)) (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) p0021 p0027
  have p0029 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)
  have p0030 :=
    Nominal.mp p0028 p0029
  have p0031 :=
    @g_inidm (syn_cvv)
  have p0032 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0031
  have p0033 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cvv)) p0030 p0032
  have p0034 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0011 p0033
  have p0035 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn))) p0010 p0034
  have p0036 :=
    (by simpa [syn_cwpphwcnsetfn] using (Nominal.classEqRefl (syn_cwpphwcnsetfn)))
  have p0037 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwcnsetfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) p0036
  have p0038 :=
    @g_mpbir (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) (syn_cvv)) p0035 p0037
  have p0039 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cvv)) (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) p0009 p0038
  have p0040 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)
  have p0041 :=
    Nominal.mp p0039 p0040
  have p0042 :=
    @g_inidm (syn_cvv)
  have p0043 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)) p0042
  have p0044 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)) (syn_cvv)) p0041 p0043
  have p0045 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)) p0002 p0044
  have p0046 :=
    (by simpa [syn_cwpphwgendomfn] using (Nominal.classEqRefl (syn_cwpphwgendomfn)))
  have p0047 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwgendomfn) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn))) p0046
  have p0048 :=
    @g_mpbir (syn_wfn (syn_cwpphwgendomfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn))) (syn_cvv)) p0045 p0047
  have p0049 :=
    @g_snex A
  have p0050 :=
    @g_pm3_2i (syn_wfn (syn_cwpphwgendomfn) (syn_cvv)) (.classMem (syn_csn A) (syn_cvv)) p0048 p0049
  have p0051 :=
    @g_fvco2 (syn_cvv) (syn_csn A) (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn)
  have p0052 :=
    Nominal.mp p0050 p0051
  have p0053 :=
    @g_wpphwgendomfnvalndv A hyp_wpphwgencnvfnvalndv_1
  have p0054 :=
    @g_fveq2i (syn_cfv (syn_cwpphwgendomfn) (syn_csn A)) (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A)) (syn_cimage (syn_cswap)) p0053
  have p0055 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn)) (syn_csn A)) (syn_cfv (syn_cimage (syn_cswap)) (syn_cfv (syn_cwpphwgendomfn) (syn_csn A))) (syn_cfv (syn_cimage (syn_cswap)) (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A))) p0052 p0054
  have p0056 :=
    @g_hwgenex
  have p0057 :=
    @g_hwbijex
  have p0058 :=
    @g_vvex
  have p0059 :=
    @g_xpex (syn_chwbij) (syn_cvv) p0057 p0058
  have p0060 :=
    @g_imaex (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)) p0056 p0059
  have p0061 :=
    @g_hwcnex A hyp_wpphwgencnvfnvalndv_1
  have p0062 :=
    @g_resex (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A) p0060 p0061
  have p0063 :=
    @g_wppimageswapfv (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A)) p0062
  have p0064 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn)) (syn_csn A)) (syn_cfv (syn_cimage (syn_cswap)) (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A))) (syn_ccnv (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A))) p0055 p0063
  have p0065 :=
    @g_eqtri (syn_cfv (syn_cwpphwgencnvfn) (syn_csn A)) (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn)) (syn_csn A)) (syn_ccnv (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A))) p0001 p0064
  exact p0065

noncomputable def g_wpphwnisosetfnvalndv
    (A : Class) (hyp_wpphwnisosetfnvalndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cwpphwnisosetfn) (syn_csn A)) (syn_chwniso A)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    (by simpa [syn_cwpphwnisosetfn] using (Nominal.classEqRefl (syn_cwpphwnisosetfn)))
  have p0001 :=
    @g_fveq1i (syn_csn A) (syn_cwpphwnisosetfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)))) p0000
  have p0002 :=
    @g_lnimageresfnfn
  have p0003 :=
    @g_imageswapfn
  have p0004 :=
    @g_lnimageresfnfn
  have p0005 :=
    @g_hwgenex
  have p0006 :=
    @g_hwbijex
  have p0007 :=
    @g_vvex
  have p0008 :=
    @g_xpex (syn_chwbij) (syn_cvv) p0006 p0007
  have p0009 :=
    @g_imaex (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)) p0005 p0008
  have p0010 :=
    @g_fnconstg (syn_cvv) (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cvv)
  have p0011 :=
    Nominal.mp p0009 p0010
  have p0012 :=
    @g_imageswapfn
  have p0013 :=
    @g_lnimageresfnfn
  have p0014 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn (syn_cvv))))
  have p0015 :=
    @g_hwcodesunivndv
  have p0016 :=
    @g_weex
  have p0017 :=
    @g_eqeltri (syn_chwcodes (syn_cvv)) (syn_cwe) (syn_cvv) p0015 p0016
  have p0018 :=
    @g_hwrelsex
  have p0019 :=
    @g_inex (syn_chwcodes (syn_cvv)) (syn_chwrels) p0017 p0018
  have p0020 :=
    @g_eqeltri (syn_chwcn (syn_cvv)) (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels)) (syn_cvv) p0014 p0019
  have p0021 :=
    @g_cnvex (syn_chwcn (syn_cvv)) p0020
  have p0022 :=
    @g_fnconstg (syn_cvv) (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cvv)
  have p0023 :=
    Nominal.mp p0021 p0022
  have p0024 :=
    @g_ssetex
  have p0025 :=
    @g_cnvex (syn_csset) p0024
  have p0026 :=
    @g_wppimagefn (syn_ccnv (syn_csset)) p0025
  have p0027 :=
    (by simpa [syn_cwpppowsetfn] using (Nominal.classEqRefl (syn_cwpppowsetfn)))
  have p0028 :=
    @g_fneq1i (syn_cvv) (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) p0027
  have p0029 :=
    @g_mpbir (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) (syn_wfn (syn_cimage (syn_ccnv (syn_csset))) (syn_cvv)) p0026 p0028
  have p0030 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cvv)) (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) p0023 p0029
  have p0031 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)
  have p0032 :=
    Nominal.mp p0030 p0031
  have p0033 :=
    @g_inidm (syn_cvv)
  have p0034 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0033
  have p0035 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cvv)) p0032 p0034
  have p0036 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0013 p0035
  have p0037 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn))) p0012 p0036
  have p0038 :=
    (by simpa [syn_cwpphwcnsetfn] using (Nominal.classEqRefl (syn_cwpphwcnsetfn)))
  have p0039 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwcnsetfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) p0038
  have p0040 :=
    @g_mpbir (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) (syn_cvv)) p0037 p0039
  have p0041 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cvv)) (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) p0011 p0040
  have p0042 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)
  have p0043 :=
    Nominal.mp p0041 p0042
  have p0044 :=
    @g_inidm (syn_cvv)
  have p0045 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)) p0044
  have p0046 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)) (syn_cvv)) p0043 p0045
  have p0047 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)) p0004 p0046
  have p0048 :=
    (by simpa [syn_cwpphwgendomfn] using (Nominal.classEqRefl (syn_cwpphwgendomfn)))
  have p0049 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwgendomfn) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn))) p0048
  have p0050 :=
    @g_mpbir (syn_wfn (syn_cwpphwgendomfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn))) (syn_cvv)) p0047 p0049
  have p0051 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn) p0003 p0050
  have p0052 :=
    (by simpa [syn_cwpphwgencnvfn] using (Nominal.classEqRefl (syn_cwpphwgencnvfn)))
  have p0053 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwgencnvfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn)) p0052
  have p0054 :=
    @g_mpbir (syn_wfn (syn_cwpphwgencnvfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn)) (syn_cvv)) p0051 p0053
  have p0055 :=
    @g_imageswapfn
  have p0056 :=
    @g_lnimageresfnfn
  have p0057 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn (syn_cvv))))
  have p0058 :=
    @g_hwcodesunivndv
  have p0059 :=
    @g_weex
  have p0060 :=
    @g_eqeltri (syn_chwcodes (syn_cvv)) (syn_cwe) (syn_cvv) p0058 p0059
  have p0061 :=
    @g_hwrelsex
  have p0062 :=
    @g_inex (syn_chwcodes (syn_cvv)) (syn_chwrels) p0060 p0061
  have p0063 :=
    @g_eqeltri (syn_chwcn (syn_cvv)) (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels)) (syn_cvv) p0057 p0062
  have p0064 :=
    @g_cnvex (syn_chwcn (syn_cvv)) p0063
  have p0065 :=
    @g_fnconstg (syn_cvv) (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cvv)
  have p0066 :=
    Nominal.mp p0064 p0065
  have p0067 :=
    @g_ssetex
  have p0068 :=
    @g_cnvex (syn_csset) p0067
  have p0069 :=
    @g_wppimagefn (syn_ccnv (syn_csset)) p0068
  have p0070 :=
    (by simpa [syn_cwpppowsetfn] using (Nominal.classEqRefl (syn_cwpppowsetfn)))
  have p0071 :=
    @g_fneq1i (syn_cvv) (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) p0070
  have p0072 :=
    @g_mpbir (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) (syn_wfn (syn_cimage (syn_ccnv (syn_csset))) (syn_cvv)) p0069 p0071
  have p0073 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cvv)) (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) p0066 p0072
  have p0074 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)
  have p0075 :=
    Nominal.mp p0073 p0074
  have p0076 :=
    @g_inidm (syn_cvv)
  have p0077 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0076
  have p0078 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cvv)) p0075 p0077
  have p0079 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0056 p0078
  have p0080 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn))) p0055 p0079
  have p0081 :=
    (by simpa [syn_cwpphwcnsetfn] using (Nominal.classEqRefl (syn_cwpphwcnsetfn)))
  have p0082 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwcnsetfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) p0081
  have p0083 :=
    @g_mpbir (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) (syn_cvv)) p0080 p0082
  have p0084 :=
    @g_pm3_2i (syn_wfn (syn_cwpphwgencnvfn) (syn_cvv)) (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) p0054 p0083
  have p0085 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)
  have p0086 :=
    Nominal.mp p0084 p0085
  have p0087 :=
    @g_inidm (syn_cvv)
  have p0088 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) p0087
  have p0089 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) (syn_cvv)) p0086 p0088
  have p0090 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) p0002 p0089
  have p0091 :=
    @g_snex A
  have p0092 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn))) (syn_cvv)) (.classMem (syn_csn A) (syn_cvv)) p0090 p0091
  have p0093 :=
    @g_fvco2 (syn_cvv) (syn_csn A) (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)))
  have p0094 :=
    Nominal.mp p0092 p0093
  have p0095 :=
    @g_imageswapfn
  have p0096 :=
    @g_lnimageresfnfn
  have p0097 :=
    @g_hwgenex
  have p0098 :=
    @g_hwbijex
  have p0099 :=
    @g_vvex
  have p0100 :=
    @g_xpex (syn_chwbij) (syn_cvv) p0098 p0099
  have p0101 :=
    @g_imaex (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)) p0097 p0100
  have p0102 :=
    @g_fnconstg (syn_cvv) (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cvv)
  have p0103 :=
    Nominal.mp p0101 p0102
  have p0104 :=
    @g_imageswapfn
  have p0105 :=
    @g_lnimageresfnfn
  have p0106 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn (syn_cvv))))
  have p0107 :=
    @g_hwcodesunivndv
  have p0108 :=
    @g_weex
  have p0109 :=
    @g_eqeltri (syn_chwcodes (syn_cvv)) (syn_cwe) (syn_cvv) p0107 p0108
  have p0110 :=
    @g_hwrelsex
  have p0111 :=
    @g_inex (syn_chwcodes (syn_cvv)) (syn_chwrels) p0109 p0110
  have p0112 :=
    @g_eqeltri (syn_chwcn (syn_cvv)) (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels)) (syn_cvv) p0106 p0111
  have p0113 :=
    @g_cnvex (syn_chwcn (syn_cvv)) p0112
  have p0114 :=
    @g_fnconstg (syn_cvv) (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cvv)
  have p0115 :=
    Nominal.mp p0113 p0114
  have p0116 :=
    @g_ssetex
  have p0117 :=
    @g_cnvex (syn_csset) p0116
  have p0118 :=
    @g_wppimagefn (syn_ccnv (syn_csset)) p0117
  have p0119 :=
    (by simpa [syn_cwpppowsetfn] using (Nominal.classEqRefl (syn_cwpppowsetfn)))
  have p0120 :=
    @g_fneq1i (syn_cvv) (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) p0119
  have p0121 :=
    @g_mpbir (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) (syn_wfn (syn_cimage (syn_ccnv (syn_csset))) (syn_cvv)) p0118 p0120
  have p0122 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cvv)) (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) p0115 p0121
  have p0123 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)
  have p0124 :=
    Nominal.mp p0122 p0123
  have p0125 :=
    @g_inidm (syn_cvv)
  have p0126 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0125
  have p0127 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cvv)) p0124 p0126
  have p0128 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0105 p0127
  have p0129 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn))) p0104 p0128
  have p0130 :=
    (by simpa [syn_cwpphwcnsetfn] using (Nominal.classEqRefl (syn_cwpphwcnsetfn)))
  have p0131 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwcnsetfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) p0130
  have p0132 :=
    @g_mpbir (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) (syn_cvv)) p0129 p0131
  have p0133 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cvv)) (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) p0103 p0132
  have p0134 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)
  have p0135 :=
    Nominal.mp p0133 p0134
  have p0136 :=
    @g_inidm (syn_cvv)
  have p0137 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)) p0136
  have p0138 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)) (syn_cvv)) p0135 p0137
  have p0139 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)) p0096 p0138
  have p0140 :=
    (by simpa [syn_cwpphwgendomfn] using (Nominal.classEqRefl (syn_cwpphwgendomfn)))
  have p0141 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwgendomfn) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn))) p0140
  have p0142 :=
    @g_mpbir (syn_wfn (syn_cwpphwgendomfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn))) (syn_cvv)) p0139 p0141
  have p0143 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn) p0095 p0142
  have p0144 :=
    (by simpa [syn_cwpphwgencnvfn] using (Nominal.classEqRefl (syn_cwpphwgencnvfn)))
  have p0145 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwgencnvfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn)) p0144
  have p0146 :=
    @g_mpbir (syn_wfn (syn_cwpphwgencnvfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn)) (syn_cvv)) p0143 p0145
  have p0147 :=
    @g_imageswapfn
  have p0148 :=
    @g_lnimageresfnfn
  have p0149 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn (syn_cvv))))
  have p0150 :=
    @g_hwcodesunivndv
  have p0151 :=
    @g_weex
  have p0152 :=
    @g_eqeltri (syn_chwcodes (syn_cvv)) (syn_cwe) (syn_cvv) p0150 p0151
  have p0153 :=
    @g_hwrelsex
  have p0154 :=
    @g_inex (syn_chwcodes (syn_cvv)) (syn_chwrels) p0152 p0153
  have p0155 :=
    @g_eqeltri (syn_chwcn (syn_cvv)) (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels)) (syn_cvv) p0149 p0154
  have p0156 :=
    @g_cnvex (syn_chwcn (syn_cvv)) p0155
  have p0157 :=
    @g_fnconstg (syn_cvv) (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cvv)
  have p0158 :=
    Nominal.mp p0156 p0157
  have p0159 :=
    @g_ssetex
  have p0160 :=
    @g_cnvex (syn_csset) p0159
  have p0161 :=
    @g_wppimagefn (syn_ccnv (syn_csset)) p0160
  have p0162 :=
    (by simpa [syn_cwpppowsetfn] using (Nominal.classEqRefl (syn_cwpppowsetfn)))
  have p0163 :=
    @g_fneq1i (syn_cvv) (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) p0162
  have p0164 :=
    @g_mpbir (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) (syn_wfn (syn_cimage (syn_ccnv (syn_csset))) (syn_cvv)) p0161 p0163
  have p0165 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cvv)) (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) p0158 p0164
  have p0166 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)
  have p0167 :=
    Nominal.mp p0165 p0166
  have p0168 :=
    @g_inidm (syn_cvv)
  have p0169 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0168
  have p0170 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cvv)) p0167 p0169
  have p0171 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0148 p0170
  have p0172 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn))) p0147 p0171
  have p0173 :=
    (by simpa [syn_cwpphwcnsetfn] using (Nominal.classEqRefl (syn_cwpphwcnsetfn)))
  have p0174 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwcnsetfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) p0173
  have p0175 :=
    @g_mpbir (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) (syn_cvv)) p0172 p0174
  have p0176 :=
    @g_pm3_2i (syn_wfn (syn_cwpphwgencnvfn) (syn_cvv)) (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) p0146 p0175
  have p0177 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)
  have p0178 :=
    Nominal.mp p0176 p0177
  have p0179 :=
    @g_inidm (syn_cvv)
  have p0180 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) p0179
  have p0181 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) (syn_cvv)) p0178 p0180
  have p0182 :=
    @g_snex A
  have p0183 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) (syn_cvv)) (.classMem (syn_csn A) (syn_cvv)) p0181 p0182
  have p0184 :=
    @g_fvco2 (syn_cvv) (syn_csn A) (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn))
  have p0185 :=
    Nominal.mp p0183 p0184
  have p0186 :=
    @g_imageswapfn
  have p0187 :=
    @g_lnimageresfnfn
  have p0188 :=
    @g_hwgenex
  have p0189 :=
    @g_hwbijex
  have p0190 :=
    @g_vvex
  have p0191 :=
    @g_xpex (syn_chwbij) (syn_cvv) p0189 p0190
  have p0192 :=
    @g_imaex (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)) p0188 p0191
  have p0193 :=
    @g_fnconstg (syn_cvv) (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cvv)
  have p0194 :=
    Nominal.mp p0192 p0193
  have p0195 :=
    @g_imageswapfn
  have p0196 :=
    @g_lnimageresfnfn
  have p0197 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn (syn_cvv))))
  have p0198 :=
    @g_hwcodesunivndv
  have p0199 :=
    @g_weex
  have p0200 :=
    @g_eqeltri (syn_chwcodes (syn_cvv)) (syn_cwe) (syn_cvv) p0198 p0199
  have p0201 :=
    @g_hwrelsex
  have p0202 :=
    @g_inex (syn_chwcodes (syn_cvv)) (syn_chwrels) p0200 p0201
  have p0203 :=
    @g_eqeltri (syn_chwcn (syn_cvv)) (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels)) (syn_cvv) p0197 p0202
  have p0204 :=
    @g_cnvex (syn_chwcn (syn_cvv)) p0203
  have p0205 :=
    @g_fnconstg (syn_cvv) (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cvv)
  have p0206 :=
    Nominal.mp p0204 p0205
  have p0207 :=
    @g_ssetex
  have p0208 :=
    @g_cnvex (syn_csset) p0207
  have p0209 :=
    @g_wppimagefn (syn_ccnv (syn_csset)) p0208
  have p0210 :=
    (by simpa [syn_cwpppowsetfn] using (Nominal.classEqRefl (syn_cwpppowsetfn)))
  have p0211 :=
    @g_fneq1i (syn_cvv) (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) p0210
  have p0212 :=
    @g_mpbir (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) (syn_wfn (syn_cimage (syn_ccnv (syn_csset))) (syn_cvv)) p0209 p0211
  have p0213 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cvv)) (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) p0206 p0212
  have p0214 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)
  have p0215 :=
    Nominal.mp p0213 p0214
  have p0216 :=
    @g_inidm (syn_cvv)
  have p0217 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0216
  have p0218 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cvv)) p0215 p0217
  have p0219 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0196 p0218
  have p0220 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn))) p0195 p0219
  have p0221 :=
    (by simpa [syn_cwpphwcnsetfn] using (Nominal.classEqRefl (syn_cwpphwcnsetfn)))
  have p0222 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwcnsetfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) p0221
  have p0223 :=
    @g_mpbir (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) (syn_cvv)) p0220 p0222
  have p0224 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cvv)) (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) p0194 p0223
  have p0225 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)
  have p0226 :=
    Nominal.mp p0224 p0225
  have p0227 :=
    @g_inidm (syn_cvv)
  have p0228 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)) p0227
  have p0229 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)) (syn_cvv)) p0226 p0228
  have p0230 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)) p0187 p0229
  have p0231 :=
    (by simpa [syn_cwpphwgendomfn] using (Nominal.classEqRefl (syn_cwpphwgendomfn)))
  have p0232 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwgendomfn) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn))) p0231
  have p0233 :=
    @g_mpbir (syn_wfn (syn_cwpphwgendomfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn))) (syn_cvv)) p0230 p0232
  have p0234 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn) p0186 p0233
  have p0235 :=
    (by simpa [syn_cwpphwgencnvfn] using (Nominal.classEqRefl (syn_cwpphwgencnvfn)))
  have p0236 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwgencnvfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn)) p0235
  have p0237 :=
    @g_mpbir (syn_wfn (syn_cwpphwgencnvfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn)) (syn_cvv)) p0234 p0236
  have p0238 :=
    @g_imageswapfn
  have p0239 :=
    @g_lnimageresfnfn
  have p0240 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn (syn_cvv))))
  have p0241 :=
    @g_hwcodesunivndv
  have p0242 :=
    @g_weex
  have p0243 :=
    @g_eqeltri (syn_chwcodes (syn_cvv)) (syn_cwe) (syn_cvv) p0241 p0242
  have p0244 :=
    @g_hwrelsex
  have p0245 :=
    @g_inex (syn_chwcodes (syn_cvv)) (syn_chwrels) p0243 p0244
  have p0246 :=
    @g_eqeltri (syn_chwcn (syn_cvv)) (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels)) (syn_cvv) p0240 p0245
  have p0247 :=
    @g_cnvex (syn_chwcn (syn_cvv)) p0246
  have p0248 :=
    @g_fnconstg (syn_cvv) (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cvv)
  have p0249 :=
    Nominal.mp p0247 p0248
  have p0250 :=
    @g_ssetex
  have p0251 :=
    @g_cnvex (syn_csset) p0250
  have p0252 :=
    @g_wppimagefn (syn_ccnv (syn_csset)) p0251
  have p0253 :=
    (by simpa [syn_cwpppowsetfn] using (Nominal.classEqRefl (syn_cwpppowsetfn)))
  have p0254 :=
    @g_fneq1i (syn_cvv) (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) p0253
  have p0255 :=
    @g_mpbir (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) (syn_wfn (syn_cimage (syn_ccnv (syn_csset))) (syn_cvv)) p0252 p0254
  have p0256 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cvv)) (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) p0249 p0255
  have p0257 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)
  have p0258 :=
    Nominal.mp p0256 p0257
  have p0259 :=
    @g_inidm (syn_cvv)
  have p0260 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0259
  have p0261 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cvv)) p0258 p0260
  have p0262 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0239 p0261
  have p0263 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn))) p0238 p0262
  have p0264 :=
    (by simpa [syn_cwpphwcnsetfn] using (Nominal.classEqRefl (syn_cwpphwcnsetfn)))
  have p0265 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwcnsetfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) p0264
  have p0266 :=
    @g_mpbir (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) (syn_cvv)) p0263 p0265
  have p0267 :=
    @g_snex A
  have p0268 :=
    @g_fvtxpvv (syn_csn A) (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn) p0237 p0266 p0267
  have p0269 :=
    @g_wpphwgencnvfnvalndv A hyp_wpphwnisosetfnvalndv_1
  have p0270 :=
    @g_wpphwcnsetfnvalndv A hyp_wpphwnisosetfnvalndv_1
  have p0271 :=
    @g_opeq12i (syn_cfv (syn_cwpphwgencnvfn) (syn_csn A)) (syn_ccnv (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A))) (syn_cfv (syn_cwpphwcnsetfn) (syn_csn A)) (syn_chwcn A) p0269 p0270
  have p0272 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) (syn_csn A)) (syn_cop (syn_cfv (syn_cwpphwgencnvfn) (syn_csn A)) (syn_cfv (syn_cwpphwcnsetfn) (syn_csn A))) (syn_cop (syn_ccnv (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A))) (syn_chwcn A)) p0268 p0271
  have p0273 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) (syn_csn A)) (syn_cop (syn_ccnv (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A))) (syn_chwcn A)) (syn_clnimageresfn) p0272
  have p0274 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn))) (syn_csn A)) (syn_cfv (syn_clnimageresfn) (syn_cfv (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) (syn_csn A))) (syn_cfv (syn_clnimageresfn) (syn_cop (syn_ccnv (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A))) (syn_chwcn A))) p0185 p0273
  have p0275 :=
    @g_hwgenex
  have p0276 :=
    @g_hwbijex
  have p0277 :=
    @g_vvex
  have p0278 :=
    @g_xpex (syn_chwbij) (syn_cvv) p0276 p0277
  have p0279 :=
    @g_imaex (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)) p0275 p0278
  have p0280 :=
    @g_hwcnex A hyp_wpphwnisosetfnvalndv_1
  have p0281 :=
    @g_resex (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A) p0279 p0280
  have p0282 :=
    @g_cnvex (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A)) p0281
  have p0283 :=
    @g_hwcnex A hyp_wpphwnisosetfnvalndv_1
  have p0284 :=
    @g_lnimageresfnval (syn_chwcn A) (syn_ccnv (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A))) p0282 p0283
  have p0285 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn))) (syn_csn A)) (syn_cfv (syn_clnimageresfn) (syn_cop (syn_ccnv (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A))) (syn_chwcn A))) (syn_cres (syn_ccnv (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A))) (syn_chwcn A)) p0274 p0284
  have p0286 :=
    @g_fveq2i (syn_cfv (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn))) (syn_csn A)) (syn_cres (syn_ccnv (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A))) (syn_chwcn A)) (syn_cimage (syn_cswap)) p0285
  have p0287 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)))) (syn_csn A)) (syn_cfv (syn_cimage (syn_cswap)) (syn_cfv (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn))) (syn_csn A))) (syn_cfv (syn_cimage (syn_cswap)) (syn_cres (syn_ccnv (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A))) (syn_chwcn A))) p0094 p0286
  have p0288 :=
    @g_hwgenex
  have p0289 :=
    @g_hwbijex
  have p0290 :=
    @g_vvex
  have p0291 :=
    @g_xpex (syn_chwbij) (syn_cvv) p0289 p0290
  have p0292 :=
    @g_imaex (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)) p0288 p0291
  have p0293 :=
    @g_hwcnex A hyp_wpphwnisosetfnvalndv_1
  have p0294 :=
    @g_resex (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A) p0292 p0293
  have p0295 :=
    @g_cnvex (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A)) p0294
  have p0296 :=
    @g_hwcnex A hyp_wpphwnisosetfnvalndv_1
  have p0297 :=
    @g_resex (syn_ccnv (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A))) (syn_chwcn A) p0295 p0296
  have p0298 :=
    @g_wppimageswapfv (syn_cres (syn_ccnv (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A))) (syn_chwcn A)) p0297
  have p0299 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)))) (syn_csn A)) (syn_cfv (syn_cimage (syn_cswap)) (syn_cres (syn_ccnv (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A))) (syn_chwcn A))) (syn_ccnv (syn_cres (syn_ccnv (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A))) (syn_chwcn A))) p0287 p0298
  have p0300 :=
    @g_hwnisogendrrndv A
  have p0301 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)))) (syn_csn A)) (syn_ccnv (syn_cres (syn_ccnv (syn_cres (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_chwcn A))) (syn_chwcn A))) (syn_chwniso A) p0299 p0300
  have p0302 :=
    @g_eqtri (syn_cfv (syn_cwpphwnisosetfn) (syn_csn A)) (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)))) (syn_csn A)) (syn_chwniso A) p0001 p0301
  exact p0302

noncomputable def g_wpphnpairfnvalndv
    (A : Class) (hyp_wpphnpairfnvalndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cwpphnpairfn) (syn_csn A)) (syn_cop (syn_chwniso A) (syn_chwcn A))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    (by simpa [syn_cwpphnpairfn] using (Nominal.classEqRefl (syn_cwpphnpairfn)))
  have p0001 :=
    @g_fveq1i (syn_csn A) (syn_cwpphnpairfn) (syn_ctxp (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn)) p0000
  have p0002 :=
    @g_imageswapfn
  have p0003 :=
    @g_lnimageresfnfn
  have p0004 :=
    @g_imageswapfn
  have p0005 :=
    @g_lnimageresfnfn
  have p0006 :=
    @g_hwgenex
  have p0007 :=
    @g_hwbijex
  have p0008 :=
    @g_vvex
  have p0009 :=
    @g_xpex (syn_chwbij) (syn_cvv) p0007 p0008
  have p0010 :=
    @g_imaex (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)) p0006 p0009
  have p0011 :=
    @g_fnconstg (syn_cvv) (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cvv)
  have p0012 :=
    Nominal.mp p0010 p0011
  have p0013 :=
    @g_imageswapfn
  have p0014 :=
    @g_lnimageresfnfn
  have p0015 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn (syn_cvv))))
  have p0016 :=
    @g_hwcodesunivndv
  have p0017 :=
    @g_weex
  have p0018 :=
    @g_eqeltri (syn_chwcodes (syn_cvv)) (syn_cwe) (syn_cvv) p0016 p0017
  have p0019 :=
    @g_hwrelsex
  have p0020 :=
    @g_inex (syn_chwcodes (syn_cvv)) (syn_chwrels) p0018 p0019
  have p0021 :=
    @g_eqeltri (syn_chwcn (syn_cvv)) (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels)) (syn_cvv) p0015 p0020
  have p0022 :=
    @g_cnvex (syn_chwcn (syn_cvv)) p0021
  have p0023 :=
    @g_fnconstg (syn_cvv) (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cvv)
  have p0024 :=
    Nominal.mp p0022 p0023
  have p0025 :=
    @g_ssetex
  have p0026 :=
    @g_cnvex (syn_csset) p0025
  have p0027 :=
    @g_wppimagefn (syn_ccnv (syn_csset)) p0026
  have p0028 :=
    (by simpa [syn_cwpppowsetfn] using (Nominal.classEqRefl (syn_cwpppowsetfn)))
  have p0029 :=
    @g_fneq1i (syn_cvv) (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) p0028
  have p0030 :=
    @g_mpbir (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) (syn_wfn (syn_cimage (syn_ccnv (syn_csset))) (syn_cvv)) p0027 p0029
  have p0031 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cvv)) (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) p0024 p0030
  have p0032 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)
  have p0033 :=
    Nominal.mp p0031 p0032
  have p0034 :=
    @g_inidm (syn_cvv)
  have p0035 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0034
  have p0036 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cvv)) p0033 p0035
  have p0037 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0014 p0036
  have p0038 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn))) p0013 p0037
  have p0039 :=
    (by simpa [syn_cwpphwcnsetfn] using (Nominal.classEqRefl (syn_cwpphwcnsetfn)))
  have p0040 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwcnsetfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) p0039
  have p0041 :=
    @g_mpbir (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) (syn_cvv)) p0038 p0040
  have p0042 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cvv)) (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) p0012 p0041
  have p0043 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)
  have p0044 :=
    Nominal.mp p0042 p0043
  have p0045 :=
    @g_inidm (syn_cvv)
  have p0046 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)) p0045
  have p0047 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)) (syn_cvv)) p0044 p0046
  have p0048 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)) p0005 p0047
  have p0049 :=
    (by simpa [syn_cwpphwgendomfn] using (Nominal.classEqRefl (syn_cwpphwgendomfn)))
  have p0050 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwgendomfn) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn))) p0049
  have p0051 :=
    @g_mpbir (syn_wfn (syn_cwpphwgendomfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn))) (syn_cvv)) p0048 p0050
  have p0052 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn) p0004 p0051
  have p0053 :=
    (by simpa [syn_cwpphwgencnvfn] using (Nominal.classEqRefl (syn_cwpphwgencnvfn)))
  have p0054 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwgencnvfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn)) p0053
  have p0055 :=
    @g_mpbir (syn_wfn (syn_cwpphwgencnvfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn)) (syn_cvv)) p0052 p0054
  have p0056 :=
    @g_imageswapfn
  have p0057 :=
    @g_lnimageresfnfn
  have p0058 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn (syn_cvv))))
  have p0059 :=
    @g_hwcodesunivndv
  have p0060 :=
    @g_weex
  have p0061 :=
    @g_eqeltri (syn_chwcodes (syn_cvv)) (syn_cwe) (syn_cvv) p0059 p0060
  have p0062 :=
    @g_hwrelsex
  have p0063 :=
    @g_inex (syn_chwcodes (syn_cvv)) (syn_chwrels) p0061 p0062
  have p0064 :=
    @g_eqeltri (syn_chwcn (syn_cvv)) (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels)) (syn_cvv) p0058 p0063
  have p0065 :=
    @g_cnvex (syn_chwcn (syn_cvv)) p0064
  have p0066 :=
    @g_fnconstg (syn_cvv) (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cvv)
  have p0067 :=
    Nominal.mp p0065 p0066
  have p0068 :=
    @g_ssetex
  have p0069 :=
    @g_cnvex (syn_csset) p0068
  have p0070 :=
    @g_wppimagefn (syn_ccnv (syn_csset)) p0069
  have p0071 :=
    (by simpa [syn_cwpppowsetfn] using (Nominal.classEqRefl (syn_cwpppowsetfn)))
  have p0072 :=
    @g_fneq1i (syn_cvv) (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) p0071
  have p0073 :=
    @g_mpbir (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) (syn_wfn (syn_cimage (syn_ccnv (syn_csset))) (syn_cvv)) p0070 p0072
  have p0074 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cvv)) (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) p0067 p0073
  have p0075 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)
  have p0076 :=
    Nominal.mp p0074 p0075
  have p0077 :=
    @g_inidm (syn_cvv)
  have p0078 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0077
  have p0079 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cvv)) p0076 p0078
  have p0080 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0057 p0079
  have p0081 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn))) p0056 p0080
  have p0082 :=
    (by simpa [syn_cwpphwcnsetfn] using (Nominal.classEqRefl (syn_cwpphwcnsetfn)))
  have p0083 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwcnsetfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) p0082
  have p0084 :=
    @g_mpbir (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) (syn_cvv)) p0081 p0083
  have p0085 :=
    @g_pm3_2i (syn_wfn (syn_cwpphwgencnvfn) (syn_cvv)) (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) p0055 p0084
  have p0086 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)
  have p0087 :=
    Nominal.mp p0085 p0086
  have p0088 :=
    @g_inidm (syn_cvv)
  have p0089 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) p0088
  have p0090 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) (syn_cvv)) p0087 p0089
  have p0091 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) p0003 p0090
  have p0092 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn))) p0002 p0091
  have p0093 :=
    (by simpa [syn_cwpphwnisosetfn] using (Nominal.classEqRefl (syn_cwpphwnisosetfn)))
  have p0094 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwnisosetfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)))) p0093
  have p0095 :=
    @g_mpbir (syn_wfn (syn_cwpphwnisosetfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)))) (syn_cvv)) p0092 p0094
  have p0096 :=
    @g_imageswapfn
  have p0097 :=
    @g_lnimageresfnfn
  have p0098 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn (syn_cvv))))
  have p0099 :=
    @g_hwcodesunivndv
  have p0100 :=
    @g_weex
  have p0101 :=
    @g_eqeltri (syn_chwcodes (syn_cvv)) (syn_cwe) (syn_cvv) p0099 p0100
  have p0102 :=
    @g_hwrelsex
  have p0103 :=
    @g_inex (syn_chwcodes (syn_cvv)) (syn_chwrels) p0101 p0102
  have p0104 :=
    @g_eqeltri (syn_chwcn (syn_cvv)) (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels)) (syn_cvv) p0098 p0103
  have p0105 :=
    @g_cnvex (syn_chwcn (syn_cvv)) p0104
  have p0106 :=
    @g_fnconstg (syn_cvv) (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cvv)
  have p0107 :=
    Nominal.mp p0105 p0106
  have p0108 :=
    @g_ssetex
  have p0109 :=
    @g_cnvex (syn_csset) p0108
  have p0110 :=
    @g_wppimagefn (syn_ccnv (syn_csset)) p0109
  have p0111 :=
    (by simpa [syn_cwpppowsetfn] using (Nominal.classEqRefl (syn_cwpppowsetfn)))
  have p0112 :=
    @g_fneq1i (syn_cvv) (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) p0111
  have p0113 :=
    @g_mpbir (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) (syn_wfn (syn_cimage (syn_ccnv (syn_csset))) (syn_cvv)) p0110 p0112
  have p0114 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cvv)) (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) p0107 p0113
  have p0115 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)
  have p0116 :=
    Nominal.mp p0114 p0115
  have p0117 :=
    @g_inidm (syn_cvv)
  have p0118 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0117
  have p0119 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cvv)) p0116 p0118
  have p0120 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0097 p0119
  have p0121 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn))) p0096 p0120
  have p0122 :=
    (by simpa [syn_cwpphwcnsetfn] using (Nominal.classEqRefl (syn_cwpphwcnsetfn)))
  have p0123 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwcnsetfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) p0122
  have p0124 :=
    @g_mpbir (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) (syn_cvv)) p0121 p0123
  have p0125 :=
    @g_snex A
  have p0126 :=
    @g_fvtxpvv (syn_csn A) (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn) p0095 p0124 p0125
  have p0127 :=
    @g_wpphwnisosetfnvalndv A hyp_wpphnpairfnvalndv_1
  have p0128 :=
    @g_wpphwcnsetfnvalndv A hyp_wpphnpairfnvalndv_1
  have p0129 :=
    @g_opeq12i (syn_cfv (syn_cwpphwnisosetfn) (syn_csn A)) (syn_chwniso A) (syn_cfv (syn_cwpphwcnsetfn) (syn_csn A)) (syn_chwcn A) p0127 p0128
  have p0130 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn)) (syn_csn A)) (syn_cop (syn_cfv (syn_cwpphwnisosetfn) (syn_csn A)) (syn_cfv (syn_cwpphwcnsetfn) (syn_csn A))) (syn_cop (syn_chwniso A) (syn_chwcn A)) p0126 p0129
  have p0131 :=
    @g_eqtri (syn_cfv (syn_cwpphnpairfn) (syn_csn A)) (syn_cfv (syn_ctxp (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn)) (syn_csn A)) (syn_cop (syn_chwniso A) (syn_chwcn A)) p0001 p0130
  exact p0131

#print axioms g_wpphnpairfnvalndv

end NFChoice.DirectNominalPrf.WPPReplay
