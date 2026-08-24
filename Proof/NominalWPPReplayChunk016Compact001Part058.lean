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
import NominalWPPReplayChunk016Compact001Part057

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

noncomputable def g_wpphninputfnexndv
     :
    Nominal.NPrf (.classMem (syn_cwpphninputfn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_cwpphninputfn] using (Nominal.classEqRefl (syn_cwpphninputfn)))
  have p0001 :=
    (by simpa [syn_cwpphnpairfn] using (Nominal.classEqRefl (syn_cwpphnpairfn)))
  have p0002 :=
    (by simpa [syn_cwpphwnisosetfn] using (Nominal.classEqRefl (syn_cwpphwnisosetfn)))
  have p0003 :=
    @g_swapex
  have p0004 :=
    @g_imageex (syn_cswap) p0003
  have p0005 :=
    @g_lnimageresfnex
  have p0006 :=
    (by simpa [syn_cwpphwgencnvfn] using (Nominal.classEqRefl (syn_cwpphwgencnvfn)))
  have p0007 :=
    @g_swapex
  have p0008 :=
    @g_imageex (syn_cswap) p0007
  have p0009 :=
    (by simpa [syn_cwpphwgendomfn] using (Nominal.classEqRefl (syn_cwpphwgendomfn)))
  have p0010 :=
    @g_lnimageresfnex
  have p0011 :=
    @g_vvex
  have p0012 :=
    @g_snex (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
  have p0013 :=
    @g_xpex (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))) p0011 p0012
  have p0014 :=
    (by simpa [syn_cwpphwcnsetfn] using (Nominal.classEqRefl (syn_cwpphwcnsetfn)))
  have p0015 :=
    @g_swapex
  have p0016 :=
    @g_imageex (syn_cswap) p0015
  have p0017 :=
    @g_lnimageresfnex
  have p0018 :=
    @g_vvex
  have p0019 :=
    @g_snex (syn_ccnv (syn_chwcn (syn_cvv)))
  have p0020 :=
    @g_xpex (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))) p0018 p0019
  have p0021 :=
    (by simpa [syn_cwpppowsetfn] using (Nominal.classEqRefl (syn_cwpppowsetfn)))
  have p0022 :=
    @g_ssetex
  have p0023 :=
    @g_cnvex (syn_csset) p0022
  have p0024 :=
    @g_imageex (syn_ccnv (syn_csset)) p0023
  have p0025 :=
    @g_eqeltri (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) (syn_cvv) p0021 p0024
  have p0026 :=
    @g_txpex (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn) p0020 p0025
  have p0027 :=
    @g_coex (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0017 p0026
  have p0028 :=
    @g_coex (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn))) p0016 p0027
  have p0029 :=
    @g_eqeltri (syn_cwpphwcnsetfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) (syn_cvv) p0014 p0028
  have p0030 :=
    @g_txpex (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn) p0013 p0029
  have p0031 :=
    @g_coex (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)) p0010 p0030
  have p0032 :=
    @g_eqeltri (syn_cwpphwgendomfn) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn))) (syn_cvv) p0009 p0031
  have p0033 :=
    @g_coex (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn) p0008 p0032
  have p0034 :=
    @g_eqeltri (syn_cwpphwgencnvfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn)) (syn_cvv) p0006 p0033
  have p0035 :=
    (by simpa [syn_cwpphwcnsetfn] using (Nominal.classEqRefl (syn_cwpphwcnsetfn)))
  have p0036 :=
    @g_swapex
  have p0037 :=
    @g_imageex (syn_cswap) p0036
  have p0038 :=
    @g_lnimageresfnex
  have p0039 :=
    @g_vvex
  have p0040 :=
    @g_snex (syn_ccnv (syn_chwcn (syn_cvv)))
  have p0041 :=
    @g_xpex (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))) p0039 p0040
  have p0042 :=
    (by simpa [syn_cwpppowsetfn] using (Nominal.classEqRefl (syn_cwpppowsetfn)))
  have p0043 :=
    @g_ssetex
  have p0044 :=
    @g_cnvex (syn_csset) p0043
  have p0045 :=
    @g_imageex (syn_ccnv (syn_csset)) p0044
  have p0046 :=
    @g_eqeltri (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) (syn_cvv) p0042 p0045
  have p0047 :=
    @g_txpex (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn) p0041 p0046
  have p0048 :=
    @g_coex (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0038 p0047
  have p0049 :=
    @g_coex (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn))) p0037 p0048
  have p0050 :=
    @g_eqeltri (syn_cwpphwcnsetfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) (syn_cvv) p0035 p0049
  have p0051 :=
    @g_txpex (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn) p0034 p0050
  have p0052 :=
    @g_coex (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) p0005 p0051
  have p0053 :=
    @g_coex (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn))) p0004 p0052
  have p0054 :=
    @g_eqeltri (syn_cwpphwnisosetfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)))) (syn_cvv) p0002 p0053
  have p0055 :=
    (by simpa [syn_cwpphwcnsetfn] using (Nominal.classEqRefl (syn_cwpphwcnsetfn)))
  have p0056 :=
    @g_swapex
  have p0057 :=
    @g_imageex (syn_cswap) p0056
  have p0058 :=
    @g_lnimageresfnex
  have p0059 :=
    @g_vvex
  have p0060 :=
    @g_snex (syn_ccnv (syn_chwcn (syn_cvv)))
  have p0061 :=
    @g_xpex (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv)))) p0059 p0060
  have p0062 :=
    (by simpa [syn_cwpppowsetfn] using (Nominal.classEqRefl (syn_cwpppowsetfn)))
  have p0063 :=
    @g_ssetex
  have p0064 :=
    @g_cnvex (syn_csset) p0063
  have p0065 :=
    @g_imageex (syn_ccnv (syn_csset)) p0064
  have p0066 :=
    @g_eqeltri (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) (syn_cvv) p0062 p0065
  have p0067 :=
    @g_txpex (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn) p0061 p0066
  have p0068 :=
    @g_coex (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0058 p0067
  have p0069 :=
    @g_coex (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn))) p0057 p0068
  have p0070 :=
    @g_eqeltri (syn_cwpphwcnsetfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) (syn_cvv) p0055 p0069
  have p0071 :=
    @g_txpex (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn) p0054 p0070
  have p0072 :=
    @g_eqeltri (syn_cwpphnpairfn) (syn_ctxp (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn)) (syn_cvv) p0001 p0071
  have p0073 :=
    @g_siex (syn_cwpphnpairfn) p0072
  have p0074 :=
    @g_eqeltri (syn_cwpphninputfn) (syn_csi (syn_cwpphnpairfn)) (syn_cvv) p0000 p0073
  exact p0074

noncomputable def g_wpphninputfnmapndv
     :
    Nominal.NPrf (syn_wf (syn_cwpphninputfn) (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_imageswapfn
  have p0001 :=
    @g_lnimageresfnfn
  have p0002 :=
    @g_imageswapfn
  have p0003 :=
    @g_lnimageresfnfn
  have p0004 :=
    @g_hwgenex
  have p0005 :=
    @g_hwbijex
  have p0006 :=
    @g_vvex
  have p0007 :=
    @g_xpex (syn_chwbij) (syn_cvv) p0005 p0006
  have p0008 :=
    @g_imaex (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)) p0004 p0007
  have p0009 :=
    @g_fnconstg (syn_cvv) (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cvv)
  have p0010 :=
    Nominal.mp p0008 p0009
  have p0011 :=
    @g_imageswapfn
  have p0012 :=
    @g_lnimageresfnfn
  have p0013 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn (syn_cvv))))
  have p0014 :=
    @g_hwcodesunivndv
  have p0015 :=
    @g_weex
  have p0016 :=
    @g_eqeltri (syn_chwcodes (syn_cvv)) (syn_cwe) (syn_cvv) p0014 p0015
  have p0017 :=
    @g_hwrelsex
  have p0018 :=
    @g_inex (syn_chwcodes (syn_cvv)) (syn_chwrels) p0016 p0017
  have p0019 :=
    @g_eqeltri (syn_chwcn (syn_cvv)) (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels)) (syn_cvv) p0013 p0018
  have p0020 :=
    @g_cnvex (syn_chwcn (syn_cvv)) p0019
  have p0021 :=
    @g_fnconstg (syn_cvv) (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cvv)
  have p0022 :=
    Nominal.mp p0020 p0021
  have p0023 :=
    @g_ssetex
  have p0024 :=
    @g_cnvex (syn_csset) p0023
  have p0025 :=
    @g_wppimagefn (syn_ccnv (syn_csset)) p0024
  have p0026 :=
    (by simpa [syn_cwpppowsetfn] using (Nominal.classEqRefl (syn_cwpppowsetfn)))
  have p0027 :=
    @g_fneq1i (syn_cvv) (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) p0026
  have p0028 :=
    @g_mpbir (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) (syn_wfn (syn_cimage (syn_ccnv (syn_csset))) (syn_cvv)) p0025 p0027
  have p0029 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cvv)) (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) p0022 p0028
  have p0030 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)
  have p0031 :=
    Nominal.mp p0029 p0030
  have p0032 :=
    @g_inidm (syn_cvv)
  have p0033 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0032
  have p0034 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cvv)) p0031 p0033
  have p0035 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0012 p0034
  have p0036 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn))) p0011 p0035
  have p0037 :=
    (by simpa [syn_cwpphwcnsetfn] using (Nominal.classEqRefl (syn_cwpphwcnsetfn)))
  have p0038 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwcnsetfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) p0037
  have p0039 :=
    @g_mpbir (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) (syn_cvv)) p0036 p0038
  have p0040 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cvv)) (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) p0010 p0039
  have p0041 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)
  have p0042 :=
    Nominal.mp p0040 p0041
  have p0043 :=
    @g_inidm (syn_cvv)
  have p0044 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)) p0043
  have p0045 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)) (syn_cvv)) p0042 p0044
  have p0046 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)) p0003 p0045
  have p0047 :=
    (by simpa [syn_cwpphwgendomfn] using (Nominal.classEqRefl (syn_cwpphwgendomfn)))
  have p0048 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwgendomfn) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn))) p0047
  have p0049 :=
    @g_mpbir (syn_wfn (syn_cwpphwgendomfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn))) (syn_cvv)) p0046 p0048
  have p0050 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn) p0002 p0049
  have p0051 :=
    (by simpa [syn_cwpphwgencnvfn] using (Nominal.classEqRefl (syn_cwpphwgencnvfn)))
  have p0052 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwgencnvfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn)) p0051
  have p0053 :=
    @g_mpbir (syn_wfn (syn_cwpphwgencnvfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn)) (syn_cvv)) p0050 p0052
  have p0054 :=
    @g_imageswapfn
  have p0055 :=
    @g_lnimageresfnfn
  have p0056 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn (syn_cvv))))
  have p0057 :=
    @g_hwcodesunivndv
  have p0058 :=
    @g_weex
  have p0059 :=
    @g_eqeltri (syn_chwcodes (syn_cvv)) (syn_cwe) (syn_cvv) p0057 p0058
  have p0060 :=
    @g_hwrelsex
  have p0061 :=
    @g_inex (syn_chwcodes (syn_cvv)) (syn_chwrels) p0059 p0060
  have p0062 :=
    @g_eqeltri (syn_chwcn (syn_cvv)) (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels)) (syn_cvv) p0056 p0061
  have p0063 :=
    @g_cnvex (syn_chwcn (syn_cvv)) p0062
  have p0064 :=
    @g_fnconstg (syn_cvv) (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cvv)
  have p0065 :=
    Nominal.mp p0063 p0064
  have p0066 :=
    @g_ssetex
  have p0067 :=
    @g_cnvex (syn_csset) p0066
  have p0068 :=
    @g_wppimagefn (syn_ccnv (syn_csset)) p0067
  have p0069 :=
    (by simpa [syn_cwpppowsetfn] using (Nominal.classEqRefl (syn_cwpppowsetfn)))
  have p0070 :=
    @g_fneq1i (syn_cvv) (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) p0069
  have p0071 :=
    @g_mpbir (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) (syn_wfn (syn_cimage (syn_ccnv (syn_csset))) (syn_cvv)) p0068 p0070
  have p0072 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cvv)) (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) p0065 p0071
  have p0073 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)
  have p0074 :=
    Nominal.mp p0072 p0073
  have p0075 :=
    @g_inidm (syn_cvv)
  have p0076 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0075
  have p0077 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cvv)) p0074 p0076
  have p0078 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0055 p0077
  have p0079 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn))) p0054 p0078
  have p0080 :=
    (by simpa [syn_cwpphwcnsetfn] using (Nominal.classEqRefl (syn_cwpphwcnsetfn)))
  have p0081 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwcnsetfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) p0080
  have p0082 :=
    @g_mpbir (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) (syn_cvv)) p0079 p0081
  have p0083 :=
    @g_pm3_2i (syn_wfn (syn_cwpphwgencnvfn) (syn_cvv)) (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) p0053 p0082
  have p0084 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)
  have p0085 :=
    Nominal.mp p0083 p0084
  have p0086 :=
    @g_inidm (syn_cvv)
  have p0087 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) p0086
  have p0088 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) (syn_cvv)) p0085 p0087
  have p0089 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) p0001 p0088
  have p0090 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn))) p0000 p0089
  have p0091 :=
    (by simpa [syn_cwpphwnisosetfn] using (Nominal.classEqRefl (syn_cwpphwnisosetfn)))
  have p0092 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwnisosetfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)))) p0091
  have p0093 :=
    @g_mpbir (syn_wfn (syn_cwpphwnisosetfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)))) (syn_cvv)) p0090 p0092
  have p0094 :=
    @g_imageswapfn
  have p0095 :=
    @g_lnimageresfnfn
  have p0096 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn (syn_cvv))))
  have p0097 :=
    @g_hwcodesunivndv
  have p0098 :=
    @g_weex
  have p0099 :=
    @g_eqeltri (syn_chwcodes (syn_cvv)) (syn_cwe) (syn_cvv) p0097 p0098
  have p0100 :=
    @g_hwrelsex
  have p0101 :=
    @g_inex (syn_chwcodes (syn_cvv)) (syn_chwrels) p0099 p0100
  have p0102 :=
    @g_eqeltri (syn_chwcn (syn_cvv)) (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels)) (syn_cvv) p0096 p0101
  have p0103 :=
    @g_cnvex (syn_chwcn (syn_cvv)) p0102
  have p0104 :=
    @g_fnconstg (syn_cvv) (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cvv)
  have p0105 :=
    Nominal.mp p0103 p0104
  have p0106 :=
    @g_ssetex
  have p0107 :=
    @g_cnvex (syn_csset) p0106
  have p0108 :=
    @g_wppimagefn (syn_ccnv (syn_csset)) p0107
  have p0109 :=
    (by simpa [syn_cwpppowsetfn] using (Nominal.classEqRefl (syn_cwpppowsetfn)))
  have p0110 :=
    @g_fneq1i (syn_cvv) (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) p0109
  have p0111 :=
    @g_mpbir (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) (syn_wfn (syn_cimage (syn_ccnv (syn_csset))) (syn_cvv)) p0108 p0110
  have p0112 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cvv)) (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) p0105 p0111
  have p0113 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)
  have p0114 :=
    Nominal.mp p0112 p0113
  have p0115 :=
    @g_inidm (syn_cvv)
  have p0116 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0115
  have p0117 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cvv)) p0114 p0116
  have p0118 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0095 p0117
  have p0119 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn))) p0094 p0118
  have p0120 :=
    (by simpa [syn_cwpphwcnsetfn] using (Nominal.classEqRefl (syn_cwpphwcnsetfn)))
  have p0121 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwcnsetfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) p0120
  have p0122 :=
    @g_mpbir (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) (syn_cvv)) p0119 p0121
  have p0123 :=
    @g_pm3_2i (syn_wfn (syn_cwpphwnisosetfn) (syn_cvv)) (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) p0093 p0122
  have p0124 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn)
  have p0125 :=
    Nominal.mp p0123 p0124
  have p0126 :=
    @g_inidm (syn_cvv)
  have p0127 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn)) p0126
  have p0128 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn)) (syn_cvv)) p0125 p0127
  have p0129 :=
    (by simpa [syn_cwpphnpairfn] using (Nominal.classEqRefl (syn_cwpphnpairfn)))
  have p0130 :=
    @g_fneq1i (syn_cvv) (syn_cwpphnpairfn) (syn_ctxp (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn)) p0129
  have p0131 :=
    @g_mpbir (syn_wfn (syn_cwpphnpairfn) (syn_cvv)) (syn_wfn (syn_ctxp (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn)) (syn_cvv)) p0128 p0130
  have p0132 :=
    @g_ssv (syn_crn (syn_cwpphnpairfn))
  have p0133 :=
    @g_pm3_2i (syn_wfn (syn_cwpphnpairfn) (syn_cvv)) (syn_wss (syn_crn (syn_cwpphnpairfn)) (syn_cvv)) p0131 p0132
  have p0134 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf (syn_cwpphnpairfn) (syn_cvv) (syn_cvv))))
  have p0135 :=
    @g_mpbir (syn_wf (syn_cwpphnpairfn) (syn_cvv) (syn_cvv)) (syn_wa (syn_wfn (syn_cwpphnpairfn) (syn_cvv)) (syn_wss (syn_crn (syn_cwpphnpairfn)) (syn_cvv))) p0133 p0134
  have p0136 :=
    @g_sifmap (syn_cvv) (syn_cvv) (syn_cwpphnpairfn)
  have p0137 :=
    Nominal.mp p0135 p0136
  have p0138 :=
    (by simpa [syn_cwpphninputfn] using (Nominal.classEqRefl (syn_cwpphninputfn)))
  have p0139 :=
    @g_feq1i (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)) (syn_cwpphninputfn) (syn_csi (syn_cwpphnpairfn)) p0138
  have p0140 :=
    @g_mpbir (syn_wf (syn_cwpphninputfn) (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) (syn_wf (syn_csi (syn_cwpphnpairfn)) (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))) p0137 p0139
  exact p0140

noncomputable def g_wpphninputfnvalndv
    (A : Class) (hyp_wpphninputfnvalndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cwpphninputfn) (syn_csn (syn_csn A))) (syn_csn (syn_cop (syn_chwniso A) (syn_chwcn A)))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    (by simpa [syn_cwpphninputfn] using (Nominal.classEqRefl (syn_cwpphninputfn)))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_csn A)) (syn_cwpphninputfn) (syn_csi (syn_cwpphnpairfn)) p0000
  have p0002 :=
    @g_snex A
  have p0003 :=
    @g_imageswapfn
  have p0004 :=
    @g_lnimageresfnfn
  have p0005 :=
    @g_imageswapfn
  have p0006 :=
    @g_lnimageresfnfn
  have p0007 :=
    @g_hwgenex
  have p0008 :=
    @g_hwbijex
  have p0009 :=
    @g_vvex
  have p0010 :=
    @g_xpex (syn_chwbij) (syn_cvv) p0008 p0009
  have p0011 :=
    @g_imaex (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)) p0007 p0010
  have p0012 :=
    @g_fnconstg (syn_cvv) (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cvv)
  have p0013 :=
    Nominal.mp p0011 p0012
  have p0014 :=
    @g_imageswapfn
  have p0015 :=
    @g_lnimageresfnfn
  have p0016 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn (syn_cvv))))
  have p0017 :=
    @g_hwcodesunivndv
  have p0018 :=
    @g_weex
  have p0019 :=
    @g_eqeltri (syn_chwcodes (syn_cvv)) (syn_cwe) (syn_cvv) p0017 p0018
  have p0020 :=
    @g_hwrelsex
  have p0021 :=
    @g_inex (syn_chwcodes (syn_cvv)) (syn_chwrels) p0019 p0020
  have p0022 :=
    @g_eqeltri (syn_chwcn (syn_cvv)) (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels)) (syn_cvv) p0016 p0021
  have p0023 :=
    @g_cnvex (syn_chwcn (syn_cvv)) p0022
  have p0024 :=
    @g_fnconstg (syn_cvv) (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cvv)
  have p0025 :=
    Nominal.mp p0023 p0024
  have p0026 :=
    @g_ssetex
  have p0027 :=
    @g_cnvex (syn_csset) p0026
  have p0028 :=
    @g_wppimagefn (syn_ccnv (syn_csset)) p0027
  have p0029 :=
    (by simpa [syn_cwpppowsetfn] using (Nominal.classEqRefl (syn_cwpppowsetfn)))
  have p0030 :=
    @g_fneq1i (syn_cvv) (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) p0029
  have p0031 :=
    @g_mpbir (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) (syn_wfn (syn_cimage (syn_ccnv (syn_csset))) (syn_cvv)) p0028 p0030
  have p0032 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cvv)) (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) p0025 p0031
  have p0033 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)
  have p0034 :=
    Nominal.mp p0032 p0033
  have p0035 :=
    @g_inidm (syn_cvv)
  have p0036 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0035
  have p0037 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cvv)) p0034 p0036
  have p0038 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0015 p0037
  have p0039 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn))) p0014 p0038
  have p0040 :=
    (by simpa [syn_cwpphwcnsetfn] using (Nominal.classEqRefl (syn_cwpphwcnsetfn)))
  have p0041 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwcnsetfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) p0040
  have p0042 :=
    @g_mpbir (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) (syn_cvv)) p0039 p0041
  have p0043 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cvv)) (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) p0013 p0042
  have p0044 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)
  have p0045 :=
    Nominal.mp p0043 p0044
  have p0046 :=
    @g_inidm (syn_cvv)
  have p0047 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)) p0046
  have p0048 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)) (syn_cvv)) p0045 p0047
  have p0049 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn)) p0006 p0048
  have p0050 :=
    (by simpa [syn_cwpphwgendomfn] using (Nominal.classEqRefl (syn_cwpphwgendomfn)))
  have p0051 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwgendomfn) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn))) p0050
  have p0052 :=
    @g_mpbir (syn_wfn (syn_cwpphwgendomfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))))) (syn_cwpphwcnsetfn))) (syn_cvv)) p0049 p0051
  have p0053 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn) p0005 p0052
  have p0054 :=
    (by simpa [syn_cwpphwgencnvfn] using (Nominal.classEqRefl (syn_cwpphwgencnvfn)))
  have p0055 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwgencnvfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn)) p0054
  have p0056 :=
    @g_mpbir (syn_wfn (syn_cwpphwgencnvfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_cwpphwgendomfn)) (syn_cvv)) p0053 p0055
  have p0057 :=
    @g_imageswapfn
  have p0058 :=
    @g_lnimageresfnfn
  have p0059 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn (syn_cvv))))
  have p0060 :=
    @g_hwcodesunivndv
  have p0061 :=
    @g_weex
  have p0062 :=
    @g_eqeltri (syn_chwcodes (syn_cvv)) (syn_cwe) (syn_cvv) p0060 p0061
  have p0063 :=
    @g_hwrelsex
  have p0064 :=
    @g_inex (syn_chwcodes (syn_cvv)) (syn_chwrels) p0062 p0063
  have p0065 :=
    @g_eqeltri (syn_chwcn (syn_cvv)) (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels)) (syn_cvv) p0059 p0064
  have p0066 :=
    @g_cnvex (syn_chwcn (syn_cvv)) p0065
  have p0067 :=
    @g_fnconstg (syn_cvv) (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cvv)
  have p0068 :=
    Nominal.mp p0066 p0067
  have p0069 :=
    @g_ssetex
  have p0070 :=
    @g_cnvex (syn_csset) p0069
  have p0071 :=
    @g_wppimagefn (syn_ccnv (syn_csset)) p0070
  have p0072 :=
    (by simpa [syn_cwpppowsetfn] using (Nominal.classEqRefl (syn_cwpppowsetfn)))
  have p0073 :=
    @g_fneq1i (syn_cvv) (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) p0072
  have p0074 :=
    @g_mpbir (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) (syn_wfn (syn_cimage (syn_ccnv (syn_csset))) (syn_cvv)) p0071 p0073
  have p0075 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cvv)) (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) p0068 p0074
  have p0076 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)
  have p0077 :=
    Nominal.mp p0075 p0076
  have p0078 :=
    @g_inidm (syn_cvv)
  have p0079 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0078
  have p0080 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cvv)) p0077 p0079
  have p0081 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0058 p0080
  have p0082 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn))) p0057 p0081
  have p0083 :=
    (by simpa [syn_cwpphwcnsetfn] using (Nominal.classEqRefl (syn_cwpphwcnsetfn)))
  have p0084 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwcnsetfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) p0083
  have p0085 :=
    @g_mpbir (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) (syn_cvv)) p0082 p0084
  have p0086 :=
    @g_pm3_2i (syn_wfn (syn_cwpphwgencnvfn) (syn_cvv)) (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) p0056 p0085
  have p0087 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)
  have p0088 :=
    Nominal.mp p0086 p0087
  have p0089 :=
    @g_inidm (syn_cvv)
  have p0090 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) p0089
  have p0091 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) (syn_cvv)) p0088 p0090
  have p0092 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)) p0004 p0091
  have p0093 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn))) p0003 p0092
  have p0094 :=
    (by simpa [syn_cwpphwnisosetfn] using (Nominal.classEqRefl (syn_cwpphwnisosetfn)))
  have p0095 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwnisosetfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)))) p0094
  have p0096 :=
    @g_mpbir (syn_wfn (syn_cwpphwnisosetfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cwpphwgencnvfn) (syn_cwpphwcnsetfn)))) (syn_cvv)) p0093 p0095
  have p0097 :=
    @g_imageswapfn
  have p0098 :=
    @g_lnimageresfnfn
  have p0099 :=
    (by simpa [syn_chwcn] using (Nominal.classEqRefl (syn_chwcn (syn_cvv))))
  have p0100 :=
    @g_hwcodesunivndv
  have p0101 :=
    @g_weex
  have p0102 :=
    @g_eqeltri (syn_chwcodes (syn_cvv)) (syn_cwe) (syn_cvv) p0100 p0101
  have p0103 :=
    @g_hwrelsex
  have p0104 :=
    @g_inex (syn_chwcodes (syn_cvv)) (syn_chwrels) p0102 p0103
  have p0105 :=
    @g_eqeltri (syn_chwcn (syn_cvv)) (syn_cin (syn_chwcodes (syn_cvv)) (syn_chwrels)) (syn_cvv) p0099 p0104
  have p0106 :=
    @g_cnvex (syn_chwcn (syn_cvv)) p0105
  have p0107 :=
    @g_fnconstg (syn_cvv) (syn_ccnv (syn_chwcn (syn_cvv))) (syn_cvv)
  have p0108 :=
    Nominal.mp p0106 p0107
  have p0109 :=
    @g_ssetex
  have p0110 :=
    @g_cnvex (syn_csset) p0109
  have p0111 :=
    @g_wppimagefn (syn_ccnv (syn_csset)) p0110
  have p0112 :=
    (by simpa [syn_cwpppowsetfn] using (Nominal.classEqRefl (syn_cwpppowsetfn)))
  have p0113 :=
    @g_fneq1i (syn_cvv) (syn_cwpppowsetfn) (syn_cimage (syn_ccnv (syn_csset))) p0112
  have p0114 :=
    @g_mpbir (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) (syn_wfn (syn_cimage (syn_ccnv (syn_csset))) (syn_cvv)) p0111 p0113
  have p0115 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cvv)) (syn_wfn (syn_cwpppowsetfn) (syn_cvv)) p0108 p0114
  have p0116 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)
  have p0117 :=
    Nominal.mp p0115 p0116
  have p0118 :=
    @g_inidm (syn_cvv)
  have p0119 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0118
  have p0120 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) (syn_cvv)) p0117 p0119
  have p0121 :=
    @g_fncovv (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)) p0098 p0120
  have p0122 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn))) p0097 p0121
  have p0123 :=
    (by simpa [syn_cwpphwcnsetfn] using (Nominal.classEqRefl (syn_cwpphwcnsetfn)))
  have p0124 :=
    @g_fneq1i (syn_cvv) (syn_cwpphwcnsetfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) p0123
  have p0125 :=
    @g_mpbir (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_ccom (syn_clnimageresfn) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn (syn_ccnv (syn_chwcn (syn_cvv))))) (syn_cwpppowsetfn)))) (syn_cvv)) p0122 p0124
  have p0126 :=
    @g_pm3_2i (syn_wfn (syn_cwpphwnisosetfn) (syn_cvv)) (syn_wfn (syn_cwpphwcnsetfn) (syn_cvv)) p0096 p0125
  have p0127 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn)
  have p0128 :=
    Nominal.mp p0126 p0127
  have p0129 :=
    @g_inidm (syn_cvv)
  have p0130 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn)) p0129
  have p0131 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn)) (syn_cvv)) p0128 p0130
  have p0132 :=
    (by simpa [syn_cwpphnpairfn] using (Nominal.classEqRefl (syn_cwpphnpairfn)))
  have p0133 :=
    @g_fneq1i (syn_cvv) (syn_cwpphnpairfn) (syn_ctxp (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn)) p0132
  have p0134 :=
    @g_mpbir (syn_wfn (syn_cwpphnpairfn) (syn_cvv)) (syn_wfn (syn_ctxp (syn_cwpphwnisosetfn) (syn_cwpphwcnsetfn)) (syn_cvv)) p0131 p0133
  have p0135 :=
    @g_ssv (syn_crn (syn_cwpphnpairfn))
  have p0136 :=
    @g_pm3_2i (syn_wfn (syn_cwpphnpairfn) (syn_cvv)) (syn_wss (syn_crn (syn_cwpphnpairfn)) (syn_cvv)) p0134 p0135
  have p0137 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf (syn_cwpphnpairfn) (syn_cvv) (syn_cvv))))
  have p0138 :=
    @g_mpbir (syn_wf (syn_cwpphnpairfn) (syn_cvv) (syn_cvv)) (syn_wa (syn_wfn (syn_cwpphnpairfn) (syn_cvv)) (syn_wss (syn_crn (syn_cwpphnpairfn)) (syn_cvv))) p0136 p0137
  have p0139 :=
    @g_sifvald (syn_cvv) (syn_cvv) (syn_csn A) (syn_cwpphnpairfn) p0138
  have p0140 :=
    Nominal.mp p0002 p0139
  have p0141 :=
    @g_wpphnpairfnvalndv A hyp_wpphninputfnvalndv_1
  have p0142 :=
    @g_sneqi (syn_cfv (syn_cwpphnpairfn) (syn_csn A)) (syn_cop (syn_chwniso A) (syn_chwcn A)) p0141
  have p0143 :=
    @g_eqtri (syn_cfv (syn_csi (syn_cwpphnpairfn)) (syn_csn (syn_csn A))) (syn_csn (syn_cfv (syn_cwpphnpairfn) (syn_csn A))) (syn_csn (syn_cop (syn_chwniso A) (syn_chwcn A))) p0140 p0142
  have p0144 :=
    @g_eqtri (syn_cfv (syn_cwpphninputfn) (syn_csn (syn_csn A))) (syn_cfv (syn_csi (syn_cwpphnpairfn)) (syn_csn (syn_csn A))) (syn_csn (syn_cop (syn_chwniso A) (syn_chwcn A))) p0001 p0143
  exact p0144

noncomputable def g_fdpointimagevvdndv
    (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cvv)) (.classEq (syn_cima (syn_cfdpointrel (syn_cvv)) (syn_csn (syn_csn A))) (syn_cpw1 (syn_cpw1 A)))) := by
  let proofSupport : Finset Var := A.fv
  let c : Var := freshVar proofSupport 0
  have fresh_c : c ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_c_not_A : c ∉ A.fv := by
    intro h
    exact fresh_c (h)
  have dv_cache_0001 : c ∉ ((syn_cvv)).fv := by
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : c ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : c ∉ ((Wff.imp (.classMem A (syn_cvv)) (.classEq (syn_cima (syn_cfdpointrel (syn_cvv)) (syn_csn (syn_csn A))) (syn_cpw1 (syn_cpw1 A))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpointrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classMem A (syn_cvv))
  have p0001 :=
    @g_id (.classEq (.cv c) A)
  have p0002 :=
    @g_eleq1d (.classEq (.cv c) A) (.cv c) A (syn_cvv) p0001
  have p0003 :=
    @g_id (.classEq (.cv c) A)
  have p0004 :=
    @g_sneqd (.classEq (.cv c) A) (.cv c) A p0003
  have p0005 :=
    @g_sneqd (.classEq (.cv c) A) (syn_csn (.cv c)) (syn_csn A) p0004
  have p0006 :=
    @g_imaeq2d (.classEq (.cv c) A) (syn_csn (syn_csn (.cv c))) (syn_csn (syn_csn A)) (syn_cfdpointrel (syn_cvv)) p0005
  have p0007 :=
    @g_id (.classEq (.cv c) A)
  have p0008 :=
    @g_pw1eq (.cv c) A
  have p0009 :=
    @g_syl (.classEq (.cv c) A) (.classEq (.cv c) A) (.classEq (syn_cpw1 (.cv c)) (syn_cpw1 A)) p0007 p0008
  have p0010 :=
    @g_pw1eq (syn_cpw1 (.cv c)) (syn_cpw1 A)
  have p0011 :=
    @g_syl (.classEq (.cv c) A) (.classEq (syn_cpw1 (.cv c)) (syn_cpw1 A)) (.classEq (syn_cpw1 (syn_cpw1 (.cv c))) (syn_cpw1 (syn_cpw1 A))) p0009 p0010
  have p0012 :=
    @g_eqeq12d (.classEq (.cv c) A) (syn_cima (syn_cfdpointrel (syn_cvv)) (syn_csn (syn_csn (.cv c)))) (syn_cima (syn_cfdpointrel (syn_cvv)) (syn_csn (syn_csn A))) (syn_cpw1 (syn_cpw1 (.cv c))) (syn_cpw1 (syn_cpw1 A)) p0006 p0011
  have p0013 :=
    @g_imbi12d (.classEq (.cv c) A) (.classMem (.cv c) (syn_cvv)) (.classMem A (syn_cvv)) (.classEq (syn_cima (syn_cfdpointrel (syn_cvv)) (syn_csn (syn_csn (.cv c)))) (syn_cpw1 (syn_cpw1 (.cv c)))) (.classEq (syn_cima (syn_cfdpointrel (syn_cvv)) (syn_csn (syn_csn A))) (syn_cpw1 (syn_cpw1 A))) p0002 p0012
  have p0014 :=
    @g_vvex
  have p0015 :=
    @g_fdpointimage (syn_cvv) c dv_cache_0001 p0014
  have p0016 :=
    @g_vtoclg (.imp (.classMem (.cv c) (syn_cvv)) (.classEq (syn_cima (syn_cfdpointrel (syn_cvv)) (syn_csn (syn_csn (.cv c)))) (syn_cpw1 (syn_cpw1 (.cv c))))) (.imp (.classMem A (syn_cvv)) (.classEq (syn_cima (syn_cfdpointrel (syn_cvv)) (syn_csn (syn_csn A))) (syn_cpw1 (syn_cpw1 A)))) c A (syn_cvv) dv_cache_0002 dv_cache_0003 p0013 p0015
  have p0017 :=
    @g_mpd (.classMem A (syn_cvv)) (.classMem A (syn_cvv)) (.classEq (syn_cima (syn_cfdpointrel (syn_cvv)) (syn_csn (syn_csn A))) (syn_cpw1 (syn_cpw1 A))) p0000 p0016
  exact p0017

noncomputable def g_wppqkrelkernelexndv
     :
    Nominal.NPrf (.classMem (syn_cwppqkrelkernel) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_cwppqkrelkernel] using (Nominal.classEqRefl (syn_cwppqkrelkernel)))
  have p0001 :=
    @g_vvex
  have p0002 :=
    @g_vvex
  have p0003 :=
    @g_vvex
  have p0004 :=
    @g_xpkex (syn_cvv) (syn_cvv) p0002 p0003
  have p0005 :=
    @g_xpkex (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv)) p0001 p0004
  have p0006 :=
    @g_setconslem5
  have p0007 :=
    @g_inex (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) p0005 p0006
  have p0008 :=
    @g_eqeltri (syn_cwppqkrelkernel) (syn_cin (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cvv) p0000 p0007
  exact p0008

noncomputable def g_wppqkrelkernelvalndv
    (A : Class) :
    Nominal.NPrf (.classEq (syn_cimak (syn_cwppqkrelkernel) (syn_cpw1 (syn_cpw1 A))) (syn_cqkrel A)) := by
  let proofSupport : Finset Var := A.fv
  let z : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_z_ne_x : z ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0005 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0006 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    (by simpa [syn_cwppqkrelkernel] using (Nominal.classEqRefl (syn_cwppqkrelkernel)))
  have p0001 :=
    @g_imakeq1i (syn_cwppqkrelkernel) (syn_cin (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 A)) p0000
  have p0002 :=
    @g_setconslem6 x y z A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_qkrel x y z A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0004 :=
    @g_eqtr4i (syn_cimak (syn_cin (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 A))) (.cab z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_copk (.cv x) (.cv y))) (.classMem (syn_cop (.cv x) (.cv y)) A))))) (syn_cqkrel A) p0002 p0003
  have p0005 :=
    @g_eqtri (syn_cimak (syn_cwppqkrelkernel) (syn_cpw1 (syn_cpw1 A))) (syn_cimak (syn_cin (syn_cxpk (syn_cvv) (syn_cxpk (syn_cvv) (syn_cvv))) (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 A))) (syn_cqkrel A) p0001 p0004
  exact p0005

#print axioms g_wppqkrelkernelvalndv

end NFChoice.DirectNominalPrf.WPPReplay
