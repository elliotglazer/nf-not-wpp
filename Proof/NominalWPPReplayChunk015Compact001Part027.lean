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
import NominalWPPReplayChunk015Compact001Part026

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

noncomputable def g_lnimageopval
    (B : Class) (R : Class) (hyp_lnimageopval_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_lnimageopval_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_clnimageop) (syn_cop R B)) (syn_cima R B)) := by
  let proofSupport : Finset Var := B.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_clnimageop] using (Nominal.classEqRefl (syn_clnimageop)))
  have p0001 :=
    @g_fveq1i (syn_cop R B) (syn_clnimageop) (syn_ccom (syn_cranfn) (syn_clnimageresfn)) p0000
  have p0002 :=
    @g_fnlndifop
  have p0003 :=
    @g_ln1stfn
  have p0004 :=
    @g_fnlndifop
  have p0005 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfn (syn_clndifop) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_clndifop)
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_inidm (syn_cvv)
  have p0009 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c1st) (syn_clndifop)) p0008
  have p0010 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c1st) (syn_clndifop)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c1st) (syn_clndifop)) (syn_cvv)) p0007 p0009
  have p0011 :=
    @g_fncovv (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop)) p0002 p0010
  have p0012 :=
    (by simpa [syn_clninterop] using (Nominal.classEqRefl (syn_clninterop)))
  have p0013 :=
    @g_fneq1i (syn_cvv) (syn_clninterop) (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop))) p0012
  have p0014 :=
    @g_mpbir (syn_wfn (syn_clninterop) (syn_cvv)) (syn_wfn (syn_ccom (syn_clndifop) (syn_ctxp (syn_c1st) (syn_clndifop))) (syn_cvv)) p0011 p0013
  have p0015 :=
    @g_ln1stfn
  have p0016 :=
    @g_fncross
  have p0017 :=
    @g_ln2ndfn
  have p0018 :=
    @g_vvex
  have p0019 :=
    @g_fnconstg (syn_cvv) (syn_cvv) (syn_cvv)
  have p0020 :=
    Nominal.mp p0018 p0019
  have p0021 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (syn_wfn (syn_cxp (syn_cvv) (syn_csn (syn_cvv))) (syn_cvv)) p0017 p0020
  have p0022 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))
  have p0023 :=
    Nominal.mp p0021 p0022
  have p0024 :=
    @g_inidm (syn_cvv)
  have p0025 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) p0024
  have p0026 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) (syn_cvv)) p0023 p0025
  have p0027 :=
    @g_fncovv (syn_ccross) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv)))) p0016 p0026
  have p0028 :=
    (by simpa [syn_clnimagecrossfn] using (Nominal.classEqRefl (syn_clnimagecrossfn)))
  have p0029 :=
    @g_fneq1i (syn_cvv) (syn_clnimagecrossfn) (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))))) p0028
  have p0030 :=
    @g_mpbir (syn_wfn (syn_clnimagecrossfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_ccross) (syn_ctxp (syn_c2nd) (syn_cxp (syn_cvv) (syn_csn (syn_cvv))))) (syn_cvv)) p0027 p0029
  have p0031 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (syn_wfn (syn_clnimagecrossfn) (syn_cvv)) p0015 p0030
  have p0032 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c1st) (syn_clnimagecrossfn)
  have p0033 :=
    Nominal.mp p0031 p0032
  have p0034 :=
    @g_inidm (syn_cvv)
  have p0035 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) p0034
  have p0036 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) (syn_cvv)) p0033 p0035
  have p0037 :=
    @g_fncovv (syn_clninterop) (syn_ctxp (syn_c1st) (syn_clnimagecrossfn)) p0014 p0036
  have p0038 :=
    (by simpa [syn_clnimageresfn] using (Nominal.classEqRefl (syn_clnimageresfn)))
  have p0039 :=
    @g_fneq1i (syn_cvv) (syn_clnimageresfn) (syn_ccom (syn_clninterop) (syn_ctxp (syn_c1st) (syn_clnimagecrossfn))) p0038
  have p0040 :=
    @g_mpbir (syn_wfn (syn_clnimageresfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clninterop) (syn_ctxp (syn_c1st) (syn_clnimagecrossfn))) (syn_cvv)) p0037 p0039
  have p0041 :=
    @g_opex R B hyp_lnimageopval_1 hyp_lnimageopval_2
  have p0042 :=
    @g_pm3_2i (syn_wfn (syn_clnimageresfn) (syn_cvv)) (.classMem (syn_cop R B) (syn_cvv)) p0040 p0041
  have p0043 :=
    @g_fvco2 (syn_cvv) (syn_cop R B) (syn_cranfn) (syn_clnimageresfn)
  have p0044 :=
    Nominal.mp p0042 p0043
  have p0045 :=
    @g_eqtri (syn_cfv (syn_clnimageop) (syn_cop R B)) (syn_cfv (syn_ccom (syn_cranfn) (syn_clnimageresfn)) (syn_cop R B)) (syn_cfv (syn_cranfn) (syn_cfv (syn_clnimageresfn) (syn_cop R B))) p0001 p0044
  have p0046 :=
    @g_lnimageresfnval B R hyp_lnimageopval_1 hyp_lnimageopval_2
  have p0047 :=
    @g_fveq2i (syn_cfv (syn_clnimageresfn) (syn_cop R B)) (syn_cres R B) (syn_cranfn) p0046
  have p0048 :=
    @g_eqtri (syn_cfv (syn_clnimageop) (syn_cop R B)) (syn_cfv (syn_cranfn) (syn_cfv (syn_clnimageresfn) (syn_cop R B))) (syn_cfv (syn_cranfn) (syn_cres R B)) p0045 p0047
  have p0049 :=
    @g_resex R B hyp_lnimageopval_1 hyp_lnimageopval_2
  have p0050 :=
    @g_fvranfn (syn_cres R B) (syn_cvv)
  have p0051 :=
    Nominal.mp p0049 p0050
  have p0052 :=
    @g_eqtri (syn_cfv (syn_clnimageop) (syn_cop R B)) (syn_cfv (syn_cranfn) (syn_cres R B)) (syn_crn (syn_cres R B)) p0048 p0051
  have p0053 :=
    @g_dfima3 R B
  have p0054 :=
    @g_eqcomi (syn_cima R B) (syn_crn (syn_cres R B)) p0053
  have p0055 :=
    @g_eqtri (syn_cfv (syn_clnimageop) (syn_cop R B)) (syn_crn (syn_cres R B)) (syn_cima R B) p0052 p0054
  exact p0055

noncomputable def g_lnpwcnvkerfnval
    (D : Class) (R : Class) (hyp_lnpwcnvkerfnval_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_lnpwcnvkerfnval_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_clnpwcnvkerfn) (syn_cop R D)) (syn_ccnv (syn_clnker R))) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_clnpwcnvkerfn] using (Nominal.classEqRefl (syn_clnpwcnvkerfn)))
  have p0001 :=
    @g_fveq1i (syn_cop R D) (syn_clnpwcnvkerfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_clnpwkerfn)) p0000
  have p0002 :=
    @g_lnpwkerfnfn
  have p0003 :=
    @g_opex R D hyp_lnpwcnvkerfnval_1 hyp_lnpwcnvkerfnval_2
  have p0004 :=
    @g_pm3_2i (syn_wfn (syn_clnpwkerfn) (syn_cvv)) (.classMem (syn_cop R D) (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_fvco2 (syn_cvv) (syn_cop R D) (syn_cimage (syn_cswap)) (syn_clnpwkerfn)
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_eqtri (syn_cfv (syn_clnpwcnvkerfn) (syn_cop R D)) (syn_cfv (syn_ccom (syn_cimage (syn_cswap)) (syn_clnpwkerfn)) (syn_cop R D)) (syn_cfv (syn_cimage (syn_cswap)) (syn_cfv (syn_clnpwkerfn) (syn_cop R D))) p0001 p0006
  have p0008 :=
    @g_lnpwkerfnval D R hyp_lnpwcnvkerfnval_1 hyp_lnpwcnvkerfnval_2
  have p0009 :=
    @g_fveq2i (syn_cfv (syn_clnpwkerfn) (syn_cop R D)) (syn_clnker R) (syn_cimage (syn_cswap)) p0008
  have p0010 :=
    @g_eqtri (syn_cfv (syn_clnpwcnvkerfn) (syn_cop R D)) (syn_cfv (syn_cimage (syn_cswap)) (syn_cfv (syn_clnpwkerfn) (syn_cop R D))) (syn_cfv (syn_cimage (syn_cswap)) (syn_clnker R)) p0007 p0009
  have p0011 :=
    @g_swapex
  have p0012 :=
    @g_lnkerex R hyp_lnpwcnvkerfnval_1
  have p0013 :=
    @g_fvimagecl (syn_clnker R) (syn_cswap) p0011 p0012
  have p0014 :=
    @g_dfcnv2 (syn_clnker R)
  have p0015 :=
    @g_eqcomi (syn_ccnv (syn_clnker R)) (syn_cima (syn_cswap) (syn_clnker R)) p0014
  have p0016 :=
    @g_eqtri (syn_cfv (syn_cimage (syn_cswap)) (syn_clnker R)) (syn_cima (syn_cswap) (syn_clnker R)) (syn_ccnv (syn_clnker R)) p0013 p0015
  have p0017 :=
    @g_eqtri (syn_cfv (syn_clnpwcnvkerfn) (syn_cop R D)) (syn_cfv (syn_cimage (syn_cswap)) (syn_clnker R)) (syn_ccnv (syn_clnker R)) p0010 p0016
  exact p0017

noncomputable def g_lnpwclasspairfnval
    (D : Class) (R : Class) (S : Class) (hyp_lnpwclasspairfnval_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_lnpwclasspairfnval_2 : Nominal.NPrf (.classMem D (syn_cvv))) (hyp_lnpwclasspairfnval_3 : Nominal.NPrf (.classMem S (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_clnpwclasspairfn) (syn_cop (syn_cop R D) S)) (syn_cop (syn_ccnv (syn_clnker R)) S)) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ S.fv
  have p0000 :=
    (by simpa [syn_clnpwclasspairfn] using (Nominal.classEqRefl (syn_clnpwclasspairfn)))
  have p0001 :=
    @g_fveq1i (syn_cop (syn_cop R D) S) (syn_clnpwclasspairfn) (syn_ctxp (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_c2nd)) p0000
  have p0002 :=
    @g_imageswapfn
  have p0003 :=
    @g_lnpwkerfnfn
  have p0004 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_clnpwkerfn) p0002 p0003
  have p0005 :=
    (by simpa [syn_clnpwcnvkerfn] using (Nominal.classEqRefl (syn_clnpwcnvkerfn)))
  have p0006 :=
    @g_fneq1i (syn_cvv) (syn_clnpwcnvkerfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_clnpwkerfn)) p0005
  have p0007 :=
    @g_mpbir (syn_wfn (syn_clnpwcnvkerfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_clnpwkerfn)) (syn_cvv)) p0004 p0006
  have p0008 :=
    @g_ln1stfn
  have p0009 :=
    @g_fncovv (syn_clnpwcnvkerfn) (syn_c1st) p0007 p0008
  have p0010 :=
    @g_ln2ndfn
  have p0011 :=
    @g_opex R D hyp_lnpwclasspairfnval_1 hyp_lnpwclasspairfnval_2
  have p0012 :=
    @g_opex (syn_cop R D) S p0011 hyp_lnpwclasspairfnval_3
  have p0013 :=
    @g_fvtxpvv (syn_cop (syn_cop R D) S) (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_c2nd) p0009 p0010 p0012
  have p0014 :=
    @g_ln1stfn
  have p0015 :=
    @g_opex R D hyp_lnpwclasspairfnval_1 hyp_lnpwclasspairfnval_2
  have p0016 :=
    @g_opex (syn_cop R D) S p0015 hyp_lnpwclasspairfnval_3
  have p0017 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (.classMem (syn_cop (syn_cop R D) S) (syn_cvv)) p0014 p0016
  have p0018 :=
    @g_fvco2 (syn_cvv) (syn_cop (syn_cop R D) S) (syn_clnpwcnvkerfn) (syn_c1st)
  have p0019 :=
    Nominal.mp p0017 p0018
  have p0020 :=
    @g_opex R D hyp_lnpwclasspairfnval_1 hyp_lnpwclasspairfnval_2
  have p0021 :=
    @g_opfv1st (syn_cop R D) S p0020 hyp_lnpwclasspairfnval_3
  have p0022 :=
    @g_fveq2i (syn_cfv (syn_c1st) (syn_cop (syn_cop R D) S)) (syn_cop R D) (syn_clnpwcnvkerfn) p0021
  have p0023 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_cop (syn_cop R D) S)) (syn_cfv (syn_clnpwcnvkerfn) (syn_cfv (syn_c1st) (syn_cop (syn_cop R D) S))) (syn_cfv (syn_clnpwcnvkerfn) (syn_cop R D)) p0019 p0022
  have p0024 :=
    @g_lnpwcnvkerfnval D R hyp_lnpwclasspairfnval_1 hyp_lnpwclasspairfnval_2
  have p0025 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_cop (syn_cop R D) S)) (syn_cfv (syn_clnpwcnvkerfn) (syn_cop R D)) (syn_ccnv (syn_clnker R)) p0023 p0024
  have p0026 :=
    @g_opex R D hyp_lnpwclasspairfnval_1 hyp_lnpwclasspairfnval_2
  have p0027 :=
    @g_opfv2nd (syn_cop R D) S p0026 hyp_lnpwclasspairfnval_3
  have p0028 :=
    @g_opeq12i (syn_cfv (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_cop (syn_cop R D) S)) (syn_ccnv (syn_clnker R)) (syn_cfv (syn_c2nd) (syn_cop (syn_cop R D) S)) S p0025 p0027
  have p0029 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_c2nd)) (syn_cop (syn_cop R D) S)) (syn_cop (syn_cfv (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_cop (syn_cop R D) S)) (syn_cfv (syn_c2nd) (syn_cop (syn_cop R D) S))) (syn_cop (syn_ccnv (syn_clnker R)) S) p0013 p0028
  have p0030 :=
    @g_eqtri (syn_cfv (syn_clnpwclasspairfn) (syn_cop (syn_cop R D) S)) (syn_cfv (syn_ctxp (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_c2nd)) (syn_cop (syn_cop R D) S)) (syn_cop (syn_ccnv (syn_clnker R)) S) p0001 p0029
  exact p0030

noncomputable def g_lnpwclassfnfn
     :
    Nominal.NPrf (syn_wfn (syn_clnpwclassfn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_lnimageopfn
  have p0001 :=
    @g_imageswapfn
  have p0002 :=
    @g_lnpwkerfnfn
  have p0003 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_clnpwkerfn) p0001 p0002
  have p0004 :=
    (by simpa [syn_clnpwcnvkerfn] using (Nominal.classEqRefl (syn_clnpwcnvkerfn)))
  have p0005 :=
    @g_fneq1i (syn_cvv) (syn_clnpwcnvkerfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_clnpwkerfn)) p0004
  have p0006 :=
    @g_mpbir (syn_wfn (syn_clnpwcnvkerfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_clnpwkerfn)) (syn_cvv)) p0003 p0005
  have p0007 :=
    @g_ln1stfn
  have p0008 :=
    @g_fncovv (syn_clnpwcnvkerfn) (syn_c1st) p0006 p0007
  have p0009 :=
    @g_ln2ndfn
  have p0010 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0008 p0009
  have p0011 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_c2nd)
  have p0012 :=
    Nominal.mp p0010 p0011
  have p0013 :=
    @g_inidm (syn_cvv)
  have p0014 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_c2nd)) p0013
  have p0015 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_c2nd)) (syn_cvv)) p0012 p0014
  have p0016 :=
    (by simpa [syn_clnpwclasspairfn] using (Nominal.classEqRefl (syn_clnpwclasspairfn)))
  have p0017 :=
    @g_fneq1i (syn_cvv) (syn_clnpwclasspairfn) (syn_ctxp (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_c2nd)) p0016
  have p0018 :=
    @g_mpbir (syn_wfn (syn_clnpwclasspairfn) (syn_cvv)) (syn_wfn (syn_ctxp (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_c2nd)) (syn_cvv)) p0015 p0017
  have p0019 :=
    @g_fncovv (syn_clnimageop) (syn_clnpwclasspairfn) p0000 p0018
  have p0020 :=
    (by simpa [syn_clnpwclassfn] using (Nominal.classEqRefl (syn_clnpwclassfn)))
  have p0021 :=
    @g_fneq1i (syn_cvv) (syn_clnpwclassfn) (syn_ccom (syn_clnimageop) (syn_clnpwclasspairfn)) p0020
  have p0022 :=
    @g_mpbir (syn_wfn (syn_clnpwclassfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_clnimageop) (syn_clnpwclasspairfn)) (syn_cvv)) p0019 p0021
  exact p0022

noncomputable def g_lnpwclassfnex
     :
    Nominal.NPrf (.classMem (syn_clnpwclassfn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_clnpwclassfn] using (Nominal.classEqRefl (syn_clnpwclassfn)))
  have p0001 :=
    @g_lnimageopex
  have p0002 :=
    (by simpa [syn_clnpwclasspairfn] using (Nominal.classEqRefl (syn_clnpwclasspairfn)))
  have p0003 :=
    (by simpa [syn_clnpwcnvkerfn] using (Nominal.classEqRefl (syn_clnpwcnvkerfn)))
  have p0004 :=
    @g_swapex
  have p0005 :=
    @g_imageex (syn_cswap) p0004
  have p0006 :=
    @g_lnpwkerfnex
  have p0007 :=
    @g_coex (syn_cimage (syn_cswap)) (syn_clnpwkerfn) p0005 p0006
  have p0008 :=
    @g_eqeltri (syn_clnpwcnvkerfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_clnpwkerfn)) (syn_cvv) p0003 p0007
  have p0009 :=
    @g_n_1stex
  have p0010 :=
    @g_coex (syn_clnpwcnvkerfn) (syn_c1st) p0008 p0009
  have p0011 :=
    @g_n_2ndex
  have p0012 :=
    @g_txpex (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_c2nd) p0010 p0011
  have p0013 :=
    @g_eqeltri (syn_clnpwclasspairfn) (syn_ctxp (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_c2nd)) (syn_cvv) p0002 p0012
  have p0014 :=
    @g_coex (syn_clnimageop) (syn_clnpwclasspairfn) p0001 p0013
  have p0015 :=
    @g_eqeltri (syn_clnpwclassfn) (syn_ccom (syn_clnimageop) (syn_clnpwclasspairfn)) (syn_cvv) p0000 p0014
  exact p0015

noncomputable def g_lnpwclassfnval
    (D : Class) (R : Class) (S : Class) (hyp_lnpwclassfnval_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_lnpwclassfnval_2 : Nominal.NPrf (.classMem D (syn_cvv))) (hyp_lnpwclassfnval_3 : Nominal.NPrf (.classMem S (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) S)) (syn_cima (syn_ccnv (syn_clnker R)) S)) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ S.fv
  have p0000 :=
    (by simpa [syn_clnpwclassfn] using (Nominal.classEqRefl (syn_clnpwclassfn)))
  have p0001 :=
    @g_fveq1i (syn_cop (syn_cop R D) S) (syn_clnpwclassfn) (syn_ccom (syn_clnimageop) (syn_clnpwclasspairfn)) p0000
  have p0002 :=
    @g_imageswapfn
  have p0003 :=
    @g_lnpwkerfnfn
  have p0004 :=
    @g_fncovv (syn_cimage (syn_cswap)) (syn_clnpwkerfn) p0002 p0003
  have p0005 :=
    (by simpa [syn_clnpwcnvkerfn] using (Nominal.classEqRefl (syn_clnpwcnvkerfn)))
  have p0006 :=
    @g_fneq1i (syn_cvv) (syn_clnpwcnvkerfn) (syn_ccom (syn_cimage (syn_cswap)) (syn_clnpwkerfn)) p0005
  have p0007 :=
    @g_mpbir (syn_wfn (syn_clnpwcnvkerfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_cswap)) (syn_clnpwkerfn)) (syn_cvv)) p0004 p0006
  have p0008 :=
    @g_ln1stfn
  have p0009 :=
    @g_fncovv (syn_clnpwcnvkerfn) (syn_c1st) p0007 p0008
  have p0010 :=
    @g_ln2ndfn
  have p0011 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_cvv)) (syn_wfn (syn_c2nd) (syn_cvv)) p0009 p0010
  have p0012 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_c2nd)
  have p0013 :=
    Nominal.mp p0011 p0012
  have p0014 :=
    @g_inidm (syn_cvv)
  have p0015 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_c2nd)) p0014
  have p0016 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_c2nd)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_c2nd)) (syn_cvv)) p0013 p0015
  have p0017 :=
    (by simpa [syn_clnpwclasspairfn] using (Nominal.classEqRefl (syn_clnpwclasspairfn)))
  have p0018 :=
    @g_fneq1i (syn_cvv) (syn_clnpwclasspairfn) (syn_ctxp (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_c2nd)) p0017
  have p0019 :=
    @g_mpbir (syn_wfn (syn_clnpwclasspairfn) (syn_cvv)) (syn_wfn (syn_ctxp (syn_ccom (syn_clnpwcnvkerfn) (syn_c1st)) (syn_c2nd)) (syn_cvv)) p0016 p0018
  have p0020 :=
    @g_opex R D hyp_lnpwclassfnval_1 hyp_lnpwclassfnval_2
  have p0021 :=
    @g_opex (syn_cop R D) S p0020 hyp_lnpwclassfnval_3
  have p0022 :=
    @g_pm3_2i (syn_wfn (syn_clnpwclasspairfn) (syn_cvv)) (.classMem (syn_cop (syn_cop R D) S) (syn_cvv)) p0019 p0021
  have p0023 :=
    @g_fvco2 (syn_cvv) (syn_cop (syn_cop R D) S) (syn_clnimageop) (syn_clnpwclasspairfn)
  have p0024 :=
    Nominal.mp p0022 p0023
  have p0025 :=
    @g_eqtri (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) S)) (syn_cfv (syn_ccom (syn_clnimageop) (syn_clnpwclasspairfn)) (syn_cop (syn_cop R D) S)) (syn_cfv (syn_clnimageop) (syn_cfv (syn_clnpwclasspairfn) (syn_cop (syn_cop R D) S))) p0001 p0024
  have p0026 :=
    @g_lnpwclasspairfnval D R S hyp_lnpwclassfnval_1 hyp_lnpwclassfnval_2 hyp_lnpwclassfnval_3
  have p0027 :=
    @g_fveq2i (syn_cfv (syn_clnpwclasspairfn) (syn_cop (syn_cop R D) S)) (syn_cop (syn_ccnv (syn_clnker R)) S) (syn_clnimageop) p0026
  have p0028 :=
    @g_eqtri (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) S)) (syn_cfv (syn_clnimageop) (syn_cfv (syn_clnpwclasspairfn) (syn_cop (syn_cop R D) S))) (syn_cfv (syn_clnimageop) (syn_cop (syn_ccnv (syn_clnker R)) S)) p0025 p0027
  have p0029 :=
    @g_lnkerex R hyp_lnpwclassfnval_1
  have p0030 :=
    @g_cnvex (syn_clnker R) p0029
  have p0031 :=
    @g_lnimageopval S (syn_ccnv (syn_clnker R)) p0030 hyp_lnpwclassfnval_3
  have p0032 :=
    @g_eqtri (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) S)) (syn_cfv (syn_clnimageop) (syn_cop (syn_ccnv (syn_clnker R)) S)) (syn_cima (syn_ccnv (syn_clnker R)) S) p0028 p0031
  exact p0032

noncomputable def g_lnpwpw1secondfnfn
     :
    Nominal.NPrf (syn_wfn (syn_clnpwpw1secondfn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_fnfullfun (syn_cpw1fn)
  have p0001 :=
    @g_n_2ndex
  have p0002 :=
    @g_wppimagefn (syn_c2nd) p0001
  have p0003 :=
    @g_fncovv (syn_cfullfun (syn_cpw1fn)) (syn_cimage (syn_c2nd)) p0000 p0002
  have p0004 :=
    (by simpa [syn_clnpwpw1secondfn] using (Nominal.classEqRefl (syn_clnpwpw1secondfn)))
  have p0005 :=
    @g_fneq1i (syn_cvv) (syn_clnpwpw1secondfn) (syn_ccom (syn_cfullfun (syn_cpw1fn)) (syn_cimage (syn_c2nd))) p0004
  have p0006 :=
    @g_mpbir (syn_wfn (syn_clnpwpw1secondfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cfullfun (syn_cpw1fn)) (syn_cimage (syn_c2nd))) (syn_cvv)) p0003 p0005
  exact p0006

noncomputable def g_lnpwpw1secondfnex
     :
    Nominal.NPrf (.classMem (syn_clnpwpw1secondfn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_clnpwpw1secondfn] using (Nominal.classEqRefl (syn_clnpwpw1secondfn)))
  have p0001 :=
    @g_pw1fnex
  have p0002 :=
    @g_fullfunex (syn_cpw1fn) p0001
  have p0003 :=
    @g_n_2ndex
  have p0004 :=
    @g_imageex (syn_c2nd) p0003
  have p0005 :=
    @g_coex (syn_cfullfun (syn_cpw1fn)) (syn_cimage (syn_c2nd)) p0002 p0004
  have p0006 :=
    @g_eqeltri (syn_clnpwpw1secondfn) (syn_ccom (syn_cfullfun (syn_cpw1fn)) (syn_cimage (syn_c2nd))) (syn_cvv) p0000 p0005
  exact p0006

noncomputable def g_lnpwpw1secondfnval
    (D : Class) (R : Class) (hyp_lnpwpw1secondfnval_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_lnpwpw1secondfnval_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_clnpwpw1secondfn) (syn_csn (syn_cop R D))) (syn_cpw1 D)) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  have dv_cache_0001 : Disjoint ((syn_csn (syn_cop R D))).fv ((syn_c2nd)).fv := by
    exact (show Disjoint ((syn_csn (syn_cop R D))).fv ((syn_c2nd)).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd]; exact (show Disjoint (((syn_cop R D)).fv) ((∅ : Finset Var)) from (by simp))))
  have p0000 :=
    (by simpa [syn_clnpwpw1secondfn] using (Nominal.classEqRefl (syn_clnpwpw1secondfn)))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_cop R D)) (syn_clnpwpw1secondfn) (syn_ccom (syn_cfullfun (syn_cpw1fn)) (syn_cimage (syn_c2nd))) p0000
  have p0002 :=
    @g_n_2ndex
  have p0003 :=
    @g_wppimagefn (syn_c2nd) p0002
  have p0004 :=
    @g_snex (syn_cop R D)
  have p0005 :=
    @g_pm3_2i (syn_wfn (syn_cimage (syn_c2nd)) (syn_cvv)) (.classMem (syn_csn (syn_cop R D)) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_fvco2 (syn_cvv) (syn_csn (syn_cop R D)) (syn_cfullfun (syn_cpw1fn)) (syn_cimage (syn_c2nd))
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_eqtri (syn_cfv (syn_clnpwpw1secondfn) (syn_csn (syn_cop R D))) (syn_cfv (syn_ccom (syn_cfullfun (syn_cpw1fn)) (syn_cimage (syn_c2nd))) (syn_csn (syn_cop R D))) (syn_cfv (syn_cfullfun (syn_cpw1fn)) (syn_cfv (syn_cimage (syn_c2nd)) (syn_csn (syn_cop R D)))) p0001 p0007
  have p0009 :=
    @g_n_2ndex
  have p0010 :=
    @g_snex (syn_cop R D)
  have p0011 :=
    @g_wppfvimage (syn_csn (syn_cop R D)) (syn_c2nd) dv_cache_0001 p0009 p0010
  have p0012 :=
    @g_ln2ndfn
  have p0013 :=
    @g_opex R D hyp_lnpwpw1secondfnval_1 hyp_lnpwpw1secondfnval_2
  have p0014 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (.classMem (syn_cop R D) (syn_cvv)) p0012 p0013
  have p0015 :=
    @g_fnsnfv (syn_cvv) (syn_cop R D) (syn_c2nd)
  have p0016 :=
    Nominal.mp p0014 p0015
  have p0017 :=
    @g_eqcomi (syn_csn (syn_cfv (syn_c2nd) (syn_cop R D))) (syn_cima (syn_c2nd) (syn_csn (syn_cop R D))) p0016
  have p0018 :=
    @g_opfv2nd R D hyp_lnpwpw1secondfnval_1 hyp_lnpwpw1secondfnval_2
  have p0019 :=
    @g_sneqi (syn_cfv (syn_c2nd) (syn_cop R D)) D p0018
  have p0020 :=
    @g_eqtri (syn_cima (syn_c2nd) (syn_csn (syn_cop R D))) (syn_csn (syn_cfv (syn_c2nd) (syn_cop R D))) (syn_csn D) p0017 p0019
  have p0021 :=
    @g_eqtri (syn_cfv (syn_cimage (syn_c2nd)) (syn_csn (syn_cop R D))) (syn_cima (syn_c2nd) (syn_csn (syn_cop R D))) (syn_csn D) p0011 p0020
  have p0022 :=
    @g_fveq2i (syn_cfv (syn_cimage (syn_c2nd)) (syn_csn (syn_cop R D))) (syn_csn D) (syn_cfullfun (syn_cpw1fn)) p0021
  have p0023 :=
    @g_eqtri (syn_cfv (syn_clnpwpw1secondfn) (syn_csn (syn_cop R D))) (syn_cfv (syn_cfullfun (syn_cpw1fn)) (syn_cfv (syn_cimage (syn_c2nd)) (syn_csn (syn_cop R D)))) (syn_cfv (syn_cfullfun (syn_cpw1fn)) (syn_csn D)) p0008 p0022
  have p0024 :=
    @g_fvfullfun (syn_csn D) (syn_cpw1fn)
  have p0025 :=
    @g_eqtri (syn_cfv (syn_clnpwpw1secondfn) (syn_csn (syn_cop R D))) (syn_cfv (syn_cfullfun (syn_cpw1fn)) (syn_csn D)) (syn_cfv (syn_cpw1fn) (syn_csn D)) p0023 p0024
  have p0026 :=
    @g_pw1fnval D hyp_lnpwpw1secondfnval_2
  have p0027 :=
    @g_eqtri (syn_cfv (syn_clnpwpw1secondfn) (syn_csn (syn_cop R D))) (syn_cfv (syn_cpw1fn) (syn_csn D)) (syn_cpw1 D) p0025 p0026
  exact p0027

noncomputable def g_lnpwquoinputfnfn
     :
    Nominal.NPrf (syn_wfn (syn_clnpwquoinputfn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_fncross
  have p0001 :=
    @g_fnresi (syn_cvv)
  have p0002 :=
    @g_resid (syn_cid)
  have p0003 :=
    @g_fneq1i (syn_cvv) (syn_cres (syn_cid) (syn_cvv)) (syn_cid) p0002
  have p0004 :=
    @g_mpbi (syn_wfn (syn_cres (syn_cid) (syn_cvv)) (syn_cvv)) (syn_wfn (syn_cid) (syn_cvv)) p0001 p0003
  have p0005 :=
    @g_fnfullfun (syn_cpw1fn)
  have p0006 :=
    @g_n_2ndex
  have p0007 :=
    @g_wppimagefn (syn_c2nd) p0006
  have p0008 :=
    @g_fncovv (syn_cfullfun (syn_cpw1fn)) (syn_cimage (syn_c2nd)) p0005 p0007
  have p0009 :=
    (by simpa [syn_clnpwpw1secondfn] using (Nominal.classEqRefl (syn_clnpwpw1secondfn)))
  have p0010 :=
    @g_fneq1i (syn_cvv) (syn_clnpwpw1secondfn) (syn_ccom (syn_cfullfun (syn_cpw1fn)) (syn_cimage (syn_c2nd))) p0009
  have p0011 :=
    @g_mpbir (syn_wfn (syn_clnpwpw1secondfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cfullfun (syn_cpw1fn)) (syn_cimage (syn_c2nd))) (syn_cvv)) p0008 p0010
  have p0012 :=
    @g_pm3_2i (syn_wfn (syn_cid) (syn_cvv)) (syn_wfn (syn_clnpwpw1secondfn) (syn_cvv)) p0004 p0011
  have p0013 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cid) (syn_clnpwpw1secondfn)
  have p0014 :=
    Nominal.mp p0012 p0013
  have p0015 :=
    @g_inidm (syn_cvv)
  have p0016 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn)) p0015
  have p0017 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn)) (syn_cvv)) p0014 p0016
  have p0018 :=
    @g_fncovv (syn_ccross) (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn)) p0000 p0017
  have p0019 :=
    (by simpa [syn_clnpwquoinputfn] using (Nominal.classEqRefl (syn_clnpwquoinputfn)))
  have p0020 :=
    @g_fneq1i (syn_cvv) (syn_clnpwquoinputfn) (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn))) p0019
  have p0021 :=
    @g_mpbir (syn_wfn (syn_clnpwquoinputfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn))) (syn_cvv)) p0018 p0020
  exact p0021

noncomputable def g_lnpwquoinputfnex
     :
    Nominal.NPrf (.classMem (syn_clnpwquoinputfn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_clnpwquoinputfn] using (Nominal.classEqRefl (syn_clnpwquoinputfn)))
  have p0001 :=
    @g_crossex
  have p0002 :=
    @g_idex
  have p0003 :=
    (by simpa [syn_clnpwpw1secondfn] using (Nominal.classEqRefl (syn_clnpwpw1secondfn)))
  have p0004 :=
    @g_pw1fnex
  have p0005 :=
    @g_fullfunex (syn_cpw1fn) p0004
  have p0006 :=
    @g_n_2ndex
  have p0007 :=
    @g_imageex (syn_c2nd) p0006
  have p0008 :=
    @g_coex (syn_cfullfun (syn_cpw1fn)) (syn_cimage (syn_c2nd)) p0005 p0007
  have p0009 :=
    @g_eqeltri (syn_clnpwpw1secondfn) (syn_ccom (syn_cfullfun (syn_cpw1fn)) (syn_cimage (syn_c2nd))) (syn_cvv) p0003 p0008
  have p0010 :=
    @g_txpex (syn_cid) (syn_clnpwpw1secondfn) p0002 p0009
  have p0011 :=
    @g_coex (syn_ccross) (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn)) p0001 p0010
  have p0012 :=
    @g_eqeltri (syn_clnpwquoinputfn) (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn))) (syn_cvv) p0000 p0011
  exact p0012

noncomputable def g_lnpwquoinputfnval
    (D : Class) (R : Class) (hyp_lnpwquoinputfnval_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_lnpwquoinputfnval_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_clnpwquoinputfn) (syn_csn (syn_cop R D))) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_clnpwquoinputfn] using (Nominal.classEqRefl (syn_clnpwquoinputfn)))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_cop R D)) (syn_clnpwquoinputfn) (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn))) p0000
  have p0002 :=
    @g_fnresi (syn_cvv)
  have p0003 :=
    @g_resid (syn_cid)
  have p0004 :=
    @g_fneq1i (syn_cvv) (syn_cres (syn_cid) (syn_cvv)) (syn_cid) p0003
  have p0005 :=
    @g_mpbi (syn_wfn (syn_cres (syn_cid) (syn_cvv)) (syn_cvv)) (syn_wfn (syn_cid) (syn_cvv)) p0002 p0004
  have p0006 :=
    @g_fnfullfun (syn_cpw1fn)
  have p0007 :=
    @g_n_2ndex
  have p0008 :=
    @g_wppimagefn (syn_c2nd) p0007
  have p0009 :=
    @g_fncovv (syn_cfullfun (syn_cpw1fn)) (syn_cimage (syn_c2nd)) p0006 p0008
  have p0010 :=
    (by simpa [syn_clnpwpw1secondfn] using (Nominal.classEqRefl (syn_clnpwpw1secondfn)))
  have p0011 :=
    @g_fneq1i (syn_cvv) (syn_clnpwpw1secondfn) (syn_ccom (syn_cfullfun (syn_cpw1fn)) (syn_cimage (syn_c2nd))) p0010
  have p0012 :=
    @g_mpbir (syn_wfn (syn_clnpwpw1secondfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cfullfun (syn_cpw1fn)) (syn_cimage (syn_c2nd))) (syn_cvv)) p0009 p0011
  have p0013 :=
    @g_pm3_2i (syn_wfn (syn_cid) (syn_cvv)) (syn_wfn (syn_clnpwpw1secondfn) (syn_cvv)) p0005 p0012
  have p0014 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cid) (syn_clnpwpw1secondfn)
  have p0015 :=
    Nominal.mp p0013 p0014
  have p0016 :=
    @g_inidm (syn_cvv)
  have p0017 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn)) p0016
  have p0018 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn)) (syn_cvv)) p0015 p0017
  have p0019 :=
    @g_snex (syn_cop R D)
  have p0020 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn)) (syn_cvv)) (.classMem (syn_csn (syn_cop R D)) (syn_cvv)) p0018 p0019
  have p0021 :=
    @g_fvco2 (syn_cvv) (syn_csn (syn_cop R D)) (syn_ccross) (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn))
  have p0022 :=
    Nominal.mp p0020 p0021
  have p0023 :=
    @g_eqtri (syn_cfv (syn_clnpwquoinputfn) (syn_csn (syn_cop R D))) (syn_cfv (syn_ccom (syn_ccross) (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn))) (syn_csn (syn_cop R D))) (syn_cfv (syn_ccross) (syn_cfv (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn)) (syn_csn (syn_cop R D)))) p0001 p0022
  have p0024 :=
    @g_fnresi (syn_cvv)
  have p0025 :=
    @g_resid (syn_cid)
  have p0026 :=
    @g_fneq1i (syn_cvv) (syn_cres (syn_cid) (syn_cvv)) (syn_cid) p0025
  have p0027 :=
    @g_mpbi (syn_wfn (syn_cres (syn_cid) (syn_cvv)) (syn_cvv)) (syn_wfn (syn_cid) (syn_cvv)) p0024 p0026
  have p0028 :=
    @g_fnfullfun (syn_cpw1fn)
  have p0029 :=
    @g_n_2ndex
  have p0030 :=
    @g_wppimagefn (syn_c2nd) p0029
  have p0031 :=
    @g_fncovv (syn_cfullfun (syn_cpw1fn)) (syn_cimage (syn_c2nd)) p0028 p0030
  have p0032 :=
    (by simpa [syn_clnpwpw1secondfn] using (Nominal.classEqRefl (syn_clnpwpw1secondfn)))
  have p0033 :=
    @g_fneq1i (syn_cvv) (syn_clnpwpw1secondfn) (syn_ccom (syn_cfullfun (syn_cpw1fn)) (syn_cimage (syn_c2nd))) p0032
  have p0034 :=
    @g_mpbir (syn_wfn (syn_clnpwpw1secondfn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cfullfun (syn_cpw1fn)) (syn_cimage (syn_c2nd))) (syn_cvv)) p0031 p0033
  have p0035 :=
    @g_snex (syn_cop R D)
  have p0036 :=
    @g_fvtxpvv (syn_csn (syn_cop R D)) (syn_cid) (syn_clnpwpw1secondfn) p0027 p0034 p0035
  have p0037 :=
    @g_snex (syn_cop R D)
  have p0038 :=
    @g_fvi (syn_csn (syn_cop R D)) (syn_cvv)
  have p0039 :=
    Nominal.mp p0037 p0038
  have p0040 :=
    @g_lnpwpw1secondfnval D R hyp_lnpwquoinputfnval_1 hyp_lnpwquoinputfnval_2
  have p0041 :=
    @g_opeq12i (syn_cfv (syn_cid) (syn_csn (syn_cop R D))) (syn_csn (syn_cop R D)) (syn_cfv (syn_clnpwpw1secondfn) (syn_csn (syn_cop R D))) (syn_cpw1 D) p0039 p0040
  have p0042 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn)) (syn_csn (syn_cop R D))) (syn_cop (syn_cfv (syn_cid) (syn_csn (syn_cop R D))) (syn_cfv (syn_clnpwpw1secondfn) (syn_csn (syn_cop R D)))) (syn_cop (syn_csn (syn_cop R D)) (syn_cpw1 D)) p0036 p0041
  have p0043 :=
    @g_fveq2i (syn_cfv (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn)) (syn_csn (syn_cop R D))) (syn_cop (syn_csn (syn_cop R D)) (syn_cpw1 D)) (syn_ccross) p0042
  have p0044 :=
    @g_eqtri (syn_cfv (syn_clnpwquoinputfn) (syn_csn (syn_cop R D))) (syn_cfv (syn_ccross) (syn_cfv (syn_ctxp (syn_cid) (syn_clnpwpw1secondfn)) (syn_csn (syn_cop R D)))) (syn_cfv (syn_ccross) (syn_cop (syn_csn (syn_cop R D)) (syn_cpw1 D))) p0023 p0043
  have p0045 :=
    (by simpa [syn_co] using (Nominal.classEqRefl (syn_co (syn_csn (syn_cop R D)) (syn_ccross) (syn_cpw1 D))))
  have p0046 :=
    @g_eqcomi (syn_co (syn_csn (syn_cop R D)) (syn_ccross) (syn_cpw1 D)) (syn_cfv (syn_ccross) (syn_cop (syn_csn (syn_cop R D)) (syn_cpw1 D))) p0045
  have p0047 :=
    @g_snex (syn_cop R D)
  have p0048 :=
    @g_pw1ex D hyp_lnpwquoinputfnval_2
  have p0049 :=
    @g_pm3_2i (.classMem (syn_csn (syn_cop R D)) (syn_cvv)) (.classMem (syn_cpw1 D) (syn_cvv)) p0047 p0048
  have p0050 :=
    @g_ovcross (syn_csn (syn_cop R D)) (syn_cpw1 D) (syn_cvv) (syn_cvv)
  have p0051 :=
    Nominal.mp p0049 p0050
  have p0052 :=
    @g_eqtri (syn_cfv (syn_ccross) (syn_cop (syn_csn (syn_cop R D)) (syn_cpw1 D))) (syn_co (syn_csn (syn_cop R D)) (syn_ccross) (syn_cpw1 D)) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)) p0046 p0051
  have p0053 :=
    @g_eqtri (syn_cfv (syn_clnpwquoinputfn) (syn_csn (syn_cop R D))) (syn_cfv (syn_ccross) (syn_cop (syn_csn (syn_cop R D)) (syn_cpw1 D))) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)) p0044 p0052
  exact p0053

noncomputable def g_lnpwquofnfn
     :
    Nominal.NPrf (syn_wfn (syn_clnpwquofn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_lnpwclassfnex
  have p0001 :=
    @g_wppimagefn (syn_clnpwclassfn) p0000
  have p0002 :=
    @g_lnpwquoinputfnfn
  have p0003 :=
    @g_fncovv (syn_cimage (syn_clnpwclassfn)) (syn_clnpwquoinputfn) p0001 p0002
  have p0004 :=
    (by simpa [syn_clnpwquofn] using (Nominal.classEqRefl (syn_clnpwquofn)))
  have p0005 :=
    @g_fneq1i (syn_cvv) (syn_clnpwquofn) (syn_ccom (syn_cimage (syn_clnpwclassfn)) (syn_clnpwquoinputfn)) p0004
  have p0006 :=
    @g_mpbir (syn_wfn (syn_clnpwquofn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cimage (syn_clnpwclassfn)) (syn_clnpwquoinputfn)) (syn_cvv)) p0003 p0005
  exact p0006

noncomputable def g_lnpwquofnex
     :
    Nominal.NPrf (.classMem (syn_clnpwquofn) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_clnpwquofn] using (Nominal.classEqRefl (syn_clnpwquofn)))
  have p0001 :=
    @g_lnpwclassfnex
  have p0002 :=
    @g_imageex (syn_clnpwclassfn) p0001
  have p0003 :=
    @g_lnpwquoinputfnex
  have p0004 :=
    @g_coex (syn_cimage (syn_clnpwclassfn)) (syn_clnpwquoinputfn) p0002 p0003
  have p0005 :=
    @g_eqeltri (syn_clnpwquofn) (syn_ccom (syn_cimage (syn_clnpwclassfn)) (syn_clnpwquoinputfn)) (syn_cvv) p0000 p0004
  exact p0005

noncomputable def g_lnpwquofnrawval
    (D : Class) (R : Class) (hyp_lnpwquofnrawval_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_lnpwquofnrawval_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_clnpwquofn) (syn_csn (syn_cop R D))) (syn_cima (syn_clnpwclassfn) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)))) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  have p0000 :=
    (by simpa [syn_clnpwquofn] using (Nominal.classEqRefl (syn_clnpwquofn)))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_cop R D)) (syn_clnpwquofn) (syn_ccom (syn_cimage (syn_clnpwclassfn)) (syn_clnpwquoinputfn)) p0000
  have p0002 :=
    @g_lnpwquoinputfnfn
  have p0003 :=
    @g_snex (syn_cop R D)
  have p0004 :=
    @g_pm3_2i (syn_wfn (syn_clnpwquoinputfn) (syn_cvv)) (.classMem (syn_csn (syn_cop R D)) (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_fvco2 (syn_cvv) (syn_csn (syn_cop R D)) (syn_cimage (syn_clnpwclassfn)) (syn_clnpwquoinputfn)
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_eqtri (syn_cfv (syn_clnpwquofn) (syn_csn (syn_cop R D))) (syn_cfv (syn_ccom (syn_cimage (syn_clnpwclassfn)) (syn_clnpwquoinputfn)) (syn_csn (syn_cop R D))) (syn_cfv (syn_cimage (syn_clnpwclassfn)) (syn_cfv (syn_clnpwquoinputfn) (syn_csn (syn_cop R D)))) p0001 p0006
  have p0008 :=
    @g_lnpwquoinputfnval D R hyp_lnpwquofnrawval_1 hyp_lnpwquofnrawval_2
  have p0009 :=
    @g_fveq2i (syn_cfv (syn_clnpwquoinputfn) (syn_csn (syn_cop R D))) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)) (syn_cimage (syn_clnpwclassfn)) p0008
  have p0010 :=
    @g_eqtri (syn_cfv (syn_clnpwquofn) (syn_csn (syn_cop R D))) (syn_cfv (syn_cimage (syn_clnpwclassfn)) (syn_cfv (syn_clnpwquoinputfn) (syn_csn (syn_cop R D)))) (syn_cfv (syn_cimage (syn_clnpwclassfn)) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))) p0007 p0009
  have p0011 :=
    @g_lnpwclassfnex
  have p0012 :=
    @g_snex (syn_cop R D)
  have p0013 :=
    @g_pw1ex D hyp_lnpwquofnrawval_2
  have p0014 :=
    @g_xpex (syn_csn (syn_cop R D)) (syn_cpw1 D) p0012 p0013
  have p0015 :=
    @g_fvimagecl (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D)) (syn_clnpwclassfn) p0011 p0014
  have p0016 :=
    @g_eqtri (syn_cfv (syn_clnpwquofn) (syn_csn (syn_cop R D))) (syn_cfv (syn_cimage (syn_clnpwclassfn)) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))) (syn_cima (syn_clnpwclassfn) (syn_cxp (syn_csn (syn_cop R D)) (syn_cpw1 D))) p0010 p0015
  exact p0016

noncomputable def g_lnpwclassfnsnval
    (D : Class) (R : Class) (X : Class) (hyp_lnpwclassfnsnval_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_lnpwclassfnsnval_2 : Nominal.NPrf (.classMem D (syn_cvv))) (hyp_lnpwclassfnsnval_3 : Nominal.NPrf (.classMem X (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (syn_csn X))) (syn_cec X (syn_clnker R))) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ X.fv
  have p0000 :=
    @g_snex X
  have p0001 :=
    @g_lnpwclassfnval D R (syn_csn X) hyp_lnpwclassfnsnval_1 hyp_lnpwclassfnsnval_2 p0000
  have p0002 :=
    (by simpa [syn_clnker] using (Nominal.classEqRefl (syn_clnker R)))
  have p0003 :=
    @g_cnveqi (syn_clnker R) (syn_cin R (syn_ccnv R)) p0002
  have p0004 :=
    @g_cnvin R (syn_ccnv R)
  have p0005 :=
    @g_cnvcnv R
  have p0006 :=
    @g_ineq2i (syn_ccnv (syn_ccnv R)) R (syn_ccnv R) p0005
  have p0007 :=
    @g_eqtri (syn_ccnv (syn_cin R (syn_ccnv R))) (syn_cin (syn_ccnv R) (syn_ccnv (syn_ccnv R))) (syn_cin (syn_ccnv R) R) p0004 p0006
  have p0008 :=
    @g_eqtri (syn_ccnv (syn_clnker R)) (syn_ccnv (syn_cin R (syn_ccnv R))) (syn_cin (syn_ccnv R) R) p0003 p0007
  have p0009 :=
    @g_incom (syn_ccnv R) R
  have p0010 :=
    @g_eqtri (syn_ccnv (syn_clnker R)) (syn_cin (syn_ccnv R) R) (syn_cin R (syn_ccnv R)) p0008 p0009
  have p0011 :=
    (by simpa [syn_clnker] using (Nominal.classEqRefl (syn_clnker R)))
  have p0012 :=
    @g_eqcomi (syn_clnker R) (syn_cin R (syn_ccnv R)) p0011
  have p0013 :=
    @g_eqtri (syn_ccnv (syn_clnker R)) (syn_cin R (syn_ccnv R)) (syn_clnker R) p0010 p0012
  have p0014 :=
    @g_imaeq1i (syn_ccnv (syn_clnker R)) (syn_clnker R) (syn_csn X) p0013
  have p0015 :=
    @g_eqtri (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (syn_csn X))) (syn_cima (syn_ccnv (syn_clnker R)) (syn_csn X)) (syn_cima (syn_clnker R) (syn_csn X)) p0001 p0014
  have p0016 :=
    (by simpa [syn_cec] using (Nominal.classEqRefl (syn_cec X (syn_clnker R))))
  have p0017 :=
    @g_eqcomi (syn_cec X (syn_clnker R)) (syn_cima (syn_clnker R) (syn_csn X)) p0016
  have p0018 :=
    @g_eqtri (syn_cfv (syn_clnpwclassfn) (syn_cop (syn_cop R D) (syn_csn X))) (syn_cima (syn_clnker R) (syn_csn X)) (syn_cec X (syn_clnker R)) p0015 p0017
  exact p0018

#print axioms g_lnpwclassfnsnval

end NFChoice.DirectNominalPrf.WPPReplay
