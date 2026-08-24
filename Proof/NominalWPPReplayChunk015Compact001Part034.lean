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
import NominalWPPReplayChunk015Compact001Part033

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

noncomputable def g_wpppowateqval
    (D : Class) (n : Var) (F : Class) (hyp_wpppowateqval_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wpppowateqval_2 : Nominal.NPrf (.classMem D (syn_cdm F))) (hyp_wpppowateqval_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) :
    Nominal.NPrf (.imp (.classMem (.cv n) (syn_cnnc)) (syn_wb (.classMem (.cv n) (syn_cwpppowateq F D)) (.classEq (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))) (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) (.cv n)))))) := by
  let proofSupport : Finset Var := D.fv ∪ ({n} : Finset Var) ∪ F.fv
  have p0000 :=
    (by simpa [syn_cwpppowateq] using (Nominal.classEqRefl (syn_cwpppowateq F D)))
  have p0001 :=
    @g_eleq2i (syn_cwpppowateq F D) (syn_cuni1 (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_cwppimageat D) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))) (syn_csi (syn_cfrec F D))))) (.cv n) p0000
  have p0002 :=
    @g_vex n
  have p0003 :=
    @g_eluni1 (.cv n) (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_cwppimageat D) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))) (syn_csi (syn_cfrec F D)))) p0002
  have p0004 :=
    @g_bitri (.classMem (.cv n) (syn_cwpppowateq F D)) (.classMem (.cv n) (syn_cuni1 (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_cwppimageat D) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))) (syn_csi (syn_cfrec F D)))))) (.classMem (syn_csn (.cv n)) (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_cwppimageat D) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))) (syn_csi (syn_cfrec F D))))) p0001 p0003
  have p0005 :=
    @g_a1i (syn_wb (.classMem (.cv n) (syn_cwpppowateq F D)) (.classMem (syn_csn (.cv n)) (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_cwppimageat D) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))) (syn_csi (syn_cfrec F D)))))) (.classMem (.cv n) (syn_cnnc)) p0004
  have p0006 :=
    @g_elex D (syn_cdm F)
  have p0007 :=
    Nominal.mp hyp_wpppowateqval_2 p0006
  have p0008 :=
    @g_wppimageatfn D p0007
  have p0009 :=
    @g_fnfun (syn_cvv) (syn_cwppimageat D)
  have p0010 :=
    Nominal.mp p0008 p0009
  have p0011 :=
    @g_elex F (syn_cfuns)
  have p0012 :=
    Nominal.mp hyp_wpppowateqval_1 p0011
  have p0013 :=
    @g_wpppowcorefn F p0012
  have p0014 :=
    @g_fnfun (syn_cnnc) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0015 :=
    Nominal.mp p0013 p0014
  have p0016 :=
    @g_fntcfn
  have p0017 :=
    @g_fnfun (syn_c1c) (syn_ctcfn)
  have p0018 :=
    Nominal.mp p0016 p0017
  have p0019 :=
    @g_pm3_2i (syn_wfun (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) (syn_wfun (syn_ctcfn)) p0015 p0018
  have p0020 :=
    @g_funco (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)
  have p0021 :=
    Nominal.mp p0019 p0020
  have p0022 :=
    @g_pm3_2i (syn_wfun (syn_cwppimageat D)) (syn_wfun (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))) p0010 p0021
  have p0023 :=
    @g_funco (syn_cwppimageat D) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))
  have p0024 :=
    Nominal.mp p0022 p0023
  have p0025 :=
    @g_a1i (syn_wfun (syn_ccom (syn_cwppimageat D) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))) (.classMem (.cv n) (syn_cnnc)) p0024
  have p0026 :=
    @g_n_3pm3_2i (.classMem F (syn_cfuns)) (.classMem D (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F)) hyp_wpppowateqval_1 hyp_wpppowateqval_2 hyp_wpppowateqval_3
  have p0027 :=
    @g_wpporbitfnndv F D
  have p0028 :=
    Nominal.mp p0026 p0027
  have p0029 :=
    @g_fnfun (syn_cnnc) (syn_cfrec F D)
  have p0030 :=
    Nominal.mp p0028 p0029
  have p0031 :=
    @g_funsi (syn_cfrec F D)
  have p0032 :=
    Nominal.mp p0030 p0031
  have p0033 :=
    @g_a1i (syn_wfun (syn_csi (syn_cfrec F D))) (.classMem (.cv n) (syn_cnnc)) p0032
  have p0034 :=
    @g_fvex (syn_csn (.cv n)) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))
  have p0035 :=
    @g_elex D (syn_cdm F)
  have p0036 :=
    Nominal.mp hyp_wpppowateqval_2 p0035
  have p0037 :=
    @g_wppimageatfn D p0036
  have p0038 :=
    @g_fndm (syn_cvv) (syn_cwppimageat D)
  have p0039 :=
    Nominal.mp p0037 p0038
  have p0040 :=
    @g_eleqtrri (syn_cfv (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)) (syn_csn (.cv n))) (syn_cvv) (syn_cdm (syn_cwppimageat D)) p0034 p0039
  have p0041 :=
    @g_a1i (.classMem (syn_cfv (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)) (syn_csn (.cv n))) (syn_cdm (syn_cwppimageat D))) (.classMem (.cv n) (syn_cnnc)) p0040
  have p0042 :=
    @g_elex F (syn_cfuns)
  have p0043 :=
    Nominal.mp hyp_wpppowateqval_1 p0042
  have p0044 :=
    @g_wpppowcorefn F p0043
  have p0045 :=
    @g_fnfun (syn_cnnc) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0046 :=
    Nominal.mp p0044 p0045
  have p0047 :=
    @g_fntcfn
  have p0048 :=
    @g_fnfun (syn_c1c) (syn_ctcfn)
  have p0049 :=
    Nominal.mp p0047 p0048
  have p0050 :=
    @g_pm3_2i (syn_wfun (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) (syn_wfun (syn_ctcfn)) p0046 p0049
  have p0051 :=
    @g_funco (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)
  have p0052 :=
    Nominal.mp p0050 p0051
  have p0053 :=
    @g_a1i (syn_wfun (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))) (.classMem (.cv n) (syn_cnnc)) p0052
  have p0054 :=
    @g_nntccl (.cv n)
  have p0055 :=
    @g_vex n
  have p0056 :=
    @g_tcfnfv (.cv n) p0055
  have p0057 :=
    @g_a1i (.classEq (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_ctc (.cv n))) (.classMem (.cv n) (syn_cnnc)) p0056
  have p0058 :=
    @g_eleq1d (.classMem (.cv n) (syn_cnnc)) (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_ctc (.cv n)) (syn_cnnc) p0057
  have p0059 :=
    @g_mpbird (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_cnnc)) (.classMem (syn_ctc (.cv n)) (syn_cnnc)) p0054 p0058
  have p0060 :=
    @g_elex F (syn_cfuns)
  have p0061 :=
    Nominal.mp hyp_wpppowateqval_1 p0060
  have p0062 :=
    @g_wpppowcorefn F p0061
  have p0063 :=
    @g_fndm (syn_cnnc) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0064 :=
    Nominal.mp p0062 p0063
  have p0065 :=
    @g_eleq2i (syn_cdm (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) (syn_cnnc) (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) p0064
  have p0066 :=
    @g_a1i (syn_wb (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_cdm (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))) (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_cnnc))) (.classMem (.cv n) (syn_cnnc)) p0065
  have p0067 :=
    @g_mpbird (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_cdm (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))) (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_cnnc)) p0059 p0066
  have p0068 :=
    @g_fntcfn
  have p0069 :=
    @g_fnfun (syn_c1c) (syn_ctcfn)
  have p0070 :=
    Nominal.mp p0068 p0069
  have p0071 :=
    @g_vex n
  have p0072 :=
    @g_snel1c (.cv n) p0071
  have p0073 :=
    @g_fntcfn
  have p0074 :=
    @g_fndm (syn_c1c) (syn_ctcfn)
  have p0075 :=
    Nominal.mp p0073 p0074
  have p0076 :=
    @g_eleqtrri (syn_csn (.cv n)) (syn_c1c) (syn_cdm (syn_ctcfn)) p0072 p0075
  have p0077 :=
    @g_pm3_2i (syn_wfun (syn_ctcfn)) (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ctcfn))) p0070 p0076
  have p0078 :=
    @g_dmfco (syn_csn (.cv n)) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)
  have p0079 :=
    Nominal.mp p0077 p0078
  have p0080 :=
    @g_a1i (syn_wb (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))) (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_cdm (syn_cfrec (syn_cwpppostcomp F) (syn_cid))))) (.classMem (.cv n) (syn_cnnc)) p0079
  have p0081 :=
    @g_mpbird (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))) (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_cdm (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))) p0067 p0080
  have p0082 :=
    @g_jca (.classMem (.cv n) (syn_cnnc)) (syn_wfun (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))) (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))) p0053 p0081
  have p0083 :=
    @g_dmfco (syn_csn (.cv n)) (syn_cwppimageat D) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))
  have p0084 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) (syn_wa (syn_wfun (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))) (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))))) (syn_wb (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ccom (syn_cwppimageat D) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))))) (.classMem (syn_cfv (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)) (syn_csn (.cv n))) (syn_cdm (syn_cwppimageat D)))) p0082 p0083
  have p0085 :=
    @g_mpbird (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ccom (syn_cwppimageat D) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))))) (.classMem (syn_cfv (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)) (syn_csn (.cv n))) (syn_cdm (syn_cwppimageat D))) p0041 p0084
  have p0086 :=
    @g_snelpw1 (.cv n) (syn_cnnc)
  have p0087 :=
    @g_biimpri (.classMem (syn_csn (.cv n)) (syn_cpw1 (syn_cnnc))) (.classMem (.cv n) (syn_cnnc)) p0086
  have p0088 :=
    @g_dmsi (syn_cfrec F D)
  have p0089 :=
    @g_n_3pm3_2i (.classMem F (syn_cfuns)) (.classMem D (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F)) hyp_wpppowateqval_1 hyp_wpppowateqval_2 hyp_wpppowateqval_3
  have p0090 :=
    @g_wpporbitfnndv F D
  have p0091 :=
    Nominal.mp p0089 p0090
  have p0092 :=
    @g_fndm (syn_cnnc) (syn_cfrec F D)
  have p0093 :=
    Nominal.mp p0091 p0092
  have p0094 :=
    @g_pw1eq (syn_cdm (syn_cfrec F D)) (syn_cnnc)
  have p0095 :=
    Nominal.mp p0093 p0094
  have p0096 :=
    @g_eqtri (syn_cdm (syn_csi (syn_cfrec F D))) (syn_cpw1 (syn_cdm (syn_cfrec F D))) (syn_cpw1 (syn_cnnc)) p0088 p0095
  have p0097 :=
    @g_a1i (.classEq (syn_cdm (syn_csi (syn_cfrec F D))) (syn_cpw1 (syn_cnnc))) (.classMem (.cv n) (syn_cnnc)) p0096
  have p0098 :=
    @g_eleqtrrd (.classMem (.cv n) (syn_cnnc)) (syn_csn (.cv n)) (syn_cpw1 (syn_cnnc)) (syn_cdm (syn_csi (syn_cfrec F D))) p0087 p0097
  have p0099 :=
    @g_jca (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ccom (syn_cwppimageat D) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))))) (.classMem (syn_csn (.cv n)) (syn_cdm (syn_csi (syn_cfrec F D)))) p0085 p0098
  have p0100 :=
    @g_n_3jca (.classMem (.cv n) (syn_cnnc)) (syn_wfun (syn_ccom (syn_cwppimageat D) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))) (syn_wfun (syn_csi (syn_cfrec F D))) (syn_wa (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ccom (syn_cwppimageat D) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))))) (.classMem (syn_csn (.cv n)) (syn_cdm (syn_csi (syn_cfrec F D))))) p0025 p0033 p0099
  have p0101 :=
    @g_funeqfix (syn_csn (.cv n)) (syn_ccom (syn_cwppimageat D) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))) (syn_csi (syn_cfrec F D))
  have p0102 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) (syn_w3a (syn_wfun (syn_ccom (syn_cwppimageat D) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))) (syn_wfun (syn_csi (syn_cfrec F D))) (syn_wa (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ccom (syn_cwppimageat D) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))))) (.classMem (syn_csn (.cv n)) (syn_cdm (syn_csi (syn_cfrec F D)))))) (syn_wb (.classMem (syn_csn (.cv n)) (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_cwppimageat D) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))) (syn_csi (syn_cfrec F D))))) (.classEq (syn_cfv (syn_ccom (syn_cwppimageat D) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))) (syn_csn (.cv n))) (syn_cfv (syn_csi (syn_cfrec F D)) (syn_csn (.cv n))))) p0100 p0101
  have p0103 :=
    @g_bitrd (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpppowateq F D)) (.classMem (syn_csn (.cv n)) (syn_cfix (syn_ccom (syn_ccnv (syn_ccom (syn_cwppimageat D) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))) (syn_csi (syn_cfrec F D))))) (.classEq (syn_cfv (syn_ccom (syn_cwppimageat D) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))) (syn_csn (.cv n))) (syn_cfv (syn_csi (syn_cfrec F D)) (syn_csn (.cv n)))) p0005 p0102
  have p0104 :=
    @g_elex F (syn_cfuns)
  have p0105 :=
    Nominal.mp hyp_wpppowateqval_1 p0104
  have p0106 :=
    @g_wpppowcorefn F p0105
  have p0107 :=
    @g_fnfun (syn_cnnc) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0108 :=
    Nominal.mp p0106 p0107
  have p0109 :=
    @g_fntcfn
  have p0110 :=
    @g_fnfun (syn_c1c) (syn_ctcfn)
  have p0111 :=
    Nominal.mp p0109 p0110
  have p0112 :=
    @g_pm3_2i (syn_wfun (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) (syn_wfun (syn_ctcfn)) p0108 p0111
  have p0113 :=
    @g_funco (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)
  have p0114 :=
    Nominal.mp p0112 p0113
  have p0115 :=
    @g_a1i (syn_wfun (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))) (.classMem (.cv n) (syn_cnnc)) p0114
  have p0116 :=
    @g_nntccl (.cv n)
  have p0117 :=
    @g_vex n
  have p0118 :=
    @g_tcfnfv (.cv n) p0117
  have p0119 :=
    @g_a1i (.classEq (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_ctc (.cv n))) (.classMem (.cv n) (syn_cnnc)) p0118
  have p0120 :=
    @g_eleq1d (.classMem (.cv n) (syn_cnnc)) (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_ctc (.cv n)) (syn_cnnc) p0119
  have p0121 :=
    @g_mpbird (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_cnnc)) (.classMem (syn_ctc (.cv n)) (syn_cnnc)) p0116 p0120
  have p0122 :=
    @g_elex F (syn_cfuns)
  have p0123 :=
    Nominal.mp hyp_wpppowateqval_1 p0122
  have p0124 :=
    @g_wpppowcorefn F p0123
  have p0125 :=
    @g_fndm (syn_cnnc) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0126 :=
    Nominal.mp p0124 p0125
  have p0127 :=
    @g_eleq2i (syn_cdm (syn_cfrec (syn_cwpppostcomp F) (syn_cid))) (syn_cnnc) (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) p0126
  have p0128 :=
    @g_a1i (syn_wb (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_cdm (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))) (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_cnnc))) (.classMem (.cv n) (syn_cnnc)) p0127
  have p0129 :=
    @g_mpbird (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_cdm (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))) (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_cnnc)) p0121 p0128
  have p0130 :=
    @g_fntcfn
  have p0131 :=
    @g_fnfun (syn_c1c) (syn_ctcfn)
  have p0132 :=
    Nominal.mp p0130 p0131
  have p0133 :=
    @g_vex n
  have p0134 :=
    @g_snel1c (.cv n) p0133
  have p0135 :=
    @g_fntcfn
  have p0136 :=
    @g_fndm (syn_c1c) (syn_ctcfn)
  have p0137 :=
    Nominal.mp p0135 p0136
  have p0138 :=
    @g_eleqtrri (syn_csn (.cv n)) (syn_c1c) (syn_cdm (syn_ctcfn)) p0134 p0137
  have p0139 :=
    @g_pm3_2i (syn_wfun (syn_ctcfn)) (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ctcfn))) p0132 p0138
  have p0140 :=
    @g_dmfco (syn_csn (.cv n)) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)
  have p0141 :=
    Nominal.mp p0139 p0140
  have p0142 :=
    @g_a1i (syn_wb (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))) (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_cdm (syn_cfrec (syn_cwpppostcomp F) (syn_cid))))) (.classMem (.cv n) (syn_cnnc)) p0141
  have p0143 :=
    @g_mpbird (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))) (.classMem (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_cdm (syn_cfrec (syn_cwpppostcomp F) (syn_cid)))) p0129 p0142
  have p0144 :=
    @g_jca (.classMem (.cv n) (syn_cnnc)) (syn_wfun (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))) (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)))) p0115 p0143
  have p0145 :=
    @g_fvco (syn_csn (.cv n)) (syn_cwppimageat D) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))
  have p0146 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) (syn_wa (syn_wfun (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))) (.classMem (syn_csn (.cv n)) (syn_cdm (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))))) (.classEq (syn_cfv (syn_ccom (syn_cwppimageat D) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))) (syn_csn (.cv n))) (syn_cfv (syn_cwppimageat D) (syn_cfv (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)) (syn_csn (.cv n))))) p0144 p0145
  have p0147 :=
    @g_fntcfn
  have p0148 :=
    @g_vex n
  have p0149 :=
    @g_snel1c (.cv n) p0148
  have p0150 :=
    @g_pm3_2i (syn_wfn (syn_ctcfn) (syn_c1c)) (.classMem (syn_csn (.cv n)) (syn_c1c)) p0147 p0149
  have p0151 :=
    @g_fvco2 (syn_c1c) (syn_csn (.cv n)) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)
  have p0152 :=
    Nominal.mp p0150 p0151
  have p0153 :=
    @g_vex n
  have p0154 :=
    @g_tcfnfv (.cv n) p0153
  have p0155 :=
    @g_fveq2i (syn_cfv (syn_ctcfn) (syn_csn (.cv n))) (syn_ctc (.cv n)) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) p0154
  have p0156 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)) (syn_csn (.cv n))) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cfv (syn_ctcfn) (syn_csn (.cv n)))) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))) p0152 p0155
  have p0157 :=
    @g_a1i (.classEq (syn_cfv (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)) (syn_csn (.cv n))) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))) (.classMem (.cv n) (syn_cnnc)) p0156
  have p0158 :=
    @g_fveq2d (.classMem (.cv n) (syn_cnnc)) (syn_cfv (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)) (syn_csn (.cv n))) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))) (syn_cwppimageat D) p0157
  have p0159 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc)) (syn_cfv (syn_ccom (syn_cwppimageat D) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))) (syn_csn (.cv n))) (syn_cfv (syn_cwppimageat D) (syn_cfv (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)) (syn_csn (.cv n)))) (syn_cfv (syn_cwppimageat D) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))) p0146 p0158
  have p0160 :=
    @g_elex D (syn_cdm F)
  have p0161 :=
    Nominal.mp hyp_wpppowateqval_2 p0160
  have p0162 :=
    @g_fvex (syn_ctc (.cv n)) (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0163 :=
    @g_wppimageatfv D (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))) p0161 p0162
  have p0164 :=
    @g_a1i (.classEq (syn_cfv (syn_cwppimageat D) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))) (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))) (syn_csn D))) (.classMem (.cv n) (syn_cnnc)) p0163
  have p0165 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc)) (syn_cfv (syn_ccom (syn_cwppimageat D) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))) (syn_csn (.cv n))) (syn_cfv (syn_cwppimageat D) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n)))) (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))) (syn_csn D)) p0159 p0164
  have p0166 :=
    @g_n_3pm3_2i (.classMem F (syn_cfuns)) (.classMem D (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F)) hyp_wpppowateqval_1 hyp_wpppowateqval_2 hyp_wpppowateqval_3
  have p0167 :=
    @g_wpporbitfnndv F D
  have p0168 :=
    Nominal.mp p0166 p0167
  have p0169 :=
    @g_sifnvalv n (syn_cnnc) (syn_cfrec F D)
  have p0170 :=
    @g_mpan (syn_wfn (syn_cfrec F D) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_cfv (syn_csi (syn_cfrec F D)) (syn_csn (.cv n))) (syn_csn (syn_cfv (syn_cfrec F D) (.cv n)))) p0168 p0169
  have p0171 :=
    @g_eqeq12d (.classMem (.cv n) (syn_cnnc)) (syn_cfv (syn_ccom (syn_cwppimageat D) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))) (syn_csn (.cv n))) (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))) (syn_csn D)) (syn_cfv (syn_csi (syn_cfrec F D)) (syn_csn (.cv n))) (syn_csn (syn_cfv (syn_cfrec F D) (.cv n))) p0165 p0170
  have p0172 :=
    @g_bitrd (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpppowateq F D)) (.classEq (syn_cfv (syn_ccom (syn_cwppimageat D) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))) (syn_csn (.cv n))) (syn_cfv (syn_csi (syn_cfrec F D)) (syn_csn (.cv n)))) (.classEq (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))) (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) (.cv n)))) p0103 p0171
  exact p0172

noncomputable def g_wpppowateqvalcl
    (B : Class) (D : Class) (F : Class) (hyp_wpppowateqvalcl_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wpppowateqvalcl_2 : Nominal.NPrf (.classMem D (syn_cdm F))) (hyp_wpppowateqvalcl_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) :
    Nominal.NPrf (.imp (.classMem B (syn_cnnc)) (syn_wb (.classMem B (syn_cwpppowateq F D)) (.classEq (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc B)) (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) B))))) := by
  let proofSupport : Finset Var := B.fv ∪ D.fv ∪ F.fv
  let n : Var := freshVar proofSupport 0
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_B : n ∉ B.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_n_not_D : n ∉ D.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_not_F : n ∉ F.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have dv_cache_0001 : n ∉ (B).fv := by
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : n ∉ ((Wff.imp (.classMem B (syn_cnnc)) (syn_wb (.classMem B (syn_cwpppowateq F D)) (.classEq (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc B)) (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) B)))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowateq, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppostcomp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_B, fresh_n_not_D, fresh_n_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classMem B (syn_cnnc))
  have p0001 :=
    @g_id (.classEq (.cv n) B)
  have p0002 :=
    @g_eleq1d (.classEq (.cv n) B) (.cv n) B (syn_cnnc) p0001
  have p0003 :=
    @g_id (.classEq (.cv n) B)
  have p0004 :=
    @g_eleq1d (.classEq (.cv n) B) (.cv n) B (syn_cwpppowateq F D) p0003
  have p0005 :=
    @g_id (.classEq (.cv n) B)
  have p0006 :=
    @g_tceq (.cv n) B
  have p0007 :=
    @g_syl (.classEq (.cv n) B) (.classEq (.cv n) B) (.classEq (syn_ctc (.cv n)) (syn_ctc B)) p0005 p0006
  have p0008 :=
    @g_fveq2d (.classEq (.cv n) B) (syn_ctc (.cv n)) (syn_ctc B) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) p0007
  have p0009 :=
    @g_imaeq1d (.classEq (.cv n) B) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc B)) (syn_csn D) p0008
  have p0010 :=
    @g_id (.classEq (.cv n) B)
  have p0011 :=
    @g_fveq2d (.classEq (.cv n) B) (.cv n) B (syn_cfrec F D) p0010
  have p0012 :=
    @g_sneqd (.classEq (.cv n) B) (syn_cfv (syn_cfrec F D) (.cv n)) (syn_cfv (syn_cfrec F D) B) p0011
  have p0013 :=
    @g_eqeq12d (.classEq (.cv n) B) (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))) (syn_csn D)) (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc B)) (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) (.cv n))) (syn_csn (syn_cfv (syn_cfrec F D) B)) p0009 p0012
  have p0014 :=
    @g_bibi12d (.classEq (.cv n) B) (.classMem (.cv n) (syn_cwpppowateq F D)) (.classMem B (syn_cwpppowateq F D)) (.classEq (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))) (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) (.cv n)))) (.classEq (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc B)) (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) B))) p0004 p0013
  have p0015 :=
    @g_imbi12d (.classEq (.cv n) B) (.classMem (.cv n) (syn_cnnc)) (.classMem B (syn_cnnc)) (syn_wb (.classMem (.cv n) (syn_cwpppowateq F D)) (.classEq (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))) (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) (.cv n))))) (syn_wb (.classMem B (syn_cwpppowateq F D)) (.classEq (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc B)) (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) B)))) p0002 p0014
  have p0016 :=
    @g_wpppowateqval D n F hyp_wpppowateqvalcl_1 hyp_wpppowateqvalcl_2 hyp_wpppowateqvalcl_3
  have p0017 :=
    @g_vtoclg (.imp (.classMem (.cv n) (syn_cnnc)) (syn_wb (.classMem (.cv n) (syn_cwpppowateq F D)) (.classEq (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv n))) (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) (.cv n)))))) (.imp (.classMem B (syn_cnnc)) (syn_wb (.classMem B (syn_cwpppowateq F D)) (.classEq (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc B)) (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) B))))) n B (syn_cnnc) dv_cache_0001 dv_cache_0002 p0015 p0016
  have p0018 :=
    @g_mpd (.classMem B (syn_cnnc)) (.classMem B (syn_cnnc)) (syn_wb (.classMem B (syn_cwpppowateq F D)) (.classEq (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc B)) (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) B)))) p0000 p0017
  exact p0018

noncomputable def g_wpppowcoresuccl
    (B : Class) (F : Class) (hyp_wpppowcoresuccl_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem B (syn_cnnc)) (.classEq (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc B (syn_c1c))) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B)))) := by
  let proofSupport : Finset Var := B.fv ∪ F.fv
  let n : Var := freshVar proofSupport 0
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_B : n ∉ B.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (h))
  have fresh_n_not_F : n ∉ F.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have dv_cache_0001 : n ∉ (F).fv := by
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : n ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : n ∉ ((Wff.imp (.classMem B (syn_cnnc)) (.classEq (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc B (syn_c1c))) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B))))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppostcomp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_B, fresh_n_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classMem B (syn_cnnc))
  have p0001 :=
    @g_id (.classEq (.cv n) B)
  have p0002 :=
    @g_eleq1d (.classEq (.cv n) B) (.cv n) B (syn_cnnc) p0001
  have p0003 :=
    @g_id (.classEq (.cv n) B)
  have p0004 :=
    @g_addceq1d (.classEq (.cv n) B) (.cv n) B (syn_c1c) p0003
  have p0005 :=
    @g_fveq2d (.classEq (.cv n) B) (syn_cplc (.cv n) (syn_c1c)) (syn_cplc B (syn_c1c)) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) p0004
  have p0006 :=
    @g_id (.classEq (.cv n) B)
  have p0007 :=
    @g_fveq2d (.classEq (.cv n) B) (.cv n) B (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) p0006
  have p0008 :=
    @g_coeq2d (.classEq (.cv n) B) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B) F p0007
  have p0009 :=
    @g_eqeq12d (.classEq (.cv n) B) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (.cv n) (syn_c1c))) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc B (syn_c1c))) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n))) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B)) p0005 p0008
  have p0010 :=
    @g_imbi12d (.classEq (.cv n) B) (.classMem (.cv n) (syn_cnnc)) (.classMem B (syn_cnnc)) (.classEq (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (.cv n) (syn_c1c))) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n)))) (.classEq (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc B (syn_c1c))) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B))) p0002 p0009
  have p0011 :=
    @g_wpppowcoresuc n F dv_cache_0001 hyp_wpppowcoresuccl_1
  have p0012 :=
    @g_vtoclg (.imp (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (.cv n) (syn_c1c))) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (.cv n))))) (.imp (.classMem B (syn_cnnc)) (.classEq (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc B (syn_c1c))) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B)))) n B (syn_cnnc) dv_cache_0002 dv_cache_0003 p0010 p0011
  have p0013 :=
    @g_mpd (.classMem B (syn_cnnc)) (.classMem B (syn_cnnc)) (.classEq (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc B (syn_c1c))) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) B))) p0000 p0012
  exact p0013

noncomputable def g_wpppowateqall
    (D : Class) (F : Class) (N : Class) (hyp_wpppowateqall_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wpppowateqall_2 : Nominal.NPrf (.classMem D (syn_cdm F))) (hyp_wpppowateqall_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) :
    Nominal.NPrf (.imp (.classMem N (syn_cnnc)) (.classMem N (syn_cwpppowateq F D))) := by
  let proofSupport : Finset Var := D.fv ∪ F.fv ∪ N.fv
  let n : Var := freshVar proofSupport 0
  let m : Var := freshVar proofSupport 1
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_D : n ∉ D.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_n_not_F : n ∉ F.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_not_N : n ∉ N.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have fresh_m : m ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_m_not_D : m ∉ D.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_m_not_F : m ∉ F.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_m_not_N : m ∉ N.fv := by
    intro h
    exact fresh_m (Finset.mem_union_right _ (h))
  have fresh_n_ne_m : n ≠ m := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_m_ne_n : m ≠ n :=
    Ne.symm fresh_n_ne_m
  have dv_cache_0001 : n ∉ ((syn_cwpppowateq F D)).fv := by
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowateq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_D, fresh_n_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : n ∉ (N).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_N, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : n ∉ ((Wff.classMem (.cv m) (syn_cwpppowateq F D))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowateq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_m, fresh_n_not_D, fresh_n_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : m ∉ ((Wff.classMem (.cv n) (syn_cwpppowateq F D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowateq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_n, fresh_m_not_D, fresh_m_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : n ∉ ((Wff.classMem (syn_c0c) (syn_cwpppowateq F D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowateq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_D, fresh_n_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : n ∉ ((Wff.classMem N (syn_cwpppowateq F D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowateq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_N, fresh_n_not_D, fresh_n_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : n ∉ ((Wff.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cwpppowateq F D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowateq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_m, fresh_n_not_D, fresh_n_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : n ≠ m := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show n ≠ m from (by exact fresh_n_ne_m))
  have p0000 :=
    @g_elex F (syn_cfuns)
  have p0001 :=
    Nominal.mp hyp_wpppowateqall_1 p0000
  have p0002 :=
    @g_elex D (syn_cdm F)
  have p0003 :=
    Nominal.mp hyp_wpppowateqall_2 p0002
  have p0004 :=
    @g_wpppowateqex D F p0001 p0003
  have p0005 :=
    @g_abid2 n (syn_cwpppowateq F D) dv_cache_0001
  have p0006 :=
    @g_eleq1i (.cab n (.classMem (.cv n) (syn_cwpppowateq F D))) (syn_cwpppowateq F D) (syn_cvv) p0005
  have p0007 :=
    @g_mpbir (.classMem (.cab n (.classMem (.cv n) (syn_cwpppowateq F D))) (syn_cvv)) (.classMem (syn_cwpppowateq F D) (syn_cvv)) p0004 p0006
  have p0008 :=
    @g_id (.classEq (.cv n) (syn_c0c))
  have p0009 :=
    @g_eleq1d (.classEq (.cv n) (syn_c0c)) (.cv n) (syn_c0c) (syn_cwpppowateq F D) p0008
  have p0010 :=
    @g_id (.classEq (.cv n) (.cv m))
  have p0011 :=
    @g_eleq1d (.classEq (.cv n) (.cv m)) (.cv n) (.cv m) (syn_cwpppowateq F D) p0010
  have p0012 :=
    @g_id (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c)))
  have p0013 :=
    @g_eleq1d (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c))) (.cv n) (syn_cplc (.cv m) (syn_c1c)) (syn_cwpppowateq F D) p0012
  have p0014 :=
    @g_id (.classEq (.cv n) N)
  have p0015 :=
    @g_eleq1d (.classEq (.cv n) N) (.cv n) N (syn_cwpppowateq F D) p0014
  have p0016 :=
    @g_tc0c
  have p0017 :=
    @g_fveq2i (syn_ctc (syn_c0c)) (syn_c0c) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) p0016
  have p0018 :=
    @g_elex F (syn_cfuns)
  have p0019 :=
    Nominal.mp hyp_wpppowateqall_1 p0018
  have p0020 :=
    @g_wpppowcore0 F p0019
  have p0021 :=
    @g_eqtri (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_c0c))) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_c0c)) (syn_cid) p0017 p0020
  have p0022 :=
    @g_imaeq1i (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_c0c))) (syn_cid) (syn_csn D) p0021
  have p0023 :=
    @g_imai (syn_csn D)
  have p0024 :=
    @g_eqtri (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_c0c))) (syn_csn D)) (syn_cima (syn_cid) (syn_csn D)) (syn_csn D) p0022 p0023
  have p0025 :=
    @g_n_3pm3_2i (.classMem F (syn_cfuns)) (.classMem D (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F)) hyp_wpppowateqall_1 hyp_wpppowateqall_2 hyp_wpppowateqall_3
  have p0026 :=
    @g_wpporbit0ndv F D
  have p0027 :=
    Nominal.mp p0025 p0026
  have p0028 :=
    @g_sneqi (syn_cfv (syn_cfrec F D) (syn_c0c)) D p0027
  have p0029 :=
    @g_eqcomi (syn_csn (syn_cfv (syn_cfrec F D) (syn_c0c))) (syn_csn D) p0028
  have p0030 :=
    @g_eqtri (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_c0c))) (syn_csn D)) (syn_csn D) (syn_csn (syn_cfv (syn_cfrec F D) (syn_c0c))) p0024 p0029
  have p0031 :=
    @g_peano1
  have p0032 :=
    @g_wpppowateqvalcl (syn_c0c) D F hyp_wpppowateqall_1 hyp_wpppowateqall_2 hyp_wpppowateqall_3
  have p0033 :=
    Nominal.mp p0031 p0032
  have p0034 :=
    @g_mpbir (.classMem (syn_c0c) (syn_cwpppowateq F D)) (.classEq (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_c0c))) (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) (syn_c0c)))) p0030 p0033
  have p0035 :=
    @g_simpl (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D))
  have p0036 :=
    @g_nntcsuc (.cv m)
  have p0037 :=
    @g_syl (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D))) (.classMem (.cv m) (syn_cnnc)) (.classEq (syn_ctc (syn_cplc (.cv m) (syn_c1c))) (syn_cplc (syn_ctc (.cv m)) (syn_c1c))) p0035 p0036
  have p0038 :=
    @g_fveq2d (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D))) (syn_ctc (syn_cplc (.cv m) (syn_c1c))) (syn_cplc (syn_ctc (.cv m)) (syn_c1c)) (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) p0037
  have p0039 :=
    @g_simpl (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D))
  have p0040 :=
    @g_nntccl (.cv m)
  have p0041 :=
    @g_syl (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D))) (.classMem (.cv m) (syn_cnnc)) (.classMem (syn_ctc (.cv m)) (syn_cnnc)) p0039 p0040
  have p0042 :=
    @g_elex F (syn_cfuns)
  have p0043 :=
    Nominal.mp hyp_wpppowateqall_1 p0042
  have p0044 :=
    @g_wpppowcoresuccl (syn_ctc (.cv m)) F p0043
  have p0045 :=
    @g_syl (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D))) (.classMem (syn_ctc (.cv m)) (syn_cnnc)) (.classEq (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (syn_ctc (.cv m)) (syn_c1c))) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv m))))) p0041 p0044
  have p0046 :=
    @g_eqtrd (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D))) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_cplc (.cv m) (syn_c1c)))) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cplc (syn_ctc (.cv m)) (syn_c1c))) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv m)))) p0038 p0045
  have p0047 :=
    @g_imaeq1d (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D))) (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_cplc (.cv m) (syn_c1c)))) (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv m)))) (syn_csn D) p0046
  have p0048 :=
    @g_imaco F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv m))) (syn_csn D)
  have p0049 :=
    @g_a1i (.classEq (syn_cima (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv m)))) (syn_csn D)) (syn_cima F (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv m))) (syn_csn D)))) (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D))) p0048
  have p0050 :=
    @g_eqtrd (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D))) (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_cplc (.cv m) (syn_c1c)))) (syn_csn D)) (syn_cima (syn_ccom F (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv m)))) (syn_csn D)) (syn_cima F (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv m))) (syn_csn D))) p0047 p0049
  have p0051 :=
    @g_simpr (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D))
  have p0052 :=
    @g_simpl (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D))
  have p0053 :=
    @g_wpppowateqval D m F hyp_wpppowateqall_1 hyp_wpppowateqall_2 hyp_wpppowateqall_3
  have p0054 :=
    @g_syl (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D))) (.classMem (.cv m) (syn_cnnc)) (syn_wb (.classMem (.cv m) (syn_cwpppowateq F D)) (.classEq (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv m))) (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) (.cv m))))) p0052 p0053
  have p0055 :=
    @g_biimpd (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D))) (.classMem (.cv m) (syn_cwpppowateq F D)) (.classEq (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv m))) (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) (.cv m)))) p0054
  have p0056 :=
    @g_mpd (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D))) (.classMem (.cv m) (syn_cwpppowateq F D)) (.classEq (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv m))) (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) (.cv m)))) p0051 p0055
  have p0057 :=
    @g_imaeq2d (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D))) (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv m))) (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) (.cv m))) F p0056
  have p0058 :=
    @g_eqtrd (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D))) (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_cplc (.cv m) (syn_c1c)))) (syn_csn D)) (syn_cima F (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (.cv m))) (syn_csn D))) (syn_cima F (syn_csn (syn_cfv (syn_cfrec F D) (.cv m)))) p0050 p0057
  have p0059 :=
    @g_elfunsi F
  have p0060 :=
    Nominal.mp hyp_wpppowateqall_1 p0059
  have p0061 :=
    @g_funfn F
  have p0062 :=
    @g_biimpi (syn_wfun F) (syn_wfn F (syn_cdm F)) p0061
  have p0063 :=
    Nominal.mp p0060 p0062
  have p0064 :=
    @g_a1i (syn_wfn F (syn_cdm F)) (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D))) p0063
  have p0065 :=
    @g_simpl (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D))
  have p0066 :=
    @g_n_3pm3_2i (.classMem F (syn_cfuns)) (.classMem D (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F)) hyp_wpppowateqall_1 hyp_wpppowateqall_2 hyp_wpppowateqall_3
  have p0067 :=
    @g_frecdomfv F D (.cv m)
  have p0068 :=
    @g_mpan (syn_w3a (.classMem F (syn_cfuns)) (.classMem D (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem (.cv m) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec F D) (.cv m)) (syn_cdm F)) p0066 p0067
  have p0069 :=
    @g_syl (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D))) (.classMem (.cv m) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec F D) (.cv m)) (syn_cdm F)) p0065 p0068
  have p0070 :=
    @g_jca (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D))) (syn_wfn F (syn_cdm F)) (.classMem (syn_cfv (syn_cfrec F D) (.cv m)) (syn_cdm F)) p0064 p0069
  have p0071 :=
    @g_fnsnfv (syn_cdm F) (syn_cfv (syn_cfrec F D) (.cv m)) F
  have p0072 :=
    @g_syl (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D))) (syn_wa (syn_wfn F (syn_cdm F)) (.classMem (syn_cfv (syn_cfrec F D) (.cv m)) (syn_cdm F))) (.classEq (syn_csn (syn_cfv F (syn_cfv (syn_cfrec F D) (.cv m)))) (syn_cima F (syn_csn (syn_cfv (syn_cfrec F D) (.cv m))))) p0070 p0071
  have p0073 :=
    @g_eqcomd (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D))) (syn_csn (syn_cfv F (syn_cfv (syn_cfrec F D) (.cv m)))) (syn_cima F (syn_csn (syn_cfv (syn_cfrec F D) (.cv m)))) p0072
  have p0074 :=
    @g_eqtrd (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D))) (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_cplc (.cv m) (syn_c1c)))) (syn_csn D)) (syn_cima F (syn_csn (syn_cfv (syn_cfrec F D) (.cv m)))) (syn_csn (syn_cfv F (syn_cfv (syn_cfrec F D) (.cv m)))) p0058 p0073
  have p0075 :=
    @g_simpl (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D))
  have p0076 :=
    @g_n_3pm3_2i (.classMem F (syn_cfuns)) (.classMem D (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F)) hyp_wpppowateqall_1 hyp_wpppowateqall_2 hyp_wpppowateqall_3
  have p0077 :=
    @g_wpporbitsucndv F D (.cv m)
  have p0078 :=
    @g_mpan (syn_w3a (.classMem F (syn_cfuns)) (.classMem D (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem (.cv m) (syn_cnnc)) (.classEq (syn_cfv (syn_cfrec F D) (syn_cplc (.cv m) (syn_c1c))) (syn_cfv F (syn_cfv (syn_cfrec F D) (.cv m)))) p0076 p0077
  have p0079 :=
    @g_syl (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D))) (.classMem (.cv m) (syn_cnnc)) (.classEq (syn_cfv (syn_cfrec F D) (syn_cplc (.cv m) (syn_c1c))) (syn_cfv F (syn_cfv (syn_cfrec F D) (.cv m)))) p0075 p0078
  have p0080 :=
    @g_sneqd (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D))) (syn_cfv (syn_cfrec F D) (syn_cplc (.cv m) (syn_c1c))) (syn_cfv F (syn_cfv (syn_cfrec F D) (.cv m))) p0079
  have p0081 :=
    @g_eqcomd (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D))) (syn_csn (syn_cfv (syn_cfrec F D) (syn_cplc (.cv m) (syn_c1c)))) (syn_csn (syn_cfv F (syn_cfv (syn_cfrec F D) (.cv m)))) p0080
  have p0082 :=
    @g_eqtrd (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D))) (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_cplc (.cv m) (syn_c1c)))) (syn_csn D)) (syn_csn (syn_cfv F (syn_cfv (syn_cfrec F D) (.cv m)))) (syn_csn (syn_cfv (syn_cfrec F D) (syn_cplc (.cv m) (syn_c1c)))) p0074 p0081
  have p0083 :=
    @g_simpl (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D))
  have p0084 :=
    @g_peano2 (.cv m)
  have p0085 :=
    @g_syl (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D))) (.classMem (.cv m) (syn_cnnc)) (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cnnc)) p0083 p0084
  have p0086 :=
    @g_wpppowateqvalcl (syn_cplc (.cv m) (syn_c1c)) D F hyp_wpppowateqall_1 hyp_wpppowateqall_2 hyp_wpppowateqall_3
  have p0087 :=
    @g_syl (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D))) (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cnnc)) (syn_wb (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cwpppowateq F D)) (.classEq (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_cplc (.cv m) (syn_c1c)))) (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) (syn_cplc (.cv m) (syn_c1c)))))) p0085 p0086
  have p0088 :=
    @g_mpbird (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D))) (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cwpppowateq F D)) (.classEq (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc (syn_cplc (.cv m) (syn_c1c)))) (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) (syn_cplc (.cv m) (syn_c1c))))) p0082 p0087
  have p0089 :=
    @g_ex (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cwpppowateq F D)) (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cwpppowateq F D)) p0088
  have p0090_e02_recanon : Nominal.NPrf (.imp (.objEq n m) (syn_wb (.classMem (.cv n) (syn_cwpppowateq F D)) (.classMem (.cv m) (syn_cwpppowateq F D)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cwpppowateq syn_cuni1 syn_cuni syn_wex syn_wa syn_cin syn_ccompl syn_cnin syn_wnan syn_c1c syn_cfix syn_crn syn_cima syn_wrex syn_wbr syn_cop syn_cun syn_cvv syn_ccom syn_copab syn_ccnv syn_csi syn_cfrec syn_cclos1 syn_cint syn_csn syn_cpprod syn_ctxp syn_cmpt syn_cplc
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowateq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0011
  have p0090 :=
    @g_finds (.classMem (.cv n) (syn_cwpppowateq F D)) (.classMem (syn_c0c) (syn_cwpppowateq F D)) (.classMem (.cv m) (syn_cwpppowateq F D)) (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cwpppowateq F D)) (.classMem N (syn_cwpppowateq F D)) n m N dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 p0007 p0009 p0090_e02_recanon p0013 p0015 p0034 p0089
  exact p0090

noncomputable def g_wpppowatact
    (D : Class) (F : Class) (N : Class) (hyp_wpppowatact_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wpppowatact_2 : Nominal.NPrf (.classMem D (syn_cdm F))) (hyp_wpppowatact_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) :
    Nominal.NPrf (.imp (.classMem N (syn_cnnc)) (.classEq (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc N)) (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) N)))) := by
  let proofSupport : Finset Var := D.fv ∪ F.fv ∪ N.fv
  have p0000 :=
    @g_wpppowateqall D F N hyp_wpppowatact_1 hyp_wpppowatact_2 hyp_wpppowatact_3
  have p0001 :=
    @g_wpppowateqvalcl N D F hyp_wpppowatact_1 hyp_wpppowatact_2 hyp_wpppowatact_3
  have p0002 :=
    @g_mpbid (.classMem N (syn_cnnc)) (.classMem N (syn_cwpppowateq F D)) (.classEq (syn_cima (syn_cfv (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctc N)) (syn_csn D)) (syn_csn (syn_cfv (syn_cfrec F D) N))) p0000 p0001
  exact p0002

#print axioms g_wpppowatact

end NFChoice.DirectNominalPrf.WPPReplay
