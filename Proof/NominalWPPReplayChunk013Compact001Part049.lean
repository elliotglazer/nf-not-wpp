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
import NominalWPPReplayChunk013Compact001Part048

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

noncomputable def g_sbthlem1
    (A : Class) (B : Class) (C : Class) (D : Class) (R : Class) (G : Class) (X : Class) (hyp_sbthlem1_1 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_sbthlem1_2 : Nominal.NPrf (.classMem X (syn_cvv))) (hyp_sbthlem1_3 : Nominal.NPrf (.classEq G (syn_cclos1 (syn_cdif X (syn_crn R)) R))) (hyp_sbthlem1_4 : Nominal.NPrf (.classEq A (syn_cin X G))) (hyp_sbthlem1_5 : Nominal.NPrf (.classEq B (syn_cdif X G))) (hyp_sbthlem1_6 : Nominal.NPrf (.classEq C (syn_cin (syn_crn R) G))) (hyp_sbthlem1_7 : Nominal.NPrf (.classEq D (syn_cdif (syn_crn R) G))) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X))) (syn_wbr (syn_crn R) (syn_cen) X)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv ∪ G.fv ∪ X.fv
  have p0000 :=
    (by simpa [syn_wb, syn_wf1] using (Nominal.biimpRefl (syn_wf1 R (syn_cdm R) (syn_crn R))))
  have p0001 :=
    @g_ssid (syn_crn R)
  have p0002 :=
    (by simpa [syn_wb, syn_wf] using (Nominal.biimpRefl (syn_wf R (syn_cdm R) (syn_crn R))))
  have p0003 :=
    @g_mpbiran2 (syn_wf R (syn_cdm R) (syn_crn R)) (syn_wfn R (syn_cdm R)) (syn_wss (syn_crn R) (syn_crn R)) p0001 p0002
  have p0004 :=
    @g_funfn R
  have p0005 :=
    @g_bitr4i (syn_wf R (syn_cdm R) (syn_crn R)) (syn_wfn R (syn_cdm R)) (syn_wfun R) p0003 p0004
  have p0006 :=
    @g_anbi1i (syn_wf R (syn_cdm R) (syn_crn R)) (syn_wfun R) (syn_wfun (syn_ccnv R)) p0005
  have p0007 :=
    @g_bitri (syn_wf1 R (syn_cdm R) (syn_crn R)) (syn_wa (syn_wf R (syn_cdm R) (syn_crn R)) (syn_wfun (syn_ccnv R))) (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) p0000 p0006
  have p0008 :=
    @g_biimpri (syn_wf1 R (syn_cdm R) (syn_crn R)) (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) p0007
  have p0009 :=
    @g_inss1 X G
  have p0010 :=
    @g_sstr (syn_cin X G) X (syn_cdm R)
  have p0011 :=
    @g_mpan (syn_wss (syn_cin X G) X) (syn_wss X (syn_cdm R)) (syn_wss (syn_cin X G) (syn_cdm R)) p0009 p0010
  have p0012 :=
    @g_syl5eqss (syn_wss X (syn_cdm R)) A (syn_cin X G) (syn_cdm R) hyp_sbthlem1_4 p0011
  have p0013 :=
    @g_adantr (syn_wss X (syn_cdm R)) (syn_wss A (syn_cdm R)) (syn_wss (syn_crn R) X) p0012
  have p0014 :=
    @g_f1ores (syn_cdm R) (syn_crn R) A R
  have p0015 :=
    @g_syl2an (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wf1 R (syn_cdm R) (syn_crn R)) (syn_wss A (syn_cdm R)) (syn_wf1o (syn_cres R A) A (syn_cima R A)) (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X)) p0008 p0013 p0014
  have p0016 :=
    @g_rnex R hyp_sbthlem1_1
  have p0017 :=
    @g_difex X (syn_crn R) hyp_sbthlem1_2 p0016
  have p0018 :=
    @g_clos1ex R (syn_cdif X (syn_crn R)) p0017 hyp_sbthlem1_1
  have p0019 :=
    @g_eqeltri G (syn_cclos1 (syn_cdif X (syn_crn R)) R) (syn_cvv) hyp_sbthlem1_3 p0018
  have p0020 :=
    @g_inex X G hyp_sbthlem1_2 p0019
  have p0021 :=
    @g_eqeltri A (syn_cin X G) (syn_cvv) hyp_sbthlem1_4 p0020
  have p0022 :=
    @g_resex R A hyp_sbthlem1_1 p0021
  have p0023 :=
    @g_f1oen A (syn_cima R A) (syn_cres R A) p0022
  have p0024 :=
    @g_syl (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X))) (syn_wf1o (syn_cres R A) A (syn_cima R A)) (syn_wbr A (syn_cen) (syn_cima R A)) p0015 p0023
  have p0025 :=
    @g_clos1baseima G R (syn_cdif X (syn_crn R)) p0017 hyp_sbthlem1_1 hyp_sbthlem1_3
  have p0026 :=
    @g_ineq2i G (syn_cun (syn_cdif X (syn_crn R)) (syn_cima R G)) (syn_crn R) p0025
  have p0027 :=
    @g_indi (syn_crn R) (syn_cdif X (syn_crn R)) (syn_cima R G)
  have p0028 :=
    @g_disjdif (syn_crn R) X
  have p0029 :=
    @g_uneq1i (syn_cin (syn_crn R) (syn_cdif X (syn_crn R))) (syn_c0) (syn_cin (syn_crn R) (syn_cima R G)) p0028
  have p0030 :=
    @g_uncom (syn_c0) (syn_cin (syn_crn R) (syn_cima R G))
  have p0031 :=
    @g_un0 (syn_cin (syn_crn R) (syn_cima R G))
  have p0032 :=
    @g_eqtri (syn_cun (syn_c0) (syn_cin (syn_crn R) (syn_cima R G))) (syn_cun (syn_cin (syn_crn R) (syn_cima R G)) (syn_c0)) (syn_cin (syn_crn R) (syn_cima R G)) p0030 p0031
  have p0033 :=
    @g_n_3eqtri (syn_cin (syn_crn R) (syn_cun (syn_cdif X (syn_crn R)) (syn_cima R G))) (syn_cun (syn_cin (syn_crn R) (syn_cdif X (syn_crn R))) (syn_cin (syn_crn R) (syn_cima R G))) (syn_cun (syn_c0) (syn_cin (syn_crn R) (syn_cima R G))) (syn_cin (syn_crn R) (syn_cima R G)) p0027 p0029 p0032
  have p0034 :=
    @g_n_3eqtri C (syn_cin (syn_crn R) G) (syn_cin (syn_crn R) (syn_cun (syn_cdif X (syn_crn R)) (syn_cima R G))) (syn_cin (syn_crn R) (syn_cima R G)) hyp_sbthlem1_6 p0026 p0033
  have p0035 :=
    @g_inss2 (syn_crn R) (syn_cima R G)
  have p0036 :=
    @g_a1i (syn_wss (syn_cin (syn_crn R) (syn_cima R G)) (syn_cima R G)) (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X))) p0035
  have p0037 :=
    @g_syl5eqss (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X))) C (syn_cin (syn_crn R) (syn_cima R G)) (syn_cima R G) p0034 p0036
  have p0038 :=
    @g_imassrn R G
  have p0039 :=
    @g_simprr (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X)
  have p0040 :=
    @g_syl5ss (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X))) (syn_cima R G) (syn_crn R) X p0038 p0039
  have p0041 :=
    @g_difss X (syn_crn R)
  have p0042 :=
    @g_jctil (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X))) (syn_wss (syn_cima R G) X) (syn_wss (syn_cdif X (syn_crn R)) X) p0040 p0041
  have p0043 :=
    @g_unss (syn_cdif X (syn_crn R)) (syn_cima R G) X
  have p0044 :=
    @g_sylib (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X))) (syn_wa (syn_wss (syn_cdif X (syn_crn R)) X) (syn_wss (syn_cima R G) X)) (syn_wss (syn_cun (syn_cdif X (syn_crn R)) (syn_cima R G)) X) p0042 p0043
  have p0045 :=
    @g_syl5eqss (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X))) G (syn_cun (syn_cdif X (syn_crn R)) (syn_cima R G)) X p0025 p0044
  have p0046 :=
    @g_sseqin2 G X
  have p0047 :=
    @g_sylib (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X))) (syn_wss G X) (.classEq (syn_cin X G) G) p0045 p0046
  have p0048 :=
    @g_syl5eq (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X))) A (syn_cin X G) G hyp_sbthlem1_4 p0047
  have p0049 :=
    @g_imaeq2d (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X))) A G R p0048
  have p0050 :=
    @g_sseqtr4d (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X))) C (syn_cima R G) (syn_cima R A) p0037 p0049
  have p0051 :=
    @g_ssun2 (syn_cima R G) (syn_cdif X (syn_crn R))
  have p0052 :=
    @g_sseqtr4i (syn_cima R G) (syn_cun (syn_cdif X (syn_crn R)) (syn_cima R G)) G p0051 p0025
  have p0053 :=
    @g_sseq1d (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X))) (syn_cima R A) (syn_cima R G) G p0049
  have p0054 :=
    @g_mpbiri (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X))) (syn_wss (syn_cima R A) G) (syn_wss (syn_cima R G) G) p0052 p0053
  have p0055 :=
    @g_imassrn R A
  have p0056 :=
    @g_jctil (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X))) (syn_wss (syn_cima R A) G) (syn_wss (syn_cima R A) (syn_crn R)) p0054 p0055
  have p0057 :=
    @g_ssin (syn_cima R A) (syn_crn R) G
  have p0058 :=
    @g_sylib (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X))) (syn_wa (syn_wss (syn_cima R A) (syn_crn R)) (syn_wss (syn_cima R A) G)) (syn_wss (syn_cima R A) (syn_cin (syn_crn R) G)) p0056 p0057
  have p0059 :=
    @g_syl6sseqr (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X))) (syn_cima R A) (syn_cin (syn_crn R) G) C p0058 hyp_sbthlem1_6
  have p0060 :=
    @g_eqssd (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X))) C (syn_cima R A) p0050 p0059
  have p0061 :=
    @g_breqtrrd (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X))) A (syn_cima R A) C (syn_cen) p0024 p0060
  have p0062 :=
    @g_difex X G hyp_sbthlem1_2 p0019
  have p0063 :=
    @g_eqeltri B (syn_cdif X G) (syn_cvv) hyp_sbthlem1_5 p0062
  have p0064 :=
    @g_enrflx B p0063
  have p0065 :=
    @g_difsscompl X G
  have p0066 :=
    @g_a1i (syn_wss (syn_cdif X G) (syn_ccompl G)) (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X))) p0065
  have p0067 :=
    (by simpa [syn_cdif] using (Nominal.classEqRefl (syn_cdif X G)))
  have p0068 :=
    @g_clos1base G R (syn_cdif X (syn_crn R)) hyp_sbthlem1_3
  have p0069 :=
    @g_sscon34 (syn_cdif X (syn_crn R)) G
  have p0070 :=
    @g_mpbi (syn_wss (syn_cdif X (syn_crn R)) G) (syn_wss (syn_ccompl G) (syn_ccompl (syn_cdif X (syn_crn R)))) p0068 p0069
  have p0071 :=
    (by simpa [syn_cdif] using (Nominal.classEqRefl (syn_cdif X (syn_crn R))))
  have p0072 :=
    @g_compleqi (syn_cdif X (syn_crn R)) (syn_cin X (syn_ccompl (syn_crn R))) p0071
  have p0073 :=
    @g_iinun X (syn_ccompl (syn_crn R))
  have p0074 :=
    @g_dblcompl (syn_crn R)
  have p0075 :=
    @g_uneq2i (syn_ccompl (syn_ccompl (syn_crn R))) (syn_crn R) (syn_ccompl X) p0074
  have p0076 :=
    @g_n_3eqtri (syn_ccompl (syn_cdif X (syn_crn R))) (syn_ccompl (syn_cin X (syn_ccompl (syn_crn R)))) (syn_cun (syn_ccompl X) (syn_ccompl (syn_ccompl (syn_crn R)))) (syn_cun (syn_ccompl X) (syn_crn R)) p0072 p0073 p0075
  have p0077 :=
    @g_sseqtri (syn_ccompl G) (syn_ccompl (syn_cdif X (syn_crn R))) (syn_cun (syn_ccompl X) (syn_crn R)) p0070 p0076
  have p0078 :=
    @g_sslin (syn_ccompl G) (syn_cun (syn_ccompl X) (syn_crn R)) X
  have p0079 :=
    Nominal.mp p0077 p0078
  have p0080 :=
    @g_eqsstri (syn_cdif X G) (syn_cin X (syn_ccompl G)) (syn_cin X (syn_cun (syn_ccompl X) (syn_crn R))) p0067 p0079
  have p0081 :=
    @g_indi X (syn_ccompl X) (syn_crn R)
  have p0082 :=
    @g_incompl X
  have p0083 :=
    @g_uneq1i (syn_cin X (syn_ccompl X)) (syn_c0) (syn_cin X (syn_crn R)) p0082
  have p0084 :=
    @g_uncom (syn_c0) (syn_cin X (syn_crn R))
  have p0085 :=
    @g_un0 (syn_cin X (syn_crn R))
  have p0086 :=
    @g_eqtri (syn_cun (syn_c0) (syn_cin X (syn_crn R))) (syn_cun (syn_cin X (syn_crn R)) (syn_c0)) (syn_cin X (syn_crn R)) p0084 p0085
  have p0087 :=
    @g_n_3eqtri (syn_cin X (syn_cun (syn_ccompl X) (syn_crn R))) (syn_cun (syn_cin X (syn_ccompl X)) (syn_cin X (syn_crn R))) (syn_cun (syn_c0) (syn_cin X (syn_crn R))) (syn_cin X (syn_crn R)) p0081 p0083 p0086
  have p0088 :=
    @g_inss2 X (syn_crn R)
  have p0089 :=
    @g_eqsstri (syn_cin X (syn_cun (syn_ccompl X) (syn_crn R))) (syn_cin X (syn_crn R)) (syn_crn R) p0087 p0088
  have p0090 :=
    @g_sstri (syn_cdif X G) (syn_cin X (syn_cun (syn_ccompl X) (syn_crn R))) (syn_crn R) p0080 p0089
  have p0091 :=
    @g_jctil (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X))) (syn_wss (syn_cdif X G) (syn_ccompl G)) (syn_wss (syn_cdif X G) (syn_crn R)) p0066 p0090
  have p0092 :=
    @g_ssin (syn_cdif X G) (syn_crn R) (syn_ccompl G)
  have p0093 :=
    @g_sylib (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X))) (syn_wa (syn_wss (syn_cdif X G) (syn_crn R)) (syn_wss (syn_cdif X G) (syn_ccompl G))) (syn_wss (syn_cdif X G) (syn_cin (syn_crn R) (syn_ccompl G))) p0091 p0092
  have p0094 :=
    (by simpa [syn_cdif] using (Nominal.classEqRefl (syn_cdif (syn_crn R) G)))
  have p0095 :=
    @g_eqtri D (syn_cdif (syn_crn R) G) (syn_cin (syn_crn R) (syn_ccompl G)) hyp_sbthlem1_7 p0094
  have p0096 :=
    @g_n_3sstr4g (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X))) (syn_cdif X G) (syn_cin (syn_crn R) (syn_ccompl G)) B D p0093 hyp_sbthlem1_5 p0095
  have p0097 :=
    @g_ssdif (syn_crn R) X G
  have p0098 :=
    @g_syl (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X))) (syn_wss (syn_crn R) X) (syn_wss (syn_cdif (syn_crn R) G) (syn_cdif X G)) p0039 p0097
  have p0099 :=
    @g_n_3sstr4g (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X))) (syn_cdif (syn_crn R) G) (syn_cdif X G) D B p0098 hyp_sbthlem1_7 hyp_sbthlem1_5
  have p0100 :=
    @g_eqssd (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X))) B D p0096 p0099
  have p0101 :=
    @g_syl5breq (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X))) B B D (syn_cen) p0064 p0100
  have p0102 :=
    @g_ineq12i A (syn_cin X G) B (syn_cdif X G) hyp_sbthlem1_4 hyp_sbthlem1_5
  have p0103 :=
    @g_inindif X G
  have p0104 :=
    @g_eqtri (syn_cin A B) (syn_cin (syn_cin X G) (syn_cdif X G)) (syn_c0) p0102 p0103
  have p0105 :=
    @g_ineq12i C (syn_cin (syn_crn R) G) D (syn_cdif (syn_crn R) G) hyp_sbthlem1_6 hyp_sbthlem1_7
  have p0106 :=
    @g_inindif (syn_crn R) G
  have p0107 :=
    @g_eqtri (syn_cin C D) (syn_cin (syn_cin (syn_crn R) G) (syn_cdif (syn_crn R) G)) (syn_c0) p0105 p0106
  have p0108 :=
    @g_unen A C B D
  have p0109 :=
    @g_mpanr12 (syn_wa (syn_wbr A (syn_cen) C) (syn_wbr B (syn_cen) D)) (.classEq (syn_cin A B) (syn_c0)) (.classEq (syn_cin C D) (syn_c0)) (syn_wbr (syn_cun A B) (syn_cen) (syn_cun C D)) p0104 p0107 p0108
  have p0110 :=
    @g_syl2anc (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X))) (syn_wbr A (syn_cen) C) (syn_wbr B (syn_cen) D) (syn_wbr (syn_cun A B) (syn_cen) (syn_cun C D)) p0061 p0101 p0109
  have p0111 :=
    @g_ensym (syn_cun A B) (syn_cun C D)
  have p0112 :=
    @g_sylib (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X))) (syn_wbr (syn_cun A B) (syn_cen) (syn_cun C D)) (syn_wbr (syn_cun C D) (syn_cen) (syn_cun A B)) p0110 p0111
  have p0113 :=
    @g_uneq12i C (syn_cin (syn_crn R) G) D (syn_cdif (syn_crn R) G) hyp_sbthlem1_6 hyp_sbthlem1_7
  have p0114 :=
    @g_inundif (syn_crn R) G
  have p0115 :=
    @g_eqtri (syn_cun C D) (syn_cun (syn_cin (syn_crn R) G) (syn_cdif (syn_crn R) G)) (syn_crn R) p0113 p0114
  have p0116 :=
    @g_uneq12i A (syn_cin X G) B (syn_cdif X G) hyp_sbthlem1_4 hyp_sbthlem1_5
  have p0117 :=
    @g_inundif X G
  have p0118 :=
    @g_eqtri (syn_cun A B) (syn_cun (syn_cin X G) (syn_cdif X G)) X p0116 p0117
  have p0119 :=
    @g_n_3brtr3g (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wa (syn_wss X (syn_cdm R)) (syn_wss (syn_crn R) X))) (syn_cun C D) (syn_cun A B) (syn_crn R) X (syn_cen) p0112 p0115 p0118
  exact p0119

noncomputable def g_sbthlem2
    (B : Class) (R : Class) (V : Class) (hyp_sbthlem2_1 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_w3a (.classMem B V) (syn_wss B (syn_cdm R)) (syn_wss (syn_crn R) B))) (syn_wbr (syn_crn R) (syn_cen) B)) := by
  let proofSupport : Finset Var := B.fv ∪ R.fv ∪ V.fv
  let b : Var := freshVar proofSupport 0
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_b_not_R : b ∉ R.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_not_V : b ∉ V.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have dv_cache_0001 : b ∉ (B).fv := by
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : b ∉ ((Wff.imp (syn_wa (syn_wss B (syn_cdm R)) (syn_wss (syn_crn R) B)) (.imp (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wbr (syn_crn R) (syn_cen) B)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_B, fresh_b_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_sseq1 (.cv b) B (syn_cdm R)
  have p0001 :=
    @g_sseq2 (.cv b) B (syn_crn R)
  have p0002 :=
    @g_anbi12d (.classEq (.cv b) B) (syn_wss (.cv b) (syn_cdm R)) (syn_wss B (syn_cdm R)) (syn_wss (syn_crn R) (.cv b)) (syn_wss (syn_crn R) B) p0000 p0001
  have p0003 :=
    @g_breq2 (.cv b) B (syn_crn R) (syn_cen)
  have p0004 :=
    @g_imbi2d (.classEq (.cv b) B) (syn_wbr (syn_crn R) (syn_cen) (.cv b)) (syn_wbr (syn_crn R) (syn_cen) B) (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) p0003
  have p0005 :=
    @g_imbi12d (.classEq (.cv b) B) (syn_wa (syn_wss (.cv b) (syn_cdm R)) (syn_wss (syn_crn R) (.cv b))) (syn_wa (syn_wss B (syn_cdm R)) (syn_wss (syn_crn R) B)) (.imp (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wbr (syn_crn R) (syn_cen) (.cv b))) (.imp (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wbr (syn_crn R) (syn_cen) B)) p0002 p0004
  have p0006 :=
    @g_vex b
  have p0007 :=
    @g_eqid (syn_cclos1 (syn_cdif (.cv b) (syn_crn R)) R)
  have p0008 :=
    @g_eqid (syn_cin (.cv b) (syn_cclos1 (syn_cdif (.cv b) (syn_crn R)) R))
  have p0009 :=
    @g_eqid (syn_cdif (.cv b) (syn_cclos1 (syn_cdif (.cv b) (syn_crn R)) R))
  have p0010 :=
    @g_eqid (syn_cin (syn_crn R) (syn_cclos1 (syn_cdif (.cv b) (syn_crn R)) R))
  have p0011 :=
    @g_eqid (syn_cdif (syn_crn R) (syn_cclos1 (syn_cdif (.cv b) (syn_crn R)) R))
  have p0012 :=
    @g_sbthlem1 (syn_cin (.cv b) (syn_cclos1 (syn_cdif (.cv b) (syn_crn R)) R)) (syn_cdif (.cv b) (syn_cclos1 (syn_cdif (.cv b) (syn_crn R)) R)) (syn_cin (syn_crn R) (syn_cclos1 (syn_cdif (.cv b) (syn_crn R)) R)) (syn_cdif (syn_crn R) (syn_cclos1 (syn_cdif (.cv b) (syn_crn R)) R)) R (syn_cclos1 (syn_cdif (.cv b) (syn_crn R)) R) (.cv b) hyp_sbthlem2_1 p0006 p0007 p0008 p0009 p0010 p0011
  have p0013 :=
    @g_expcom (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wa (syn_wss (.cv b) (syn_cdm R)) (syn_wss (syn_crn R) (.cv b))) (syn_wbr (syn_crn R) (syn_cen) (.cv b)) p0012
  have p0014 :=
    @g_vtoclg (.imp (syn_wa (syn_wss (.cv b) (syn_cdm R)) (syn_wss (syn_crn R) (.cv b))) (.imp (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wbr (syn_crn R) (syn_cen) (.cv b)))) (.imp (syn_wa (syn_wss B (syn_cdm R)) (syn_wss (syn_crn R) B)) (.imp (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wbr (syn_crn R) (syn_cen) B))) b B V dv_cache_0001 dv_cache_0002 p0005 p0013
  have p0015 :=
    @g_n_3impib (.classMem B V) (syn_wss B (syn_cdm R)) (syn_wss (syn_crn R) B) (.imp (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wbr (syn_crn R) (syn_cen) B)) p0014
  have p0016 :=
    @g_impcom (syn_w3a (.classMem B V) (syn_wss B (syn_cdm R)) (syn_wss (syn_crn R) B)) (syn_wa (syn_wfun R) (syn_wfun (syn_ccnv R))) (syn_wbr (syn_crn R) (syn_cen) B) p0015
  exact p0016

noncomputable def g_sbthlem3
    (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (syn_wbr A (syn_cen) C) (syn_wss C B)) (syn_wa (syn_wbr B (syn_cen) D) (syn_wss D A))) (syn_wbr A (syn_cen) B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  let r : Var := freshVar proofSupport 0
  let s : Var := freshVar proofSupport 1
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_r_not_B : r ∉ B.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_r_not_C : r ∉ C.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_not_D : r ∉ D.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_s : s ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_s_not_A : s ∉ A.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_s_not_B : s ∉ B.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_s_not_C : s ∉ C.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_s_not_D : s ∉ D.fv := by
    intro h
    exact fresh_s (Finset.mem_union_right _ (h))
  have fresh_r_ne_s : r ≠ s := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_s_ne_r : s ≠ r :=
    Ne.symm fresh_r_ne_s
  have dv_cache_0001 : r ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : r ∉ (C).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : s ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : s ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : s ∉ ((syn_wf1o (.cv r) A C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_A, fresh_s_not_C, fresh_s_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : r ∉ ((syn_wf1o (.cv s) B D)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_B, fresh_r_not_D, fresh_r_ne_s, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : r ∉ ((Wff.imp (syn_wa (syn_wss C B) (syn_wss D A)) (syn_wbr A (syn_cen) D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_C, fresh_r_not_B, fresh_r_not_D, fresh_r_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : s ∉ ((Wff.imp (syn_wa (syn_wss C B) (syn_wss D A)) (syn_wbr A (syn_cen) D))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_C, fresh_s_not_B, fresh_s_not_D, fresh_s_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_bren A C r dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_bren B D s dv_cache_0003 dv_cache_0004
  have p0002 :=
    @g_anbi12i (syn_wbr A (syn_cen) C) (syn_wex r (syn_wf1o (.cv r) A C)) (syn_wbr B (syn_cen) D) (syn_wex s (syn_wf1o (.cv s) B D)) p0000 p0001
  have p0003 :=
    @g_eeanv (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D) r s dv_cache_0005 dv_cache_0006
  have p0004 :=
    @g_bitr4i (syn_wa (syn_wbr A (syn_cen) C) (syn_wbr B (syn_cen) D)) (syn_wa (syn_wex r (syn_wf1o (.cv r) A C)) (syn_wex s (syn_wf1o (.cv s) B D))) (syn_wex r (syn_wex s (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D)))) p0002 p0003
  have p0005 :=
    @g_simprl (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D)) (syn_wss C B) (syn_wss D A)
  have p0006 :=
    @g_f1ofo A C (.cv r)
  have p0007 :=
    @g_forn A C (.cv r)
  have p0008 :=
    @g_syl (syn_wf1o (.cv r) A C) (syn_wfo (.cv r) A C) (.classEq (syn_crn (.cv r)) C) p0006 p0007
  have p0009 :=
    @g_ad2antrr (syn_wf1o (.cv r) A C) (.classEq (syn_crn (.cv r)) C) (syn_wf1o (.cv s) B D) (syn_wa (syn_wss C B) (syn_wss D A)) p0008
  have p0010 :=
    @g_f1odm B D (.cv s)
  have p0011 :=
    @g_ad2antlr (syn_wf1o (.cv s) B D) (.classEq (syn_cdm (.cv s)) B) (syn_wf1o (.cv r) A C) (syn_wa (syn_wss C B) (syn_wss D A)) p0010
  have p0012 :=
    @g_n_3sstr4d (syn_wa (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D)) (syn_wa (syn_wss C B) (syn_wss D A))) C B (syn_crn (.cv r)) (syn_cdm (.cv s)) p0005 p0009 p0011
  have p0013 :=
    @g_dmcosseq (.cv s) (.cv r)
  have p0014 :=
    @g_syl (syn_wa (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D)) (syn_wa (syn_wss C B) (syn_wss D A))) (syn_wss (syn_crn (.cv r)) (syn_cdm (.cv s))) (.classEq (syn_cdm (syn_ccom (.cv s) (.cv r))) (syn_cdm (.cv r))) p0012 p0013
  have p0015 :=
    @g_f1odm A C (.cv r)
  have p0016 :=
    @g_ad2antrr (syn_wf1o (.cv r) A C) (.classEq (syn_cdm (.cv r)) A) (syn_wf1o (.cv s) B D) (syn_wa (syn_wss C B) (syn_wss D A)) p0015
  have p0017 :=
    @g_eqtrd (syn_wa (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D)) (syn_wa (syn_wss C B) (syn_wss D A))) (syn_cdm (syn_ccom (.cv s) (.cv r))) (syn_cdm (.cv r)) A p0014 p0016
  have p0018 :=
    @g_f1ofun B D (.cv s)
  have p0019 :=
    @g_f1ofun A C (.cv r)
  have p0020 :=
    @g_funco (.cv s) (.cv r)
  have p0021 :=
    @g_syl2anr (syn_wf1o (.cv s) B D) (syn_wfun (.cv s)) (syn_wfun (.cv r)) (syn_wfun (syn_ccom (.cv s) (.cv r))) (syn_wf1o (.cv r) A C) p0018 p0019 p0020
  have p0022 :=
    @g_dff1o2 A C (.cv r)
  have p0023 :=
    @g_simp2bi (syn_wf1o (.cv r) A C) (syn_wfn (.cv r) A) (syn_wfun (syn_ccnv (.cv r))) (.classEq (syn_crn (.cv r)) C) p0022
  have p0024 :=
    @g_dff1o2 B D (.cv s)
  have p0025 :=
    @g_simp2bi (syn_wf1o (.cv s) B D) (syn_wfn (.cv s) B) (syn_wfun (syn_ccnv (.cv s))) (.classEq (syn_crn (.cv s)) D) p0024
  have p0026 :=
    @g_funco (syn_ccnv (.cv r)) (syn_ccnv (.cv s))
  have p0027 :=
    @g_syl2an (syn_wf1o (.cv r) A C) (syn_wfun (syn_ccnv (.cv r))) (syn_wfun (syn_ccnv (.cv s))) (syn_wfun (syn_ccom (syn_ccnv (.cv r)) (syn_ccnv (.cv s)))) (syn_wf1o (.cv s) B D) p0023 p0025 p0026
  have p0028 :=
    @g_cnvco (.cv s) (.cv r)
  have p0029 :=
    @g_funeqi (syn_ccnv (syn_ccom (.cv s) (.cv r))) (syn_ccom (syn_ccnv (.cv r)) (syn_ccnv (.cv s))) p0028
  have p0030 :=
    @g_sylibr (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D)) (syn_wfun (syn_ccom (syn_ccnv (.cv r)) (syn_ccnv (.cv s)))) (syn_wfun (syn_ccnv (syn_ccom (.cv s) (.cv r)))) p0027 p0029
  have p0031 :=
    @g_jca (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D)) (syn_wfun (syn_ccom (.cv s) (.cv r))) (syn_wfun (syn_ccnv (syn_ccom (.cv s) (.cv r)))) p0021 p0030
  have p0032 :=
    @g_adantr (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D)) (syn_wa (syn_wfun (syn_ccom (.cv s) (.cv r))) (syn_wfun (syn_ccnv (syn_ccom (.cv s) (.cv r))))) (syn_wa (syn_wss C B) (syn_wss D A)) p0031
  have p0033 :=
    @g_dff1o2 (syn_cdm (syn_ccom (.cv s) (.cv r))) (syn_crn (syn_ccom (.cv s) (.cv r))) (syn_ccom (.cv s) (.cv r))
  have p0034 :=
    @g_funfn (syn_ccom (.cv s) (.cv r))
  have p0035 :=
    @g_anbi1i (syn_wfun (syn_ccom (.cv s) (.cv r))) (syn_wfn (syn_ccom (.cv s) (.cv r)) (syn_cdm (syn_ccom (.cv s) (.cv r)))) (syn_wfun (syn_ccnv (syn_ccom (.cv s) (.cv r)))) p0034
  have p0036 :=
    @g_eqid (syn_crn (syn_ccom (.cv s) (.cv r)))
  have p0037 :=
    (by simpa [syn_wb, syn_w3a] using (Nominal.biimpRefl (syn_w3a (syn_wfn (syn_ccom (.cv s) (.cv r)) (syn_cdm (syn_ccom (.cv s) (.cv r)))) (syn_wfun (syn_ccnv (syn_ccom (.cv s) (.cv r)))) (.classEq (syn_crn (syn_ccom (.cv s) (.cv r))) (syn_crn (syn_ccom (.cv s) (.cv r)))))))
  have p0038 :=
    @g_mpbiran2 (syn_w3a (syn_wfn (syn_ccom (.cv s) (.cv r)) (syn_cdm (syn_ccom (.cv s) (.cv r)))) (syn_wfun (syn_ccnv (syn_ccom (.cv s) (.cv r)))) (.classEq (syn_crn (syn_ccom (.cv s) (.cv r))) (syn_crn (syn_ccom (.cv s) (.cv r))))) (syn_wa (syn_wfn (syn_ccom (.cv s) (.cv r)) (syn_cdm (syn_ccom (.cv s) (.cv r)))) (syn_wfun (syn_ccnv (syn_ccom (.cv s) (.cv r))))) (.classEq (syn_crn (syn_ccom (.cv s) (.cv r))) (syn_crn (syn_ccom (.cv s) (.cv r)))) p0036 p0037
  have p0039 :=
    @g_bitr4i (syn_wa (syn_wfun (syn_ccom (.cv s) (.cv r))) (syn_wfun (syn_ccnv (syn_ccom (.cv s) (.cv r))))) (syn_wa (syn_wfn (syn_ccom (.cv s) (.cv r)) (syn_cdm (syn_ccom (.cv s) (.cv r)))) (syn_wfun (syn_ccnv (syn_ccom (.cv s) (.cv r))))) (syn_w3a (syn_wfn (syn_ccom (.cv s) (.cv r)) (syn_cdm (syn_ccom (.cv s) (.cv r)))) (syn_wfun (syn_ccnv (syn_ccom (.cv s) (.cv r)))) (.classEq (syn_crn (syn_ccom (.cv s) (.cv r))) (syn_crn (syn_ccom (.cv s) (.cv r))))) p0035 p0038
  have p0040 :=
    @g_bitr4i (syn_wf1o (syn_ccom (.cv s) (.cv r)) (syn_cdm (syn_ccom (.cv s) (.cv r))) (syn_crn (syn_ccom (.cv s) (.cv r)))) (syn_w3a (syn_wfn (syn_ccom (.cv s) (.cv r)) (syn_cdm (syn_ccom (.cv s) (.cv r)))) (syn_wfun (syn_ccnv (syn_ccom (.cv s) (.cv r)))) (.classEq (syn_crn (syn_ccom (.cv s) (.cv r))) (syn_crn (syn_ccom (.cv s) (.cv r))))) (syn_wa (syn_wfun (syn_ccom (.cv s) (.cv r))) (syn_wfun (syn_ccnv (syn_ccom (.cv s) (.cv r))))) p0033 p0039
  have p0041 :=
    @g_sylibr (syn_wa (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D)) (syn_wa (syn_wss C B) (syn_wss D A))) (syn_wa (syn_wfun (syn_ccom (.cv s) (.cv r))) (syn_wfun (syn_ccnv (syn_ccom (.cv s) (.cv r))))) (syn_wf1o (syn_ccom (.cv s) (.cv r)) (syn_cdm (syn_ccom (.cv s) (.cv r))) (syn_crn (syn_ccom (.cv s) (.cv r)))) p0032 p0040
  have p0042 :=
    @g_vex s
  have p0043 :=
    @g_vex r
  have p0044 :=
    @g_coex (.cv s) (.cv r) p0042 p0043
  have p0045 :=
    @g_f1oen (syn_cdm (syn_ccom (.cv s) (.cv r))) (syn_crn (syn_ccom (.cv s) (.cv r))) (syn_ccom (.cv s) (.cv r)) p0044
  have p0046 :=
    @g_syl (syn_wa (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D)) (syn_wa (syn_wss C B) (syn_wss D A))) (syn_wf1o (syn_ccom (.cv s) (.cv r)) (syn_cdm (syn_ccom (.cv s) (.cv r))) (syn_crn (syn_ccom (.cv s) (.cv r)))) (syn_wbr (syn_cdm (syn_ccom (.cv s) (.cv r))) (syn_cen) (syn_crn (syn_ccom (.cv s) (.cv r)))) p0041 p0045
  have p0047 :=
    @g_eqbrtrrd (syn_wa (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D)) (syn_wa (syn_wss C B) (syn_wss D A))) (syn_cdm (syn_ccom (.cv s) (.cv r))) A (syn_crn (syn_ccom (.cv s) (.cv r))) (syn_cen) p0017 p0046
  have p0048 :=
    @g_f1ofo B D (.cv s)
  have p0049 :=
    @g_forn B D (.cv s)
  have p0050 :=
    @g_syl (syn_wf1o (.cv s) B D) (syn_wfo (.cv s) B D) (.classEq (syn_crn (.cv s)) D) p0048 p0049
  have p0051 :=
    @g_rnex (.cv s) p0042
  have p0052 :=
    @g_syl6eqelr (syn_wf1o (.cv s) B D) D (syn_crn (.cv s)) (syn_cvv) p0050 p0051
  have p0053 :=
    @g_ad2antlr (syn_wf1o (.cv s) B D) (.classMem D (syn_cvv)) (syn_wf1o (.cv r) A C) (syn_wa (syn_wss C B) (syn_wss D A)) p0052
  have p0054 :=
    @g_simprr (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D)) (syn_wss C B) (syn_wss D A)
  have p0055 :=
    @g_sseqtr4d (syn_wa (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D)) (syn_wa (syn_wss C B) (syn_wss D A))) D A (syn_cdm (syn_ccom (.cv s) (.cv r))) p0054 p0017
  have p0056 :=
    @g_rncoss (.cv s) (.cv r)
  have p0057 :=
    @g_ad2antlr (syn_wf1o (.cv s) B D) (.classEq (syn_crn (.cv s)) D) (syn_wf1o (.cv r) A C) (syn_wa (syn_wss C B) (syn_wss D A)) p0050
  have p0058 :=
    @g_syl5sseq (syn_wa (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D)) (syn_wa (syn_wss C B) (syn_wss D A))) (syn_crn (.cv s)) (syn_crn (syn_ccom (.cv s) (.cv r))) D p0056 p0057
  have p0059 :=
    @g_sbthlem2 D (syn_ccom (.cv s) (.cv r)) (syn_cvv) p0044
  have p0060 :=
    @g_syl13anc (syn_wa (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D)) (syn_wa (syn_wss C B) (syn_wss D A))) (syn_wa (syn_wfun (syn_ccom (.cv s) (.cv r))) (syn_wfun (syn_ccnv (syn_ccom (.cv s) (.cv r))))) (.classMem D (syn_cvv)) (syn_wss D (syn_cdm (syn_ccom (.cv s) (.cv r)))) (syn_wss (syn_crn (syn_ccom (.cv s) (.cv r))) D) (syn_wbr (syn_crn (syn_ccom (.cv s) (.cv r))) (syn_cen) D) p0032 p0053 p0055 p0058 p0059
  have p0061 :=
    @g_entr A (syn_crn (syn_ccom (.cv s) (.cv r))) D
  have p0062 :=
    @g_syl2anc (syn_wa (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D)) (syn_wa (syn_wss C B) (syn_wss D A))) (syn_wbr A (syn_cen) (syn_crn (syn_ccom (.cv s) (.cv r)))) (syn_wbr (syn_crn (syn_ccom (.cv s) (.cv r))) (syn_cen) D) (syn_wbr A (syn_cen) D) p0047 p0060 p0061
  have p0063 :=
    @g_ex (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D)) (syn_wa (syn_wss C B) (syn_wss D A)) (syn_wbr A (syn_cen) D) p0062
  have p0064 :=
    @g_exlimivv (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D)) (.imp (syn_wa (syn_wss C B) (syn_wss D A)) (syn_wbr A (syn_cen) D)) r s dv_cache_0007 dv_cache_0008 p0063
  have p0065 :=
    @g_sylbi (syn_wa (syn_wbr A (syn_cen) C) (syn_wbr B (syn_cen) D)) (syn_wex r (syn_wex s (syn_wa (syn_wf1o (.cv r) A C) (syn_wf1o (.cv s) B D)))) (.imp (syn_wa (syn_wss C B) (syn_wss D A)) (syn_wbr A (syn_cen) D)) p0004 p0064
  have p0066 :=
    @g_imp (syn_wa (syn_wbr A (syn_cen) C) (syn_wbr B (syn_cen) D)) (syn_wa (syn_wss C B) (syn_wss D A)) (syn_wbr A (syn_cen) D) p0065
  have p0067 :=
    @g_an4s (syn_wbr A (syn_cen) C) (syn_wbr B (syn_cen) D) (syn_wss C B) (syn_wss D A) (syn_wbr A (syn_cen) D) p0066
  have p0068 :=
    @g_ensymi B D
  have p0069 :=
    @g_ad2antrl (syn_wbr B (syn_cen) D) (syn_wbr D (syn_cen) B) (syn_wa (syn_wbr A (syn_cen) C) (syn_wss C B)) (syn_wss D A) p0068
  have p0070 :=
    @g_entr A D B
  have p0071 :=
    @g_syl2anc (syn_wa (syn_wa (syn_wbr A (syn_cen) C) (syn_wss C B)) (syn_wa (syn_wbr B (syn_cen) D) (syn_wss D A))) (syn_wbr A (syn_cen) D) (syn_wbr D (syn_cen) B) (syn_wbr A (syn_cen) B) p0067 p0069 p0070
  exact p0071

#print axioms g_sbthlem3

end NFChoice.DirectNominalPrf.WPPReplay
