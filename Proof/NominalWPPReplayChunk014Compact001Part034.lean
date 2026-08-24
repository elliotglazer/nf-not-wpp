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
import NominalWPPReplayChunk014Compact001Part033

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

noncomputable def g_hwgenval
    (R : Class) (f : Var) (hyp_hwgenval_1 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) R)) (syn_cop (syn_cop R (syn_cdm (.cv f))) (syn_cop (syn_ccom (syn_ccom (.cv f) R) (syn_ccnv (.cv f))) (syn_crn (.cv f))))) := by
  let proofSupport : Finset Var := R.fv ∪ ({f} : Finset Var)
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_ne_f : x ≠ f := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_f_ne_x : f ≠ x :=
    Ne.symm fresh_x_ne_f
  have dv_cache_0001 : x ∉ ((syn_cvv)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    (by simpa [syn_chwgen] using (Nominal.classEqRefl (syn_chwgen)))
  have p0001 :=
    @g_fveq1i (syn_cop (.cv f) R) (syn_chwgen) (syn_ctxp (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))) p0000
  have p0002 :=
    @g_eqid (syn_cfv (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cop (.cv f) R))
  have p0003 :=
    @g_n_2ndfo
  have p0004 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_vex x
  have p0007 :=
    @g_dmex (.cv x) p0006
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_domfn x
  have p0009 :=
    @g_fnmpti x (syn_cvv) (syn_cdm (.cv x)) (syn_cdomfn) dv_cache_0001 p0007 p0008
  have p0010 :=
    @g_n_1stfo
  have p0011 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0012 :=
    Nominal.mp p0010 p0011
  have p0013 :=
    @g_ssv (syn_crn (syn_c1st))
  have p0014 :=
    @g_n_3pm3_2i (syn_wfn (syn_cdomfn) (syn_cvv)) (syn_wfn (syn_c1st) (syn_cvv)) (syn_wss (syn_crn (syn_c1st)) (syn_cvv)) p0009 p0012 p0013
  have p0015 :=
    @g_fnco (syn_cvv) (syn_cvv) (syn_cdomfn) (syn_c1st)
  have p0016 :=
    Nominal.mp p0014 p0015
  have p0017 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (syn_wfn (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cvv)) p0005 p0016
  have p0018 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))
  have p0019 :=
    Nominal.mp p0017 p0018
  have p0020 :=
    @g_inidm (syn_cvv)
  have p0021 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) p0020
  have p0022 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cvv)) p0019 p0021
  have p0023 :=
    @g_vex f
  have p0024 :=
    @g_opex (.cv f) R p0023 hyp_hwgenval_1
  have p0025 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cvv)) (.classMem (syn_cop (.cv f) R) (syn_cvv)) p0022 p0024
  have p0026 :=
    @g_fnbrfvb (syn_cvv) (syn_cop (.cv f) R) (syn_cfv (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cop (.cv f) R)) (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
  have p0027 :=
    Nominal.mp p0025 p0026
  have p0028 :=
    @g_mpbi (.classEq (syn_cfv (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cop (.cv f) R)) (syn_cfv (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cop (.cv f) R))) (syn_wbr (syn_cop (.cv f) R) (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cfv (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cop (.cv f) R))) p0002 p0027
  have p0029 :=
    @g_eqid (syn_cfv (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cop (.cv f) R))
  have p0030 :=
    @g_hwtrnfn
  have p0031 :=
    @g_vex x
  have p0032 :=
    @g_rnex (.cv x) p0031
  have p0033 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ranfn x
  have p0034 :=
    @g_fnmpti x (syn_cvv) (syn_crn (.cv x)) (syn_cranfn) dv_cache_0001 p0032 p0033
  have p0035 :=
    @g_n_1stfo
  have p0036 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0037 :=
    Nominal.mp p0035 p0036
  have p0038 :=
    @g_ssv (syn_crn (syn_c1st))
  have p0039 :=
    @g_n_3pm3_2i (syn_wfn (syn_cranfn) (syn_cvv)) (syn_wfn (syn_c1st) (syn_cvv)) (syn_wss (syn_crn (syn_c1st)) (syn_cvv)) p0034 p0037 p0038
  have p0040 :=
    @g_fnco (syn_cvv) (syn_cvv) (syn_cranfn) (syn_c1st)
  have p0041 :=
    Nominal.mp p0039 p0040
  have p0042 :=
    @g_pm3_2i (syn_wfn (syn_chwtrn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cvv)) p0030 p0041
  have p0043 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))
  have p0044 :=
    Nominal.mp p0042 p0043
  have p0045 :=
    @g_inidm (syn_cvv)
  have p0046 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) p0045
  have p0047 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cvv)) p0044 p0046
  have p0048 :=
    @g_vex f
  have p0049 :=
    @g_opex (.cv f) R p0048 hyp_hwgenval_1
  have p0050 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cvv)) (.classMem (syn_cop (.cv f) R) (syn_cvv)) p0047 p0049
  have p0051 :=
    @g_fnbrfvb (syn_cvv) (syn_cop (.cv f) R) (syn_cfv (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cop (.cv f) R)) (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))
  have p0052 :=
    Nominal.mp p0050 p0051
  have p0053 :=
    @g_mpbi (.classEq (syn_cfv (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cop (.cv f) R)) (syn_cfv (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cop (.cv f) R))) (syn_wbr (syn_cop (.cv f) R) (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cfv (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cop (.cv f) R))) p0029 p0052
  have p0054 :=
    @g_pm3_2i (syn_wbr (syn_cop (.cv f) R) (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cfv (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cop (.cv f) R))) (syn_wbr (syn_cop (.cv f) R) (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cfv (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cop (.cv f) R))) p0028 p0053
  have p0055 :=
    @g_trtxp (syn_cop (.cv f) R) (syn_cfv (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cop (.cv f) R)) (syn_cfv (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cop (.cv f) R)) (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))
  have p0056 :=
    @g_mpbir (syn_wbr (syn_cop (.cv f) R) (syn_ctxp (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))) (syn_cop (syn_cfv (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cop (.cv f) R)) (syn_cfv (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cop (.cv f) R)))) (syn_wa (syn_wbr (syn_cop (.cv f) R) (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cfv (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cop (.cv f) R))) (syn_wbr (syn_cop (.cv f) R) (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cfv (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cop (.cv f) R)))) p0054 p0055
  have p0057 :=
    @g_n_2ndfo
  have p0058 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0059 :=
    Nominal.mp p0057 p0058
  have p0060 :=
    @g_vex x
  have p0061 :=
    @g_dmex (.cv x) p0060
  have p0062 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_domfn x
  have p0063 :=
    @g_fnmpti x (syn_cvv) (syn_cdm (.cv x)) (syn_cdomfn) dv_cache_0001 p0061 p0062
  have p0064 :=
    @g_n_1stfo
  have p0065 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0066 :=
    Nominal.mp p0064 p0065
  have p0067 :=
    @g_ssv (syn_crn (syn_c1st))
  have p0068 :=
    @g_n_3pm3_2i (syn_wfn (syn_cdomfn) (syn_cvv)) (syn_wfn (syn_c1st) (syn_cvv)) (syn_wss (syn_crn (syn_c1st)) (syn_cvv)) p0063 p0066 p0067
  have p0069 :=
    @g_fnco (syn_cvv) (syn_cvv) (syn_cdomfn) (syn_c1st)
  have p0070 :=
    Nominal.mp p0068 p0069
  have p0071 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (syn_wfn (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cvv)) p0059 p0070
  have p0072 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))
  have p0073 :=
    Nominal.mp p0071 p0072
  have p0074 :=
    @g_inidm (syn_cvv)
  have p0075 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) p0074
  have p0076 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cvv)) p0073 p0075
  have p0077 :=
    @g_hwtrnfn
  have p0078 :=
    @g_vex x
  have p0079 :=
    @g_rnex (.cv x) p0078
  have p0080 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ranfn x
  have p0081 :=
    @g_fnmpti x (syn_cvv) (syn_crn (.cv x)) (syn_cranfn) dv_cache_0001 p0079 p0080
  have p0082 :=
    @g_n_1stfo
  have p0083 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0084 :=
    Nominal.mp p0082 p0083
  have p0085 :=
    @g_ssv (syn_crn (syn_c1st))
  have p0086 :=
    @g_n_3pm3_2i (syn_wfn (syn_cranfn) (syn_cvv)) (syn_wfn (syn_c1st) (syn_cvv)) (syn_wss (syn_crn (syn_c1st)) (syn_cvv)) p0081 p0084 p0085
  have p0087 :=
    @g_fnco (syn_cvv) (syn_cvv) (syn_cranfn) (syn_c1st)
  have p0088 :=
    Nominal.mp p0086 p0087
  have p0089 :=
    @g_pm3_2i (syn_wfn (syn_chwtrn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cvv)) p0077 p0088
  have p0090 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))
  have p0091 :=
    Nominal.mp p0089 p0090
  have p0092 :=
    @g_inidm (syn_cvv)
  have p0093 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) p0092
  have p0094 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cvv)) p0091 p0093
  have p0095 :=
    @g_pm3_2i (syn_wfn (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cvv)) (syn_wfn (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cvv)) p0076 p0094
  have p0096 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))
  have p0097 :=
    Nominal.mp p0095 p0096
  have p0098 :=
    @g_inidm (syn_cvv)
  have p0099 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))) p0098
  have p0100 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))) (syn_cvv)) p0097 p0099
  have p0101 :=
    @g_fnfun (syn_cvv) (syn_ctxp (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))))
  have p0102 :=
    Nominal.mp p0100 p0101
  have p0103 :=
    @g_funbrfv (syn_cop (.cv f) R) (syn_cop (syn_cfv (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cop (.cv f) R)) (syn_cfv (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cop (.cv f) R))) (syn_ctxp (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))))
  have p0104 :=
    Nominal.mp p0102 p0103
  have p0105 :=
    Nominal.mp p0056 p0104
  have p0106 :=
    @g_eqid (syn_cfv (syn_c2nd) (syn_cop (.cv f) R))
  have p0107 :=
    @g_n_2ndfo
  have p0108 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0109 :=
    Nominal.mp p0107 p0108
  have p0110 :=
    @g_vex f
  have p0111 :=
    @g_opex (.cv f) R p0110 hyp_hwgenval_1
  have p0112 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (.classMem (syn_cop (.cv f) R) (syn_cvv)) p0109 p0111
  have p0113 :=
    @g_fnbrfvb (syn_cvv) (syn_cop (.cv f) R) (syn_cfv (syn_c2nd) (syn_cop (.cv f) R)) (syn_c2nd)
  have p0114 :=
    Nominal.mp p0112 p0113
  have p0115 :=
    @g_mpbi (.classEq (syn_cfv (syn_c2nd) (syn_cop (.cv f) R)) (syn_cfv (syn_c2nd) (syn_cop (.cv f) R))) (syn_wbr (syn_cop (.cv f) R) (syn_c2nd) (syn_cfv (syn_c2nd) (syn_cop (.cv f) R))) p0106 p0114
  have p0116 :=
    @g_eqid (syn_cfv (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cop (.cv f) R))
  have p0117 :=
    @g_vex x
  have p0118 :=
    @g_dmex (.cv x) p0117
  have p0119 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_domfn x
  have p0120 :=
    @g_fnmpti x (syn_cvv) (syn_cdm (.cv x)) (syn_cdomfn) dv_cache_0001 p0118 p0119
  have p0121 :=
    @g_n_1stfo
  have p0122 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0123 :=
    Nominal.mp p0121 p0122
  have p0124 :=
    @g_ssv (syn_crn (syn_c1st))
  have p0125 :=
    @g_n_3pm3_2i (syn_wfn (syn_cdomfn) (syn_cvv)) (syn_wfn (syn_c1st) (syn_cvv)) (syn_wss (syn_crn (syn_c1st)) (syn_cvv)) p0120 p0123 p0124
  have p0126 :=
    @g_fnco (syn_cvv) (syn_cvv) (syn_cdomfn) (syn_c1st)
  have p0127 :=
    Nominal.mp p0125 p0126
  have p0128 :=
    @g_vex f
  have p0129 :=
    @g_opex (.cv f) R p0128 hyp_hwgenval_1
  have p0130 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cvv)) (.classMem (syn_cop (.cv f) R) (syn_cvv)) p0127 p0129
  have p0131 :=
    @g_fnbrfvb (syn_cvv) (syn_cop (.cv f) R) (syn_cfv (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cop (.cv f) R)) (syn_ccom (syn_cdomfn) (syn_c1st))
  have p0132 :=
    Nominal.mp p0130 p0131
  have p0133 :=
    @g_mpbi (.classEq (syn_cfv (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cop (.cv f) R)) (syn_cfv (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cop (.cv f) R))) (syn_wbr (syn_cop (.cv f) R) (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cfv (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cop (.cv f) R))) p0116 p0132
  have p0134 :=
    @g_pm3_2i (syn_wbr (syn_cop (.cv f) R) (syn_c2nd) (syn_cfv (syn_c2nd) (syn_cop (.cv f) R))) (syn_wbr (syn_cop (.cv f) R) (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cfv (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cop (.cv f) R))) p0115 p0133
  have p0135 :=
    @g_trtxp (syn_cop (.cv f) R) (syn_cfv (syn_c2nd) (syn_cop (.cv f) R)) (syn_cfv (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cop (.cv f) R)) (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))
  have p0136 :=
    @g_mpbir (syn_wbr (syn_cop (.cv f) R) (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cop (syn_cfv (syn_c2nd) (syn_cop (.cv f) R)) (syn_cfv (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cop (.cv f) R)))) (syn_wa (syn_wbr (syn_cop (.cv f) R) (syn_c2nd) (syn_cfv (syn_c2nd) (syn_cop (.cv f) R))) (syn_wbr (syn_cop (.cv f) R) (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cfv (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cop (.cv f) R)))) p0134 p0135
  have p0137 :=
    @g_n_2ndfo
  have p0138 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0139 :=
    Nominal.mp p0137 p0138
  have p0140 :=
    @g_vex x
  have p0141 :=
    @g_dmex (.cv x) p0140
  have p0142 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_domfn x
  have p0143 :=
    @g_fnmpti x (syn_cvv) (syn_cdm (.cv x)) (syn_cdomfn) dv_cache_0001 p0141 p0142
  have p0144 :=
    @g_n_1stfo
  have p0145 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0146 :=
    Nominal.mp p0144 p0145
  have p0147 :=
    @g_ssv (syn_crn (syn_c1st))
  have p0148 :=
    @g_n_3pm3_2i (syn_wfn (syn_cdomfn) (syn_cvv)) (syn_wfn (syn_c1st) (syn_cvv)) (syn_wss (syn_crn (syn_c1st)) (syn_cvv)) p0143 p0146 p0147
  have p0149 :=
    @g_fnco (syn_cvv) (syn_cvv) (syn_cdomfn) (syn_c1st)
  have p0150 :=
    Nominal.mp p0148 p0149
  have p0151 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (syn_wfn (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cvv)) p0139 p0150
  have p0152 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))
  have p0153 :=
    Nominal.mp p0151 p0152
  have p0154 :=
    @g_inidm (syn_cvv)
  have p0155 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) p0154
  have p0156 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cvv)) p0153 p0155
  have p0157 :=
    @g_fnfun (syn_cvv) (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
  have p0158 :=
    Nominal.mp p0156 p0157
  have p0159 :=
    @g_funbrfv (syn_cop (.cv f) R) (syn_cop (syn_cfv (syn_c2nd) (syn_cop (.cv f) R)) (syn_cfv (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cop (.cv f) R))) (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st)))
  have p0160 :=
    Nominal.mp p0158 p0159
  have p0161 :=
    Nominal.mp p0136 p0160
  have p0162 :=
    @g_vex f
  have p0163 :=
    @g_opfv2nd (.cv f) R p0162 hyp_hwgenval_1
  have p0164 :=
    @g_n_1stfo
  have p0165 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0166 :=
    Nominal.mp p0164 p0165
  have p0167 :=
    @g_vex f
  have p0168 :=
    @g_opex (.cv f) R p0167 hyp_hwgenval_1
  have p0169 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (.classMem (syn_cop (.cv f) R) (syn_cvv)) p0166 p0168
  have p0170 :=
    @g_fvco2 (syn_cvv) (syn_cop (.cv f) R) (syn_cdomfn) (syn_c1st)
  have p0171 :=
    Nominal.mp p0169 p0170
  have p0172 :=
    @g_vex f
  have p0173 :=
    @g_opfv1st (.cv f) R p0172 hyp_hwgenval_1
  have p0174 :=
    @g_fveq2i (syn_cfv (syn_c1st) (syn_cop (.cv f) R)) (.cv f) (syn_cdomfn) p0173
  have p0175 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cop (.cv f) R)) (syn_cfv (syn_cdomfn) (syn_cfv (syn_c1st) (syn_cop (.cv f) R))) (syn_cfv (syn_cdomfn) (.cv f)) p0171 p0174
  have p0176 :=
    @g_vex f
  have p0177 :=
    @g_fvdomfn (.cv f) (syn_cvv)
  have p0178 :=
    Nominal.mp p0176 p0177
  have p0179 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cop (.cv f) R)) (syn_cfv (syn_cdomfn) (.cv f)) (syn_cdm (.cv f)) p0175 p0178
  have p0180 :=
    @g_opeq12i (syn_cfv (syn_c2nd) (syn_cop (.cv f) R)) R (syn_cfv (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cop (.cv f) R)) (syn_cdm (.cv f)) p0163 p0179
  have p0181 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cop (.cv f) R)) (syn_cop (syn_cfv (syn_c2nd) (syn_cop (.cv f) R)) (syn_cfv (syn_ccom (syn_cdomfn) (syn_c1st)) (syn_cop (.cv f) R))) (syn_cop R (syn_cdm (.cv f))) p0161 p0180
  have p0182 :=
    @g_eqid (syn_cfv (syn_chwtrn) (syn_cop (.cv f) R))
  have p0183 :=
    @g_hwtrnfn
  have p0184 :=
    @g_vex f
  have p0185 :=
    @g_opex (.cv f) R p0184 hyp_hwgenval_1
  have p0186 :=
    @g_pm3_2i (syn_wfn (syn_chwtrn) (syn_cvv)) (.classMem (syn_cop (.cv f) R) (syn_cvv)) p0183 p0185
  have p0187 :=
    @g_fnbrfvb (syn_cvv) (syn_cop (.cv f) R) (syn_cfv (syn_chwtrn) (syn_cop (.cv f) R)) (syn_chwtrn)
  have p0188 :=
    Nominal.mp p0186 p0187
  have p0189 :=
    @g_mpbi (.classEq (syn_cfv (syn_chwtrn) (syn_cop (.cv f) R)) (syn_cfv (syn_chwtrn) (syn_cop (.cv f) R))) (syn_wbr (syn_cop (.cv f) R) (syn_chwtrn) (syn_cfv (syn_chwtrn) (syn_cop (.cv f) R))) p0182 p0188
  have p0190 :=
    @g_eqid (syn_cfv (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cop (.cv f) R))
  have p0191 :=
    @g_vex x
  have p0192 :=
    @g_rnex (.cv x) p0191
  have p0193 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ranfn x
  have p0194 :=
    @g_fnmpti x (syn_cvv) (syn_crn (.cv x)) (syn_cranfn) dv_cache_0001 p0192 p0193
  have p0195 :=
    @g_n_1stfo
  have p0196 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0197 :=
    Nominal.mp p0195 p0196
  have p0198 :=
    @g_ssv (syn_crn (syn_c1st))
  have p0199 :=
    @g_n_3pm3_2i (syn_wfn (syn_cranfn) (syn_cvv)) (syn_wfn (syn_c1st) (syn_cvv)) (syn_wss (syn_crn (syn_c1st)) (syn_cvv)) p0194 p0197 p0198
  have p0200 :=
    @g_fnco (syn_cvv) (syn_cvv) (syn_cranfn) (syn_c1st)
  have p0201 :=
    Nominal.mp p0199 p0200
  have p0202 :=
    @g_vex f
  have p0203 :=
    @g_opex (.cv f) R p0202 hyp_hwgenval_1
  have p0204 :=
    @g_pm3_2i (syn_wfn (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cvv)) (.classMem (syn_cop (.cv f) R) (syn_cvv)) p0201 p0203
  have p0205 :=
    @g_fnbrfvb (syn_cvv) (syn_cop (.cv f) R) (syn_cfv (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cop (.cv f) R)) (syn_ccom (syn_cranfn) (syn_c1st))
  have p0206 :=
    Nominal.mp p0204 p0205
  have p0207 :=
    @g_mpbi (.classEq (syn_cfv (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cop (.cv f) R)) (syn_cfv (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cop (.cv f) R))) (syn_wbr (syn_cop (.cv f) R) (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cfv (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cop (.cv f) R))) p0190 p0206
  have p0208 :=
    @g_pm3_2i (syn_wbr (syn_cop (.cv f) R) (syn_chwtrn) (syn_cfv (syn_chwtrn) (syn_cop (.cv f) R))) (syn_wbr (syn_cop (.cv f) R) (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cfv (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cop (.cv f) R))) p0189 p0207
  have p0209 :=
    @g_trtxp (syn_cop (.cv f) R) (syn_cfv (syn_chwtrn) (syn_cop (.cv f) R)) (syn_cfv (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cop (.cv f) R)) (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))
  have p0210 :=
    @g_mpbir (syn_wbr (syn_cop (.cv f) R) (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cop (syn_cfv (syn_chwtrn) (syn_cop (.cv f) R)) (syn_cfv (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cop (.cv f) R)))) (syn_wa (syn_wbr (syn_cop (.cv f) R) (syn_chwtrn) (syn_cfv (syn_chwtrn) (syn_cop (.cv f) R))) (syn_wbr (syn_cop (.cv f) R) (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cfv (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cop (.cv f) R)))) p0208 p0209
  have p0211 :=
    @g_hwtrnfn
  have p0212 :=
    @g_vex x
  have p0213 :=
    @g_rnex (.cv x) p0212
  have p0214 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ranfn x
  have p0215 :=
    @g_fnmpti x (syn_cvv) (syn_crn (.cv x)) (syn_cranfn) dv_cache_0001 p0213 p0214
  have p0216 :=
    @g_n_1stfo
  have p0217 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0218 :=
    Nominal.mp p0216 p0217
  have p0219 :=
    @g_ssv (syn_crn (syn_c1st))
  have p0220 :=
    @g_n_3pm3_2i (syn_wfn (syn_cranfn) (syn_cvv)) (syn_wfn (syn_c1st) (syn_cvv)) (syn_wss (syn_crn (syn_c1st)) (syn_cvv)) p0215 p0218 p0219
  have p0221 :=
    @g_fnco (syn_cvv) (syn_cvv) (syn_cranfn) (syn_c1st)
  have p0222 :=
    Nominal.mp p0220 p0221
  have p0223 :=
    @g_pm3_2i (syn_wfn (syn_chwtrn) (syn_cvv)) (syn_wfn (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cvv)) p0211 p0222
  have p0224 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))
  have p0225 :=
    Nominal.mp p0223 p0224
  have p0226 :=
    @g_inidm (syn_cvv)
  have p0227 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) p0226
  have p0228 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cvv)) p0225 p0227
  have p0229 :=
    @g_fnfun (syn_cvv) (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))
  have p0230 :=
    Nominal.mp p0228 p0229
  have p0231 :=
    @g_funbrfv (syn_cop (.cv f) R) (syn_cop (syn_cfv (syn_chwtrn) (syn_cop (.cv f) R)) (syn_cfv (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cop (.cv f) R))) (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))
  have p0232 :=
    Nominal.mp p0230 p0231
  have p0233 :=
    Nominal.mp p0210 p0232
  have p0234 :=
    @g_hwtrnval R f hyp_hwgenval_1
  have p0235 :=
    @g_n_1stfo
  have p0236 :=
    @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0237 :=
    Nominal.mp p0235 p0236
  have p0238 :=
    @g_vex f
  have p0239 :=
    @g_opex (.cv f) R p0238 hyp_hwgenval_1
  have p0240 :=
    @g_pm3_2i (syn_wfn (syn_c1st) (syn_cvv)) (.classMem (syn_cop (.cv f) R) (syn_cvv)) p0237 p0239
  have p0241 :=
    @g_fvco2 (syn_cvv) (syn_cop (.cv f) R) (syn_cranfn) (syn_c1st)
  have p0242 :=
    Nominal.mp p0240 p0241
  have p0243 :=
    @g_vex f
  have p0244 :=
    @g_opfv1st (.cv f) R p0243 hyp_hwgenval_1
  have p0245 :=
    @g_fveq2i (syn_cfv (syn_c1st) (syn_cop (.cv f) R)) (.cv f) (syn_cranfn) p0244
  have p0246 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cop (.cv f) R)) (syn_cfv (syn_cranfn) (syn_cfv (syn_c1st) (syn_cop (.cv f) R))) (syn_cfv (syn_cranfn) (.cv f)) p0242 p0245
  have p0247 :=
    @g_vex f
  have p0248 :=
    @g_fvranfn (.cv f) (syn_cvv)
  have p0249 :=
    Nominal.mp p0247 p0248
  have p0250 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cop (.cv f) R)) (syn_cfv (syn_cranfn) (.cv f)) (syn_crn (.cv f)) p0246 p0249
  have p0251 :=
    @g_opeq12i (syn_cfv (syn_chwtrn) (syn_cop (.cv f) R)) (syn_ccom (syn_ccom (.cv f) R) (syn_ccnv (.cv f))) (syn_cfv (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cop (.cv f) R)) (syn_crn (.cv f)) p0234 p0250
  have p0252 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cop (.cv f) R)) (syn_cop (syn_cfv (syn_chwtrn) (syn_cop (.cv f) R)) (syn_cfv (syn_ccom (syn_cranfn) (syn_c1st)) (syn_cop (.cv f) R))) (syn_cop (syn_ccom (syn_ccom (.cv f) R) (syn_ccnv (.cv f))) (syn_crn (.cv f))) p0233 p0251
  have p0253 :=
    @g_opeq12i (syn_cfv (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cop (.cv f) R)) (syn_cop R (syn_cdm (.cv f))) (syn_cfv (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cop (.cv f) R)) (syn_cop (syn_ccom (syn_ccom (.cv f) R) (syn_ccnv (.cv f))) (syn_crn (.cv f))) p0181 p0252
  have p0254 :=
    @g_eqtri (syn_cfv (syn_ctxp (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))) (syn_cop (.cv f) R)) (syn_cop (syn_cfv (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_cop (.cv f) R)) (syn_cfv (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st))) (syn_cop (.cv f) R))) (syn_cop (syn_cop R (syn_cdm (.cv f))) (syn_cop (syn_ccom (syn_ccom (.cv f) R) (syn_ccnv (.cv f))) (syn_crn (.cv f)))) p0105 p0253
  have p0255 :=
    @g_eqtri (syn_cfv (syn_chwgen) (syn_cop (.cv f) R)) (syn_cfv (syn_ctxp (syn_ctxp (syn_c2nd) (syn_ccom (syn_cdomfn) (syn_c1st))) (syn_ctxp (syn_chwtrn) (syn_ccom (syn_cranfn) (syn_c1st)))) (syn_cop (.cv f) R)) (syn_cop (syn_cop R (syn_cdm (.cv f))) (syn_cop (syn_ccom (syn_ccom (.cv f) R) (syn_ccnv (.cv f))) (syn_crn (.cv f)))) p0001 p0254
  exact p0255

noncomputable def g_elhwnisogen
    (v : Var) (u : Var) (A : Class) (f : Var) (r : Var) (dv_A_f : f ∉ A.fv) (dv_A_r : r ∉ A.fv) (dv_f_r : f ≠ r) (dv_f_u : f ≠ u) (dv_f_v : f ≠ v) (dv_r_u : r ≠ u) (dv_r_v : r ≠ v) :
    Nominal.NPrf (syn_wb (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (.cv v))))))) := by
  let proofSupport : Finset Var := ({v} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv ∪ ({f} : Finset Var) ∪ ({r} : Finset Var)
  let p : Var := freshVar proofSupport 0
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_ne_v : p ≠ v := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_v_ne_p : v ≠ p :=
    Ne.symm fresh_p_ne_v
  have fresh_p_ne_u : p ≠ u := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_u_ne_p : u ≠ p :=
    Ne.symm fresh_p_ne_u
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_p_ne_f : p ≠ f := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_ne_p : f ≠ p :=
    Ne.symm fresh_p_ne_f
  have fresh_p_ne_r : p ≠ r := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_p : r ≠ p :=
    Ne.symm fresh_p_ne_r
  have dv_cache_0001 : p ∉ ((syn_cxp (syn_chwbij) (syn_cvv))).fv := by
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbij, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((syn_cop (.cv u) (.cv v))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_u, fresh_p_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : p ∉ ((syn_chwgen)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwgen, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : p ∉ ((syn_chwbij)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbij, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : f ∉ ((syn_chwbij)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbij, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : r ∉ ((syn_chwbij)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbij, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : p ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : f ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : r ∉ ((syn_cvv)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : f ∉ ((Wff.classEq (syn_cfv (syn_chwgen) (.cv p)) (syn_cop (.cv u) (.cv v)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwgen, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_f_ne_p, dv_f_u, dv_f_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : r ∉ ((Wff.classEq (syn_cfv (syn_chwgen) (.cv p)) (syn_cop (.cv u) (.cv v)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwgen, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_p, dv_r_u, dv_r_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : p ∉ ((Wff.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (.cv v)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwgen, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_f, fresh_p_ne_r, fresh_p_ne_u, fresh_p_ne_v, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : p ≠ f := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show p ≠ f from (by exact fresh_p_ne_f))
  have dv_cache_0014 : p ≠ r := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show p ≠ r from (by exact fresh_p_ne_r))
  have dv_cache_0015 : f ≠ r := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show f ≠ r from (by exact dv_f_r))
  have p0000 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv u) (syn_chwniso A) (.cv v))))
  have p0001 :=
    (by simpa [syn_chwniso] using (Nominal.classEqRefl (syn_chwniso A)))
  have p0002 :=
    @g_eleq2i (syn_chwniso A) (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cxp (syn_chwcn A) (syn_chwcn A))) (syn_cop (.cv u) (.cv v)) p0001
  have p0003 :=
    @g_elin (syn_cop (.cv u) (.cv v)) (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cxp (syn_chwcn A) (syn_chwcn A))
  have p0004 :=
    @g_hwgenfn
  have p0005 :=
    @g_ssv (syn_cxp (syn_chwbij) (syn_cvv))
  have p0006 :=
    @g_pm3_2i (syn_wfn (syn_chwgen) (syn_cvv)) (syn_wss (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_fvelimab p (syn_cvv) (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cop (.cv u) (.cv v)) (syn_chwgen) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_fveq2 (.cv p) (syn_cop (.cv f) (.cv r)) (syn_chwgen)
  have p0010 :=
    @g_eqeq1d (.classEq (.cv p) (syn_cop (.cv f) (.cv r))) (syn_cfv (syn_chwgen) (.cv p)) (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (.cv v)) p0009
  have p0011 :=
    @g_rexxp (.classEq (syn_cfv (syn_chwgen) (.cv p)) (syn_cop (.cv u) (.cv v))) (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (.cv v))) p f r (syn_chwbij) (syn_cvv) dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 p0010
  have p0012 :=
    @g_bitri (.classMem (syn_cop (.cv u) (.cv v)) (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))) (syn_wrex p (syn_cxp (syn_chwbij) (syn_cvv)) (.classEq (syn_cfv (syn_chwgen) (.cv p)) (syn_cop (.cv u) (.cv v)))) (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (.cv v))))) p0008 p0011
  have p0013 :=
    @g_opelxp (.cv u) (.cv v) (syn_chwcn A) (syn_chwcn A)
  have p0014 :=
    @g_anbi12i (.classMem (syn_cop (.cv u) (.cv v)) (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))) (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (.cv v))))) (.classMem (syn_cop (.cv u) (.cv v)) (syn_cxp (syn_chwcn A) (syn_chwcn A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0012 p0013
  have p0015 :=
    @g_ancom (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (.cv v))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
  have p0016 :=
    @g_bitri (syn_wa (.classMem (syn_cop (.cv u) (.cv v)) (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))) (.classMem (syn_cop (.cv u) (.cv v)) (syn_cxp (syn_chwcn A) (syn_chwcn A)))) (syn_wa (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (.cv v))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (.cv v)))))) p0014 p0015
  have p0017 :=
    @g_bitri (.classMem (syn_cop (.cv u) (.cv v)) (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cxp (syn_chwcn A) (syn_chwcn A)))) (syn_wa (.classMem (syn_cop (.cv u) (.cv v)) (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))) (.classMem (syn_cop (.cv u) (.cv v)) (syn_cxp (syn_chwcn A) (syn_chwcn A)))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (.cv v)))))) p0003 p0016
  have p0018 :=
    @g_bitri (.classMem (syn_cop (.cv u) (.cv v)) (syn_chwniso A)) (.classMem (syn_cop (.cv u) (.cv v)) (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cxp (syn_chwcn A) (syn_chwcn A)))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (.cv v)))))) p0002 p0017
  have p0019 :=
    @g_bitri (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (.classMem (syn_cop (.cv u) (.cv v)) (syn_chwniso A)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (.cv v)))))) p0000 p0018
  exact p0019

noncomputable def g_elhwnisogenval
    (v : Var) (u : Var) (A : Class) (f : Var) (r : Var) (dv_A_f : f ∉ A.fv) (dv_A_r : r ∉ A.fv) (dv_f_r : f ≠ r) (dv_f_u : f ≠ u) (dv_f_v : f ≠ v) (dv_r_u : r ≠ u) (dv_r_v : r ≠ v) :
    Nominal.NPrf (syn_wb (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v))))))) := by
  let proofSupport : Finset Var := ({v} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv ∪ ({f} : Finset Var) ∪ ({r} : Finset Var)
  have dv_cache_0001 : f ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : r ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : f ≠ r := by
    clear dv_cache_0001 dv_cache_0002
    exact (show f ≠ r from (by exact dv_f_r))
  have dv_cache_0004 : f ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show f ≠ u from (by exact dv_f_u))
  have dv_cache_0005 : f ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show f ≠ v from (by exact dv_f_v))
  have dv_cache_0006 : r ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show r ≠ u from (by exact dv_r_u))
  have dv_cache_0007 : r ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show r ≠ v from (by exact dv_r_v))
  have p0000 :=
    @g_elhwnisogen v u A f r dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 :=
    @g_vex r
  have p0002 :=
    @g_hwgenval (.cv r) f p0001
  have p0003 :=
    @g_eqeq1i (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))) (syn_cop (.cv u) (.cv v)) p0002
  have p0004 :=
    @g_opth (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv u) (.cv v)
  have p0005 :=
    @g_bitri (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (.cv v))) (.classEq (syn_cop (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))) (syn_cop (.cv u) (.cv v))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v))) p0003 p0004
  have p0006 :=
    @g_rexbii (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (.cv v))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v))) r (syn_cvv) p0005
  have p0007 :=
    @g_rexbii (syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (.cv v)))) (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v)))) f (syn_chwbij) p0006
  have p0008 :=
    @g_anbi2i (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (.cv v))))) (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0007
  have p0009 :=
    @g_bitri (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv) (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (.cv u) (.cv v)))))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v)))))) p0000 p0008
  exact p0009

noncomputable def g_elhwnisogenfun
    (v : Var) (u : Var) (A : Class) (f : Var) (r : Var) (dv_A_f : f ∉ A.fv) (dv_A_r : r ∉ A.fv) (dv_f_r : f ≠ r) (dv_f_u : f ≠ u) (dv_f_v : f ≠ v) (dv_r_u : r ≠ u) (dv_r_v : r ≠ v) :
    Nominal.NPrf (syn_wb (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wex f (syn_wa (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f)))) (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v)))))))) := by
  let proofSupport : Finset Var := ({v} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv ∪ ({f} : Finset Var) ∪ ({r} : Finset Var)
  have dv_cache_0001 : f ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : r ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : f ≠ r := by
    clear dv_cache_0001 dv_cache_0002
    exact (show f ≠ r from (by exact dv_f_r))
  have dv_cache_0004 : f ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show f ≠ u from (by exact dv_f_u))
  have dv_cache_0005 : f ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show f ≠ v from (by exact dv_f_v))
  have dv_cache_0006 : r ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show r ≠ u from (by exact dv_r_u))
  have dv_cache_0007 : r ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show r ≠ v from (by exact dv_r_v))
  have p0000 :=
    @g_elhwnisogenval v u A f r dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v)))))))
  have p0002 :=
    @g_elhwbij f
  have p0003 :=
    @g_anbi1i (.classMem (.cv f) (syn_chwbij)) (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f)))) (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v)))) p0002
  have p0004 :=
    @g_exbii (syn_wa (.classMem (.cv f) (syn_chwbij)) (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v))))) (syn_wa (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f)))) (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v))))) f p0003
  have p0005 :=
    @g_bitri (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v))))) (syn_wex f (syn_wa (.classMem (.cv f) (syn_chwbij)) (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v)))))) (syn_wex f (syn_wa (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f)))) (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v)))))) p0001 p0004
  have p0006 :=
    @g_anbi2i (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v))))) (syn_wex f (syn_wa (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f)))) (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v)))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0005
  have p0007 :=
    @g_bitri (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wrex f (syn_chwbij) (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v)))))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wex f (syn_wa (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f)))) (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v))))))) p0000 p0006
  exact p0007

noncomputable def g_hwbijf1o
    (f : Var) :
    Nominal.NPrf (syn_wb (.classMem (.cv f) (syn_chwbij)) (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))) := by
  let proofSupport : Finset Var := ({f} : Finset Var)
  have p0000 :=
    @g_elhwbij f
  have p0001 :=
    @g_funfn (.cv f)
  have p0002 :=
    @g_anbi1i (syn_wfun (.cv f)) (syn_wfn (.cv f) (syn_cdm (.cv f))) (syn_wfun (syn_ccnv (.cv f))) p0001
  have p0003 :=
    @g_f1orn (syn_cdm (.cv f)) (.cv f)
  have p0004 :=
    @g_bicomi (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (syn_wfn (.cv f) (syn_cdm (.cv f))) (syn_wfun (syn_ccnv (.cv f)))) p0003
  have p0005 :=
    @g_bitri (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f)))) (syn_wa (syn_wfn (.cv f) (syn_cdm (.cv f))) (syn_wfun (syn_ccnv (.cv f)))) (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) p0002 p0004
  have p0006 :=
    @g_bitri (.classMem (.cv f) (syn_chwbij)) (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f)))) (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) p0000 p0005
  exact p0006

noncomputable def g_elhwnisogenf1o
    (v : Var) (u : Var) (A : Class) (f : Var) (r : Var) (dv_A_f : f ∉ A.fv) (dv_A_r : r ∉ A.fv) (dv_f_r : f ≠ r) (dv_f_u : f ≠ u) (dv_f_v : f ≠ v) (dv_r_u : r ≠ u) (dv_r_v : r ≠ v) :
    Nominal.NPrf (syn_wb (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wex f (syn_wa (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v)))))))) := by
  let proofSupport : Finset Var := ({v} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv ∪ ({f} : Finset Var) ∪ ({r} : Finset Var)
  have dv_cache_0001 : f ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : r ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : f ≠ r := by
    clear dv_cache_0001 dv_cache_0002
    exact (show f ≠ r from (by exact dv_f_r))
  have dv_cache_0004 : f ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show f ≠ u from (by exact dv_f_u))
  have dv_cache_0005 : f ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show f ≠ v from (by exact dv_f_v))
  have dv_cache_0006 : r ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show r ≠ u from (by exact dv_r_u))
  have dv_cache_0007 : r ≠ v := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show r ≠ v from (by exact dv_r_v))
  have p0000 :=
    @g_elhwnisogenfun v u A f r dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 :=
    @g_funfn (.cv f)
  have p0002 :=
    @g_anbi1i (syn_wfun (.cv f)) (syn_wfn (.cv f) (syn_cdm (.cv f))) (syn_wfun (syn_ccnv (.cv f))) p0001
  have p0003 :=
    @g_f1orn (syn_cdm (.cv f)) (.cv f)
  have p0004 :=
    @g_bicomi (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (syn_wfn (.cv f) (syn_cdm (.cv f))) (syn_wfun (syn_ccnv (.cv f)))) p0003
  have p0005 :=
    @g_bitri (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f)))) (syn_wa (syn_wfn (.cv f) (syn_cdm (.cv f))) (syn_wfun (syn_ccnv (.cv f)))) (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) p0002 p0004
  have p0006 :=
    @g_anbi1i (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f)))) (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v)))) p0005
  have p0007 :=
    @g_exbii (syn_wa (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f)))) (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v))))) (syn_wa (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v))))) f p0006
  have p0008 :=
    @g_anbi2i (syn_wex f (syn_wa (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f)))) (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v)))))) (syn_wex f (syn_wa (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v)))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0007
  have p0009 :=
    @g_bitri (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wex f (syn_wa (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f)))) (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v))))))) (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wex f (syn_wa (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (.cv v))))))) p0000 p0008
  exact p0009

#print axioms g_elhwnisogenf1o

end NFChoice.DirectNominalPrf.WPPReplay
