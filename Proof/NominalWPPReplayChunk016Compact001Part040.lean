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
import NominalWPPReplayChunk016Compact001Part039

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

noncomputable def g_wppcandselfndv
    (C : Class) (F : Class) (hyp_wppcandselfndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem C (syn_chwcards (syn_cvv))) (.classMem C (syn_cwppcand F C))) := by
  let proofSupport : Finset Var := C.fv ∪ F.fv
  have p0000 :=
    @g_id (.classMem C (syn_chwcards (syn_cvv)))
  have p0001 :=
    @g_hwcardssnc (syn_cvv)
  have p0002 :=
    @g_ssel (syn_chwcards (syn_cvv)) (syn_cncs) C
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    @g_nclecid C
  have p0005 :=
    @g_syl (.classMem C (syn_chwcards (syn_cvv))) (.classMem C (syn_cncs)) (syn_wbr C (syn_clec) C) p0003 p0004
  have p0006 :=
    @g_jca (.classMem C (syn_chwcards (syn_cvv))) (.classMem C (syn_chwcards (syn_cvv))) (syn_wbr C (syn_clec) C) p0000 p0005
  have p0007 :=
    @g_hwcardssnc (syn_cvv)
  have p0008 :=
    @g_ssel (syn_chwcards (syn_cvv)) (syn_cncs) C
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_nclecid C
  have p0011 :=
    @g_syl (.classMem C (syn_chwcards (syn_cvv))) (.classMem C (syn_cncs)) (syn_wbr C (syn_clec) C) p0009 p0010
  have p0012 :=
    @g_elimasn (syn_clec) C C
  have p0013 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr C (syn_clec) C)))
  have p0014 :=
    @g_bitr4i (.classMem C (syn_cima (syn_clec) (syn_csn C))) (.classMem (syn_cop C C) (syn_clec)) (syn_wbr C (syn_clec) C) p0012 p0013
  have p0015 :=
    @g_sylibr (.classMem C (syn_chwcards (syn_cvv))) (syn_wbr C (syn_clec) C) (.classMem C (syn_cima (syn_clec) (syn_csn C))) p0011 p0014
  have p0016 :=
    @g_cnvex F hyp_wppcandselfndv_1
  have p0017 :=
    @g_wppimagefn (syn_ccnv F) p0016
  have p0018 :=
    @g_fnfun (syn_cvv) (syn_cimage (syn_ccnv F))
  have p0019 :=
    Nominal.mp p0017 p0018
  have p0020 :=
    @g_cnvex F hyp_wppcandselfndv_1
  have p0021 :=
    @g_imageex (syn_ccnv F) p0020
  have p0022 :=
    @g_elfuns (syn_cimage (syn_ccnv F)) p0021
  have p0023 :=
    @g_mpbir (.classMem (syn_cimage (syn_ccnv F)) (syn_cfuns)) (syn_wfun (syn_cimage (syn_ccnv F))) p0019 p0022
  have p0024 :=
    @g_lecex
  have p0025 :=
    @g_snex C
  have p0026 :=
    @g_imaex (syn_clec) (syn_csn C) p0024 p0025
  have p0027 :=
    @g_cnvex F hyp_wppcandselfndv_1
  have p0028 :=
    @g_wppimagefn (syn_ccnv F) p0027
  have p0029 :=
    @g_fndm (syn_cvv) (syn_cimage (syn_ccnv F))
  have p0030 :=
    Nominal.mp p0028 p0029
  have p0031 :=
    @g_eleqtrri (syn_cima (syn_clec) (syn_csn C)) (syn_cvv) (syn_cdm (syn_cimage (syn_ccnv F))) p0026 p0030
  have p0032 :=
    @g_ssv (syn_crn (syn_cimage (syn_ccnv F)))
  have p0033 :=
    @g_cnvex F hyp_wppcandselfndv_1
  have p0034 :=
    @g_wppimagefn (syn_ccnv F) p0033
  have p0035 :=
    @g_fndm (syn_cvv) (syn_cimage (syn_ccnv F))
  have p0036 :=
    Nominal.mp p0034 p0035
  have p0037 :=
    @g_sseqtr4i (syn_crn (syn_cimage (syn_ccnv F))) (syn_cvv) (syn_cdm (syn_cimage (syn_ccnv F))) p0032 p0036
  have p0038 :=
    @g_n_3pm3_2i (.classMem (syn_cimage (syn_ccnv F)) (syn_cfuns)) (.classMem (syn_cima (syn_clec) (syn_csn C)) (syn_cdm (syn_cimage (syn_ccnv F)))) (syn_wss (syn_crn (syn_cimage (syn_ccnv F))) (syn_cdm (syn_cimage (syn_ccnv F)))) p0023 p0031 p0037
  have p0039 :=
    @g_wpporbit0ndv (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))
  have p0040 :=
    Nominal.mp p0038 p0039
  have p0041 :=
    @g_cnvex F hyp_wppcandselfndv_1
  have p0042 :=
    @g_wppimagefn (syn_ccnv F) p0041
  have p0043 :=
    @g_fnfun (syn_cvv) (syn_cimage (syn_ccnv F))
  have p0044 :=
    Nominal.mp p0042 p0043
  have p0045 :=
    @g_cnvex F hyp_wppcandselfndv_1
  have p0046 :=
    @g_imageex (syn_ccnv F) p0045
  have p0047 :=
    @g_elfuns (syn_cimage (syn_ccnv F)) p0046
  have p0048 :=
    @g_mpbir (.classMem (syn_cimage (syn_ccnv F)) (syn_cfuns)) (syn_wfun (syn_cimage (syn_ccnv F))) p0044 p0047
  have p0049 :=
    @g_lecex
  have p0050 :=
    @g_snex C
  have p0051 :=
    @g_imaex (syn_clec) (syn_csn C) p0049 p0050
  have p0052 :=
    @g_cnvex F hyp_wppcandselfndv_1
  have p0053 :=
    @g_wppimagefn (syn_ccnv F) p0052
  have p0054 :=
    @g_fndm (syn_cvv) (syn_cimage (syn_ccnv F))
  have p0055 :=
    Nominal.mp p0053 p0054
  have p0056 :=
    @g_eleqtrri (syn_cima (syn_clec) (syn_csn C)) (syn_cvv) (syn_cdm (syn_cimage (syn_ccnv F))) p0051 p0055
  have p0057 :=
    @g_ssv (syn_crn (syn_cimage (syn_ccnv F)))
  have p0058 :=
    @g_cnvex F hyp_wppcandselfndv_1
  have p0059 :=
    @g_wppimagefn (syn_ccnv F) p0058
  have p0060 :=
    @g_fndm (syn_cvv) (syn_cimage (syn_ccnv F))
  have p0061 :=
    Nominal.mp p0059 p0060
  have p0062 :=
    @g_sseqtr4i (syn_crn (syn_cimage (syn_ccnv F))) (syn_cvv) (syn_cdm (syn_cimage (syn_ccnv F))) p0057 p0061
  have p0063 :=
    @g_n_3pm3_2i (.classMem (syn_cimage (syn_ccnv F)) (syn_cfuns)) (.classMem (syn_cima (syn_clec) (syn_csn C)) (syn_cdm (syn_cimage (syn_ccnv F)))) (syn_wss (syn_crn (syn_cimage (syn_ccnv F))) (syn_cdm (syn_cimage (syn_ccnv F)))) p0048 p0056 p0062
  have p0064 :=
    @g_wpporbitfnndv (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))
  have p0065 :=
    Nominal.mp p0063 p0064
  have p0066 :=
    @g_peano1
  have p0067 :=
    @g_fnfvelrn (syn_cnnc) (syn_c0c) (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
  have p0068 :=
    @g_mp2an (syn_wfn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_cnnc)) (.classMem (syn_c0c) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_c0c)) (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))))) p0065 p0066 p0067
  have p0069 :=
    @g_eqeltrri (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_c0c)) (syn_cima (syn_clec) (syn_csn C)) (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))) p0040 p0068
  have p0070 :=
    @g_a1i (.classMem (syn_cima (syn_clec) (syn_csn C)) (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))))) (.classMem C (syn_chwcards (syn_cvv))) p0069
  have p0071 :=
    @g_jca (.classMem C (syn_chwcards (syn_cvv))) (.classMem C (syn_cima (syn_clec) (syn_csn C))) (.classMem (syn_cima (syn_clec) (syn_csn C)) (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))))) p0015 p0070
  have p0072 :=
    @g_elunii C (syn_cima (syn_clec) (syn_csn C)) (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))))
  have p0073 :=
    @g_syl (.classMem C (syn_chwcards (syn_cvv))) (syn_wa (.classMem C (syn_cima (syn_clec) (syn_csn C))) (.classMem (syn_cima (syn_clec) (syn_csn C)) (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))))) (.classMem C (syn_cuni (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))))) p0071 p0072
  have p0074 :=
    (by simpa [syn_cwppreach] using (Nominal.classEqRefl (syn_cwppreach F C)))
  have p0075 :=
    @g_eleq2i (syn_cwppreach F C) (syn_cuni (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))))) C p0074
  have p0076 :=
    @g_sylibr (.classMem C (syn_chwcards (syn_cvv))) (.classMem C (syn_cuni (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))))) (.classMem C (syn_cwppreach F C)) p0073 p0075
  have p0077 :=
    @g_jca (.classMem C (syn_chwcards (syn_cvv))) (syn_wa (.classMem C (syn_chwcards (syn_cvv))) (syn_wbr C (syn_clec) C)) (.classMem C (syn_cwppreach F C)) p0006 p0076
  have p0078 :=
    @g_elwppcand C C F
  have p0079 :=
    @g_sylibr (.classMem C (syn_chwcards (syn_cvv))) (syn_wa (syn_wa (.classMem C (syn_chwcards (syn_cvv))) (syn_wbr C (syn_clec) C)) (.classMem C (syn_cwppreach F C))) (.classMem C (syn_cwppcand F C)) p0077 p0078
  exact p0079

noncomputable def g_wppcandstrictsliceemptyminndv
    (C : Class) (k : Var) (F : Class) (dv_C_k : k ∉ C.fv) (dv_F_k : k ∉ F.fv) (hyp_wppcandstrictsliceemptyminndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) (hyp_wppcandstrictsliceemptyminndv_2 : Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf (.imp (.classEq (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0)) (syn_wa (.classMem C (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr C (syn_clec) (.cv k))))) := by
  let proofSupport : Finset Var := C.fv ∪ ({k} : Finset Var) ∪ F.fv
  have dv_cache_0001 : k ∉ ((Wff.classEq (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0))).fv := by
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_k, dv_F_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_wppcandselfndv C F hyp_wppcandstrictsliceemptyminndv_1
  have p0001 :=
    Nominal.mp hyp_wppcandstrictsliceemptyminndv_2 p0000
  have p0002 :=
    @g_a1i (.classMem C (syn_cwppcand F C)) (.classEq (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0)) p0001
  have p0003 :=
    @g_hwcardssnc (syn_cvv)
  have p0004 :=
    @g_ssel (syn_chwcards (syn_cvv)) (syn_cncs) C
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    Nominal.mp hyp_wppcandstrictsliceemptyminndv_2 p0005
  have p0007 :=
    @g_nclecid C
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_a1i (syn_wbr C (syn_clec) C) (syn_wa (.classEq (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0)) (.classMem (.cv k) (syn_cwppcand F C))) p0008
  have p0010 :=
    @g_simpr (.classEq (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0)) (.classMem (.cv k) (syn_cwppcand F C))
  have p0011 :=
    @g_noel (.cv k)
  have p0012 :=
    @g_a1i (.neg (.classMem (.cv k) (syn_c0))) (syn_wa (.classEq (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0)) (.classMem (.cv k) (syn_cwppcand F C))) p0011
  have p0013 :=
    @g_simpl (.classEq (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0)) (.classMem (.cv k) (syn_cwppcand F C))
  have p0014 :=
    @g_eleq2d (syn_wa (.classEq (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0)) (.classMem (.cv k) (syn_cwppcand F C))) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0) (.cv k) p0013
  have p0015 :=
    @g_biimpd (syn_wa (.classEq (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0)) (.classMem (.cv k) (syn_cwppcand F C))) (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (.classMem (.cv k) (syn_c0)) p0014
  have p0016 :=
    @g_con3d (syn_wa (.classEq (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0)) (.classMem (.cv k) (syn_cwppcand F C))) (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (.classMem (.cv k) (syn_c0)) p0015
  have p0017 :=
    @g_mpd (syn_wa (.classEq (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0)) (.classMem (.cv k) (syn_cwppcand F C))) (.neg (.classMem (.cv k) (syn_c0))) (.neg (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))) p0012 p0016
  have p0018 :=
    @g_simpr (.classEq (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0)) (.classMem (.cv k) (syn_cwppcand F C))
  have p0019 :=
    @g_elwppcandstrictslice C k F
  have p0020 :=
    @g_biimpri (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) (syn_wa (.classMem (.cv k) (syn_cwppcand F C)) (syn_wbr (.cv k) (syn_cltc) C)) p0019
  have p0021 :=
    @g_ex (.classMem (.cv k) (syn_cwppcand F C)) (syn_wbr (.cv k) (syn_cltc) C) (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) p0020
  have p0022 :=
    @g_syl (syn_wa (.classEq (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0)) (.classMem (.cv k) (syn_cwppcand F C))) (.classMem (.cv k) (syn_cwppcand F C)) (.imp (syn_wbr (.cv k) (syn_cltc) C) (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))) p0018 p0021
  have p0023 :=
    @g_con3d (syn_wa (.classEq (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0)) (.classMem (.cv k) (syn_cwppcand F C))) (syn_wbr (.cv k) (syn_cltc) C) (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))) p0022
  have p0024 :=
    @g_mpd (syn_wa (.classEq (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0)) (.classMem (.cv k) (syn_cwppcand F C))) (.neg (.classMem (.cv k) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))) (.neg (syn_wbr (.cv k) (syn_cltc) C)) p0017 p0023
  have p0025 :=
    @g_jca (syn_wa (.classEq (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0)) (.classMem (.cv k) (syn_cwppcand F C))) (.classMem (.cv k) (syn_cwppcand F C)) (.neg (syn_wbr (.cv k) (syn_cltc) C)) p0010 p0024
  have p0026 :=
    @g_wppcandnltpivoteqd C k F
  have p0027 :=
    @g_syl (syn_wa (.classEq (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0)) (.classMem (.cv k) (syn_cwppcand F C))) (syn_wa (.classMem (.cv k) (syn_cwppcand F C)) (.neg (syn_wbr (.cv k) (syn_cltc) C))) (.classEq (.cv k) C) p0025 p0026
  have p0028 :=
    @g_breqtrrd (syn_wa (.classEq (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0)) (.classMem (.cv k) (syn_cwppcand F C))) C C (.cv k) (syn_clec) p0009 p0027
  have p0029 :=
    @g_ex (.classEq (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0)) (.classMem (.cv k) (syn_cwppcand F C)) (syn_wbr C (syn_clec) (.cv k)) p0028
  have p0030 :=
    @g_ralrimiv (.classEq (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0)) (syn_wbr C (syn_clec) (.cv k)) k (syn_cwppcand F C) dv_cache_0001 p0029
  have p0031 :=
    @g_jca (.classEq (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0)) (.classMem C (syn_cwppcand F C)) (syn_wral k (syn_cwppcand F C) (syn_wbr C (syn_clec) (.cv k))) p0002 p0030
  exact p0031

noncomputable def g_wppcandstrictsliceemptypublicminndv
    (z : Var) (C : Class) (n : Var) (F : Class) (dv_C_n : n ∉ C.fv) (dv_C_z : z ∉ C.fv) (dv_F_n : n ∉ F.fv) (dv_F_z : z ∉ F.fv) (dv_n_z : n ≠ z) (hyp_wppcandstrictsliceemptypublicminndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) (hyp_wppcandstrictsliceemptypublicminndv_2 : Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf (.imp (.classEq (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0)) (syn_wrex n (syn_cwppcand F C) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))))) := by
  let proofSupport : Finset Var := ({z} : Finset Var) ∪ C.fv ∪ ({n} : Finset Var) ∪ F.fv
  have dv_cache_0001 : z ∉ (C).fv := by
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ (F).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((Wff.classEq (.cv n) C)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_n_z), dv_C_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : n ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : n ∉ ((syn_cwppcand F C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_n, dv_F_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : n ∉ ((syn_wral z (syn_cwppcand F C) (syn_wbr C (syn_clec) (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_n, dv_F_n, dv_n_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_wppcandstrictsliceemptyminndv C z F dv_cache_0001 dv_cache_0002 hyp_wppcandstrictsliceemptypublicminndv_1 hyp_wppcandstrictsliceemptypublicminndv_2
  have p0001 :=
    @g_id (.classEq (.cv n) C)
  have p0002 :=
    @g_breq1d (.classEq (.cv n) C) (.cv n) C (.cv z) (syn_clec) p0001
  have p0003 :=
    @g_ralbidv (.classEq (.cv n) C) (syn_wbr (.cv n) (syn_clec) (.cv z)) (syn_wbr C (syn_clec) (.cv z)) z (syn_cwppcand F C) dv_cache_0003 p0002
  have p0004 :=
    @g_rspcev (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z))) (syn_wral z (syn_cwppcand F C) (syn_wbr C (syn_clec) (.cv z))) n C (syn_cwppcand F C) dv_cache_0004 dv_cache_0005 dv_cache_0006 p0003
  have p0005 :=
    @g_syl (.classEq (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0)) (syn_wa (.classMem C (syn_cwppcand F C)) (syn_wral z (syn_cwppcand F C) (syn_wbr C (syn_clec) (.cv z)))) (syn_wrex n (syn_cwppcand F C) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z)))) p0000 p0004
  exact p0005

noncomputable def g_wppcandminfixedpivotdrfdv
    (z : Var) (C : Class) (D : Class) (R : Class) (n : Var) (F : Class) (dv_C_n : n ∉ C.fv) (dv_C_z : z ∉ C.fv) (dv_D_n : n ∉ D.fv) (dv_D_z : z ∉ D.fv) (dv_F_n : n ∉ F.fv) (dv_F_z : z ∉ F.fv) (dv_R_n : n ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_n_z : n ≠ z) (hyp_wppcandminfixedpivotdrfdv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) (hyp_wppcandminfixedpivotdrfdv_2 : Nominal.NPrf (.classEq C (syn_cnc D))) (hyp_wppcandminfixedpivotdrfdv_3 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (syn_wrex n (syn_cwppcand F C) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z)))) := by
  let proofSupport : Finset Var := ({z} : Finset Var) ∪ C.fv ∪ D.fv ∪ R.fv ∪ ({n} : Finset Var) ∪ F.fv
  let c : Var := freshVar proofSupport 0
  let s : Var := freshVar proofSupport 1
  let d : Var := freshVar proofSupport 2
  let k : Var := freshVar proofSupport 3
  let q : Var := freshVar proofSupport 4
  have fresh_c : c ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_c_ne_z : c ≠ z := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_z_ne_c : z ≠ c :=
    Ne.symm fresh_c_ne_z
  have fresh_c_not_C : c ∉ C.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_c_not_D : c ∉ D.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_c_not_R : c ∉ R.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_c_ne_n : c ≠ n := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_c : n ≠ c :=
    Ne.symm fresh_c_ne_n
  have fresh_c_not_F : c ∉ F.fv := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (h))
  have fresh_s : s ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_s_ne_z : s ≠ z := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_z_ne_s : z ≠ s :=
    Ne.symm fresh_s_ne_z
  have fresh_s_not_C : s ∉ C.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_s_not_D : s ∉ D.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_s_not_R : s ∉ R.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_s_ne_n : s ≠ n := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_s : n ≠ s :=
    Ne.symm fresh_s_ne_n
  have fresh_s_not_F : s ∉ F.fv := by
    intro h
    exact fresh_s (Finset.mem_union_right _ (h))
  have fresh_d : d ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_d_ne_z : d ≠ z := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_z_ne_d : z ≠ d :=
    Ne.symm fresh_d_ne_z
  have fresh_d_not_C : d ∉ C.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_d_not_D : d ∉ D.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_d_not_R : d ∉ R.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_d_ne_n : d ≠ n := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_d : n ≠ d :=
    Ne.symm fresh_d_ne_n
  have fresh_d_not_F : d ∉ F.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_k : k ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_k_ne_z : k ≠ z := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_z_ne_k : z ≠ k :=
    Ne.symm fresh_k_ne_z
  have fresh_k_not_C : k ∉ C.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_k_not_D : k ∉ D.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_k_not_R : k ∉ R.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_k_ne_n : k ≠ n := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_k : n ≠ k :=
    Ne.symm fresh_k_ne_n
  have fresh_k_not_F : k ∉ F.fv := by
    intro h
    exact fresh_k (Finset.mem_union_right _ (h))
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_q_ne_z : q ≠ z := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_z_ne_q : z ≠ q :=
    Ne.symm fresh_q_ne_z
  have fresh_q_not_C : q ∉ C.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_q_not_D : q ∉ D.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_q_not_R : q ∉ R.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_q_ne_n : q ≠ n := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_q : n ≠ q :=
    Ne.symm fresh_q_ne_n
  have fresh_q_not_F : q ∉ F.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_c_ne_s : c ≠ s := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_s_ne_c : s ≠ c :=
    Ne.symm fresh_c_ne_s
  have fresh_c_ne_d : c ≠ d := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_d_ne_c : d ≠ c :=
    Ne.symm fresh_c_ne_d
  have fresh_c_ne_k : c ≠ k := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_k_ne_c : k ≠ c :=
    Ne.symm fresh_c_ne_k
  have fresh_c_ne_q : c ≠ q := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_q_ne_c : q ≠ c :=
    Ne.symm fresh_c_ne_q
  have fresh_s_ne_d : s ≠ d := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_d_ne_s : d ≠ s :=
    Ne.symm fresh_s_ne_d
  have fresh_s_ne_k : s ≠ k := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_k_ne_s : k ≠ s :=
    Ne.symm fresh_s_ne_k
  have fresh_s_ne_q : s ≠ q := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_q_ne_s : q ≠ s :=
    Ne.symm fresh_s_ne_q
  have fresh_d_ne_k : d ≠ k := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_k_ne_d : k ≠ d :=
    Ne.symm fresh_d_ne_k
  have fresh_d_ne_q : d ≠ q := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_q_ne_d : q ≠ d :=
    Ne.symm fresh_d_ne_q
  have fresh_k_ne_q : k ≠ q := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_q_ne_k : q ≠ k :=
    Ne.symm fresh_k_ne_q
  have dv_cache_0001 : d ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : s ∉ (D).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : d ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : s ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : d ∉ ((syn_wa (syn_wbr R (syn_cwe) D) (.classEq (.cv c) (syn_cnc D)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_not_R, fresh_d_not_D, fresh_d_ne_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : s ∉ ((syn_wa (syn_wbr R (syn_cwe) D) (.classEq (.cv c) (syn_cnc D)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_R, fresh_s_not_D, fresh_s_ne_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : d ≠ s := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show d ≠ s from (by exact fresh_d_ne_s))
  have dv_cache_0008 : d ≠ c := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show d ≠ c from (by exact fresh_d_ne_c))
  have dv_cache_0009 : c ≠ s := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show c ≠ s from (by exact fresh_c_ne_s))
  have dv_cache_0010 : c ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : c ∉ ((Wff.imp (.classEq C (syn_cnc D)) (.classMem C (syn_chwcards (syn_cvv))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_C, fresh_c_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : n ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : z ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : n ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : z ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : n ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show n ≠ z from (by exact dv_n_z))
  have dv_cache_0017 : k ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : q ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : k ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : q ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : k ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : q ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : k ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : q ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : k ≠ q := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (show k ≠ q from (by exact fresh_k_ne_q))
  have dv_cache_0026 : n ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : z ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0028 : n ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0029 : z ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0030 : k ≠ n := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (show k ≠ n from (by exact fresh_k_ne_n))
  have dv_cache_0031 : k ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (show k ≠ z from (by exact fresh_k_ne_z))
  have dv_cache_0032 : n ≠ q := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (show n ≠ q from (by exact fresh_n_ne_q))
  have dv_cache_0033 : q ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (show q ≠ z from (by exact fresh_q_ne_z))
  have p0000 :=
    @g_ncex D
  have p0001 :=
    @g_eqeltri C (syn_cnc D) (syn_cvv) hyp_wppcandminfixedpivotdrfdv_2 p0000
  have p0002 :=
    @g_id (.classEq (.cv c) C)
  have p0003 :=
    @g_eqeq1d (.classEq (.cv c) C) (.cv c) C (syn_cnc D) p0002
  have p0004 :=
    @g_id (.classEq (.cv c) C)
  have p0005 :=
    @g_eleq1d (.classEq (.cv c) C) (.cv c) C (syn_chwcards (syn_cvv)) p0004
  have p0006 :=
    @g_imbi12d (.classEq (.cv c) C) (.classEq (.cv c) (syn_cnc D)) (.classEq C (syn_cnc D)) (.classMem (.cv c) (syn_chwcards (syn_cvv))) (.classMem C (syn_chwcards (syn_cvv))) p0003 p0005
  have p0007 :=
    @g_a1i (syn_wbr R (syn_cwe) D) (.classEq (.cv c) (syn_cnc D)) hyp_wppcandminfixedpivotdrfdv_1
  have p0008 :=
    @g_id (.classEq (.cv c) (syn_cnc D))
  have p0009 :=
    @g_jca (.classEq (.cv c) (syn_cnc D)) (syn_wbr R (syn_cwe) D) (.classEq (.cv c) (syn_cnc D)) p0007 p0008
  have p0010 :=
    @g_brex R D (syn_cwe)
  have p0011 :=
    Nominal.mp hyp_wppcandminfixedpivotdrfdv_1 p0010
  have p0012 :=
    @g_simpr (.classMem R (syn_cvv)) (.classMem D (syn_cvv))
  have p0013 :=
    Nominal.mp p0011 p0012
  have p0014 :=
    @g_brex R D (syn_cwe)
  have p0015 :=
    Nominal.mp hyp_wppcandminfixedpivotdrfdv_1 p0014
  have p0016 :=
    @g_simpl (.classMem R (syn_cvv)) (.classMem D (syn_cvv))
  have p0017 :=
    Nominal.mp p0015 p0016
  have p0018 :=
    @g_simpr (.classEq (.cv d) D) (.classEq (.cv s) R)
  have p0019 :=
    @g_simpl (.classEq (.cv d) D) (.classEq (.cv s) R)
  have p0020 :=
    @g_breq12d (syn_wa (.classEq (.cv d) D) (.classEq (.cv s) R)) (.cv s) R (.cv d) D (syn_cwe) p0018 p0019
  have p0021 :=
    @g_simpl (.classEq (.cv d) D) (.classEq (.cv s) R)
  have p0022 :=
    @g_nceqd (syn_wa (.classEq (.cv d) D) (.classEq (.cv s) R)) (.cv d) D p0021
  have p0023 :=
    @g_eqeq2d (syn_wa (.classEq (.cv d) D) (.classEq (.cv s) R)) (syn_cnc (.cv d)) (syn_cnc D) (.cv c) p0022
  have p0024 :=
    @g_anbi12d (syn_wa (.classEq (.cv d) D) (.classEq (.cv s) R)) (syn_wbr (.cv s) (syn_cwe) (.cv d)) (syn_wbr R (syn_cwe) D) (.classEq (.cv c) (syn_cnc (.cv d))) (.classEq (.cv c) (syn_cnc D)) p0020 p0023
  have p0025 :=
    @g_spc2ev (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv c) (syn_cnc (.cv d)))) (syn_wa (syn_wbr R (syn_cwe) D) (.classEq (.cv c) (syn_cnc D))) d s D R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 p0013 p0017 p0024
  have p0026 :=
    @g_syl (.classEq (.cv c) (syn_cnc D)) (syn_wa (syn_wbr R (syn_cwe) D) (.classEq (.cv c) (syn_cnc D))) (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv c) (syn_cnc (.cv d)))))) p0009 p0025
  have p0027 :=
    @g_elhwcardswev c s d dv_cache_0008 dv_cache_0007 dv_cache_0009
  have p0028 :=
    @g_biimpri (.classMem (.cv c) (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv c) (syn_cnc (.cv d)))))) p0027
  have p0029 :=
    @g_syl (.classEq (.cv c) (syn_cnc D)) (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv c) (syn_cnc (.cv d)))))) (.classMem (.cv c) (syn_chwcards (syn_cvv))) p0026 p0028
  have p0030 :=
    @g_vtoclg (.imp (.classEq (.cv c) (syn_cnc D)) (.classMem (.cv c) (syn_chwcards (syn_cvv)))) (.imp (.classEq C (syn_cnc D)) (.classMem C (syn_chwcards (syn_cvv)))) c C (syn_cvv) dv_cache_0010 dv_cache_0011 p0006 p0029
  have p0031 :=
    Nominal.mp p0001 p0030
  have p0032 :=
    Nominal.mp hyp_wppcandminfixedpivotdrfdv_2 p0031
  have p0033 :=
    @g_wppcandstrictsliceemptypublicminndv z C n F dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 hyp_wppcandminfixedpivotdrfdv_3 p0032
  have p0034 :=
    @g_wppcandstrictslicecutrepfixdrfdv C D R k F q dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 hyp_wppcandminfixedpivotdrfdv_1 hyp_wppcandminfixedpivotdrfdv_2
  have p0035 :=
    @g_wppcandstrictslicenonemptyminndv z C D R k n F q dv_cache_0017 dv_cache_0012 dv_cache_0018 dv_cache_0013 dv_cache_0019 dv_cache_0026 dv_cache_0020 dv_cache_0027 dv_cache_0021 dv_cache_0014 dv_cache_0022 dv_cache_0015 dv_cache_0023 dv_cache_0028 dv_cache_0024 dv_cache_0029 dv_cache_0030 dv_cache_0025 dv_cache_0031 dv_cache_0032 dv_cache_0016 dv_cache_0033 hyp_wppcandminfixedpivotdrfdv_1 hyp_wppcandminfixedpivotdrfdv_3 p0034
  have p0036 :=
    @g_pm2_61ine (syn_wrex n (syn_cwppcand F C) (syn_wral z (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv z)))) (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))) (syn_c0) p0033 p0035
  exact p0036

noncomputable def g_wecomparisondefaultemptywe
     :
    Nominal.NPrf (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe) (syn_c0)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_finlewe
  have p0001 :=
    @g_a1i (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cwe) (syn_cnnc)) syn_wtru p0000
  have p0002 :=
    @g_n_0ss (syn_cnnc)
  have p0003 :=
    @g_a1i (syn_wss (syn_c0) (syn_cnnc)) syn_wtru p0002
  have p0004 :=
    @g_n_0ex
  have p0005 :=
    @g_a1i (.classMem (syn_c0) (syn_cvv)) syn_wtru p0004
  have p0006 :=
    @g_werestrndv syn_wtru (syn_c0) (syn_cnnc) (syn_ckqrel (syn_clefin)) p0001 p0003 p0005
  have p0007 :=
    @g_trud (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe) (syn_c0)) p0006
  exact p0007

#print axioms g_wecomparisondefaultemptywe

end NFChoice.DirectNominalPrf.WPPReplay
