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
import NominalWPPReplayChunk017Compact001Part068

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

noncomputable def g_wppconcrete6globalnonfixedfromhnshiftndv
    (y : Var) (hyp_wppconcrete6globalnonfixedfromhnshiftndv_1 : Nominal.NPrf (.neg (syn_wbr (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_clec) (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))) :
    Nominal.NPrf (syn_wral y (syn_chwcards (syn_cvv)) (.imp (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y)) (syn_wne (.cv y) (syn_ctc (.cv y))))) := by
  let proofSupport : Finset Var := ({y} : Finset Var)
  have p0000 :=
    @g_hncardtc6oneeqndv
  have p0001 :=
    @g_breq1i (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_clec) p0000
  have p0002 :=
    @g_mtbir (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (syn_wbr (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_clec) (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) hyp_wppconcrete6globalnonfixedfromhnshiftndv_1 p0001
  have p0003 :=
    @g_a1i (.neg (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) p0002
  have p0004 :=
    @g_simpl (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))
  have p0005 :=
    @g_simprd (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y)) p0004
  have p0006 :=
    @g_simpl (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))
  have p0007 :=
    @g_simpld (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y)) p0006
  have p0008 :=
    @g_hwcardssnc (syn_cvv)
  have p0009 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (.cv y) p0008
  have p0010 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.classMem (.cv y) (syn_cncs)) p0007 p0009
  have p0011 :=
    @g_tlenc1c (.cv y)
  have p0012 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.classMem (.cv y) (syn_cncs)) (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_cnc (syn_c1c))) p0010 p0011
  have p0013 :=
    @g_simpr (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))
  have p0014 :=
    @g_breq1d (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.cv y) (syn_ctc (.cv y)) (syn_cnc (syn_c1c)) (syn_clec) p0013
  have p0015 :=
    @g_mpbird (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (syn_wbr (.cv y) (syn_clec) (syn_cnc (syn_c1c))) (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_cnc (syn_c1c))) p0012 p0014
  have p0016 :=
    @g_simpl (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))
  have p0017 :=
    @g_simpld (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y)) p0016
  have p0018 :=
    @g_hwcardssnc (syn_cvv)
  have p0019 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (.cv y) p0018
  have p0020 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.classMem (.cv y) (syn_cncs)) p0017 p0019
  have p0021 :=
    @g_n_1cex
  have p0022 :=
    @g_ncelncsi (syn_c1c) p0021
  have p0023 :=
    @g_a1i (.classMem (syn_cnc (syn_c1c)) (syn_cncs)) (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) p0022
  have p0024 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.classMem (.cv y) (syn_cncs)) (.classMem (syn_cnc (syn_c1c)) (syn_cncs)) p0020 p0023
  have p0025 :=
    @g_tlecg (.cv y) (syn_cnc (syn_c1c))
  have p0026 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (syn_wa (.classMem (.cv y) (syn_cncs)) (.classMem (syn_cnc (syn_c1c)) (syn_cncs))) (syn_wb (syn_wbr (.cv y) (syn_clec) (syn_cnc (syn_c1c))) (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_cnc (syn_c1c))))) p0024 p0025
  have p0027 :=
    @g_mpbid (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (syn_wbr (.cv y) (syn_clec) (syn_cnc (syn_c1c))) (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_cnc (syn_c1c)))) p0015 p0026
  have p0028 :=
    @g_simpr (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))
  have p0029 :=
    @g_breq1d (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.cv y) (syn_ctc (.cv y)) (syn_ctc (syn_cnc (syn_c1c))) (syn_clec) p0028
  have p0030 :=
    @g_mpbird (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_cnc (syn_c1c)))) (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_cnc (syn_c1c)))) p0027 p0029
  have p0031 :=
    @g_simpl (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))
  have p0032 :=
    @g_simpld (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y)) p0031
  have p0033 :=
    @g_hwcardssnc (syn_cvv)
  have p0034 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (.cv y) p0033
  have p0035 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.classMem (.cv y) (syn_cncs)) p0032 p0034
  have p0036 :=
    @g_n_1cex
  have p0037 :=
    @g_ncelncsi (syn_c1c) p0036
  have p0038 :=
    @g_tccl (syn_cnc (syn_c1c))
  have p0039 :=
    Nominal.mp p0037 p0038
  have p0040 :=
    @g_a1i (.classMem (syn_ctc (syn_cnc (syn_c1c))) (syn_cncs)) (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) p0039
  have p0041 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.classMem (.cv y) (syn_cncs)) (.classMem (syn_ctc (syn_cnc (syn_c1c))) (syn_cncs)) p0035 p0040
  have p0042 :=
    @g_tlecg (.cv y) (syn_ctc (syn_cnc (syn_c1c)))
  have p0043 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (syn_wa (.classMem (.cv y) (syn_cncs)) (.classMem (syn_ctc (syn_cnc (syn_c1c))) (syn_cncs))) (syn_wb (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_cnc (syn_c1c)))) (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))) p0041 p0042
  have p0044 :=
    @g_mpbid (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_cnc (syn_c1c)))) (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))) p0030 p0043
  have p0045 :=
    @g_simpr (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))
  have p0046 :=
    @g_breq1d (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.cv y) (syn_ctc (.cv y)) (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))) (syn_clec) p0045
  have p0047 :=
    @g_mpbird (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))) (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))) p0044 p0046
  have p0048 :=
    @g_simpl (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))
  have p0049 :=
    @g_simpld (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y)) p0048
  have p0050 :=
    @g_hwcardssnc (syn_cvv)
  have p0051 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (.cv y) p0050
  have p0052 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.classMem (.cv y) (syn_cncs)) p0049 p0051
  have p0053 :=
    @g_n_1cex
  have p0054 :=
    @g_ncelncsi (syn_c1c) p0053
  have p0055 :=
    @g_tccl (syn_cnc (syn_c1c))
  have p0056 :=
    Nominal.mp p0054 p0055
  have p0057 :=
    @g_tccl (syn_ctc (syn_cnc (syn_c1c)))
  have p0058 :=
    Nominal.mp p0056 p0057
  have p0059 :=
    @g_a1i (.classMem (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))) (syn_cncs)) (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) p0058
  have p0060 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.classMem (.cv y) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))) (syn_cncs)) p0052 p0059
  have p0061 :=
    @g_tlecg (.cv y) (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))
  have p0062 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (syn_wa (.classMem (.cv y) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))) (syn_cncs))) (syn_wb (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))) (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))) p0060 p0061
  have p0063 :=
    @g_mpbid (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))) (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))) p0047 p0062
  have p0064 :=
    @g_simpr (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))
  have p0065 :=
    @g_breq1d (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.cv y) (syn_ctc (.cv y)) (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))) (syn_clec) p0064
  have p0066 :=
    @g_mpbird (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))) (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))) p0063 p0065
  have p0067 :=
    @g_simpl (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))
  have p0068 :=
    @g_simpld (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y)) p0067
  have p0069 :=
    @g_hwcardssnc (syn_cvv)
  have p0070 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (.cv y) p0069
  have p0071 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.classMem (.cv y) (syn_cncs)) p0068 p0070
  have p0072 :=
    @g_n_1cex
  have p0073 :=
    @g_ncelncsi (syn_c1c) p0072
  have p0074 :=
    @g_tccl (syn_cnc (syn_c1c))
  have p0075 :=
    Nominal.mp p0073 p0074
  have p0076 :=
    @g_tccl (syn_ctc (syn_cnc (syn_c1c)))
  have p0077 :=
    Nominal.mp p0075 p0076
  have p0078 :=
    @g_tccl (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))
  have p0079 :=
    Nominal.mp p0077 p0078
  have p0080 :=
    @g_a1i (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))) (syn_cncs)) (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) p0079
  have p0081 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.classMem (.cv y) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))) (syn_cncs)) p0071 p0080
  have p0082 :=
    @g_tlecg (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))
  have p0083 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (syn_wa (.classMem (.cv y) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))) (syn_cncs))) (syn_wb (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))) (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))) p0081 p0082
  have p0084 :=
    @g_mpbid (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))) (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))) p0066 p0083
  have p0085 :=
    @g_simpr (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))
  have p0086 :=
    @g_breq1d (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.cv y) (syn_ctc (.cv y)) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))) (syn_clec) p0085
  have p0087 :=
    @g_mpbird (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))) (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))) p0084 p0086
  have p0088 :=
    @g_simpl (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))
  have p0089 :=
    @g_simpld (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y)) p0088
  have p0090 :=
    @g_hwcardssnc (syn_cvv)
  have p0091 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (.cv y) p0090
  have p0092 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.classMem (.cv y) (syn_cncs)) p0089 p0091
  have p0093 :=
    @g_n_1cex
  have p0094 :=
    @g_ncelncsi (syn_c1c) p0093
  have p0095 :=
    @g_tccl (syn_cnc (syn_c1c))
  have p0096 :=
    Nominal.mp p0094 p0095
  have p0097 :=
    @g_tccl (syn_ctc (syn_cnc (syn_c1c)))
  have p0098 :=
    Nominal.mp p0096 p0097
  have p0099 :=
    @g_tccl (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))
  have p0100 :=
    Nominal.mp p0098 p0099
  have p0101 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))
  have p0102 :=
    Nominal.mp p0100 p0101
  have p0103 :=
    @g_a1i (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))) (syn_cncs)) (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) p0102
  have p0104 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.classMem (.cv y) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))) (syn_cncs)) p0092 p0103
  have p0105 :=
    @g_tlecg (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))
  have p0106 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (syn_wa (.classMem (.cv y) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))) (syn_cncs))) (syn_wb (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))) (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))) p0104 p0105
  have p0107 :=
    @g_mpbid (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))) (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))) p0087 p0106
  have p0108 :=
    @g_simpr (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))
  have p0109 :=
    @g_breq1d (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.cv y) (syn_ctc (.cv y)) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))) (syn_clec) p0108
  have p0110 :=
    @g_mpbird (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))) (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))) p0107 p0109
  have p0111 :=
    @g_simpl (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))
  have p0112 :=
    @g_simpld (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y)) p0111
  have p0113 :=
    @g_hwcardssnc (syn_cvv)
  have p0114 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (.cv y) p0113
  have p0115 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.classMem (.cv y) (syn_cncs)) p0112 p0114
  have p0116 :=
    @g_n_1cex
  have p0117 :=
    @g_ncelncsi (syn_c1c) p0116
  have p0118 :=
    @g_tccl (syn_cnc (syn_c1c))
  have p0119 :=
    Nominal.mp p0117 p0118
  have p0120 :=
    @g_tccl (syn_ctc (syn_cnc (syn_c1c)))
  have p0121 :=
    Nominal.mp p0119 p0120
  have p0122 :=
    @g_tccl (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))
  have p0123 :=
    Nominal.mp p0121 p0122
  have p0124 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))
  have p0125 :=
    Nominal.mp p0123 p0124
  have p0126 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))
  have p0127 :=
    Nominal.mp p0125 p0126
  have p0128 :=
    @g_a1i (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))) (syn_cncs)) (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) p0127
  have p0129 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.classMem (.cv y) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))) (syn_cncs)) p0115 p0128
  have p0130 :=
    @g_tlecg (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))
  have p0131 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (syn_wa (.classMem (.cv y) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))) (syn_cncs))) (syn_wb (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))) (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))))) p0129 p0130
  have p0132 :=
    @g_mpbid (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))) (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))) p0110 p0131
  have p0133 :=
    @g_simpr (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))
  have p0134 :=
    @g_breq1d (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.cv y) (syn_ctc (.cv y)) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))) (syn_clec) p0133
  have p0135 :=
    @g_mpbird (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))) (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))) p0132 p0134
  have p0136 :=
    @g_simpl (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))
  have p0137 :=
    @g_simpld (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y)) p0136
  have p0138 :=
    @g_hwcardssnc (syn_cvv)
  have p0139 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (.cv y) p0138
  have p0140 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.classMem (.cv y) (syn_cncs)) p0137 p0139
  have p0141 :=
    @g_n_1cex
  have p0142 :=
    @g_ncelncsi (syn_c1c) p0141
  have p0143 :=
    @g_tccl (syn_cnc (syn_c1c))
  have p0144 :=
    Nominal.mp p0142 p0143
  have p0145 :=
    @g_tccl (syn_ctc (syn_cnc (syn_c1c)))
  have p0146 :=
    Nominal.mp p0144 p0145
  have p0147 :=
    @g_tccl (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))
  have p0148 :=
    Nominal.mp p0146 p0147
  have p0149 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))
  have p0150 :=
    Nominal.mp p0148 p0149
  have p0151 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))
  have p0152 :=
    Nominal.mp p0150 p0151
  have p0153 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))
  have p0154 :=
    Nominal.mp p0152 p0153
  have p0155 :=
    @g_a1i (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))) (syn_cncs)) (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) p0154
  have p0156 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.classMem (.cv y) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))) (syn_cncs)) p0140 p0155
  have p0157 :=
    @g_tlecg (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))
  have p0158 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (syn_wa (.classMem (.cv y) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))) (syn_cncs))) (syn_wb (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))) (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))))) p0156 p0157
  have p0159 :=
    @g_mpbid (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))) (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))))) p0135 p0158
  have p0160 :=
    @g_simpr (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))
  have p0161 :=
    @g_breq1d (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.cv y) (syn_ctc (.cv y)) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))) (syn_clec) p0160
  have p0162 :=
    @g_mpbird (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))))) (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))))) p0159 p0161
  have p0163 :=
    @g_simpl (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))
  have p0164 :=
    @g_simpld (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y)) p0163
  have p0165 :=
    @g_hwcardssnc (syn_cvv)
  have p0166 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (.cv y) p0165
  have p0167 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.classMem (.cv y) (syn_cncs)) p0164 p0166
  have p0168 :=
    @g_n_1cex
  have p0169 :=
    @g_ncelncsi (syn_c1c) p0168
  have p0170 :=
    @g_tccl (syn_cnc (syn_c1c))
  have p0171 :=
    Nominal.mp p0169 p0170
  have p0172 :=
    @g_tccl (syn_ctc (syn_cnc (syn_c1c)))
  have p0173 :=
    Nominal.mp p0171 p0172
  have p0174 :=
    @g_tccl (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))
  have p0175 :=
    Nominal.mp p0173 p0174
  have p0176 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))
  have p0177 :=
    Nominal.mp p0175 p0176
  have p0178 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))
  have p0179 :=
    Nominal.mp p0177 p0178
  have p0180 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))
  have p0181 :=
    Nominal.mp p0179 p0180
  have p0182 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))
  have p0183 :=
    Nominal.mp p0181 p0182
  have p0184 :=
    @g_a1i (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))) (syn_cncs)) (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) p0183
  have p0185 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.classMem (.cv y) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))) (syn_cncs)) p0167 p0184
  have p0186 :=
    @g_tlecg (.cv y) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))))
  have p0187 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (syn_wa (.classMem (.cv y) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))) (syn_cncs))) (syn_wb (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))))) (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))))))) p0185 p0186
  have p0188 :=
    @g_mpbid (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))))) (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))))) p0162 p0187
  have p0189 :=
    @g_simpr (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))
  have p0190 :=
    @g_breq1d (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.cv y) (syn_ctc (.cv y)) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))))) (syn_clec) p0189
  have p0191 :=
    @g_mpbird (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))))) (syn_wbr (syn_ctc (.cv y)) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))))) p0188 p0190
  have p0192 :=
    @g_tcnc1c
  have p0193 :=
    @g_tceq (syn_ctc (syn_cnc (syn_c1c))) (syn_cnc (syn_cpw1 (syn_c1c)))
  have p0194 :=
    Nominal.mp p0192 p0193
  have p0195 :=
    @g_n_1cex
  have p0196 :=
    @g_pw1ex (syn_c1c) p0195
  have p0197 :=
    @g_tcnc (syn_cpw1 (syn_c1c)) p0196
  have p0198 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))) (syn_ctc (syn_cnc (syn_cpw1 (syn_c1c)))) (syn_cnc (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0194 p0197
  have p0199 :=
    @g_tceq (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))) (syn_cnc (syn_cpw1 (syn_cpw1 (syn_c1c))))
  have p0200 :=
    Nominal.mp p0198 p0199
  have p0201 :=
    @g_n_1cex
  have p0202 :=
    @g_pw1ex (syn_c1c) p0201
  have p0203 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0202
  have p0204 :=
    @g_tcnc (syn_cpw1 (syn_cpw1 (syn_c1c))) p0203
  have p0205 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))) (syn_ctc (syn_cnc (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0200 p0204
  have p0206 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))) (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
  have p0207 :=
    Nominal.mp p0205 p0206
  have p0208 :=
    @g_n_1cex
  have p0209 :=
    @g_pw1ex (syn_c1c) p0208
  have p0210 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0209
  have p0211 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0210
  have p0212 :=
    @g_tcnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0211
  have p0213 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))) (syn_ctc (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0207 p0212
  have p0214 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))) (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
  have p0215 :=
    Nominal.mp p0213 p0214
  have p0216 :=
    @g_n_1cex
  have p0217 :=
    @g_pw1ex (syn_c1c) p0216
  have p0218 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0217
  have p0219 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0218
  have p0220 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0219
  have p0221 :=
    @g_tcnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0220
  have p0222 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))) (syn_ctc (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) p0215 p0221
  have p0223 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))) (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
  have p0224 :=
    Nominal.mp p0222 p0223
  have p0225 :=
    @g_n_1cex
  have p0226 :=
    @g_pw1ex (syn_c1c) p0225
  have p0227 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0226
  have p0228 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0227
  have p0229 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0228
  have p0230 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0229
  have p0231 :=
    @g_tcnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0230
  have p0232 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))) (syn_ctc (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) p0224 p0231
  have p0233 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))) (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
  have p0234 :=
    Nominal.mp p0232 p0233
  have p0235 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))) (syn_ctc (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
  have p0236 :=
    Nominal.mp p0234 p0235
  have p0237 :=
    @g_breq2i (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c)))))))))) (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (.cv y) (syn_clec) p0236
  have p0238 :=
    @g_sylib (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_c1c))))))))))) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) p0191 p0237
  have p0239 :=
    @g_jca (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y)) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) p0005 p0238
  have p0240 :=
    @g_hncardnc1ndv
  have p0241 :=
    @g_tccl (syn_chncard (syn_c1c))
  have p0242 :=
    Nominal.mp p0240 p0241
  have p0243 :=
    @g_tccl (syn_ctc (syn_chncard (syn_c1c)))
  have p0244 :=
    Nominal.mp p0242 p0243
  have p0245 :=
    @g_tccl (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))
  have p0246 :=
    Nominal.mp p0244 p0245
  have p0247 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))
  have p0248 :=
    Nominal.mp p0246 p0247
  have p0249 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))
  have p0250 :=
    Nominal.mp p0248 p0249
  have p0251 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))
  have p0252 :=
    Nominal.mp p0250 p0251
  have p0253 :=
    @g_a1i (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_cncs)) (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) p0252
  have p0254 :=
    @g_simpl (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))
  have p0255 :=
    @g_simpld (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y)) p0254
  have p0256 :=
    @g_hwcardssnc (syn_cvv)
  have p0257 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (.cv y) p0256
  have p0258 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.classMem (.cv y) (syn_cncs)) p0255 p0257
  have p0259 :=
    @g_n_1cex
  have p0260 :=
    @g_pw1ex (syn_c1c) p0259
  have p0261 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0260
  have p0262 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0261
  have p0263 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0262
  have p0264 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0263
  have p0265 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0264
  have p0266 :=
    @g_ncelncsi (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) p0265
  have p0267 :=
    @g_tccl (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
  have p0268 :=
    Nominal.mp p0266 p0267
  have p0269 :=
    @g_tccl (syn_ctc (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
  have p0270 :=
    Nominal.mp p0268 p0269
  have p0271 :=
    @g_a1i (.classMem (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_cncs)) (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) p0270
  have p0272 :=
    @g_n_3jca (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_cncs)) (.classMem (.cv y) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_cncs)) p0253 p0258 p0271
  have p0273 :=
    @g_lectr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (.cv y) (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
  have p0274 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (syn_w3a (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_cncs)) (.classMem (.cv y) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_cncs))) (.imp (syn_wa (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y)) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) p0272 p0273
  have p0275 :=
    @g_mpd (syn_wa (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y)))) (syn_wa (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y)) (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) p0239 p0274
  have p0276 :=
    @g_ex (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) p0275
  have p0277 :=
    @g_mtod (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (.classEq (.cv y) (syn_ctc (.cv y))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) p0003 p0276
  have p0278 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (.cv y) (syn_ctc (.cv y)))))
  have p0279 :=
    @g_a1i (syn_wb (syn_wne (.cv y) (syn_ctc (.cv y))) (.neg (.classEq (.cv y) (syn_ctc (.cv y))))) (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) p0278
  have p0280 :=
    @g_mpbird (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y))) (syn_wne (.cv y) (syn_ctc (.cv y))) (.neg (.classEq (.cv y) (syn_ctc (.cv y)))) p0277 p0279
  have p0281 :=
    @g_ex (.classMem (.cv y) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y)) (syn_wne (.cv y) (syn_ctc (.cv y))) p0280
  have p0282 :=
    @g_rgen (.imp (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (.cv y)) (syn_wne (.cv y) (syn_ctc (.cv y)))) y (syn_chwcards (syn_cvv)) p0281
  exact p0282

noncomputable def g_wppconcrete6rnhwcardsndv
     :
    Nominal.NPrf (syn_wss (syn_crn (syn_cwppconcrete6fn)) (syn_chwcards (syn_cvv))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have p0000 :=
    @g_pwexg (.cv u) (syn_cvv)
  have p0001 :=
    @g_pwexg (syn_cpw (.cv u)) (syn_cvv)
  have p0002 :=
    @g_syl (.classMem (.cv u) (syn_cvv)) (.classMem (syn_cpw (.cv u)) (syn_cvv)) (.classMem (syn_cpw (syn_cpw (.cv u))) (syn_cvv)) p0000 p0001
  have p0003 :=
    @g_hnordexg (syn_cpw (syn_cpw (.cv u)))
  have p0004 :=
    @g_syl (.classMem (.cv u) (syn_cvv)) (.classMem (syn_cpw (syn_cpw (.cv u))) (syn_cvv)) (.classMem (syn_chnord (syn_cpw (syn_cpw (.cv u)))) (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_hncardhwcardsndv (syn_chnord (syn_cpw (syn_cpw (.cv u))))
  have p0006 :=
    @g_syl (.classMem (.cv u) (syn_cvv)) (.classMem (syn_chnord (syn_cpw (syn_cpw (.cv u)))) (syn_cvv)) (.classMem (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv u))))) (syn_chwcards (syn_cvv))) p0004 p0005
  have p0007 :=
    @g_rgen (.classMem (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv u))))) (syn_chwcards (syn_cvv))) u (syn_cvv) p0006
  have p0008 :=
    @g_wppconcrete6rnhwcardsredndv u p0007
  exact p0008

noncomputable def g_wppconcrete6thresholdhwcardsndv
     :
    Nominal.NPrf (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_chwcards (syn_cvv))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_hncardtc6oneeqndv
  have p0001 :=
    @g_n_1cex
  have p0002 :=
    @g_pw1ex (syn_c1c) p0001
  have p0003 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0002
  have p0004 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0003
  have p0005 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0004
  have p0006 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0005
  have p0007 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0006
  have p0008 :=
    @g_hncardhwcardsndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_eqeltri (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_chwcards (syn_cvv)) p0000 p0009
  exact p0010

noncomputable def g_wppconcrete6stoppedtchomfullndv
    (x : Var) :
    Nominal.NPrf (syn_wral x (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (.classEq (syn_ctc (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.cv x))) (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_ctc (.cv x))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var)
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_ne_x : u ≠ x := by
    intro h
    exact fresh_u (Finset.mem_singleton.mpr h)
  have fresh_x_ne_u : x ≠ u :=
    Ne.symm fresh_u_ne_x
  have p0000 :=
    @g_pwexg (.cv u) (syn_cvv)
  have p0001 :=
    @g_pwexg (syn_cpw (.cv u)) (syn_cvv)
  have p0002 :=
    @g_syl (.classMem (.cv u) (syn_cvv)) (.classMem (syn_cpw (.cv u)) (syn_cvv)) (.classMem (syn_cpw (syn_cpw (.cv u))) (syn_cvv)) p0000 p0001
  have p0003 :=
    @g_hnordexg (syn_cpw (syn_cpw (.cv u)))
  have p0004 :=
    @g_syl (.classMem (.cv u) (syn_cvv)) (.classMem (syn_cpw (syn_cpw (.cv u))) (syn_cvv)) (.classMem (syn_chnord (syn_cpw (syn_cpw (.cv u)))) (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_hncardhwcardsndv (syn_chnord (syn_cpw (syn_cpw (.cv u))))
  have p0006 :=
    @g_syl (.classMem (.cv u) (syn_cvv)) (.classMem (syn_chnord (syn_cpw (syn_cpw (.cv u)))) (syn_cvv)) (.classMem (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv u))))) (syn_chwcards (syn_cvv))) p0004 p0005
  have p0007 :=
    @g_rgen (.classMem (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv u))))) (syn_chwcards (syn_cvv))) u (syn_cvv) p0006
  have p0008 :=
    @g_wppconcrete6rnhwcardsredndv u p0007
  have p0009 :=
    @g_hncardtc6oneeqndv
  have p0010 :=
    @g_n_1cex
  have p0011 :=
    @g_pw1ex (syn_c1c) p0010
  have p0012 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0011
  have p0013 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0012
  have p0014 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0013
  have p0015 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0014
  have p0016 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0015
  have p0017 :=
    @g_hncardhwcardsndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
  have p0018 :=
    Nominal.mp p0016 p0017
  have p0019 :=
    @g_eqeltri (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_chwcards (syn_cvv)) p0009 p0018
  have p0020 :=
    @g_wppconcrete6stoppedtchomndv x p0008 p0019
  exact p0020

#print axioms g_wppconcrete6stoppedtchomfullndv

end NFChoice.DirectNominalPrf.WPPReplay
