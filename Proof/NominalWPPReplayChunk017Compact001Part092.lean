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
import NominalWPPReplayChunk017Compact001Part091

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

noncomputable def g_cfbhnpw13genericquotrepcohndv
    (C : Class) (Q : Class) (X : Class) (hyp_cfbhnpw13genericquotrepcohndv_1 : Nominal.NPrf (.classMem X (syn_cvv))) (hyp_cfbhnpw13genericquotrepcohndv_2 : Nominal.NPrf (.classMem C (syn_chwcn (syn_cpw X)))) (hyp_cfbhnpw13genericquotrepcohndv_3 : Nominal.NPrf (.classMem Q (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))))) (hyp_cfbhnpw13genericquotrepcohndv_4 : Nominal.NPrf (.classEq (syn_cuni (syn_cuni (syn_cuni Q))) (syn_cec C (syn_chwniso (syn_cpw X))))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))) Q) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))) (syn_chwniso (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X))))))) := by
  let proofSupport : Finset Var := C.fv ∪ Q.fv ∪ X.fv
  have p0000 :=
    @g_pwex X hyp_cfbhnpw13genericquotrepcohndv_1
  have p0001 :=
    @g_pw1ex (syn_cpw X) p0000
  have p0002 :=
    @g_hnsiquomapfndv (syn_cpw1 (syn_cpw X)) p0001
  have p0003 :=
    @g_sifmap (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw X)))) (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))
  have p0004 :=
    Nominal.mp p0002 p0003
  have p0005 :=
    @g_pwex X hyp_cfbhnpw13genericquotrepcohndv_1
  have p0006 :=
    @g_hnsiquomapfndv (syn_cpw X) p0005
  have p0007 :=
    @g_sifmap (syn_cpw1 (syn_chnord (syn_cpw X))) (syn_chnord (syn_cpw1 (syn_cpw X))) (syn_chnsiquomap (syn_cpw X))
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))) (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_chnsiquomap (syn_cpw X)))
  have p0010 :=
    Nominal.mp p0008 p0009
  have p0011 :=
    @g_pm3_2i (syn_wf (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw X))))) (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw X)))))) (syn_wf (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw X)))))) p0004 p0010
  have p0012 :=
    @g_fco (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw X))))) (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw X))))) (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))
  have p0013 :=
    Nominal.mp p0011 p0012
  have p0014 :=
    @g_pm3_2i (syn_wf (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw X)))))) (.classMem Q (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) p0013 hyp_cfbhnpw13genericquotrepcohndv_3
  have p0015 :=
    @g_fvco3 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw X))))) Q (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))
  have p0016 :=
    Nominal.mp p0014 p0015
  have p0017 :=
    @g_pwex X hyp_cfbhnpw13genericquotrepcohndv_1
  have p0018 :=
    @g_hnsiquomapfndv (syn_cpw X) p0017
  have p0019 :=
    @g_sifmap (syn_cpw1 (syn_chnord (syn_cpw X))) (syn_chnord (syn_cpw1 (syn_cpw X))) (syn_chnsiquomap (syn_cpw X))
  have p0020 :=
    Nominal.mp p0018 p0019
  have p0021 :=
    @g_sifmap (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))) (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_chnsiquomap (syn_cpw X)))
  have p0022 :=
    Nominal.mp p0020 p0021
  have p0023 :=
    @g_pm3_2i (syn_wf (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw X)))))) (.classMem Q (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))))) p0022 hyp_cfbhnpw13genericquotrepcohndv_3
  have p0024 :=
    @g_fvco3 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw X))))) Q (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))
  have p0025 :=
    Nominal.mp p0023 p0024
  have p0026 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))) Q
  have p0027 :=
    Nominal.mp hyp_cfbhnpw13genericquotrepcohndv_3 p0026
  have p0028 :=
    @g_simpr (.classMem (syn_cuni Q) (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (.classEq Q (syn_csn (syn_cuni Q)))
  have p0029 :=
    Nominal.mp p0027 p0028
  have p0030 :=
    @g_fveq2i Q (syn_csn (syn_cuni Q)) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))) p0029
  have p0031 :=
    @g_pwex X hyp_cfbhnpw13genericquotrepcohndv_1
  have p0032 :=
    @g_hnsiquomapfndv (syn_cpw X) p0031
  have p0033 :=
    @g_sifmap (syn_cpw1 (syn_chnord (syn_cpw X))) (syn_chnord (syn_cpw1 (syn_cpw X))) (syn_chnsiquomap (syn_cpw X))
  have p0034 :=
    Nominal.mp p0032 p0033
  have p0035 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))) Q
  have p0036 :=
    Nominal.mp hyp_cfbhnpw13genericquotrepcohndv_3 p0035
  have p0037 :=
    @g_simpl (.classMem (syn_cuni Q) (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (.classEq Q (syn_csn (syn_cuni Q)))
  have p0038 :=
    Nominal.mp p0036 p0037
  have p0039 :=
    @g_pm3_2i (syn_wf (syn_csi (syn_chnsiquomap (syn_cpw X))) (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))) (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw X))))) (.classMem (syn_cuni Q) (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) p0034 p0038
  have p0040 :=
    @g_sifvalimpclndv (syn_cuni Q) (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))) (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_chnsiquomap (syn_cpw X)))
  have p0041 :=
    Nominal.mp p0039 p0040
  have p0042 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))) Q
  have p0043 :=
    Nominal.mp hyp_cfbhnpw13genericquotrepcohndv_3 p0042
  have p0044 :=
    @g_simpl (.classMem (syn_cuni Q) (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (.classEq Q (syn_csn (syn_cuni Q)))
  have p0045 :=
    Nominal.mp p0043 p0044
  have p0046 :=
    @g_pw1argclcl (syn_cpw1 (syn_chnord (syn_cpw X))) (syn_cuni Q)
  have p0047 :=
    Nominal.mp p0045 p0046
  have p0048 :=
    @g_simpr (.classMem (syn_cuni (syn_cuni Q)) (syn_cpw1 (syn_chnord (syn_cpw X)))) (.classEq (syn_cuni Q) (syn_csn (syn_cuni (syn_cuni Q))))
  have p0049 :=
    Nominal.mp p0047 p0048
  have p0050 :=
    @g_fveq2i (syn_cuni Q) (syn_csn (syn_cuni (syn_cuni Q))) (syn_csi (syn_chnsiquomap (syn_cpw X))) p0049
  have p0051 :=
    @g_pwex X hyp_cfbhnpw13genericquotrepcohndv_1
  have p0052 :=
    @g_hnsiquomapfndv (syn_cpw X) p0051
  have p0053 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))) Q
  have p0054 :=
    Nominal.mp hyp_cfbhnpw13genericquotrepcohndv_3 p0053
  have p0055 :=
    @g_simpl (.classMem (syn_cuni Q) (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (.classEq Q (syn_csn (syn_cuni Q)))
  have p0056 :=
    Nominal.mp p0054 p0055
  have p0057 :=
    @g_pw1argclcl (syn_cpw1 (syn_chnord (syn_cpw X))) (syn_cuni Q)
  have p0058 :=
    Nominal.mp p0056 p0057
  have p0059 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni Q)) (syn_cpw1 (syn_chnord (syn_cpw X)))) (.classEq (syn_cuni Q) (syn_csn (syn_cuni (syn_cuni Q))))
  have p0060 :=
    Nominal.mp p0058 p0059
  have p0061 :=
    @g_pm3_2i (syn_wf (syn_chnsiquomap (syn_cpw X)) (syn_cpw1 (syn_chnord (syn_cpw X))) (syn_chnord (syn_cpw1 (syn_cpw X)))) (.classMem (syn_cuni (syn_cuni Q)) (syn_cpw1 (syn_chnord (syn_cpw X)))) p0052 p0060
  have p0062 :=
    @g_sifvalimpclndv (syn_cuni (syn_cuni Q)) (syn_cpw1 (syn_chnord (syn_cpw X))) (syn_chnord (syn_cpw1 (syn_cpw X))) (syn_chnsiquomap (syn_cpw X))
  have p0063 :=
    Nominal.mp p0061 p0062
  have p0064 :=
    @g_eqtri (syn_cfv (syn_csi (syn_chnsiquomap (syn_cpw X))) (syn_cuni Q)) (syn_cfv (syn_csi (syn_chnsiquomap (syn_cpw X))) (syn_csn (syn_cuni (syn_cuni Q)))) (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))) p0050 p0063
  have p0065 :=
    @g_sneqi (syn_cfv (syn_csi (syn_chnsiquomap (syn_cpw X))) (syn_cuni Q)) (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))) p0064
  have p0066 :=
    @g_eqtri (syn_cfv (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))) (syn_csn (syn_cuni Q))) (syn_csn (syn_cfv (syn_csi (syn_chnsiquomap (syn_cpw X))) (syn_cuni Q))) (syn_csn (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))))) p0041 p0065
  have p0067 :=
    @g_eqtri (syn_cfv (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))) Q) (syn_cfv (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))) (syn_csn (syn_cuni Q))) (syn_csn (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))))) p0030 p0066
  have p0068 :=
    @g_fveq2i (syn_cfv (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))) Q) (syn_csn (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))))) (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) p0067
  have p0069 :=
    @g_pwex X hyp_cfbhnpw13genericquotrepcohndv_1
  have p0070 :=
    @g_pw1ex (syn_cpw X) p0069
  have p0071 :=
    @g_hnsiquomapfndv (syn_cpw1 (syn_cpw X)) p0070
  have p0072 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))) Q
  have p0073 :=
    Nominal.mp hyp_cfbhnpw13genericquotrepcohndv_3 p0072
  have p0074 :=
    @g_simpl (.classMem (syn_cuni Q) (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (.classEq Q (syn_csn (syn_cuni Q)))
  have p0075 :=
    Nominal.mp p0073 p0074
  have p0076 :=
    @g_pw1argclcl (syn_cpw1 (syn_chnord (syn_cpw X))) (syn_cuni Q)
  have p0077 :=
    Nominal.mp p0075 p0076
  have p0078 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni Q)) (syn_cpw1 (syn_chnord (syn_cpw X)))) (.classEq (syn_cuni Q) (syn_csn (syn_cuni (syn_cuni Q))))
  have p0079 :=
    Nominal.mp p0077 p0078
  have p0080 :=
    @g_pm3_2i (.classMem C (syn_chwcn (syn_cpw X))) (.classEq (syn_cuni (syn_cuni (syn_cuni Q))) (syn_cec C (syn_chwniso (syn_cpw X)))) hyp_cfbhnpw13genericquotrepcohndv_2 hyp_cfbhnpw13genericquotrepcohndv_4
  have p0081 :=
    @g_pm3_2i (.classMem (syn_cuni (syn_cuni Q)) (syn_cpw1 (syn_chnord (syn_cpw X)))) (syn_wa (.classMem C (syn_chwcn (syn_cpw X))) (.classEq (syn_cuni (syn_cuni (syn_cuni Q))) (syn_cec C (syn_chwniso (syn_cpw X))))) p0079 p0080
  have p0082 :=
    @g_pwex X hyp_cfbhnpw13genericquotrepcohndv_1
  have p0083 :=
    @g_hnsiquomaprepvalcl3ndv (syn_cpw X) C (syn_cuni (syn_cuni Q)) p0082
  have p0084 :=
    Nominal.mp p0081 p0083
  have p0085 :=
    @g_snelpw1 C (syn_chwcn (syn_cpw X))
  have p0086 :=
    @g_mpbir (.classMem (syn_csn C) (syn_cpw1 (syn_chwcn (syn_cpw X)))) (.classMem C (syn_chwcn (syn_cpw X))) hyp_cfbhnpw13genericquotrepcohndv_2 p0085
  have p0087 :=
    @g_hnsicodemapfndv (syn_cpw X)
  have p0088 :=
    @g_ffvelrni (syn_cpw1 (syn_chwcn (syn_cpw X))) (syn_chwcn (syn_cpw1 (syn_cpw X))) (syn_csn C) (syn_chnsicodemap (syn_cpw X)) p0087
  have p0089 :=
    Nominal.mp p0086 p0088
  have p0090 :=
    @g_pwex X hyp_cfbhnpw13genericquotrepcohndv_1
  have p0091 :=
    @g_pw1ex (syn_cpw X) p0090
  have p0092 :=
    @g_hwnisoclasselhnordcl (syn_cpw1 (syn_cpw X)) (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) p0091
  have p0093 :=
    Nominal.mp p0089 p0092
  have p0094 :=
    @g_eqeltri (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwniso (syn_cpw1 (syn_cpw X)))) (syn_chnord (syn_cpw1 (syn_cpw X))) p0084 p0093
  have p0095 :=
    @g_snelpw1 (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))) (syn_chnord (syn_cpw1 (syn_cpw X)))
  have p0096 :=
    @g_mpbir (.classMem (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))) (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw X))))) (.classMem (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))) (syn_chnord (syn_cpw1 (syn_cpw X)))) p0094 p0095
  have p0097 :=
    @g_pm3_2i (syn_wf (syn_chnsiquomap (syn_cpw1 (syn_cpw X))) (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw X)))) (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw X))))) (.classMem (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))) (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw X))))) p0071 p0096
  have p0098 :=
    @g_sifvalimpclndv (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))) (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw X)))) (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))
  have p0099 :=
    Nominal.mp p0097 p0098
  have p0100 :=
    @g_eqtri (syn_cfv (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_cfv (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))) Q)) (syn_cfv (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csn (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))))) (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))))) p0068 p0099
  have p0101 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))) Q) (syn_cfv (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_cfv (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))) Q)) (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))))) p0025 p0100
  have p0102 :=
    @g_fveq2i (syn_cfv (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))) Q) (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))))) (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) p0101
  have p0103 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))) Q) (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_cfv (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X))))) Q)) (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))))))) p0016 p0102
  have p0104 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))) Q
  have p0105 :=
    Nominal.mp hyp_cfbhnpw13genericquotrepcohndv_3 p0104
  have p0106 :=
    @g_simpl (.classMem (syn_cuni Q) (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (.classEq Q (syn_csn (syn_cuni Q)))
  have p0107 :=
    Nominal.mp p0105 p0106
  have p0108 :=
    @g_pw1argclcl (syn_cpw1 (syn_chnord (syn_cpw X))) (syn_cuni Q)
  have p0109 :=
    Nominal.mp p0107 p0108
  have p0110 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni Q)) (syn_cpw1 (syn_chnord (syn_cpw X)))) (.classEq (syn_cuni Q) (syn_csn (syn_cuni (syn_cuni Q))))
  have p0111 :=
    Nominal.mp p0109 p0110
  have p0112 :=
    @g_pm3_2i (.classMem C (syn_chwcn (syn_cpw X))) (.classEq (syn_cuni (syn_cuni (syn_cuni Q))) (syn_cec C (syn_chwniso (syn_cpw X)))) hyp_cfbhnpw13genericquotrepcohndv_2 hyp_cfbhnpw13genericquotrepcohndv_4
  have p0113 :=
    @g_pm3_2i (.classMem (syn_cuni (syn_cuni Q)) (syn_cpw1 (syn_chnord (syn_cpw X)))) (syn_wa (.classMem C (syn_chwcn (syn_cpw X))) (.classEq (syn_cuni (syn_cuni (syn_cuni Q))) (syn_cec C (syn_chwniso (syn_cpw X))))) p0111 p0112
  have p0114 :=
    @g_pwex X hyp_cfbhnpw13genericquotrepcohndv_1
  have p0115 :=
    @g_hnsiquomaprepvalcl3ndv (syn_cpw X) C (syn_cuni (syn_cuni Q)) p0114
  have p0116 :=
    Nominal.mp p0113 p0115
  have p0117 :=
    @g_snelpw1 C (syn_chwcn (syn_cpw X))
  have p0118 :=
    @g_mpbir (.classMem (syn_csn C) (syn_cpw1 (syn_chwcn (syn_cpw X)))) (.classMem C (syn_chwcn (syn_cpw X))) hyp_cfbhnpw13genericquotrepcohndv_2 p0117
  have p0119 :=
    @g_hnsicodemapfndv (syn_cpw X)
  have p0120 :=
    @g_ffvelrni (syn_cpw1 (syn_chwcn (syn_cpw X))) (syn_chwcn (syn_cpw1 (syn_cpw X))) (syn_csn C) (syn_chnsicodemap (syn_cpw X)) p0119
  have p0121 :=
    Nominal.mp p0118 p0120
  have p0122 :=
    @g_pwex X hyp_cfbhnpw13genericquotrepcohndv_1
  have p0123 :=
    @g_pw1ex (syn_cpw X) p0122
  have p0124 :=
    @g_hwnisoclasselhnordcl (syn_cpw1 (syn_cpw X)) (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) p0123
  have p0125 :=
    Nominal.mp p0121 p0124
  have p0126 :=
    @g_eqeltri (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwniso (syn_cpw1 (syn_cpw X)))) (syn_chnord (syn_cpw1 (syn_cpw X))) p0116 p0125
  have p0127 :=
    @g_snelpw1 (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))) (syn_chnord (syn_cpw1 (syn_cpw X)))
  have p0128 :=
    @g_mpbir (.classMem (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))) (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw X))))) (.classMem (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))) (syn_chnord (syn_cpw1 (syn_cpw X)))) p0126 p0127
  have p0129 :=
    @g_snelpw1 C (syn_chwcn (syn_cpw X))
  have p0130 :=
    @g_mpbir (.classMem (syn_csn C) (syn_cpw1 (syn_chwcn (syn_cpw X)))) (.classMem C (syn_chwcn (syn_cpw X))) hyp_cfbhnpw13genericquotrepcohndv_2 p0129
  have p0131 :=
    @g_hnsicodemapfndv (syn_cpw X)
  have p0132 :=
    @g_ffvelrni (syn_cpw1 (syn_chwcn (syn_cpw X))) (syn_chwcn (syn_cpw1 (syn_cpw X))) (syn_csn C) (syn_chnsicodemap (syn_cpw X)) p0131
  have p0133 :=
    Nominal.mp p0130 p0132
  have p0134 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))) Q
  have p0135 :=
    Nominal.mp hyp_cfbhnpw13genericquotrepcohndv_3 p0134
  have p0136 :=
    @g_simpl (.classMem (syn_cuni Q) (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (.classEq Q (syn_csn (syn_cuni Q)))
  have p0137 :=
    Nominal.mp p0135 p0136
  have p0138 :=
    @g_pw1argclcl (syn_cpw1 (syn_chnord (syn_cpw X))) (syn_cuni Q)
  have p0139 :=
    Nominal.mp p0137 p0138
  have p0140 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni Q)) (syn_cpw1 (syn_chnord (syn_cpw X)))) (.classEq (syn_cuni Q) (syn_csn (syn_cuni (syn_cuni Q))))
  have p0141 :=
    Nominal.mp p0139 p0140
  have p0142 :=
    @g_pm3_2i (.classMem C (syn_chwcn (syn_cpw X))) (.classEq (syn_cuni (syn_cuni (syn_cuni Q))) (syn_cec C (syn_chwniso (syn_cpw X)))) hyp_cfbhnpw13genericquotrepcohndv_2 hyp_cfbhnpw13genericquotrepcohndv_4
  have p0143 :=
    @g_pm3_2i (.classMem (syn_cuni (syn_cuni Q)) (syn_cpw1 (syn_chnord (syn_cpw X)))) (syn_wa (.classMem C (syn_chwcn (syn_cpw X))) (.classEq (syn_cuni (syn_cuni (syn_cuni Q))) (syn_cec C (syn_chwniso (syn_cpw X))))) p0141 p0142
  have p0144 :=
    @g_pwex X hyp_cfbhnpw13genericquotrepcohndv_1
  have p0145 :=
    @g_hnsiquomaprepvalcl3ndv (syn_cpw X) C (syn_cuni (syn_cuni Q)) p0144
  have p0146 :=
    Nominal.mp p0143 p0145
  have p0147 :=
    @g_snelpw1 C (syn_chwcn (syn_cpw X))
  have p0148 :=
    @g_mpbir (.classMem (syn_csn C) (syn_cpw1 (syn_chwcn (syn_cpw X)))) (.classMem C (syn_chwcn (syn_cpw X))) hyp_cfbhnpw13genericquotrepcohndv_2 p0147
  have p0149 :=
    @g_hnsicodemapfndv (syn_cpw X)
  have p0150 :=
    @g_ffvelrni (syn_cpw1 (syn_chwcn (syn_cpw X))) (syn_chwcn (syn_cpw1 (syn_cpw X))) (syn_csn C) (syn_chnsicodemap (syn_cpw X)) p0149
  have p0151 :=
    Nominal.mp p0148 p0150
  have p0152 :=
    @g_pwex X hyp_cfbhnpw13genericquotrepcohndv_1
  have p0153 :=
    @g_pw1ex (syn_cpw X) p0152
  have p0154 :=
    @g_hwnisoclasselhnordcl (syn_cpw1 (syn_cpw X)) (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) p0153
  have p0155 :=
    Nominal.mp p0151 p0154
  have p0156 :=
    @g_eqeltri (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwniso (syn_cpw1 (syn_cpw X)))) (syn_chnord (syn_cpw1 (syn_cpw X))) p0146 p0155
  have p0157 :=
    @g_elex (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))) (syn_chnord (syn_cpw1 (syn_cpw X)))
  have p0158 :=
    Nominal.mp p0156 p0157
  have p0159 :=
    @g_unisn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))) p0158
  have p0160 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))) Q
  have p0161 :=
    Nominal.mp hyp_cfbhnpw13genericquotrepcohndv_3 p0160
  have p0162 :=
    @g_simpl (.classMem (syn_cuni Q) (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (.classEq Q (syn_csn (syn_cuni Q)))
  have p0163 :=
    Nominal.mp p0161 p0162
  have p0164 :=
    @g_pw1argclcl (syn_cpw1 (syn_chnord (syn_cpw X))) (syn_cuni Q)
  have p0165 :=
    Nominal.mp p0163 p0164
  have p0166 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni Q)) (syn_cpw1 (syn_chnord (syn_cpw X)))) (.classEq (syn_cuni Q) (syn_csn (syn_cuni (syn_cuni Q))))
  have p0167 :=
    Nominal.mp p0165 p0166
  have p0168 :=
    @g_pm3_2i (.classMem C (syn_chwcn (syn_cpw X))) (.classEq (syn_cuni (syn_cuni (syn_cuni Q))) (syn_cec C (syn_chwniso (syn_cpw X)))) hyp_cfbhnpw13genericquotrepcohndv_2 hyp_cfbhnpw13genericquotrepcohndv_4
  have p0169 :=
    @g_pm3_2i (.classMem (syn_cuni (syn_cuni Q)) (syn_cpw1 (syn_chnord (syn_cpw X)))) (syn_wa (.classMem C (syn_chwcn (syn_cpw X))) (.classEq (syn_cuni (syn_cuni (syn_cuni Q))) (syn_cec C (syn_chwniso (syn_cpw X))))) p0167 p0168
  have p0170 :=
    @g_pwex X hyp_cfbhnpw13genericquotrepcohndv_1
  have p0171 :=
    @g_hnsiquomaprepvalcl3ndv (syn_cpw X) C (syn_cuni (syn_cuni Q)) p0170
  have p0172 :=
    Nominal.mp p0169 p0171
  have p0173 :=
    @g_eqtri (syn_cuni (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))))) (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwniso (syn_cpw1 (syn_cpw X)))) p0159 p0172
  have p0174 :=
    @g_pm3_2i (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwcn (syn_cpw1 (syn_cpw X)))) (.classEq (syn_cuni (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))))) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwniso (syn_cpw1 (syn_cpw X))))) p0133 p0173
  have p0175 :=
    @g_pm3_2i (.classMem (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))) (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw X))))) (syn_wa (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwcn (syn_cpw1 (syn_cpw X)))) (.classEq (syn_cuni (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))))) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwniso (syn_cpw1 (syn_cpw X)))))) p0128 p0174
  have p0176 :=
    @g_pwex X hyp_cfbhnpw13genericquotrepcohndv_1
  have p0177 :=
    @g_pw1ex (syn_cpw X) p0176
  have p0178 :=
    @g_hnsiquomaprepvalcl3ndv (syn_cpw1 (syn_cpw X)) (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))) p0177
  have p0179 :=
    Nominal.mp p0175 p0178
  have p0180 :=
    @g_snelpw1 C (syn_chwcn (syn_cpw X))
  have p0181 :=
    @g_mpbir (.classMem (syn_csn C) (syn_cpw1 (syn_chwcn (syn_cpw X)))) (.classMem C (syn_chwcn (syn_cpw X))) hyp_cfbhnpw13genericquotrepcohndv_2 p0180
  have p0182 :=
    @g_hnsicodemapfndv (syn_cpw X)
  have p0183 :=
    @g_ffvelrni (syn_cpw1 (syn_chwcn (syn_cpw X))) (syn_chwcn (syn_cpw1 (syn_cpw X))) (syn_csn C) (syn_chnsicodemap (syn_cpw X)) p0182
  have p0184 :=
    Nominal.mp p0181 p0183
  have p0185 :=
    @g_snelpw1 (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwcn (syn_cpw1 (syn_cpw X)))
  have p0186 :=
    @g_mpbir (.classMem (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))) (syn_cpw1 (syn_chwcn (syn_cpw1 (syn_cpw X))))) (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwcn (syn_cpw1 (syn_cpw X)))) p0184 p0185
  have p0187 :=
    @g_hnsicodemapfndv (syn_cpw1 (syn_cpw X))
  have p0188 :=
    @g_ffvelrni (syn_cpw1 (syn_chwcn (syn_cpw1 (syn_cpw X)))) (syn_chwcn (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))) (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) p0187
  have p0189 :=
    Nominal.mp p0186 p0188
  have p0190 :=
    @g_pwex X hyp_cfbhnpw13genericquotrepcohndv_1
  have p0191 :=
    @g_pw1ex (syn_cpw X) p0190
  have p0192 :=
    @g_pw1ex (syn_cpw1 (syn_cpw X)) p0191
  have p0193 :=
    @g_hwnisoclasselhnordcl (syn_cpw1 (syn_cpw1 (syn_cpw X))) (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))) p0192
  have p0194 :=
    Nominal.mp p0189 p0193
  have p0195 :=
    @g_eqeltri (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))))) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))) (syn_chwniso (syn_cpw1 (syn_cpw1 (syn_cpw X))))) (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw X)))) p0179 p0194
  have p0196 :=
    @g_snelpw1 (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))))) (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw X))))
  have p0197 :=
    @g_mpbir (.classMem (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))))) (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw X)))))) (.classMem (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))))) (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw X))))) p0195 p0196
  have p0198 :=
    @g_snelpw1 C (syn_chwcn (syn_cpw X))
  have p0199 :=
    @g_mpbir (.classMem (syn_csn C) (syn_cpw1 (syn_chwcn (syn_cpw X)))) (.classMem C (syn_chwcn (syn_cpw X))) hyp_cfbhnpw13genericquotrepcohndv_2 p0198
  have p0200 :=
    @g_hnsicodemapfndv (syn_cpw X)
  have p0201 :=
    @g_ffvelrni (syn_cpw1 (syn_chwcn (syn_cpw X))) (syn_chwcn (syn_cpw1 (syn_cpw X))) (syn_csn C) (syn_chnsicodemap (syn_cpw X)) p0200
  have p0202 :=
    Nominal.mp p0199 p0201
  have p0203 :=
    @g_snelpw1 (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwcn (syn_cpw1 (syn_cpw X)))
  have p0204 :=
    @g_mpbir (.classMem (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))) (syn_cpw1 (syn_chwcn (syn_cpw1 (syn_cpw X))))) (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwcn (syn_cpw1 (syn_cpw X)))) p0202 p0203
  have p0205 :=
    @g_hnsicodemapfndv (syn_cpw1 (syn_cpw X))
  have p0206 :=
    @g_ffvelrni (syn_cpw1 (syn_chwcn (syn_cpw1 (syn_cpw X)))) (syn_chwcn (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))) (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) p0205
  have p0207 :=
    Nominal.mp p0204 p0206
  have p0208 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))) Q
  have p0209 :=
    Nominal.mp hyp_cfbhnpw13genericquotrepcohndv_3 p0208
  have p0210 :=
    @g_simpl (.classMem (syn_cuni Q) (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (.classEq Q (syn_csn (syn_cuni Q)))
  have p0211 :=
    Nominal.mp p0209 p0210
  have p0212 :=
    @g_pw1argclcl (syn_cpw1 (syn_chnord (syn_cpw X))) (syn_cuni Q)
  have p0213 :=
    Nominal.mp p0211 p0212
  have p0214 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni Q)) (syn_cpw1 (syn_chnord (syn_cpw X)))) (.classEq (syn_cuni Q) (syn_csn (syn_cuni (syn_cuni Q))))
  have p0215 :=
    Nominal.mp p0213 p0214
  have p0216 :=
    @g_pm3_2i (.classMem C (syn_chwcn (syn_cpw X))) (.classEq (syn_cuni (syn_cuni (syn_cuni Q))) (syn_cec C (syn_chwniso (syn_cpw X)))) hyp_cfbhnpw13genericquotrepcohndv_2 hyp_cfbhnpw13genericquotrepcohndv_4
  have p0217 :=
    @g_pm3_2i (.classMem (syn_cuni (syn_cuni Q)) (syn_cpw1 (syn_chnord (syn_cpw X)))) (syn_wa (.classMem C (syn_chwcn (syn_cpw X))) (.classEq (syn_cuni (syn_cuni (syn_cuni Q))) (syn_cec C (syn_chwniso (syn_cpw X))))) p0215 p0216
  have p0218 :=
    @g_pwex X hyp_cfbhnpw13genericquotrepcohndv_1
  have p0219 :=
    @g_hnsiquomaprepvalcl3ndv (syn_cpw X) C (syn_cuni (syn_cuni Q)) p0218
  have p0220 :=
    Nominal.mp p0217 p0219
  have p0221 :=
    @g_snelpw1 C (syn_chwcn (syn_cpw X))
  have p0222 :=
    @g_mpbir (.classMem (syn_csn C) (syn_cpw1 (syn_chwcn (syn_cpw X)))) (.classMem C (syn_chwcn (syn_cpw X))) hyp_cfbhnpw13genericquotrepcohndv_2 p0221
  have p0223 :=
    @g_hnsicodemapfndv (syn_cpw X)
  have p0224 :=
    @g_ffvelrni (syn_cpw1 (syn_chwcn (syn_cpw X))) (syn_chwcn (syn_cpw1 (syn_cpw X))) (syn_csn C) (syn_chnsicodemap (syn_cpw X)) p0223
  have p0225 :=
    Nominal.mp p0222 p0224
  have p0226 :=
    @g_pwex X hyp_cfbhnpw13genericquotrepcohndv_1
  have p0227 :=
    @g_pw1ex (syn_cpw X) p0226
  have p0228 :=
    @g_hwnisoclasselhnordcl (syn_cpw1 (syn_cpw X)) (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) p0227
  have p0229 :=
    Nominal.mp p0225 p0228
  have p0230 :=
    @g_eqeltri (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwniso (syn_cpw1 (syn_cpw X)))) (syn_chnord (syn_cpw1 (syn_cpw X))) p0220 p0229
  have p0231 :=
    @g_snelpw1 (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))) (syn_chnord (syn_cpw1 (syn_cpw X)))
  have p0232 :=
    @g_mpbir (.classMem (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))) (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw X))))) (.classMem (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))) (syn_chnord (syn_cpw1 (syn_cpw X)))) p0230 p0231
  have p0233 :=
    @g_snelpw1 C (syn_chwcn (syn_cpw X))
  have p0234 :=
    @g_mpbir (.classMem (syn_csn C) (syn_cpw1 (syn_chwcn (syn_cpw X)))) (.classMem C (syn_chwcn (syn_cpw X))) hyp_cfbhnpw13genericquotrepcohndv_2 p0233
  have p0235 :=
    @g_hnsicodemapfndv (syn_cpw X)
  have p0236 :=
    @g_ffvelrni (syn_cpw1 (syn_chwcn (syn_cpw X))) (syn_chwcn (syn_cpw1 (syn_cpw X))) (syn_csn C) (syn_chnsicodemap (syn_cpw X)) p0235
  have p0237 :=
    Nominal.mp p0234 p0236
  have p0238 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))) Q
  have p0239 :=
    Nominal.mp hyp_cfbhnpw13genericquotrepcohndv_3 p0238
  have p0240 :=
    @g_simpl (.classMem (syn_cuni Q) (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (.classEq Q (syn_csn (syn_cuni Q)))
  have p0241 :=
    Nominal.mp p0239 p0240
  have p0242 :=
    @g_pw1argclcl (syn_cpw1 (syn_chnord (syn_cpw X))) (syn_cuni Q)
  have p0243 :=
    Nominal.mp p0241 p0242
  have p0244 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni Q)) (syn_cpw1 (syn_chnord (syn_cpw X)))) (.classEq (syn_cuni Q) (syn_csn (syn_cuni (syn_cuni Q))))
  have p0245 :=
    Nominal.mp p0243 p0244
  have p0246 :=
    @g_pm3_2i (.classMem C (syn_chwcn (syn_cpw X))) (.classEq (syn_cuni (syn_cuni (syn_cuni Q))) (syn_cec C (syn_chwniso (syn_cpw X)))) hyp_cfbhnpw13genericquotrepcohndv_2 hyp_cfbhnpw13genericquotrepcohndv_4
  have p0247 :=
    @g_pm3_2i (.classMem (syn_cuni (syn_cuni Q)) (syn_cpw1 (syn_chnord (syn_cpw X)))) (syn_wa (.classMem C (syn_chwcn (syn_cpw X))) (.classEq (syn_cuni (syn_cuni (syn_cuni Q))) (syn_cec C (syn_chwniso (syn_cpw X))))) p0245 p0246
  have p0248 :=
    @g_pwex X hyp_cfbhnpw13genericquotrepcohndv_1
  have p0249 :=
    @g_hnsiquomaprepvalcl3ndv (syn_cpw X) C (syn_cuni (syn_cuni Q)) p0248
  have p0250 :=
    Nominal.mp p0247 p0249
  have p0251 :=
    @g_snelpw1 C (syn_chwcn (syn_cpw X))
  have p0252 :=
    @g_mpbir (.classMem (syn_csn C) (syn_cpw1 (syn_chwcn (syn_cpw X)))) (.classMem C (syn_chwcn (syn_cpw X))) hyp_cfbhnpw13genericquotrepcohndv_2 p0251
  have p0253 :=
    @g_hnsicodemapfndv (syn_cpw X)
  have p0254 :=
    @g_ffvelrni (syn_cpw1 (syn_chwcn (syn_cpw X))) (syn_chwcn (syn_cpw1 (syn_cpw X))) (syn_csn C) (syn_chnsicodemap (syn_cpw X)) p0253
  have p0255 :=
    Nominal.mp p0252 p0254
  have p0256 :=
    @g_pwex X hyp_cfbhnpw13genericquotrepcohndv_1
  have p0257 :=
    @g_pw1ex (syn_cpw X) p0256
  have p0258 :=
    @g_hwnisoclasselhnordcl (syn_cpw1 (syn_cpw X)) (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) p0257
  have p0259 :=
    Nominal.mp p0255 p0258
  have p0260 :=
    @g_eqeltri (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwniso (syn_cpw1 (syn_cpw X)))) (syn_chnord (syn_cpw1 (syn_cpw X))) p0250 p0259
  have p0261 :=
    @g_elex (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))) (syn_chnord (syn_cpw1 (syn_cpw X)))
  have p0262 :=
    Nominal.mp p0260 p0261
  have p0263 :=
    @g_unisn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))) p0262
  have p0264 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))) Q
  have p0265 :=
    Nominal.mp hyp_cfbhnpw13genericquotrepcohndv_3 p0264
  have p0266 :=
    @g_simpl (.classMem (syn_cuni Q) (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (.classEq Q (syn_csn (syn_cuni Q)))
  have p0267 :=
    Nominal.mp p0265 p0266
  have p0268 :=
    @g_pw1argclcl (syn_cpw1 (syn_chnord (syn_cpw X))) (syn_cuni Q)
  have p0269 :=
    Nominal.mp p0267 p0268
  have p0270 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni Q)) (syn_cpw1 (syn_chnord (syn_cpw X)))) (.classEq (syn_cuni Q) (syn_csn (syn_cuni (syn_cuni Q))))
  have p0271 :=
    Nominal.mp p0269 p0270
  have p0272 :=
    @g_pm3_2i (.classMem C (syn_chwcn (syn_cpw X))) (.classEq (syn_cuni (syn_cuni (syn_cuni Q))) (syn_cec C (syn_chwniso (syn_cpw X)))) hyp_cfbhnpw13genericquotrepcohndv_2 hyp_cfbhnpw13genericquotrepcohndv_4
  have p0273 :=
    @g_pm3_2i (.classMem (syn_cuni (syn_cuni Q)) (syn_cpw1 (syn_chnord (syn_cpw X)))) (syn_wa (.classMem C (syn_chwcn (syn_cpw X))) (.classEq (syn_cuni (syn_cuni (syn_cuni Q))) (syn_cec C (syn_chwniso (syn_cpw X))))) p0271 p0272
  have p0274 :=
    @g_pwex X hyp_cfbhnpw13genericquotrepcohndv_1
  have p0275 :=
    @g_hnsiquomaprepvalcl3ndv (syn_cpw X) C (syn_cuni (syn_cuni Q)) p0274
  have p0276 :=
    Nominal.mp p0273 p0275
  have p0277 :=
    @g_eqtri (syn_cuni (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))))) (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwniso (syn_cpw1 (syn_cpw X)))) p0263 p0276
  have p0278 :=
    @g_pm3_2i (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwcn (syn_cpw1 (syn_cpw X)))) (.classEq (syn_cuni (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))))) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwniso (syn_cpw1 (syn_cpw X))))) p0237 p0277
  have p0279 :=
    @g_pm3_2i (.classMem (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))) (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw X))))) (syn_wa (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwcn (syn_cpw1 (syn_cpw X)))) (.classEq (syn_cuni (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))))) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwniso (syn_cpw1 (syn_cpw X)))))) p0232 p0278
  have p0280 :=
    @g_pwex X hyp_cfbhnpw13genericquotrepcohndv_1
  have p0281 :=
    @g_pw1ex (syn_cpw X) p0280
  have p0282 :=
    @g_hnsiquomaprepvalcl3ndv (syn_cpw1 (syn_cpw X)) (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))) p0281
  have p0283 :=
    Nominal.mp p0279 p0282
  have p0284 :=
    @g_snelpw1 C (syn_chwcn (syn_cpw X))
  have p0285 :=
    @g_mpbir (.classMem (syn_csn C) (syn_cpw1 (syn_chwcn (syn_cpw X)))) (.classMem C (syn_chwcn (syn_cpw X))) hyp_cfbhnpw13genericquotrepcohndv_2 p0284
  have p0286 :=
    @g_hnsicodemapfndv (syn_cpw X)
  have p0287 :=
    @g_ffvelrni (syn_cpw1 (syn_chwcn (syn_cpw X))) (syn_chwcn (syn_cpw1 (syn_cpw X))) (syn_csn C) (syn_chnsicodemap (syn_cpw X)) p0286
  have p0288 :=
    Nominal.mp p0285 p0287
  have p0289 :=
    @g_snelpw1 (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwcn (syn_cpw1 (syn_cpw X)))
  have p0290 :=
    @g_mpbir (.classMem (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))) (syn_cpw1 (syn_chwcn (syn_cpw1 (syn_cpw X))))) (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwcn (syn_cpw1 (syn_cpw X)))) p0288 p0289
  have p0291 :=
    @g_hnsicodemapfndv (syn_cpw1 (syn_cpw X))
  have p0292 :=
    @g_ffvelrni (syn_cpw1 (syn_chwcn (syn_cpw1 (syn_cpw X)))) (syn_chwcn (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C))) (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) p0291
  have p0293 :=
    Nominal.mp p0290 p0292
  have p0294 :=
    @g_pwex X hyp_cfbhnpw13genericquotrepcohndv_1
  have p0295 :=
    @g_pw1ex (syn_cpw X) p0294
  have p0296 :=
    @g_pw1ex (syn_cpw1 (syn_cpw X)) p0295
  have p0297 :=
    @g_hwnisoclasselhnordcl (syn_cpw1 (syn_cpw1 (syn_cpw X))) (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))) p0296
  have p0298 :=
    Nominal.mp p0293 p0297
  have p0299 :=
    @g_eqeltri (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))))) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))) (syn_chwniso (syn_cpw1 (syn_cpw1 (syn_cpw X))))) (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw X)))) p0283 p0298
  have p0300 :=
    @g_elex (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))))) (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw X))))
  have p0301 :=
    Nominal.mp p0299 p0300
  have p0302 :=
    @g_unisn (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))))) p0301
  have p0303 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))) Q
  have p0304 :=
    Nominal.mp hyp_cfbhnpw13genericquotrepcohndv_3 p0303
  have p0305 :=
    @g_simpl (.classMem (syn_cuni Q) (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (.classEq Q (syn_csn (syn_cuni Q)))
  have p0306 :=
    Nominal.mp p0304 p0305
  have p0307 :=
    @g_pw1argclcl (syn_cpw1 (syn_chnord (syn_cpw X))) (syn_cuni Q)
  have p0308 :=
    Nominal.mp p0306 p0307
  have p0309 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni Q)) (syn_cpw1 (syn_chnord (syn_cpw X)))) (.classEq (syn_cuni Q) (syn_csn (syn_cuni (syn_cuni Q))))
  have p0310 :=
    Nominal.mp p0308 p0309
  have p0311 :=
    @g_pm3_2i (.classMem C (syn_chwcn (syn_cpw X))) (.classEq (syn_cuni (syn_cuni (syn_cuni Q))) (syn_cec C (syn_chwniso (syn_cpw X)))) hyp_cfbhnpw13genericquotrepcohndv_2 hyp_cfbhnpw13genericquotrepcohndv_4
  have p0312 :=
    @g_pm3_2i (.classMem (syn_cuni (syn_cuni Q)) (syn_cpw1 (syn_chnord (syn_cpw X)))) (syn_wa (.classMem C (syn_chwcn (syn_cpw X))) (.classEq (syn_cuni (syn_cuni (syn_cuni Q))) (syn_cec C (syn_chwniso (syn_cpw X))))) p0310 p0311
  have p0313 :=
    @g_pwex X hyp_cfbhnpw13genericquotrepcohndv_1
  have p0314 :=
    @g_hnsiquomaprepvalcl3ndv (syn_cpw X) C (syn_cuni (syn_cuni Q)) p0313
  have p0315 :=
    Nominal.mp p0312 p0314
  have p0316 :=
    @g_snelpw1 C (syn_chwcn (syn_cpw X))
  have p0317 :=
    @g_mpbir (.classMem (syn_csn C) (syn_cpw1 (syn_chwcn (syn_cpw X)))) (.classMem C (syn_chwcn (syn_cpw X))) hyp_cfbhnpw13genericquotrepcohndv_2 p0316
  have p0318 :=
    @g_hnsicodemapfndv (syn_cpw X)
  have p0319 :=
    @g_ffvelrni (syn_cpw1 (syn_chwcn (syn_cpw X))) (syn_chwcn (syn_cpw1 (syn_cpw X))) (syn_csn C) (syn_chnsicodemap (syn_cpw X)) p0318
  have p0320 :=
    Nominal.mp p0317 p0319
  have p0321 :=
    @g_pwex X hyp_cfbhnpw13genericquotrepcohndv_1
  have p0322 :=
    @g_pw1ex (syn_cpw X) p0321
  have p0323 :=
    @g_hwnisoclasselhnordcl (syn_cpw1 (syn_cpw X)) (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) p0322
  have p0324 :=
    Nominal.mp p0320 p0323
  have p0325 :=
    @g_eqeltri (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwniso (syn_cpw1 (syn_cpw X)))) (syn_chnord (syn_cpw1 (syn_cpw X))) p0315 p0324
  have p0326 :=
    @g_snelpw1 (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))) (syn_chnord (syn_cpw1 (syn_cpw X)))
  have p0327 :=
    @g_mpbir (.classMem (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))) (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw X))))) (.classMem (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))) (syn_chnord (syn_cpw1 (syn_cpw X)))) p0325 p0326
  have p0328 :=
    @g_snelpw1 C (syn_chwcn (syn_cpw X))
  have p0329 :=
    @g_mpbir (.classMem (syn_csn C) (syn_cpw1 (syn_chwcn (syn_cpw X)))) (.classMem C (syn_chwcn (syn_cpw X))) hyp_cfbhnpw13genericquotrepcohndv_2 p0328
  have p0330 :=
    @g_hnsicodemapfndv (syn_cpw X)
  have p0331 :=
    @g_ffvelrni (syn_cpw1 (syn_chwcn (syn_cpw X))) (syn_chwcn (syn_cpw1 (syn_cpw X))) (syn_csn C) (syn_chnsicodemap (syn_cpw X)) p0330
  have p0332 :=
    Nominal.mp p0329 p0331
  have p0333 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))) Q
  have p0334 :=
    Nominal.mp hyp_cfbhnpw13genericquotrepcohndv_3 p0333
  have p0335 :=
    @g_simpl (.classMem (syn_cuni Q) (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (.classEq Q (syn_csn (syn_cuni Q)))
  have p0336 :=
    Nominal.mp p0334 p0335
  have p0337 :=
    @g_pw1argclcl (syn_cpw1 (syn_chnord (syn_cpw X))) (syn_cuni Q)
  have p0338 :=
    Nominal.mp p0336 p0337
  have p0339 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni Q)) (syn_cpw1 (syn_chnord (syn_cpw X)))) (.classEq (syn_cuni Q) (syn_csn (syn_cuni (syn_cuni Q))))
  have p0340 :=
    Nominal.mp p0338 p0339
  have p0341 :=
    @g_pm3_2i (.classMem C (syn_chwcn (syn_cpw X))) (.classEq (syn_cuni (syn_cuni (syn_cuni Q))) (syn_cec C (syn_chwniso (syn_cpw X)))) hyp_cfbhnpw13genericquotrepcohndv_2 hyp_cfbhnpw13genericquotrepcohndv_4
  have p0342 :=
    @g_pm3_2i (.classMem (syn_cuni (syn_cuni Q)) (syn_cpw1 (syn_chnord (syn_cpw X)))) (syn_wa (.classMem C (syn_chwcn (syn_cpw X))) (.classEq (syn_cuni (syn_cuni (syn_cuni Q))) (syn_cec C (syn_chwniso (syn_cpw X))))) p0340 p0341
  have p0343 :=
    @g_pwex X hyp_cfbhnpw13genericquotrepcohndv_1
  have p0344 :=
    @g_hnsiquomaprepvalcl3ndv (syn_cpw X) C (syn_cuni (syn_cuni Q)) p0343
  have p0345 :=
    Nominal.mp p0342 p0344
  have p0346 :=
    @g_snelpw1 C (syn_chwcn (syn_cpw X))
  have p0347 :=
    @g_mpbir (.classMem (syn_csn C) (syn_cpw1 (syn_chwcn (syn_cpw X)))) (.classMem C (syn_chwcn (syn_cpw X))) hyp_cfbhnpw13genericquotrepcohndv_2 p0346
  have p0348 :=
    @g_hnsicodemapfndv (syn_cpw X)
  have p0349 :=
    @g_ffvelrni (syn_cpw1 (syn_chwcn (syn_cpw X))) (syn_chwcn (syn_cpw1 (syn_cpw X))) (syn_csn C) (syn_chnsicodemap (syn_cpw X)) p0348
  have p0350 :=
    Nominal.mp p0347 p0349
  have p0351 :=
    @g_pwex X hyp_cfbhnpw13genericquotrepcohndv_1
  have p0352 :=
    @g_pw1ex (syn_cpw X) p0351
  have p0353 :=
    @g_hwnisoclasselhnordcl (syn_cpw1 (syn_cpw X)) (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) p0352
  have p0354 :=
    Nominal.mp p0350 p0353
  have p0355 :=
    @g_eqeltri (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwniso (syn_cpw1 (syn_cpw X)))) (syn_chnord (syn_cpw1 (syn_cpw X))) p0345 p0354
  have p0356 :=
    @g_elex (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))) (syn_chnord (syn_cpw1 (syn_cpw X)))
  have p0357 :=
    Nominal.mp p0355 p0356
  have p0358 :=
    @g_unisn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))) p0357
  have p0359 :=
    @g_pw1argclcl (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X)))) Q
  have p0360 :=
    Nominal.mp hyp_cfbhnpw13genericquotrepcohndv_3 p0359
  have p0361 :=
    @g_simpl (.classMem (syn_cuni Q) (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw X))))) (.classEq Q (syn_csn (syn_cuni Q)))
  have p0362 :=
    Nominal.mp p0360 p0361
  have p0363 :=
    @g_pw1argclcl (syn_cpw1 (syn_chnord (syn_cpw X))) (syn_cuni Q)
  have p0364 :=
    Nominal.mp p0362 p0363
  have p0365 :=
    @g_simpl (.classMem (syn_cuni (syn_cuni Q)) (syn_cpw1 (syn_chnord (syn_cpw X)))) (.classEq (syn_cuni Q) (syn_csn (syn_cuni (syn_cuni Q))))
  have p0366 :=
    Nominal.mp p0364 p0365
  have p0367 :=
    @g_pm3_2i (.classMem C (syn_chwcn (syn_cpw X))) (.classEq (syn_cuni (syn_cuni (syn_cuni Q))) (syn_cec C (syn_chwniso (syn_cpw X)))) hyp_cfbhnpw13genericquotrepcohndv_2 hyp_cfbhnpw13genericquotrepcohndv_4
  have p0368 :=
    @g_pm3_2i (.classMem (syn_cuni (syn_cuni Q)) (syn_cpw1 (syn_chnord (syn_cpw X)))) (syn_wa (.classMem C (syn_chwcn (syn_cpw X))) (.classEq (syn_cuni (syn_cuni (syn_cuni Q))) (syn_cec C (syn_chwniso (syn_cpw X))))) p0366 p0367
  have p0369 :=
    @g_pwex X hyp_cfbhnpw13genericquotrepcohndv_1
  have p0370 :=
    @g_hnsiquomaprepvalcl3ndv (syn_cpw X) C (syn_cuni (syn_cuni Q)) p0369
  have p0371 :=
    Nominal.mp p0368 p0370
  have p0372 :=
    @g_eqtri (syn_cuni (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))))) (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwniso (syn_cpw1 (syn_cpw X)))) p0358 p0371
  have p0373 :=
    @g_pm3_2i (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwcn (syn_cpw1 (syn_cpw X)))) (.classEq (syn_cuni (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))))) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwniso (syn_cpw1 (syn_cpw X))))) p0332 p0372
  have p0374 :=
    @g_pm3_2i (.classMem (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))) (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw X))))) (syn_wa (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwcn (syn_cpw1 (syn_cpw X)))) (.classEq (syn_cuni (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))))) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_chwniso (syn_cpw1 (syn_cpw X)))))) p0327 p0373
  have p0375 :=
    @g_pwex X hyp_cfbhnpw13genericquotrepcohndv_1
  have p0376 :=
    @g_pw1ex (syn_cpw X) p0375
  have p0377 :=
    @g_hnsiquomaprepvalcl3ndv (syn_cpw1 (syn_cpw X)) (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)) (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))) p0376
  have p0378 :=
    Nominal.mp p0374 p0377
  have p0379 :=
    @g_eqtri (syn_cuni (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))))))) (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))))) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))) (syn_chwniso (syn_cpw1 (syn_cpw1 (syn_cpw X))))) p0302 p0378
  have p0380 :=
    @g_pm3_2i (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))) (syn_chwcn (syn_cpw1 (syn_cpw1 (syn_cpw X))))) (.classEq (syn_cuni (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))))))) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))) (syn_chwniso (syn_cpw1 (syn_cpw1 (syn_cpw X)))))) p0207 p0379
  have p0381 :=
    @g_pm3_2i (.classMem (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))))) (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw X)))))) (syn_wa (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))) (syn_chwcn (syn_cpw1 (syn_cpw1 (syn_cpw X))))) (.classEq (syn_cuni (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))))))) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))) (syn_chwniso (syn_cpw1 (syn_cpw1 (syn_cpw X))))))) p0197 p0380
  have p0382 :=
    @g_pwex X hyp_cfbhnpw13genericquotrepcohndv_1
  have p0383 :=
    @g_pw1ex (syn_cpw X) p0382
  have p0384 :=
    @g_pw1ex (syn_cpw1 (syn_cpw X)) p0383
  have p0385 :=
    @g_hnsiquomaprepvalcl3ndv (syn_cpw1 (syn_cpw1 (syn_cpw X))) (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))) (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q)))))) p0384
  have p0386 :=
    Nominal.mp p0381 p0385
  have p0387 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 (syn_cpw X)))) (syn_csi (syn_csi (syn_chnsiquomap (syn_cpw X)))))) Q) (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsiquomap (syn_cpw X)) (syn_cuni (syn_cuni Q))))))) (syn_cec (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw1 (syn_cpw X)))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw1 (syn_cpw X))) (syn_csn (syn_cfv (syn_chnsicodemap (syn_cpw X)) (syn_csn C)))))) (syn_chwniso (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw X)))))) p0103 p0386
  exact p0387

#print axioms g_cfbhnpw13genericquotrepcohndv

end NFChoice.DirectNominalPrf.WPPReplay
