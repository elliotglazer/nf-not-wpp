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
import NominalWPPReplayChunk017Compact001Part073

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

noncomputable def g_hnsicodemap2valclndv
    (v : Var) (A : Class) (dv_A_v : v ∉ A.fv) (hyp_hnsicodemap2valclndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem (.cv v) (syn_chwcn A)) (syn_wa (.classEq (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))) (syn_cop (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v)))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))))) (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))))) := by
  let proofSupport : Finset Var := ({v} : Finset Var) ∪ A.fv
  have p0000 :=
    @g_hnsicodemapfndv A
  have p0001 :=
    @g_a1i (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) (.classMem (.cv v) (syn_chwcn A)) p0000
  have p0002 :=
    @g_id (.classMem (.cv v) (syn_chwcn A))
  have p0003 :=
    @g_snelpw1 (.cv v) (syn_chwcn A)
  have p0004 :=
    @g_sylibr (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) (.classMem (syn_csn (.cv v)) (syn_cpw1 (syn_chwcn A))) p0002 p0003
  have p0005 :=
    @g_jca (.classMem (.cv v) (syn_chwcn A)) (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) (.classMem (syn_csn (.cv v)) (syn_cpw1 (syn_chwcn A))) p0001 p0004
  have p0006 :=
    @g_ffvelrn (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)) (syn_csn (.cv v)) (syn_chnsicodemap A)
  have p0007 :=
    @g_syl (.classMem (.cv v) (syn_chwcn A)) (syn_wa (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) (.classMem (syn_csn (.cv v)) (syn_cpw1 (syn_chwcn A)))) (.classMem (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) (syn_chwcn (syn_cpw1 A))) p0005 p0006
  have p0008 :=
    @g_snelpw1 (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) (syn_chwcn (syn_cpw1 A))
  have p0009 :=
    @g_sylibr (.classMem (.cv v) (syn_chwcn A)) (.classMem (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) (syn_chwcn (syn_cpw1 A))) (.classMem (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))) (syn_cpw1 (syn_chwcn (syn_cpw1 A)))) p0007 p0008
  have p0010 :=
    @g_hnsicodemapvalclndv (syn_cpw1 A) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))
  have p0011 :=
    @g_syl (.classMem (.cv v) (syn_chwcn A)) (.classMem (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))) (syn_cpw1 (syn_chwcn (syn_cpw1 A)))) (.classEq (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))))) p0009 p0010
  have p0012 :=
    @g_fvex (syn_csn (.cv v)) (syn_chnsicodemap A)
  have p0013 :=
    @g_unisn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) p0012
  have p0014 :=
    @g_fveq2i (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))) (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) (syn_c1st) p0013
  have p0015 :=
    @g_a1i (.classEq (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))) (.classMem (.cv v) (syn_chwcn A)) p0014
  have p0016 :=
    @g_id (.classMem (.cv v) (syn_chwcn A))
  have p0017 :=
    @g_snelpw1 (.cv v) (syn_chwcn A)
  have p0018 :=
    @g_sylibr (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) (.classMem (syn_csn (.cv v)) (syn_cpw1 (syn_chwcn A))) p0016 p0017
  have p0019 :=
    @g_hnsicodemapvalclndv A (syn_csn (.cv v))
  have p0020 :=
    @g_syl (.classMem (.cv v) (syn_chwcn A)) (.classMem (syn_csn (.cv v)) (syn_cpw1 (syn_chwcn A))) (.classEq (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (syn_csn (.cv v))))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (.cv v))))))) p0018 p0019
  have p0021 :=
    @g_vex v
  have p0022 :=
    @g_unisn (.cv v) p0021
  have p0023 :=
    @g_fveq2i (syn_cuni (syn_csn (.cv v))) (.cv v) (syn_c1st) p0022
  have p0024 :=
    @g_id (.classEq (syn_cfv (syn_c1st) (syn_cuni (syn_csn (.cv v)))) (syn_cfv (syn_c1st) (.cv v)))
  have p0025 :=
    @g_sieqdndv (.classEq (syn_cfv (syn_c1st) (syn_cuni (syn_csn (.cv v)))) (syn_cfv (syn_c1st) (.cv v))) (syn_cfv (syn_c1st) (syn_cuni (syn_csn (.cv v)))) (syn_cfv (syn_c1st) (.cv v)) p0024
  have p0026 :=
    Nominal.mp p0023 p0025
  have p0027 :=
    @g_vex v
  have p0028 :=
    @g_unisn (.cv v) p0027
  have p0029 :=
    @g_fveq2i (syn_cuni (syn_csn (.cv v))) (.cv v) (syn_c2nd) p0028
  have p0030 :=
    @g_pw1eq (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (.cv v)))) (syn_cfv (syn_c2nd) (.cv v))
  have p0031 :=
    Nominal.mp p0029 p0030
  have p0032 :=
    @g_opeq12i (syn_csi (syn_cfv (syn_c1st) (syn_cuni (syn_csn (.cv v))))) (syn_csi (syn_cfv (syn_c1st) (.cv v))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (.cv v))))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))) p0026 p0031
  have p0033 :=
    @g_a1i (.classEq (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (syn_csn (.cv v))))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (.cv v)))))) (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv v))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) (.classMem (.cv v) (syn_chwcn A)) p0032
  have p0034 :=
    @g_eqtrd (.classMem (.cv v) (syn_chwcn A)) (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (syn_csn (.cv v))))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (.cv v)))))) (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv v))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) p0020 p0033
  have p0035 :=
    @g_fvex (.cv v) (syn_c1st)
  have p0036 :=
    @g_siex (syn_cfv (syn_c1st) (.cv v)) p0035
  have p0037 :=
    @g_fvex (.cv v) (syn_c2nd)
  have p0038 :=
    @g_pw1ex (syn_cfv (syn_c2nd) (.cv v)) p0037
  have p0039 :=
    @g_op1std (syn_csi (syn_cfv (syn_c1st) (.cv v))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))) (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) p0036 p0038
  have p0040 :=
    @g_syl (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv v))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) (.classEq (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))) (syn_csi (syn_cfv (syn_c1st) (.cv v)))) p0034 p0039
  have p0041 :=
    @g_eqtrd (.classMem (.cv v) (syn_chwcn A)) (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c1st) (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))) (syn_csi (syn_cfv (syn_c1st) (.cv v))) p0015 p0040
  have p0042 :=
    @g_id (.classEq (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_csi (syn_cfv (syn_c1st) (.cv v))))
  have p0043 :=
    @g_sieqdndv (.classEq (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_csi (syn_cfv (syn_c1st) (.cv v)))) (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_csi (syn_cfv (syn_c1st) (.cv v))) p0042
  have p0044 :=
    @g_syl (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_csi (syn_cfv (syn_c1st) (.cv v)))) (.classEq (syn_csi (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))) (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v))))) p0041 p0043
  have p0045 :=
    @g_fvex (syn_csn (.cv v)) (syn_chnsicodemap A)
  have p0046 :=
    @g_unisn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) p0045
  have p0047 :=
    @g_fveq2i (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))) (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) (syn_c2nd) p0046
  have p0048 :=
    @g_a1i (.classEq (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))) (.classMem (.cv v) (syn_chwcn A)) p0047
  have p0049 :=
    @g_id (.classMem (.cv v) (syn_chwcn A))
  have p0050 :=
    @g_snelpw1 (.cv v) (syn_chwcn A)
  have p0051 :=
    @g_sylibr (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) (.classMem (syn_csn (.cv v)) (syn_cpw1 (syn_chwcn A))) p0049 p0050
  have p0052 :=
    @g_hnsicodemapvalclndv A (syn_csn (.cv v))
  have p0053 :=
    @g_syl (.classMem (.cv v) (syn_chwcn A)) (.classMem (syn_csn (.cv v)) (syn_cpw1 (syn_chwcn A))) (.classEq (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (syn_csn (.cv v))))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (.cv v))))))) p0051 p0052
  have p0054 :=
    @g_vex v
  have p0055 :=
    @g_unisn (.cv v) p0054
  have p0056 :=
    @g_fveq2i (syn_cuni (syn_csn (.cv v))) (.cv v) (syn_c1st) p0055
  have p0057 :=
    @g_id (.classEq (syn_cfv (syn_c1st) (syn_cuni (syn_csn (.cv v)))) (syn_cfv (syn_c1st) (.cv v)))
  have p0058 :=
    @g_sieqdndv (.classEq (syn_cfv (syn_c1st) (syn_cuni (syn_csn (.cv v)))) (syn_cfv (syn_c1st) (.cv v))) (syn_cfv (syn_c1st) (syn_cuni (syn_csn (.cv v)))) (syn_cfv (syn_c1st) (.cv v)) p0057
  have p0059 :=
    Nominal.mp p0056 p0058
  have p0060 :=
    @g_vex v
  have p0061 :=
    @g_unisn (.cv v) p0060
  have p0062 :=
    @g_fveq2i (syn_cuni (syn_csn (.cv v))) (.cv v) (syn_c2nd) p0061
  have p0063 :=
    @g_pw1eq (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (.cv v)))) (syn_cfv (syn_c2nd) (.cv v))
  have p0064 :=
    Nominal.mp p0062 p0063
  have p0065 :=
    @g_opeq12i (syn_csi (syn_cfv (syn_c1st) (syn_cuni (syn_csn (.cv v))))) (syn_csi (syn_cfv (syn_c1st) (.cv v))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (.cv v))))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))) p0059 p0064
  have p0066 :=
    @g_a1i (.classEq (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (syn_csn (.cv v))))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (.cv v)))))) (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv v))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) (.classMem (.cv v) (syn_chwcn A)) p0065
  have p0067 :=
    @g_eqtrd (.classMem (.cv v) (syn_chwcn A)) (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (syn_csn (.cv v))))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (.cv v)))))) (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv v))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) p0053 p0066
  have p0068 :=
    @g_fvex (.cv v) (syn_c1st)
  have p0069 :=
    @g_siex (syn_cfv (syn_c1st) (.cv v)) p0068
  have p0070 :=
    @g_fvex (.cv v) (syn_c2nd)
  have p0071 :=
    @g_pw1ex (syn_cfv (syn_c2nd) (.cv v)) p0070
  have p0072 :=
    @g_op2ndd (syn_csi (syn_cfv (syn_c1st) (.cv v))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))) (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) p0069 p0071
  have p0073 :=
    @g_syl (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) (syn_cop (syn_csi (syn_cfv (syn_c1st) (.cv v))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) (.classEq (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) p0067 p0072
  have p0074 :=
    @g_eqtrd (.classMem (.cv v) (syn_chwcn A)) (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cfv (syn_c2nd) (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))) p0048 p0073
  have p0075 :=
    @g_pw1eq (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))
  have p0076 :=
    @g_syl (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) (.classEq (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) p0074 p0075
  have p0077 :=
    @g_opeq12d (.classMem (.cv v) (syn_chwcn A)) (syn_csi (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))) (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v)))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))) p0044 p0076
  have p0078 :=
    @g_eqtrd (.classMem (.cv v) (syn_chwcn A)) (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))) (syn_cop (syn_csi (syn_cfv (syn_c1st) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))))) (syn_cpw1 (syn_cfv (syn_c2nd) (syn_cuni (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))))))) (syn_cop (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v)))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v))))) p0011 p0077
  have p0079 :=
    @g_hnsicodemapfndv (syn_cpw1 A)
  have p0080 :=
    @g_a1i (syn_wf (syn_chnsicodemap (syn_cpw1 A)) (syn_cpw1 (syn_chwcn (syn_cpw1 A))) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (.classMem (.cv v) (syn_chwcn A)) p0079
  have p0081 :=
    @g_hnsicodemapfndv A
  have p0082 :=
    @g_a1i (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) (.classMem (.cv v) (syn_chwcn A)) p0081
  have p0083 :=
    @g_id (.classMem (.cv v) (syn_chwcn A))
  have p0084 :=
    @g_snelpw1 (.cv v) (syn_chwcn A)
  have p0085 :=
    @g_sylibr (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) (.classMem (syn_csn (.cv v)) (syn_cpw1 (syn_chwcn A))) p0083 p0084
  have p0086 :=
    @g_jca (.classMem (.cv v) (syn_chwcn A)) (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) (.classMem (syn_csn (.cv v)) (syn_cpw1 (syn_chwcn A))) p0082 p0085
  have p0087 :=
    @g_ffvelrn (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)) (syn_csn (.cv v)) (syn_chnsicodemap A)
  have p0088 :=
    @g_syl (.classMem (.cv v) (syn_chwcn A)) (syn_wa (syn_wf (syn_chnsicodemap A) (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A))) (.classMem (syn_csn (.cv v)) (syn_cpw1 (syn_chwcn A)))) (.classMem (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) (syn_chwcn (syn_cpw1 A))) p0086 p0087
  have p0089 :=
    @g_snelpw1 (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) (syn_chwcn (syn_cpw1 A))
  have p0090 :=
    @g_sylibr (.classMem (.cv v) (syn_chwcn A)) (.classMem (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))) (syn_chwcn (syn_cpw1 A))) (.classMem (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))) (syn_cpw1 (syn_chwcn (syn_cpw1 A)))) p0088 p0089
  have p0091 :=
    @g_jca (.classMem (.cv v) (syn_chwcn A)) (syn_wf (syn_chnsicodemap (syn_cpw1 A)) (syn_cpw1 (syn_chwcn (syn_cpw1 A))) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (.classMem (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))) (syn_cpw1 (syn_chwcn (syn_cpw1 A)))) p0080 p0090
  have p0092 :=
    @g_ffvelrn (syn_cpw1 (syn_chwcn (syn_cpw1 A))) (syn_chwcn (syn_cpw1 (syn_cpw1 A))) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))) (syn_chnsicodemap (syn_cpw1 A))
  have p0093 :=
    @g_syl (.classMem (.cv v) (syn_chwcn A)) (syn_wa (syn_wf (syn_chnsicodemap (syn_cpw1 A)) (syn_cpw1 (syn_chwcn (syn_cpw1 A))) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) (.classMem (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v)))) (syn_cpw1 (syn_chwcn (syn_cpw1 A))))) (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) p0091 p0092
  have p0094 :=
    @g_jca (.classMem (.cv v) (syn_chwcn A)) (.classEq (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))) (syn_cop (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv v)))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv v)))))) (.classMem (syn_cfv (syn_chnsicodemap (syn_cpw1 A)) (syn_csn (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv v))))) (syn_chwcn (syn_cpw1 (syn_cpw1 A)))) p0078 p0093
  exact p0094

#print axioms g_hnsicodemap2valclndv

end NFChoice.DirectNominalPrf.WPPReplay
