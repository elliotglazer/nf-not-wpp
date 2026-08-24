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
import NominalWPPReplayChunk014Compact001Part054

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

noncomputable def g_lefinantinn
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.imp (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin))) (.classEq A B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (syn_wne A (syn_c0))
  have p0001 :=
    @g_simpl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))
  have p0002 :=
    @g_simpl (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0003 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem A (syn_cnnc)) p0001 p0002
  have p0004 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (syn_wne A (syn_c0))) (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (.classMem A (syn_cnnc)) p0000 p0003
  have p0005 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (syn_wne A (syn_c0))
  have p0006 :=
    @g_simpl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))
  have p0007 :=
    @g_simpr (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0008 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem B (syn_cnnc)) p0006 p0007
  have p0009 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (syn_wne A (syn_c0))) (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (.classMem B (syn_cnnc)) p0005 p0008
  have p0010 :=
    @g_simpr (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (syn_wne A (syn_c0))
  have p0011 :=
    @g_n_3jca (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (syn_wne A (syn_c0))) (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (syn_wne A (syn_c0)) p0004 p0009 p0010
  have p0012 :=
    @g_ltfintri A B
  have p0013 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (syn_wne A (syn_c0))) (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (syn_wne A (syn_c0))) (syn_w3o (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B) (.classMem (syn_copk B A) (syn_cltfin))) p0011 p0012
  have p0014 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (syn_wne A (syn_c0))
  have p0015 :=
    @g_simpr (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))
  have p0016 :=
    @g_simpr (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin))
  have p0017 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin))) (.classMem (syn_copk B A) (syn_clefin)) p0015 p0016
  have p0018 :=
    @g_simpl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))
  have p0019 :=
    @g_simpr (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0020 :=
    @g_simpl (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0021 :=
    @g_jca (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem B (syn_cnnc)) (.classMem A (syn_cnnc)) p0019 p0020
  have p0022 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem B (syn_cnnc)) (.classMem A (syn_cnnc))) p0018 p0021
  have p0023 :=
    @g_lenltfin B A
  have p0024 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (syn_wa (.classMem B (syn_cnnc)) (.classMem A (syn_cnnc))) (syn_wb (.classMem (syn_copk B A) (syn_clefin)) (.neg (.classMem (syn_copk A B) (syn_cltfin)))) p0022 p0023
  have p0025 :=
    @g_biimpd (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (.classMem (syn_copk B A) (syn_clefin)) (.neg (.classMem (syn_copk A B) (syn_cltfin))) p0024
  have p0026 :=
    @g_mpd (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (.classMem (syn_copk B A) (syn_clefin)) (.neg (.classMem (syn_copk A B) (syn_cltfin))) p0017 p0025
  have p0027 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (syn_wne A (syn_c0))) (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (.neg (.classMem (syn_copk A B) (syn_cltfin))) p0014 p0026
  have p0028 :=
    @g_pm2_21d (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (syn_wne A (syn_c0))) (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B) p0027
  have p0029 :=
    @g_id (.classEq A B)
  have p0030 :=
    @g_a1i (.imp (.classEq A B) (.classEq A B)) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (syn_wne A (syn_c0))) p0029
  have p0031 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (syn_wne A (syn_c0))
  have p0032 :=
    @g_simpr (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))
  have p0033 :=
    @g_simpl (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin))
  have p0034 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin))) (.classMem (syn_copk A B) (syn_clefin)) p0032 p0033
  have p0035 :=
    @g_simpl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))
  have p0036 :=
    @g_lenltfin A B
  have p0037 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wb (.classMem (syn_copk A B) (syn_clefin)) (.neg (.classMem (syn_copk B A) (syn_cltfin)))) p0035 p0036
  have p0038 :=
    @g_biimpd (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (.classMem (syn_copk A B) (syn_clefin)) (.neg (.classMem (syn_copk B A) (syn_cltfin))) p0037
  have p0039 :=
    @g_mpd (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (.classMem (syn_copk A B) (syn_clefin)) (.neg (.classMem (syn_copk B A) (syn_cltfin))) p0034 p0038
  have p0040 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (syn_wne A (syn_c0))) (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (.neg (.classMem (syn_copk B A) (syn_cltfin))) p0031 p0039
  have p0041 :=
    @g_pm2_21d (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (syn_wne A (syn_c0))) (.classMem (syn_copk B A) (syn_cltfin)) (.classEq A B) p0040
  have p0042 :=
    @g_n_3jaod (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (syn_wne A (syn_c0))) (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B) (.classEq A B) (.classMem (syn_copk B A) (syn_cltfin)) p0028 p0030 p0041
  have p0043 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (syn_wne A (syn_c0))) (syn_w3o (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B) (.classMem (syn_copk B A) (syn_cltfin))) (.classEq A B) p0013 p0042
  have p0044 :=
    @g_ex (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (syn_wne A (syn_c0)) (.classEq A B) p0043
  have p0045 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (.neg (syn_wne A (syn_c0)))
  have p0046 :=
    @g_simpr (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))
  have p0047 :=
    @g_simpl (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin))
  have p0048 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin))) (.classMem (syn_copk A B) (syn_clefin)) p0046 p0047
  have p0049 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (.neg (syn_wne A (syn_c0)))) (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (.classMem (syn_copk A B) (syn_clefin)) p0045 p0048
  have p0050 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (.neg (syn_wne A (syn_c0)))
  have p0051 :=
    @g_simpl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))
  have p0052 :=
    @g_simpl (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0053 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem A (syn_cnnc)) p0051 p0052
  have p0054 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (.neg (syn_wne A (syn_c0)))) (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (.classMem A (syn_cnnc)) p0050 p0053
  have p0055 :=
    @g_elex A (syn_cnnc)
  have p0056 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (.neg (syn_wne A (syn_c0)))) (.classMem A (syn_cnnc)) (.classMem A (syn_cvv)) p0054 p0055
  have p0057 :=
    @g_simpl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (.neg (syn_wne A (syn_c0)))
  have p0058 :=
    @g_simpl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))
  have p0059 :=
    @g_simpr (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0060 :=
    @g_syl (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem B (syn_cnnc)) p0058 p0059
  have p0061 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (.neg (syn_wne A (syn_c0)))) (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (.classMem B (syn_cnnc)) p0057 p0060
  have p0062 :=
    @g_elex B (syn_cnnc)
  have p0063 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (.neg (syn_wne A (syn_c0)))) (.classMem B (syn_cnnc)) (.classMem B (syn_cvv)) p0061 p0062
  have p0064 :=
    @g_simpr (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (.neg (syn_wne A (syn_c0)))
  have p0065 :=
    @g_nne A (syn_c0)
  have p0066 :=
    @g_a1i (syn_wb (.neg (syn_wne A (syn_c0))) (.classEq A (syn_c0))) (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (.neg (syn_wne A (syn_c0)))) p0065
  have p0067 :=
    @g_mpbid (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (.neg (syn_wne A (syn_c0)))) (.neg (syn_wne A (syn_c0))) (.classEq A (syn_c0)) p0064 p0066
  have p0068 :=
    @g_n_3jca (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (.neg (syn_wne A (syn_c0)))) (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classEq A (syn_c0)) p0056 p0063 p0067
  have p0069 :=
    @g_lefinlteq0 A B (syn_cvv) (syn_cvv)
  have p0070 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (.neg (syn_wne A (syn_c0)))) (syn_w3a (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classEq A (syn_c0))) (syn_wb (.classMem (syn_copk A B) (syn_clefin)) (.classEq A B)) p0068 p0069
  have p0071 :=
    @g_mpbid (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (.neg (syn_wne A (syn_c0)))) (.classMem (syn_copk A B) (syn_clefin)) (.classEq A B) p0049 p0070
  have p0072 :=
    @g_ex (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (.neg (syn_wne A (syn_c0))) (.classEq A B) p0071
  have p0073 :=
    @g_pm2_61d (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) (syn_wne A (syn_c0)) (.classEq A B) p0044 p0072
  have p0074 :=
    @g_ex (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin))) (.classEq A B) p0073
  exact p0074

noncomputable def g_lefinconnexnn
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wo (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_simpr (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0001 :=
    @g_elex B (syn_cnnc)
  have p0002 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem B (syn_cnnc)) (.classMem B (syn_cvv)) p0000 p0001
  have p0003 :=
    @g_simpl (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0004 :=
    @g_elex A (syn_cnnc)
  have p0005 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem A (syn_cnnc)) (.classMem A (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_jca (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem B (syn_cvv)) (.classMem A (syn_cvv)) p0002 p0005
  have p0007 :=
    @g_ltlefin B A (syn_cvv) (syn_cvv)
  have p0008 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wa (.classMem B (syn_cvv)) (.classMem A (syn_cvv))) (.imp (.classMem (syn_copk B A) (syn_cltfin)) (.classMem (syn_copk B A) (syn_clefin))) p0006 p0007
  have p0009 :=
    @g_olc (.classMem (syn_copk B A) (syn_clefin)) (.classMem (syn_copk A B) (syn_clefin))
  have p0010 :=
    @g_syl6 (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B A) (syn_cltfin)) (.classMem (syn_copk B A) (syn_clefin)) (syn_wo (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin))) p0008 p0009
  have p0011 :=
    @g_lenltfin A B
  have p0012 :=
    @g_biimprd (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk A B) (syn_clefin)) (.neg (.classMem (syn_copk B A) (syn_cltfin))) p0011
  have p0013 :=
    @g_orc (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin))
  have p0014 :=
    @g_syl6 (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.neg (.classMem (syn_copk B A) (syn_cltfin))) (.classMem (syn_copk A B) (syn_clefin)) (syn_wo (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin))) p0012 p0013
  have p0015 :=
    @g_pm2_61d (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem (syn_copk B A) (syn_cltfin)) (syn_wo (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_clefin))) p0010 p0014
  exact p0015

noncomputable def g_finleor
     :
    Nominal.NPrf (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cstrict) (syn_cnnc)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have dv_cache_0001 : x ∉ ((syn_cnnc)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_ckqrel (syn_clefin))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_ckqrel (syn_clefin))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((syn_ckqrel (syn_clefin))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ (syn_wtru).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ (syn_wtru).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ (syn_wtru).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0011 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0012 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    @g_tru
  have p0001 :=
    @g_lefinex
  have p0002 :=
    @g_kqrelex (syn_clefin) p0001
  have p0003 :=
    @g_a1i (.classMem (syn_ckqrel (syn_clefin)) (syn_cvv)) syn_wtru p0002
  have p0004 :=
    @g_nncex
  have p0005 :=
    @g_a1i (.classMem (syn_cnnc) (syn_cvv)) syn_wtru p0004
  have p0006 :=
    @g_simpr syn_wtru (.classMem (.cv x) (syn_cnnc))
  have p0007 :=
    @g_elex (.cv x) (syn_cnnc)
  have p0008 :=
    @g_syl (syn_wa syn_wtru (.classMem (.cv x) (syn_cnnc))) (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv x) (syn_cvv)) p0006 p0007
  have p0009 :=
    @g_lefinrflx (.cv x) (syn_cvv)
  have p0010 :=
    @g_syl (syn_wa syn_wtru (.classMem (.cv x) (syn_cnnc))) (.classMem (.cv x) (syn_cvv)) (.classMem (syn_copk (.cv x) (.cv x)) (syn_clefin)) p0008 p0009
  have p0011 :=
    @g_simpr syn_wtru (.classMem (.cv x) (syn_cnnc))
  have p0012 :=
    @g_elex (.cv x) (syn_cnnc)
  have p0013 :=
    @g_syl (syn_wa syn_wtru (.classMem (.cv x) (syn_cnnc))) (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv x) (syn_cvv)) p0011 p0012
  have p0014 :=
    @g_simpr syn_wtru (.classMem (.cv x) (syn_cnnc))
  have p0015 :=
    @g_elex (.cv x) (syn_cnnc)
  have p0016 :=
    @g_syl (syn_wa syn_wtru (.classMem (.cv x) (syn_cnnc))) (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv x) (syn_cvv)) p0014 p0015
  have p0017 :=
    @g_jca (syn_wa syn_wtru (.classMem (.cv x) (syn_cnnc))) (.classMem (.cv x) (syn_cvv)) (.classMem (.cv x) (syn_cvv)) p0013 p0016
  have p0018 :=
    @g_kqlefinbr (.cv x) (.cv x) (syn_cvv) (syn_cvv)
  have p0019 :=
    @g_syl (syn_wa syn_wtru (.classMem (.cv x) (syn_cnnc))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv x) (syn_cvv))) (syn_wb (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv x)) (.classMem (syn_copk (.cv x) (.cv x)) (syn_clefin))) p0017 p0018
  have p0020 :=
    @g_mpbird (syn_wa syn_wtru (.classMem (.cv x) (syn_cnnc))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv x)) (.classMem (syn_copk (.cv x) (.cv x)) (syn_clefin)) p0010 p0019
  have p0021 :=
    @g_simp3 syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))
  have p0022 :=
    @g_simpl (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))
  have p0023 :=
    @g_syl (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) p0021 p0022
  have p0024 :=
    @g_simp2 syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))
  have p0025 :=
    @g_simp1 (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))
  have p0026 :=
    @g_syl (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))) (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (.classMem (.cv x) (syn_cnnc)) p0024 p0025
  have p0027 :=
    @g_elex (.cv x) (syn_cnnc)
  have p0028 :=
    @g_syl (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))) (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv x) (syn_cvv)) p0026 p0027
  have p0029 :=
    @g_simp2 syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))
  have p0030 :=
    @g_simp2 (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))
  have p0031 :=
    @g_syl (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))) (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (.classMem (.cv y) (syn_cnnc)) p0029 p0030
  have p0032 :=
    @g_elex (.cv y) (syn_cnnc)
  have p0033 :=
    @g_syl (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cvv)) p0031 p0032
  have p0034 :=
    @g_jca (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))) (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)) p0028 p0033
  have p0035 :=
    @g_kqlefinbr (.cv x) (.cv y) (syn_cvv) (syn_cvv)
  have p0036 :=
    @g_syl (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))) (syn_wb (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (.classMem (syn_copk (.cv x) (.cv y)) (syn_clefin))) p0034 p0035
  have p0037 :=
    @g_mpbid (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (.classMem (syn_copk (.cv x) (.cv y)) (syn_clefin)) p0023 p0036
  have p0038 :=
    @g_simp3 syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))
  have p0039 :=
    @g_simpr (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))
  have p0040 :=
    @g_syl (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)) p0038 p0039
  have p0041 :=
    @g_simp2 syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))
  have p0042 :=
    @g_simp2 (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))
  have p0043 :=
    @g_syl (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))) (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (.classMem (.cv y) (syn_cnnc)) p0041 p0042
  have p0044 :=
    @g_elex (.cv y) (syn_cnnc)
  have p0045 :=
    @g_syl (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cvv)) p0043 p0044
  have p0046 :=
    @g_simp2 syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))
  have p0047 :=
    @g_simp3 (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))
  have p0048 :=
    @g_syl (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))) (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (.classMem (.cv z) (syn_cnnc)) p0046 p0047
  have p0049 :=
    @g_elex (.cv z) (syn_cnnc)
  have p0050 :=
    @g_syl (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))) (.classMem (.cv z) (syn_cnnc)) (.classMem (.cv z) (syn_cvv)) p0048 p0049
  have p0051 :=
    @g_jca (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))) (.classMem (.cv y) (syn_cvv)) (.classMem (.cv z) (syn_cvv)) p0045 p0050
  have p0052 :=
    @g_kqlefinbr (.cv y) (.cv z) (syn_cvv) (syn_cvv)
  have p0053 :=
    @g_syl (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))) (syn_wa (.classMem (.cv y) (syn_cvv)) (.classMem (.cv z) (syn_cvv))) (syn_wb (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)) (.classMem (syn_copk (.cv y) (.cv z)) (syn_clefin))) p0051 p0052
  have p0054 :=
    @g_mpbid (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)) (.classMem (syn_copk (.cv y) (.cv z)) (syn_clefin)) p0040 p0053
  have p0055 :=
    @g_jca (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))) (.classMem (syn_copk (.cv x) (.cv y)) (syn_clefin)) (.classMem (syn_copk (.cv y) (.cv z)) (syn_clefin)) p0037 p0054
  have p0056 :=
    @g_simp2 syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))
  have p0057 :=
    @g_lefintrnn (.cv x) (.cv y) (.cv z)
  have p0058 :=
    @g_syl (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))) (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (.imp (syn_wa (.classMem (syn_copk (.cv x) (.cv y)) (syn_clefin)) (.classMem (syn_copk (.cv y) (.cv z)) (syn_clefin))) (.classMem (syn_copk (.cv x) (.cv z)) (syn_clefin))) p0056 p0057
  have p0059 :=
    @g_mpd (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))) (syn_wa (.classMem (syn_copk (.cv x) (.cv y)) (syn_clefin)) (.classMem (syn_copk (.cv y) (.cv z)) (syn_clefin))) (.classMem (syn_copk (.cv x) (.cv z)) (syn_clefin)) p0055 p0058
  have p0060 :=
    @g_simp2 syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))
  have p0061 :=
    @g_simp1 (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))
  have p0062 :=
    @g_syl (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))) (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (.classMem (.cv x) (syn_cnnc)) p0060 p0061
  have p0063 :=
    @g_elex (.cv x) (syn_cnnc)
  have p0064 :=
    @g_syl (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))) (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv x) (syn_cvv)) p0062 p0063
  have p0065 :=
    @g_simp2 syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))
  have p0066 :=
    @g_simp3 (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))
  have p0067 :=
    @g_syl (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))) (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (.classMem (.cv z) (syn_cnnc)) p0065 p0066
  have p0068 :=
    @g_elex (.cv z) (syn_cnnc)
  have p0069 :=
    @g_syl (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))) (.classMem (.cv z) (syn_cnnc)) (.classMem (.cv z) (syn_cvv)) p0067 p0068
  have p0070 :=
    @g_jca (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))) (.classMem (.cv x) (syn_cvv)) (.classMem (.cv z) (syn_cvv)) p0064 p0069
  have p0071 :=
    @g_kqlefinbr (.cv x) (.cv z) (syn_cvv) (syn_cvv)
  have p0072 :=
    @g_syl (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv z) (syn_cvv))) (syn_wb (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)) (.classMem (syn_copk (.cv x) (.cv z)) (syn_clefin))) p0070 p0071
  have p0073 :=
    @g_mpbird (syn_w3a syn_wtru (syn_w3a (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv z) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)) (.classMem (syn_copk (.cv x) (.cv z)) (syn_clefin)) p0059 p0072
  have p0074 :=
    @g_simp3 syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))
  have p0075 :=
    @g_simpl (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))
  have p0076 :=
    @g_syl (syn_w3a syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) p0074 p0075
  have p0077 :=
    @g_simp2 syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))
  have p0078 :=
    @g_simpl (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
  have p0079 :=
    @g_syl (syn_w3a syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))) (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (.classMem (.cv x) (syn_cnnc)) p0077 p0078
  have p0080 :=
    @g_elex (.cv x) (syn_cnnc)
  have p0081 :=
    @g_syl (syn_w3a syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))) (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv x) (syn_cvv)) p0079 p0080
  have p0082 :=
    @g_simp2 syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))
  have p0083 :=
    @g_simpr (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
  have p0084 :=
    @g_syl (syn_w3a syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))) (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (.classMem (.cv y) (syn_cnnc)) p0082 p0083
  have p0085 :=
    @g_elex (.cv y) (syn_cnnc)
  have p0086 :=
    @g_syl (syn_w3a syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cvv)) p0084 p0085
  have p0087 :=
    @g_jca (syn_w3a syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))) (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)) p0081 p0086
  have p0088 :=
    @g_kqlefinbr (.cv x) (.cv y) (syn_cvv) (syn_cvv)
  have p0089 :=
    @g_syl (syn_w3a syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))) (syn_wb (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (.classMem (syn_copk (.cv x) (.cv y)) (syn_clefin))) p0087 p0088
  have p0090 :=
    @g_mpbid (syn_w3a syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (.classMem (syn_copk (.cv x) (.cv y)) (syn_clefin)) p0076 p0089
  have p0091 :=
    @g_simp3 syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))
  have p0092 :=
    @g_simpr (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))
  have p0093 :=
    @g_syl (syn_w3a syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)) p0091 p0092
  have p0094 :=
    @g_simp2 syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))
  have p0095 :=
    @g_simpr (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
  have p0096 :=
    @g_syl (syn_w3a syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))) (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (.classMem (.cv y) (syn_cnnc)) p0094 p0095
  have p0097 :=
    @g_elex (.cv y) (syn_cnnc)
  have p0098 :=
    @g_syl (syn_w3a syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cvv)) p0096 p0097
  have p0099 :=
    @g_simp2 syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))
  have p0100 :=
    @g_simpl (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
  have p0101 :=
    @g_syl (syn_w3a syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))) (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (.classMem (.cv x) (syn_cnnc)) p0099 p0100
  have p0102 :=
    @g_elex (.cv x) (syn_cnnc)
  have p0103 :=
    @g_syl (syn_w3a syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))) (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv x) (syn_cvv)) p0101 p0102
  have p0104 :=
    @g_jca (syn_w3a syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))) (.classMem (.cv y) (syn_cvv)) (.classMem (.cv x) (syn_cvv)) p0098 p0103
  have p0105 :=
    @g_kqlefinbr (.cv y) (.cv x) (syn_cvv) (syn_cvv)
  have p0106 :=
    @g_syl (syn_w3a syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))) (syn_wa (.classMem (.cv y) (syn_cvv)) (.classMem (.cv x) (syn_cvv))) (syn_wb (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)) (.classMem (syn_copk (.cv y) (.cv x)) (syn_clefin))) p0104 p0105
  have p0107 :=
    @g_mpbid (syn_w3a syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)) (.classMem (syn_copk (.cv y) (.cv x)) (syn_clefin)) p0093 p0106
  have p0108 :=
    @g_jca (syn_w3a syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))) (.classMem (syn_copk (.cv x) (.cv y)) (syn_clefin)) (.classMem (syn_copk (.cv y) (.cv x)) (syn_clefin)) p0090 p0107
  have p0109 :=
    @g_simp2 syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))
  have p0110 :=
    @g_lefinantinn (.cv x) (.cv y)
  have p0111 :=
    @g_syl (syn_w3a syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))) (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (.imp (syn_wa (.classMem (syn_copk (.cv x) (.cv y)) (syn_clefin)) (.classMem (syn_copk (.cv y) (.cv x)) (syn_clefin))) (.classEq (.cv x) (.cv y))) p0109 p0110
  have p0112 :=
    @g_mpd (syn_w3a syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))) (syn_wa (.classMem (syn_copk (.cv x) (.cv y)) (syn_clefin)) (.classMem (syn_copk (.cv y) (.cv x)) (syn_clefin))) (.classEq (.cv x) (.cv y)) p0108 p0111
  have p0113 :=
    @g_simp2 syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
  have p0114 :=
    @g_simp3 syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
  have p0115 :=
    @g_jca (syn_w3a syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) p0113 p0114
  have p0116 :=
    @g_lefinconnexnn (.cv x) (.cv y)
  have p0117 :=
    @g_syl (syn_w3a syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wo (.classMem (syn_copk (.cv x) (.cv y)) (syn_clefin)) (.classMem (syn_copk (.cv y) (.cv x)) (syn_clefin))) p0115 p0116
  have p0118 :=
    @g_simp2 syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
  have p0119 :=
    @g_elex (.cv x) (syn_cnnc)
  have p0120 :=
    @g_syl (syn_w3a syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv x) (syn_cvv)) p0118 p0119
  have p0121 :=
    @g_simp3 syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
  have p0122 :=
    @g_elex (.cv y) (syn_cnnc)
  have p0123 :=
    @g_syl (syn_w3a syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cvv)) p0121 p0122
  have p0124 :=
    @g_jca (syn_w3a syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)) p0120 p0123
  have p0125 :=
    @g_kqlefinbr (.cv x) (.cv y) (syn_cvv) (syn_cvv)
  have p0126 :=
    @g_syl (syn_w3a syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))) (syn_wb (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (.classMem (syn_copk (.cv x) (.cv y)) (syn_clefin))) p0124 p0125
  have p0127 :=
    @g_biimprd (syn_w3a syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (.classMem (syn_copk (.cv x) (.cv y)) (syn_clefin)) p0126
  have p0128 :=
    @g_orc (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))
  have p0129 :=
    @g_syl6 (syn_w3a syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (.classMem (syn_copk (.cv x) (.cv y)) (syn_clefin)) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wo (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))) p0127 p0128
  have p0130 :=
    @g_simp3 syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
  have p0131 :=
    @g_elex (.cv y) (syn_cnnc)
  have p0132 :=
    @g_syl (syn_w3a syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cvv)) p0130 p0131
  have p0133 :=
    @g_simp2 syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
  have p0134 :=
    @g_elex (.cv x) (syn_cnnc)
  have p0135 :=
    @g_syl (syn_w3a syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv x) (syn_cvv)) p0133 p0134
  have p0136 :=
    @g_jca (syn_w3a syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (.classMem (.cv y) (syn_cvv)) (.classMem (.cv x) (syn_cvv)) p0132 p0135
  have p0137 :=
    @g_kqlefinbr (.cv y) (.cv x) (syn_cvv) (syn_cvv)
  have p0138 :=
    @g_syl (syn_w3a syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wa (.classMem (.cv y) (syn_cvv)) (.classMem (.cv x) (syn_cvv))) (syn_wb (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)) (.classMem (syn_copk (.cv y) (.cv x)) (syn_clefin))) p0136 p0137
  have p0139 :=
    @g_biimprd (syn_w3a syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)) (.classMem (syn_copk (.cv y) (.cv x)) (syn_clefin)) p0138
  have p0140 :=
    @g_olc (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y))
  have p0141 :=
    @g_syl6 (syn_w3a syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (.classMem (syn_copk (.cv y) (.cv x)) (syn_clefin)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)) (syn_wo (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))) p0139 p0140
  have p0142 :=
    @g_jaod (syn_w3a syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (.classMem (syn_copk (.cv x) (.cv y)) (syn_clefin)) (syn_wo (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))) (.classMem (syn_copk (.cv y) (.cv x)) (syn_clefin)) p0129 p0141
  have p0143 :=
    @g_mpd (syn_w3a syn_wtru (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wo (.classMem (syn_copk (.cv x) (.cv y)) (syn_clefin)) (.classMem (syn_copk (.cv y) (.cv x)) (syn_clefin))) (syn_wo (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))) p0117 p0142
  have p0144_e04_recanon : Nominal.NPrf (.imp (syn_w3a syn_wtru (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_wtru
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0112
  have p0144 :=
    @g_sod syn_wtru x y z (syn_cnnc) (syn_ckqrel (syn_clefin)) (syn_cvv) (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 p0003 p0005 p0020 p0073 p0144_e04_recanon p0143
  have p0145 :=
    Nominal.mp p0000 p0144
  exact p0145

#print axioms g_finleor

end NFChoice.DirectNominalPrf.WPPReplay
