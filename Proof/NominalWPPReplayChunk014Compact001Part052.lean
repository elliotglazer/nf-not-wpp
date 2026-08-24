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
import NominalWPPReplayChunk014Compact001Part051

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

noncomputable def g_hnwcutclassinj
    (x : Var) (y : Var) (D : Class) (R : Class) (dv_D_R : Disjoint D.fv R.fv) (hyp_hnwcutclassinj_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.imp (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.imp (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))) (.classEq (.cv x) (.cv y)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ D.fv ∪ R.fv
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have p0000 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))
  have p0001 :=
    @g_simpr (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
  have p0002 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))) p0000 p0001
  have p0003 :=
    @g_wppweconnex D R
  have p0004 :=
    Nominal.mp hyp_hnwcutclassinj_1 p0003
  have p0005 :=
    @g_a1i (syn_wbr R (syn_cconnex) D) (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) p0004
  have p0006 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))
  have p0007 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
  have p0008 :=
    @g_simpl (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0009 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv x) D) p0007 p0008
  have p0010 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (.classMem (.cv x) D) p0006 p0009
  have p0011 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))
  have p0012 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
  have p0013 :=
    @g_simpr (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0014 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv y) D) p0012 p0013
  have p0015 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (.classMem (.cv y) D) p0011 p0014
  have p0016 :=
    @g_connexd (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) D R (.cv x) (.cv y) p0005 p0010 p0015
  have p0017 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y))
  have p0018 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))
  have p0019 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
  have p0020 :=
    @g_simpl (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0021 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv x) D) p0019 p0020
  have p0022 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (.classMem (.cv x) D) p0018 p0021
  have p0023 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y))) (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (.classMem (.cv x) D) p0017 p0022
  have p0024 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y))
  have p0025 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y))
  have p0026 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))
  have p0027 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y))) (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (syn_wne (.cv x) (.cv y)) p0025 p0026
  have p0028 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y))) (syn_wbr (.cv x) R (.cv y)) (syn_wne (.cv x) (.cv y)) p0024 p0027
  have p0029 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv x) D) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wne (.cv x) (.cv y))) p0023 p0028
  have p0030 :=
    @g_elstrictseg y x D R
  have p0031 :=
    @g_biimpri (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_wa (.classMem (.cv x) D) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wne (.cv x) (.cv y)))) p0030
  have p0032 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y))) (syn_wa (.classMem (.cv x) D) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wne (.cv x) (.cv y)))) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) p0029 p0031
  have p0033 :=
    @g_ex (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) p0032
  have p0034 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x))
  have p0035 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))
  have p0036 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
  have p0037 :=
    @g_simpr (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0038 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv y) D) p0036 p0037
  have p0039 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (.classMem (.cv y) D) p0035 p0038
  have p0040 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x))) (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (.classMem (.cv y) D) p0034 p0039
  have p0041 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x))
  have p0042 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x))
  have p0043 :=
    @g_simpr (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))
  have p0044 :=
    @g_necomd (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (.cv x) (.cv y) p0043
  have p0045 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x))) (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (syn_wne (.cv y) (.cv x)) p0042 p0044
  have p0046 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x))) (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)) p0041 p0045
  have p0047 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x))) (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))) p0040 p0046
  have p0048 :=
    @g_elstrictseg x y D R
  have p0049 :=
    @g_biimpri (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))) p0048
  have p0050 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x))) (syn_wa (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0047 p0049
  have p0051 :=
    @g_ex (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0050
  have p0052 :=
    @g_orim12d (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv y)) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (syn_wbr (.cv y) R (.cv x)) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0033 p0051
  have p0053 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x))) (syn_wo (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) p0016 p0052
  have p0054 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))
  have p0055 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
  have p0056 :=
    @g_simpr (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0057 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv y) D) p0055 p0056
  have p0058 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (.classMem (.cv y) D) p0054 p0057
  have p0059 :=
    @g_hnwcutclassltne x y D R dv_cache_0001 hyp_hnwcutclassinj_1
  have p0060 :=
    @g_ex (.classMem (.cv y) D) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (.neg (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) p0059
  have p0061 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (.classMem (.cv y) D) (.imp (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (.neg (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))))) p0058 p0060
  have p0062 :=
    @g_simpl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))
  have p0063 :=
    @g_simpl (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))
  have p0064 :=
    @g_simpl (.classMem (.cv x) D) (.classMem (.cv y) D)
  have p0065 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classMem (.cv x) D) p0063 p0064
  have p0066 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (.classMem (.cv x) D) p0062 p0065
  have p0067 :=
    @g_hnwcutclassltne y x D R dv_cache_0001 hyp_hnwcutclassinj_1
  have p0068 :=
    @g_ex (.classMem (.cv x) D) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.neg (.classEq (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)))) p0067
  have p0069 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (.classMem (.cv x) D) (.imp (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.neg (.classEq (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))))) p0066 p0068
  have p0070 :=
    @g_eqcom (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))
  have p0071 :=
    @g_biimpi (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))) (.classEq (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))) p0070
  have p0072 :=
    @g_con3i (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))) (.classEq (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D))) p0071
  have p0073 :=
    @g_syl6 (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (.neg (.classEq (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)))) (.neg (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) p0069 p0072
  have p0074 :=
    @g_jaod (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (.neg (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0061 p0073
  have p0075 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (syn_wo (.classMem (.cv x) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))) (.classMem (.cv y) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (.neg (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) p0053 p0074
  have p0076 :=
    @g_pm2_21dd (syn_wa (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y))) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))) (.neg (syn_wne (.cv x) (.cv y))) p0002 p0075
  have p0077 :=
    @g_pm2_01da (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (syn_wne (.cv x) (.cv y)) p0076
  have p0078 :=
    @g_nne (.cv x) (.cv y)
  have p0079 :=
    @g_sylib (syn_wa (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)))) (.neg (syn_wne (.cv x) (.cv y))) (.classEq (.cv x) (.cv y)) p0077 p0078
  have p0080 :=
    @g_ex (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))) (.classEq (.cv x) (.cv y)) p0079
  exact p0080

noncomputable def g_hnwcutclassinjcl
    (B : Class) (C : Class) (D : Class) (R : Class) (dv_D_R : Disjoint D.fv R.fv) (hyp_hnwcutclassinjcl_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (.imp (syn_wa (.classMem B D) (.classMem C D)) (.imp (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D))) (.classEq B C))) := by
  let proofSupport : Finset Var := B.fv ∪ C.fv ∪ D.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : Disjoint ((Class.cv x)).fv (R).fv := by
    exact (show Disjoint ((Class.cv x)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({x} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show x ∉ (R).fv from (by exact fresh_x_not_R))))))
  have dv_cache_0002 : Disjoint ((Class.cv y)).fv (R).fv := by
    clear dv_cache_0001
    exact (show Disjoint ((Class.cv y)).fv (R).fv from (by rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint (({y} : Finset Var)) ((R).fv) from (Finset.disjoint_singleton_left.mpr (show y ∉ (R).fv from (by exact fresh_y_not_R))))))
  have dv_cache_0003 : Disjoint (D).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0004 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Wff.imp (syn_wa (.classMem B D) (.classMem C D)) (.imp (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D))) (.classEq B C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, fresh_y_not_D, fresh_y_not_C, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((Wff.imp (syn_wa (.classMem B D) (.classMem (.cv y) D)) (.imp (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))) (.classEq B (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, fresh_x_not_D, fresh_x_ne_y, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (.classMem B D) (.classMem C D)
  have p0001 :=
    @g_elex B D
  have p0002 :=
    @g_syl (syn_wa (.classMem B D) (.classMem C D)) (.classMem B D) (.classMem B (syn_cvv)) p0000 p0001
  have p0003 :=
    @g_simpr (.classMem B D) (.classMem C D)
  have p0004 :=
    @g_elex C D
  have p0005 :=
    @g_syl (syn_wa (.classMem B D) (.classMem C D)) (.classMem C D) (.classMem C (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_jca (syn_wa (.classMem B D) (.classMem C D)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv)) p0002 p0005
  have p0007 :=
    @g_eleq1 (.cv x) B D
  have p0008 :=
    @g_biid (.classMem (.cv y) D)
  have p0009 :=
    @g_a1i (syn_wb (.classMem (.cv y) D) (.classMem (.cv y) D)) (.classEq (.cv x) B) p0008
  have p0010 :=
    @g_anbi12d (.classEq (.cv x) B) (.classMem (.cv x) D) (.classMem B D) (.classMem (.cv y) D) (.classMem (.cv y) D) p0007 p0009
  have p0011 :=
    @g_hnwcutcodeeq3 (.cv x) B D R dv_cache_0001
  have p0012 :=
    @g_eceq1 (syn_chnwcutcode R D (.cv x)) (syn_chnwcutcode R D B) (syn_chwniso D)
  have p0013 :=
    @g_syl (.classEq (.cv x) B) (.classEq (syn_chnwcutcode R D (.cv x)) (syn_chnwcutcode R D B)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D))) p0011 p0012
  have p0014 :=
    @g_eqeq1d (.classEq (.cv x) B) (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)) p0013
  have p0015 :=
    @g_id (.classEq (.cv x) B)
  have p0016 :=
    @g_eqeq1d (.classEq (.cv x) B) (.cv x) B (.cv y) p0015
  have p0017 :=
    @g_imbi12d (.classEq (.cv x) B) (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))) (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))) (.classEq (.cv x) (.cv y)) (.classEq B (.cv y)) p0014 p0016
  have p0018 :=
    @g_imbi12d (.classEq (.cv x) B) (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (syn_wa (.classMem B D) (.classMem (.cv y) D)) (.imp (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))) (.classEq (.cv x) (.cv y))) (.imp (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))) (.classEq B (.cv y))) p0010 p0017
  have p0019 :=
    @g_biid (.classMem B D)
  have p0020 :=
    @g_a1i (syn_wb (.classMem B D) (.classMem B D)) (.classEq (.cv y) C) p0019
  have p0021 :=
    @g_eleq1 (.cv y) C D
  have p0022 :=
    @g_anbi12d (.classEq (.cv y) C) (.classMem B D) (.classMem B D) (.classMem (.cv y) D) (.classMem C D) p0020 p0021
  have p0023 :=
    @g_hnwcutcodeeq3 (.cv y) C D R dv_cache_0002
  have p0024 :=
    @g_eceq1 (syn_chnwcutcode R D (.cv y)) (syn_chnwcutcode R D C) (syn_chwniso D)
  have p0025 :=
    @g_syl (.classEq (.cv y) C) (.classEq (syn_chnwcutcode R D (.cv y)) (syn_chnwcutcode R D C)) (.classEq (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D))) p0023 p0024
  have p0026 :=
    @g_eqeq2d (.classEq (.cv y) C) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D)) p0025
  have p0027 :=
    @g_id (.classEq (.cv y) C)
  have p0028 :=
    @g_eqeq2d (.classEq (.cv y) C) (.cv y) C B p0027
  have p0029 :=
    @g_imbi12d (.classEq (.cv y) C) (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))) (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D))) (.classEq B (.cv y)) (.classEq B C) p0026 p0028
  have p0030 :=
    @g_imbi12d (.classEq (.cv y) C) (syn_wa (.classMem B D) (.classMem (.cv y) D)) (syn_wa (.classMem B D) (.classMem C D)) (.imp (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))) (.classEq B (.cv y))) (.imp (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D))) (.classEq B C)) p0022 p0029
  have p0031 :=
    @g_hnwcutclassinj x y D R dv_cache_0003 hyp_hnwcutclassinjcl_1
  have p0032 :=
    @g_vtocl2g (.imp (syn_wa (.classMem (.cv x) D) (.classMem (.cv y) D)) (.imp (.classEq (syn_cec (syn_chnwcutcode R D (.cv x)) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))) (.classEq (.cv x) (.cv y)))) (.imp (syn_wa (.classMem B D) (.classMem (.cv y) D)) (.imp (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D (.cv y)) (syn_chwniso D))) (.classEq B (.cv y)))) (.imp (syn_wa (.classMem B D) (.classMem C D)) (.imp (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D))) (.classEq B C))) x y B C (syn_cvv) (syn_cvv) dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 p0018 p0030 p0031
  have p0033 :=
    @g_syl (syn_wa (.classMem B D) (.classMem C D)) (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv))) (.imp (syn_wa (.classMem B D) (.classMem C D)) (.imp (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D))) (.classEq B C))) p0006 p0032
  have p0034 :=
    @g_pm2_43i (syn_wa (.classMem B D) (.classMem C D)) (.imp (.classEq (syn_cec (syn_chnwcutcode R D B) (syn_chwniso D)) (syn_cec (syn_chnwcutcode R D C) (syn_chwniso D))) (.classEq B C)) p0033
  exact p0034

#print axioms g_hnwcutclassinjcl

end NFChoice.DirectNominalPrf.WPPReplay
