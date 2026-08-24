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
import NominalWPPReplayChunk017Compact001Part053

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

noncomputable def g_wppstopstepfvnlecdndv
    (A : Class) (C : Class) (F : Class) (hyp_wppstopstepfvnlecdndv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppstopstepfvnlecdndv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F)))) (.imp (.neg (syn_wbr A (syn_clec) C)) (.classEq (syn_cfv (syn_cwppstopstep F C) A) A))) := by
  let proofSupport : Finset Var := A.fv ∪ C.fv ∪ F.fv
  have p0000 :=
    @g_simpl (.classMem A (syn_chwcards (syn_cvv))) (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F)))
  have p0001 :=
    @g_a1d (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F)))) (.classMem A (syn_chwcards (syn_cvv))) (.neg (syn_wbr A (syn_clec) C)) p0000
  have p0002 :=
    @g_wppstopactlecbindv A C F
  have p0003 :=
    @g_biimpd (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F)))) (.classMem A (syn_cwppstopact F C)) (syn_wbr A (syn_clec) C) p0002
  have p0004 :=
    @g_con3d (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F)))) (.classMem A (syn_cwppstopact F C)) (syn_wbr A (syn_clec) C) p0003
  have p0005 :=
    @g_jcad (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F)))) (.neg (syn_wbr A (syn_clec) C)) (.classMem A (syn_chwcards (syn_cvv))) (.neg (.classMem A (syn_cwppstopact F C))) p0001 p0004
  have p0006 :=
    @g_wppstopstepfvidleclndv A C F hyp_wppstopstepfvnlecdndv_1 hyp_wppstopstepfvnlecdndv_2
  have p0007 :=
    @g_syl6 (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F)))) (.neg (syn_wbr A (syn_clec) C)) (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.neg (.classMem A (syn_cwppstopact F C)))) (.classEq (syn_cfv (syn_cwppstopstep F C) A) A) p0005 p0006
  exact p0007

noncomputable def g_wppstopsteptchomdndv
    (x : Var) (C : Class) (F : Class) (hyp_wppstopsteptchomdndv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppstopsteptchomdndv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_chwcards (syn_cvv)))) (hyp_wppstopsteptchomdndv_3 : Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf (.imp (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.classEq (syn_ctc (syn_cfv (syn_cwppstopstep F C) (.cv x))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (.cv x))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ C.fv ∪ F.fv
  have p0000 :=
    @g_simpr (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wbr (.cv x) (syn_clec) C)
  have p0001 :=
    @g_simpl (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wbr (.cv x) (syn_clec) C)
  have p0002 :=
    @g_n_3simpa (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))
  have p0003 :=
    @g_simpl (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
  have p0004 :=
    @g_syl (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wa (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))) (.classMem (.cv x) (syn_chwcards (syn_cvv))) p0002 p0003
  have p0005 :=
    @g_n_3simpa (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))
  have p0006 :=
    @g_simpr (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
  have p0007 :=
    @g_syl (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wa (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) p0005 p0006
  have p0008 :=
    @g_simpl (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))
  have p0009 :=
    @g_syl6 (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))) (.classMem (.cv x) (syn_cdm F)) p0007 p0008
  have p0010 :=
    @g_jca (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classMem (.cv x) (syn_cdm F))) p0004 p0009
  have p0011 :=
    @g_wppstopstepfvlecdndv (.cv x) C F hyp_wppstopsteptchomdndv_1 hyp_wppstopsteptchomdndv_2
  have p0012 :=
    @g_syl (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wa (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classMem (.cv x) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_cfv (syn_cwppstopstep F C) (.cv x)) (syn_cfv F (.cv x)))) p0010 p0011
  have p0013 :=
    @g_syl (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wbr (.cv x) (syn_clec) C)) (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_cfv (syn_cwppstopstep F C) (.cv x)) (syn_cfv F (.cv x)))) p0001 p0012
  have p0014 :=
    @g_mpd (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wbr (.cv x) (syn_clec) C)) (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_cfv (syn_cwppstopstep F C) (.cv x)) (syn_cfv F (.cv x))) p0000 p0013
  have p0015 :=
    @g_tceq (syn_cfv (syn_cwppstopstep F C) (.cv x)) (syn_cfv F (.cv x))
  have p0016 :=
    @g_syl (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wbr (.cv x) (syn_clec) C)) (.classEq (syn_cfv (syn_cwppstopstep F C) (.cv x)) (syn_cfv F (.cv x))) (.classEq (syn_ctc (syn_cfv (syn_cwppstopstep F C) (.cv x))) (syn_ctc (syn_cfv F (.cv x)))) p0014 p0015
  have p0017 :=
    @g_simpr (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wbr (.cv x) (syn_clec) C)
  have p0018 :=
    @g_simpl (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wbr (.cv x) (syn_clec) C)
  have p0019 :=
    @g_n_3simpc (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))
  have p0020 :=
    @g_simpr (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))
  have p0021 :=
    @g_syl (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wa (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))) p0019 p0020
  have p0022 :=
    @g_syl (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wbr (.cv x) (syn_clec) C)) (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))))) p0018 p0021
  have p0023 :=
    @g_mpd (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wbr (.cv x) (syn_clec) C)) (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))) p0017 p0022
  have p0024 :=
    @g_simpr (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wbr (.cv x) (syn_clec) C)
  have p0025 :=
    @g_simpl (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wbr (.cv x) (syn_clec) C)
  have p0026 :=
    @g_n_3simpa (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))
  have p0027 :=
    @g_simpl (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
  have p0028 :=
    @g_syl (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wa (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))) (.classMem (.cv x) (syn_chwcards (syn_cvv))) p0026 p0027
  have p0029 :=
    @g_hwcardssnc (syn_cvv)
  have p0030 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (.cv x) p0029
  have p0031 :=
    @g_syl (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.classMem (.cv x) (syn_cncs)) p0028 p0030
  have p0032 :=
    @g_hwcardssnc (syn_cvv)
  have p0033 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) C p0032
  have p0034 :=
    Nominal.mp hyp_wppstopsteptchomdndv_3 p0033
  have p0035 :=
    @g_a1i (.classMem C (syn_cncs)) (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) p0034
  have p0036 :=
    @g_jca (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.classMem (.cv x) (syn_cncs)) (.classMem C (syn_cncs)) p0031 p0035
  have p0037 :=
    @g_tlecg (.cv x) C
  have p0038 :=
    @g_syl (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wa (.classMem (.cv x) (syn_cncs)) (.classMem C (syn_cncs))) (syn_wb (syn_wbr (.cv x) (syn_clec) C) (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C))) p0036 p0037
  have p0039 :=
    @g_biimpd (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wbr (.cv x) (syn_clec) C) (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C)) p0038
  have p0040 :=
    @g_syl (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wbr (.cv x) (syn_clec) C)) (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C))) p0025 p0039
  have p0041 :=
    @g_mpd (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wbr (.cv x) (syn_clec) C)) (syn_wbr (.cv x) (syn_clec) C) (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C)) p0024 p0040
  have p0042 :=
    @g_simpl (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wbr (.cv x) (syn_clec) C)
  have p0043 :=
    @g_n_3simpa (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))
  have p0044 :=
    @g_simpl (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
  have p0045 :=
    @g_syl (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wa (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))) (.classMem (.cv x) (syn_chwcards (syn_cvv))) p0043 p0044
  have p0046 :=
    @g_hwcardstcclndv (.cv x)
  have p0047 :=
    @g_id (.classMem (syn_ctc (.cv x)) (syn_chwcards (syn_cvv)))
  have p0048 :=
    @g_n_3syl (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.classMem (syn_ctc (.cv x)) (syn_chwcards (syn_cvv))) (.classMem (syn_ctc (.cv x)) (syn_chwcards (syn_cvv))) p0045 p0046 p0047
  have p0049 :=
    @g_n_3simpa (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))
  have p0050 :=
    @g_simpl (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
  have p0051 :=
    @g_syl (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wa (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))) (.classMem (.cv x) (syn_chwcards (syn_cvv))) p0049 p0050
  have p0052 :=
    @g_hwcardssnc (syn_cvv)
  have p0053 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (.cv x) p0052
  have p0054 :=
    @g_syl (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.classMem (.cv x) (syn_cncs)) p0051 p0053
  have p0055 :=
    @g_hwcardssnc (syn_cvv)
  have p0056 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) C p0055
  have p0057 :=
    Nominal.mp hyp_wppstopsteptchomdndv_3 p0056
  have p0058 :=
    @g_a1i (.classMem C (syn_cncs)) (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) p0057
  have p0059 :=
    @g_jca (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.classMem (.cv x) (syn_cncs)) (.classMem C (syn_cncs)) p0054 p0058
  have p0060 :=
    @g_tlecg (.cv x) C
  have p0061 :=
    @g_syl (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wa (.classMem (.cv x) (syn_cncs)) (.classMem C (syn_cncs))) (syn_wb (syn_wbr (.cv x) (syn_clec) C) (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C))) p0059 p0060
  have p0062 :=
    @g_biimprd (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wbr (.cv x) (syn_clec) C) (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C)) p0061
  have p0063 :=
    @g_n_3simpa (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))
  have p0064 :=
    @g_simpr (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
  have p0065 :=
    @g_syl (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wa (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) p0063 p0064
  have p0066 :=
    @g_syld (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C)) (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))) p0062 p0065
  have p0067 :=
    @g_simpr (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))
  have p0068 :=
    @g_syl6 (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C)) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))) (.classMem (syn_ctc (.cv x)) (syn_cdm F)) p0066 p0067
  have p0069 :=
    @g_jca (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.classMem (syn_ctc (.cv x)) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))) p0048 p0068
  have p0070 :=
    @g_wppstopstepfvlecdndv (syn_ctc (.cv x)) (syn_ctc C) F hyp_wppstopsteptchomdndv_1 hyp_wppstopsteptchomdndv_2
  have p0071 :=
    @g_syl (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wa (.classMem (syn_ctc (.cv x)) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C)) (.classEq (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (.cv x))) (syn_cfv F (syn_ctc (.cv x))))) p0069 p0070
  have p0072 :=
    @g_syl (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wbr (.cv x) (syn_clec) C)) (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.imp (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C)) (.classEq (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (.cv x))) (syn_cfv F (syn_ctc (.cv x))))) p0042 p0071
  have p0073 :=
    @g_mpd (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wbr (.cv x) (syn_clec) C)) (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C)) (.classEq (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (.cv x))) (syn_cfv F (syn_ctc (.cv x)))) p0041 p0072
  have p0074 :=
    @g_eqcomd (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wbr (.cv x) (syn_clec) C)) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (.cv x))) (syn_cfv F (syn_ctc (.cv x))) p0073
  have p0075 :=
    @g_n_3eqtrd (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wbr (.cv x) (syn_clec) C)) (syn_ctc (syn_cfv (syn_cwppstopstep F C) (.cv x))) (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (.cv x))) p0016 p0023 p0074
  have p0076 :=
    @g_ex (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv (syn_cwppstopstep F C) (.cv x))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (.cv x)))) p0075
  have p0077 :=
    @g_simpr (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.neg (syn_wbr (.cv x) (syn_clec) C))
  have p0078 :=
    @g_simpl (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.neg (syn_wbr (.cv x) (syn_clec) C))
  have p0079 :=
    @g_n_3simpa (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))
  have p0080 :=
    @g_simpl (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
  have p0081 :=
    @g_syl (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wa (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))) (.classMem (.cv x) (syn_chwcards (syn_cvv))) p0079 p0080
  have p0082 :=
    @g_n_3simpa (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))
  have p0083 :=
    @g_simpr (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
  have p0084 :=
    @g_syl (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wa (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) p0082 p0083
  have p0085 :=
    @g_simpl (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))
  have p0086 :=
    @g_syl6 (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))) (.classMem (.cv x) (syn_cdm F)) p0084 p0085
  have p0087 :=
    @g_jca (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classMem (.cv x) (syn_cdm F))) p0081 p0086
  have p0088 :=
    @g_wppstopstepfvnlecdndv (.cv x) C F hyp_wppstopsteptchomdndv_1 hyp_wppstopsteptchomdndv_2
  have p0089 :=
    @g_syl (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wa (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classMem (.cv x) (syn_cdm F)))) (.imp (.neg (syn_wbr (.cv x) (syn_clec) C)) (.classEq (syn_cfv (syn_cwppstopstep F C) (.cv x)) (.cv x))) p0087 p0088
  have p0090 :=
    @g_syl (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.neg (syn_wbr (.cv x) (syn_clec) C))) (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.imp (.neg (syn_wbr (.cv x) (syn_clec) C)) (.classEq (syn_cfv (syn_cwppstopstep F C) (.cv x)) (.cv x))) p0078 p0089
  have p0091 :=
    @g_mpd (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.neg (syn_wbr (.cv x) (syn_clec) C))) (.neg (syn_wbr (.cv x) (syn_clec) C)) (.classEq (syn_cfv (syn_cwppstopstep F C) (.cv x)) (.cv x)) p0077 p0090
  have p0092 :=
    @g_tceq (syn_cfv (syn_cwppstopstep F C) (.cv x)) (.cv x)
  have p0093 :=
    @g_syl (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.neg (syn_wbr (.cv x) (syn_clec) C))) (.classEq (syn_cfv (syn_cwppstopstep F C) (.cv x)) (.cv x)) (.classEq (syn_ctc (syn_cfv (syn_cwppstopstep F C) (.cv x))) (syn_ctc (.cv x))) p0091 p0092
  have p0094 :=
    @g_simpr (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.neg (syn_wbr (.cv x) (syn_clec) C))
  have p0095 :=
    @g_simpl (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.neg (syn_wbr (.cv x) (syn_clec) C))
  have p0096 :=
    @g_n_3simpa (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))
  have p0097 :=
    @g_simpl (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
  have p0098 :=
    @g_syl (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wa (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))) (.classMem (.cv x) (syn_chwcards (syn_cvv))) p0096 p0097
  have p0099 :=
    @g_hwcardssnc (syn_cvv)
  have p0100 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (.cv x) p0099
  have p0101 :=
    @g_syl (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.classMem (.cv x) (syn_cncs)) p0098 p0100
  have p0102 :=
    @g_hwcardssnc (syn_cvv)
  have p0103 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) C p0102
  have p0104 :=
    Nominal.mp hyp_wppstopsteptchomdndv_3 p0103
  have p0105 :=
    @g_a1i (.classMem C (syn_cncs)) (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) p0104
  have p0106 :=
    @g_jca (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.classMem (.cv x) (syn_cncs)) (.classMem C (syn_cncs)) p0101 p0105
  have p0107 :=
    @g_tlecg (.cv x) C
  have p0108 :=
    @g_syl (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wa (.classMem (.cv x) (syn_cncs)) (.classMem C (syn_cncs))) (syn_wb (syn_wbr (.cv x) (syn_clec) C) (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C))) p0106 p0107
  have p0109 :=
    @g_notbid (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wbr (.cv x) (syn_clec) C) (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C)) p0108
  have p0110 :=
    @g_biimpd (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.neg (syn_wbr (.cv x) (syn_clec) C)) (.neg (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C))) p0109
  have p0111 :=
    @g_syl (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.neg (syn_wbr (.cv x) (syn_clec) C))) (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.imp (.neg (syn_wbr (.cv x) (syn_clec) C)) (.neg (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C)))) p0095 p0110
  have p0112 :=
    @g_mpd (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.neg (syn_wbr (.cv x) (syn_clec) C))) (.neg (syn_wbr (.cv x) (syn_clec) C)) (.neg (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C))) p0094 p0111
  have p0113 :=
    @g_simpl (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.neg (syn_wbr (.cv x) (syn_clec) C))
  have p0114 :=
    @g_n_3simpa (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))
  have p0115 :=
    @g_simpl (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
  have p0116 :=
    @g_syl (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wa (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))) (.classMem (.cv x) (syn_chwcards (syn_cvv))) p0114 p0115
  have p0117 :=
    @g_hwcardstcclndv (.cv x)
  have p0118 :=
    @g_id (.classMem (syn_ctc (.cv x)) (syn_chwcards (syn_cvv)))
  have p0119 :=
    @g_n_3syl (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.classMem (syn_ctc (.cv x)) (syn_chwcards (syn_cvv))) (.classMem (syn_ctc (.cv x)) (syn_chwcards (syn_cvv))) p0116 p0117 p0118
  have p0120 :=
    @g_n_3simpa (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))
  have p0121 :=
    @g_simpl (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
  have p0122 :=
    @g_syl (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wa (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))) (.classMem (.cv x) (syn_chwcards (syn_cvv))) p0120 p0121
  have p0123 :=
    @g_hwcardssnc (syn_cvv)
  have p0124 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (.cv x) p0123
  have p0125 :=
    @g_syl (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.classMem (.cv x) (syn_cncs)) p0122 p0124
  have p0126 :=
    @g_hwcardssnc (syn_cvv)
  have p0127 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) C p0126
  have p0128 :=
    Nominal.mp hyp_wppstopsteptchomdndv_3 p0127
  have p0129 :=
    @g_a1i (.classMem C (syn_cncs)) (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) p0128
  have p0130 :=
    @g_jca (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.classMem (.cv x) (syn_cncs)) (.classMem C (syn_cncs)) p0125 p0129
  have p0131 :=
    @g_tlecg (.cv x) C
  have p0132 :=
    @g_syl (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wa (.classMem (.cv x) (syn_cncs)) (.classMem C (syn_cncs))) (syn_wb (syn_wbr (.cv x) (syn_clec) C) (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C))) p0130 p0131
  have p0133 :=
    @g_biimprd (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wbr (.cv x) (syn_clec) C) (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C)) p0132
  have p0134 :=
    @g_n_3simpa (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))
  have p0135 :=
    @g_simpr (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))
  have p0136 :=
    @g_syl (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wa (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) p0134 p0135
  have p0137 :=
    @g_syld (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C)) (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))) p0133 p0136
  have p0138 :=
    @g_simpr (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))
  have p0139 :=
    @g_syl6 (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C)) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))) (.classMem (syn_ctc (.cv x)) (syn_cdm F)) p0137 p0138
  have p0140 :=
    @g_jca (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.classMem (syn_ctc (.cv x)) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C)) (.classMem (syn_ctc (.cv x)) (syn_cdm F))) p0119 p0139
  have p0141 :=
    @g_wppstopstepfvnlecdndv (syn_ctc (.cv x)) (syn_ctc C) F hyp_wppstopsteptchomdndv_1 hyp_wppstopsteptchomdndv_2
  have p0142 :=
    @g_syl (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wa (.classMem (syn_ctc (.cv x)) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (.neg (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C))) (.classEq (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (.cv x))) (syn_ctc (.cv x)))) p0140 p0141
  have p0143 :=
    @g_syl (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.neg (syn_wbr (.cv x) (syn_clec) C))) (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.imp (.neg (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C))) (.classEq (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (.cv x))) (syn_ctc (.cv x)))) p0113 p0142
  have p0144 :=
    @g_mpd (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.neg (syn_wbr (.cv x) (syn_clec) C))) (.neg (syn_wbr (syn_ctc (.cv x)) (syn_clec) (syn_ctc C))) (.classEq (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (.cv x))) (syn_ctc (.cv x))) p0112 p0143
  have p0145 :=
    @g_eqcomd (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.neg (syn_wbr (.cv x) (syn_clec) C))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (.cv x))) (syn_ctc (.cv x)) p0144
  have p0146 :=
    @g_eqtrd (syn_wa (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.neg (syn_wbr (.cv x) (syn_clec) C))) (syn_ctc (syn_cfv (syn_cwppstopstep F C) (.cv x))) (syn_ctc (.cv x)) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (.cv x))) p0093 p0145
  have p0147 :=
    @g_ex (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (.neg (syn_wbr (.cv x) (syn_clec) C)) (.classEq (syn_ctc (syn_cfv (syn_cwppstopstep F C) (.cv x))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (.cv x)))) p0146
  have p0148 :=
    @g_pm2_61d (syn_w3a (.classMem (.cv x) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv x) (syn_clec) C) (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (syn_ctc (.cv x)) (syn_cdm F)))) (.imp (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv F (syn_ctc (.cv x)))))) (syn_wbr (.cv x) (syn_clec) C) (.classEq (syn_ctc (syn_cfv (syn_cwppstopstep F C) (.cv x))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (.cv x)))) p0076 p0147
  exact p0148

#print axioms g_wppstopsteptchomdndv

end NFChoice.DirectNominalPrf.WPPReplay
