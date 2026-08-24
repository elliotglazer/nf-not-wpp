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
import NominalWPPReplayChunk017Compact001

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

noncomputable def g_cfbhncardpowershiftndv
    (A : Class) (hyp_cfbhncardpowershiftndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_chncard (syn_cpw (syn_cpw1 A))) (syn_ctc (syn_chncard (syn_cpw A)))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_pwex A hyp_cfbhncardpowershiftndv_1
  have p0001 :=
    @g_hncardtcshiftndv (syn_cpw A) p0000
  have p0002 :=
    @g_pwex A hyp_cfbhncardpowershiftndv_1
  have p0003 :=
    @g_pw1ex (syn_cpw A) p0002
  have p0004 :=
    @g_pw1ex A hyp_cfbhncardpowershiftndv_1
  have p0005 :=
    @g_pwex (syn_cpw1 A) p0004
  have p0006 :=
    @g_ncpwpw1 A hyp_cfbhncardpowershiftndv_1
  have p0007 :=
    @g_eqcomi (syn_cnc (syn_cpw (syn_cpw1 A))) (syn_cnc (syn_cpw1 (syn_cpw A))) p0006
  have p0008 :=
    @g_hncardnceqndv (syn_cpw1 (syn_cpw A)) (syn_cpw (syn_cpw1 A)) p0003 p0005 p0007
  have p0009 :=
    @g_eqtri (syn_ctc (syn_chncard (syn_cpw A))) (syn_chncard (syn_cpw1 (syn_cpw A))) (syn_chncard (syn_cpw (syn_cpw1 A))) p0001 p0008
  have p0010 :=
    @g_eqcomi (syn_ctc (syn_chncard (syn_cpw A))) (syn_chncard (syn_cpw (syn_cpw1 A))) p0009
  exact p0010

noncomputable def g_cfbtceqi
    (A : Class) (B : Class) (hyp_cfbtceqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_ctc A) (syn_ctc B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_tceq A B
  have p0001 :=
    Nominal.mp hyp_cfbtceqi_1 p0000
  exact p0001

noncomputable def g_cfbhncardpw1ceqndv
     :
    Nominal.NPrf (.classEq (syn_chncard (syn_cpw (syn_c1c))) (syn_chncard (syn_c1c))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_n_1cex
  have p0001 :=
    @g_pwex (syn_c1c) p0000
  have p0002 :=
    @g_n_1cex
  have p0003 :=
    @g_ncpw1c
  have p0004 :=
    @g_hncardnceqndv (syn_cpw (syn_c1c)) (syn_c1c) p0001 p0002 p0003
  exact p0004

noncomputable def g_cfbhncardpwpw16stepndv
     :
    Nominal.NPrf (.classEq (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_n_1cex
  have p0001 :=
    @g_pw1ex (syn_c1c) p0000
  have p0002 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0001
  have p0003 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0002
  have p0004 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0003
  have p0005 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0004
  have p0006 :=
    @g_cfbhncardpowershiftndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0005
  exact p0006

noncomputable def g_cfbhncardpwpw15stepndv
     :
    Nominal.NPrf (.classEq (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_n_1cex
  have p0001 :=
    @g_pw1ex (syn_c1c) p0000
  have p0002 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0001
  have p0003 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0002
  have p0004 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0003
  have p0005 :=
    @g_cfbhncardpowershiftndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0004
  exact p0005

noncomputable def g_cfbhncardpwpw14stepndv
     :
    Nominal.NPrf (.classEq (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_n_1cex
  have p0001 :=
    @g_pw1ex (syn_c1c) p0000
  have p0002 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0001
  have p0003 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0002
  have p0004 :=
    @g_cfbhncardpowershiftndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0003
  exact p0004

noncomputable def g_cfbhncardpwpw13stepndv
     :
    Nominal.NPrf (.classEq (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_c1c))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_n_1cex
  have p0001 :=
    @g_pw1ex (syn_c1c) p0000
  have p0002 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0001
  have p0003 :=
    @g_cfbhncardpowershiftndv (syn_cpw1 (syn_cpw1 (syn_c1c))) p0002
  exact p0003

noncomputable def g_cfbhncardpwpw12stepndv
     :
    Nominal.NPrf (.classEq (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_c1c)))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_n_1cex
  have p0001 :=
    @g_pw1ex (syn_c1c) p0000
  have p0002 :=
    @g_cfbhncardpowershiftndv (syn_cpw1 (syn_c1c)) p0001
  exact p0002

noncomputable def g_cfbhncardpwpw11stepndv
     :
    Nominal.NPrf (.classEq (syn_chncard (syn_cpw (syn_cpw1 (syn_c1c)))) (syn_ctc (syn_chncard (syn_cpw (syn_c1c))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_n_1cex
  have p0001 :=
    @g_cfbhncardpowershiftndv (syn_c1c) p0000
  exact p0001

noncomputable def g_cfbhncardpwpw16to4ndv
     :
    Nominal.NPrf (.classEq (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_cfbhncardpwpw16stepndv
  have p0001 :=
    @g_cfbhncardpwpw15stepndv
  have p0002 :=
    @g_tceq (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    @g_eqtri (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) p0000 p0003
  exact p0004

noncomputable def g_cfbhncardpwpw14step2tndv
     :
    Nominal.NPrf (.classEq (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_cfbhncardpwpw14stepndv
  have p0001 :=
    @g_cfbtceqi (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) p0000
  have p0002 :=
    @g_cfbtceqi (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) p0001
  exact p0002

noncomputable def g_cfbhncardpwpw13step3tndv
     :
    Nominal.NPrf (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_cfbhncardpwpw13stepndv
  have p0001 :=
    @g_cfbtceqi (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0000
  have p0002 :=
    @g_cfbtceqi (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_c1c))))))) p0001
  have p0003 :=
    @g_cfbtceqi (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) p0002
  exact p0003

noncomputable def g_cfbhncardpwpw12step4tndv
     :
    Nominal.NPrf (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_c1c)))))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_cfbhncardpwpw12stepndv
  have p0001 :=
    @g_cfbtceqi (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_c1c))))) p0000
  have p0002 :=
    @g_cfbtceqi (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_c1c)))))) p0001
  have p0003 :=
    @g_cfbtceqi (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_c1c))))))) p0002
  have p0004 :=
    @g_cfbtceqi (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_c1c)))))))) p0003
  exact p0004

noncomputable def g_cfbhncardpwpw11step5tndv
     :
    Nominal.NPrf (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_c1c))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_c1c)))))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_cfbhncardpwpw11stepndv
  have p0001 :=
    @g_cfbtceqi (syn_chncard (syn_cpw (syn_cpw1 (syn_c1c)))) (syn_ctc (syn_chncard (syn_cpw (syn_c1c)))) p0000
  have p0002 :=
    @g_cfbtceqi (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_c1c))))) (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_c1c))))) p0001
  have p0003 :=
    @g_cfbtceqi (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_c1c)))))) (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_c1c)))))) p0002
  have p0004 :=
    @g_cfbtceqi (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_c1c))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_c1c))))))) p0003
  have p0005 :=
    @g_cfbtceqi (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_c1c)))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_c1c)))))))) p0004
  exact p0005

noncomputable def g_cfbhncardpwpw16to3ndv
     :
    Nominal.NPrf (.classEq (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_cfbhncardpwpw16to4ndv
  have p0001 :=
    @g_cfbhncardpwpw14step2tndv
  have p0002 :=
    @g_eqtri (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) p0000 p0001
  exact p0002

noncomputable def g_cfbhncardpwpw16to2ndv
     :
    Nominal.NPrf (.classEq (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_cfbhncardpwpw16to3ndv
  have p0001 :=
    @g_cfbhncardpwpw13step3tndv
  have p0002 :=
    @g_eqtri (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) p0000 p0001
  exact p0002

noncomputable def g_cfbhncardpwpw16to1ndv
     :
    Nominal.NPrf (.classEq (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_c1c)))))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_cfbhncardpwpw16to2ndv
  have p0001 :=
    @g_cfbhncardpwpw12step4tndv
  have p0002 :=
    @g_eqtri (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_c1c))))))))) p0000 p0001
  exact p0002

noncomputable def g_cfbhncardpwpw16to0ndv
     :
    Nominal.NPrf (.classEq (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_c1c)))))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_cfbhncardpwpw16to1ndv
  have p0001 :=
    @g_cfbhncardpwpw11step5tndv
  have p0002 :=
    @g_eqtri (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_c1c))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_c1c))))))))) p0000 p0001
  exact p0002

noncomputable def g_cfbhncardtc3forwardndv
    (A : Class) (hyp_cfbhncardtc3forwardndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_chncard A)))) (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord A)))))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_hncardtc2 A hyp_cfbhncardtc3forwardndv_1
  have p0001 :=
    @g_cfbtceqi (syn_ctc (syn_ctc (syn_chncard A))) (syn_cnc (syn_cpw1 (syn_cpw1 (syn_chnord A)))) p0000
  have p0002 :=
    @g_hnordex A hyp_cfbhncardtc3forwardndv_1
  have p0003 :=
    @g_pw1ex (syn_chnord A) p0002
  have p0004 :=
    @g_pw1ex (syn_cpw1 (syn_chnord A)) p0003
  have p0005 :=
    @g_tcnc (syn_cpw1 (syn_cpw1 (syn_chnord A))) p0004
  have p0006 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_ctc (syn_chncard A)))) (syn_ctc (syn_cnc (syn_cpw1 (syn_cpw1 (syn_chnord A))))) (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord A))))) p0001 p0005
  exact p0006

noncomputable def g_cfbhncardtc3ndv
    (A : Class) (hyp_cfbhncardtc3ndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord A))))) (syn_ctc (syn_ctc (syn_ctc (syn_chncard A))))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_cfbhncardtc3forwardndv A hyp_cfbhncardtc3ndv_1
  have p0001 :=
    @g_eqcomi (syn_ctc (syn_ctc (syn_ctc (syn_chncard A)))) (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord A))))) p0000
  exact p0001

noncomputable def g_cfbhncardpw1ceq6tndv
     :
    Nominal.NPrf (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_c1c))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_cfbhncardpw1ceqndv
  have p0001 :=
    @g_cfbtceqi (syn_chncard (syn_cpw (syn_c1c))) (syn_chncard (syn_c1c)) p0000
  have p0002 :=
    @g_cfbtceqi (syn_ctc (syn_chncard (syn_cpw (syn_c1c)))) (syn_ctc (syn_chncard (syn_c1c))) p0001
  have p0003 :=
    @g_cfbtceqi (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_c1c))))) (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))) p0002
  have p0004 :=
    @g_cfbtceqi (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_c1c)))))) (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))) p0003
  have p0005 :=
    @g_cfbtceqi (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_c1c))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))) p0004
  have p0006 :=
    @g_cfbtceqi (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_c1c)))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))) p0005
  exact p0006

noncomputable def g_cfbhncardpwpw16basendv
     :
    Nominal.NPrf (.classEq (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_cfbhncardpwpw16to0ndv
  have p0001 :=
    @g_cfbhncardpw1ceq6tndv
  have p0002 :=
    @g_eqtri (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_c1c))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) p0000 p0001
  exact p0002

noncomputable def g_cfbsourceledgerndv
     :
    Nominal.NPrf (.classEq (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_n_1cex
  have p0001 :=
    @g_pw1ex (syn_c1c) p0000
  have p0002 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0001
  have p0003 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0002
  have p0004 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0003
  have p0005 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0004
  have p0006 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0005
  have p0007 :=
    @g_pwex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) p0006
  have p0008 :=
    @g_cfbhncardtc3ndv (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) p0007
  have p0009 :=
    @g_cfbhncardpwpw16basendv
  have p0010 :=
    @g_cfbtceqi (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) p0009
  have p0011 :=
    @g_cfbtceqi (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) p0010
  have p0012 :=
    @g_cfbtceqi (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) p0011
  have p0013 :=
    @g_eqtri (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) p0008 p0012
  exact p0013

noncomputable def g_cfbhncardpw2enpw1shiftndv
    (Y : Class) (Z : Class) (hyp_cfbhncardpw2enpw1shiftndv_1 : Nominal.NPrf (.classMem Z (syn_cvv))) (hyp_cfbhncardpw2enpw1shiftndv_2 : Nominal.NPrf (.classMem Y (syn_cvv))) (hyp_cfbhncardpw2enpw1shiftndv_3 : Nominal.NPrf (syn_wbr Z (syn_cen) (syn_cpw1 Y))) :
    Nominal.NPrf (.classEq (syn_chncard (syn_cpw (syn_cpw Z))) (syn_ctc (syn_chncard (syn_cpw (syn_cpw Y))))) := by
  let proofSupport : Finset Var := Y.fv ∪ Z.fv
  have p0000 :=
    @g_pwex Z hyp_cfbhncardpw2enpw1shiftndv_1
  have p0001 :=
    @g_pwex (syn_cpw Z) p0000
  have p0002 :=
    @g_pwex Y hyp_cfbhncardpw2enpw1shiftndv_2
  have p0003 :=
    @g_pwex (syn_cpw Y) p0002
  have p0004 :=
    @g_pw1ex (syn_cpw (syn_cpw Y)) p0003
  have p0005 :=
    @g_enpw Z (syn_cpw1 Y)
  have p0006 :=
    Nominal.mp hyp_cfbhncardpw2enpw1shiftndv_3 p0005
  have p0007 :=
    @g_enpw1pw Y hyp_cfbhncardpw2enpw1shiftndv_2
  have p0008 :=
    @g_ensymi (syn_cpw1 (syn_cpw Y)) (syn_cpw (syn_cpw1 Y))
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_pm3_2i (syn_wbr (syn_cpw Z) (syn_cen) (syn_cpw (syn_cpw1 Y))) (syn_wbr (syn_cpw (syn_cpw1 Y)) (syn_cen) (syn_cpw1 (syn_cpw Y))) p0006 p0009
  have p0011 :=
    @g_entr (syn_cpw Z) (syn_cpw (syn_cpw1 Y)) (syn_cpw1 (syn_cpw Y))
  have p0012 :=
    Nominal.mp p0010 p0011
  have p0013 :=
    @g_enpw (syn_cpw Z) (syn_cpw1 (syn_cpw Y))
  have p0014 :=
    Nominal.mp p0012 p0013
  have p0015 :=
    @g_pwex Y hyp_cfbhncardpw2enpw1shiftndv_2
  have p0016 :=
    @g_enpw1pw (syn_cpw Y) p0015
  have p0017 :=
    @g_ensymi (syn_cpw1 (syn_cpw (syn_cpw Y))) (syn_cpw (syn_cpw1 (syn_cpw Y)))
  have p0018 :=
    Nominal.mp p0016 p0017
  have p0019 :=
    @g_pm3_2i (syn_wbr (syn_cpw (syn_cpw Z)) (syn_cen) (syn_cpw (syn_cpw1 (syn_cpw Y)))) (syn_wbr (syn_cpw (syn_cpw1 (syn_cpw Y))) (syn_cen) (syn_cpw1 (syn_cpw (syn_cpw Y)))) p0014 p0018
  have p0020 :=
    @g_entr (syn_cpw (syn_cpw Z)) (syn_cpw (syn_cpw1 (syn_cpw Y))) (syn_cpw1 (syn_cpw (syn_cpw Y)))
  have p0021 :=
    Nominal.mp p0019 p0020
  have p0022 :=
    @g_pwex Z hyp_cfbhncardpw2enpw1shiftndv_1
  have p0023 :=
    @g_pwex (syn_cpw Z) p0022
  have p0024 :=
    @g_eqnc (syn_cpw (syn_cpw Z)) (syn_cpw1 (syn_cpw (syn_cpw Y))) p0023
  have p0025 :=
    @g_mpbir (.classEq (syn_cnc (syn_cpw (syn_cpw Z))) (syn_cnc (syn_cpw1 (syn_cpw (syn_cpw Y))))) (syn_wbr (syn_cpw (syn_cpw Z)) (syn_cen) (syn_cpw1 (syn_cpw (syn_cpw Y)))) p0021 p0024
  have p0026 :=
    @g_hncardnceqndv (syn_cpw (syn_cpw Z)) (syn_cpw1 (syn_cpw (syn_cpw Y))) p0001 p0004 p0025
  have p0027 :=
    @g_pwex Y hyp_cfbhncardpw2enpw1shiftndv_2
  have p0028 :=
    @g_pwex (syn_cpw Y) p0027
  have p0029 :=
    @g_hncardtcshiftndv (syn_cpw (syn_cpw Y)) p0028
  have p0030 :=
    @g_eqcomi (syn_ctc (syn_chncard (syn_cpw (syn_cpw Y)))) (syn_chncard (syn_cpw1 (syn_cpw (syn_cpw Y)))) p0029
  have p0031 :=
    @g_eqtri (syn_chncard (syn_cpw (syn_cpw Z))) (syn_chncard (syn_cpw1 (syn_cpw (syn_cpw Y)))) (syn_ctc (syn_chncard (syn_cpw (syn_cpw Y)))) p0026 p0030
  exact p0031

noncomputable def g_cfbtccli
    (A : Class) (hyp_cfbtccli_1 : Nominal.NPrf (.classMem A (syn_cncs))) :
    Nominal.NPrf (.classMem (syn_ctc A) (syn_cncs)) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_tccl A
  have p0001 :=
    Nominal.mp hyp_cfbtccli_1 p0000
  exact p0001

noncomputable def g_cfbtargetqbaseexndv
     :
    Nominal.NPrf (.classMem (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_n_1cex
  have p0001 :=
    @g_pw1ex (syn_c1c) p0000
  have p0002 :=
    @g_hnordex (syn_cpw1 (syn_c1c)) p0001
  have p0003 :=
    @g_pwex (syn_chnord (syn_cpw1 (syn_c1c))) p0002
  have p0004 :=
    @g_pwex (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))) p0003
  exact p0004

noncomputable def g_cfbtargetqncndv
     :
    Nominal.NPrf (.classMem (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))) (syn_cncs)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_cfbtargetqbaseexndv
  have p0001 :=
    @g_hncardnc (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))
  have p0002 :=
    Nominal.mp p0000 p0001
  exact p0002

noncomputable def g_cfbt6hncard1ncndv
     :
    Nominal.NPrf (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_cncs)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_hncardnc1ndv
  have p0001 :=
    @g_cfbtccli (syn_chncard (syn_c1c)) p0000
  have p0002 :=
    @g_cfbtccli (syn_ctc (syn_chncard (syn_c1c))) p0001
  have p0003 :=
    @g_cfbtccli (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))) p0002
  have p0004 :=
    @g_cfbtccli (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))) p0003
  have p0005 :=
    @g_cfbtccli (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))) p0004
  have p0006 :=
    @g_cfbtccli (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))) p0005
  exact p0006

noncomputable def g_cfbt2targetqncndv
     :
    Nominal.NPrf (.classMem (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))) (syn_cncs)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_cfbtargetqncndv
  have p0001 :=
    @g_cfbtccli (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))) p0000
  have p0002 :=
    @g_cfbtccli (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))) p0001
  exact p0002

noncomputable def g_cfbfixedblockcancel3ndv
     :
    Nominal.NPrf (.imp (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_cfbt6hncard1ncndv
  have p0001 :=
    @g_cfbt2targetqncndv
  have p0002 :=
    @g_tc3lecan (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))) p0000 p0001
  exact p0002

noncomputable def g_cfbfixedblockouterhartogsndv
    (R : Class) (hyp_cfbfixedblockouterhartogsndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))) :
    Nominal.NPrf (syn_wbr (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) := by
  let proofSupport : Finset Var := R.fv
  have p0000 :=
    @g_hncardsuccshiftedndv R hyp_cfbfixedblockouterhartogsndv_1
  have p0001 :=
    @g_wppconcrete6fntc7hncard1valndv
  have p0002 :=
    @g_breqtrri (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))) (syn_chncard (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_clec) p0000 p0001
  exact p0002

noncomputable def g_cfbfixedblockpointimpndv
    (R : Class) (hyp_cfbfixedblockpointimpndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))) :
    Nominal.NPrf (.imp (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))) := by
  let proofSupport : Finset Var := R.fv
  have p0000 :=
    @g_cfbfixedblockouterhartogsndv R hyp_cfbfixedblockpointimpndv_1
  have p0001 :=
    @g_cfbt6hncard1ncndv
  have p0002 :=
    @g_cfbt2targetqncndv
  have p0003 :=
    @g_wppconcrete6tcvalncndv
  have p0004 :=
    @g_lectr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
  have p0005 :=
    @g_mp3an (.classMem (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_cncs)) (.classMem (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))) (syn_cncs)) (.classMem (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (syn_cncs)) (.imp (syn_wa (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))) p0001 p0002 p0003 p0004
  have p0006 :=
    @g_mpan2 (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) p0000 p0005
  exact p0006

noncomputable def g_cfbhnordpw1shiftensymndv
    (A : Class) (hyp_cfbhnordpw1shiftensymndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wbr (syn_chnord (syn_cpw1 A)) (syn_cen) (syn_cpw1 (syn_chnord A))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_hnordpw1shiftenndv A hyp_cfbhnordpw1shiftensymndv_1
  have p0001 :=
    @g_ensym (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A))
  have p0002 :=
    @g_mpbi (syn_wbr (syn_cpw1 (syn_chnord A)) (syn_cen) (syn_chnord (syn_cpw1 A))) (syn_wbr (syn_chnord (syn_cpw1 A)) (syn_cen) (syn_cpw1 (syn_chnord A))) p0000 p0001
  exact p0002

noncomputable def g_cfbhncardpw2hnordpw1shiftndv
    (A : Class) (hyp_cfbhncardpw2hnordpw1shiftndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 A))))) (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord A)))))) := by
  let proofSupport : Finset Var := A.fv
  have p0000 :=
    @g_pw1ex A hyp_cfbhncardpw2hnordpw1shiftndv_1
  have p0001 :=
    @g_hnordex (syn_cpw1 A) p0000
  have p0002 :=
    @g_hnordex A hyp_cfbhncardpw2hnordpw1shiftndv_1
  have p0003 :=
    @g_cfbhnordpw1shiftensymndv A hyp_cfbhncardpw2hnordpw1shiftndv_1
  have p0004 :=
    @g_cfbhncardpw2enpw1shiftndv (syn_chnord A) (syn_chnord (syn_cpw1 A)) p0001 p0002 p0003
  exact p0004

noncomputable def g_cfbtarget6stepndv
     :
    Nominal.NPrf (.classEq (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_n_1cex
  have p0001 :=
    @g_pw1ex (syn_c1c) p0000
  have p0002 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0001
  have p0003 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0002
  have p0004 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0003
  have p0005 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0004
  have p0006 :=
    @g_cfbhncardpw2hnordpw1shiftndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0005
  exact p0006

noncomputable def g_cfbtarget5stepndv
     :
    Nominal.NPrf (.classEq (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_n_1cex
  have p0001 :=
    @g_pw1ex (syn_c1c) p0000
  have p0002 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0001
  have p0003 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0002
  have p0004 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0003
  have p0005 :=
    @g_cfbhncardpw2hnordpw1shiftndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0004
  exact p0005

noncomputable def g_cfbtarget4stepndv
     :
    Nominal.NPrf (.classEq (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_n_1cex
  have p0001 :=
    @g_pw1ex (syn_c1c) p0000
  have p0002 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0001
  have p0003 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0002
  have p0004 :=
    @g_cfbhncardpw2hnordpw1shiftndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0003
  exact p0004

noncomputable def g_cfbtarget3stepndv
     :
    Nominal.NPrf (.classEq (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_n_1cex
  have p0001 :=
    @g_pw1ex (syn_c1c) p0000
  have p0002 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0001
  have p0003 :=
    @g_cfbhncardpw2hnordpw1shiftndv (syn_cpw1 (syn_cpw1 (syn_c1c))) p0002
  exact p0003

noncomputable def g_cfbtarget2stepndv
     :
    Nominal.NPrf (.classEq (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_n_1cex
  have p0001 :=
    @g_pw1ex (syn_c1c) p0000
  have p0002 :=
    @g_cfbhncardpw2hnordpw1shiftndv (syn_cpw1 (syn_c1c)) p0001
  exact p0002

noncomputable def g_cfbtarget5step1tndv
     :
    Nominal.NPrf (.classEq (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_cfbtarget5stepndv
  have p0001 :=
    @g_cfbtceqi (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) p0000
  exact p0001

noncomputable def g_cfbtarget4step2tndv
     :
    Nominal.NPrf (.classEq (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_cfbtarget4stepndv
  have p0001 :=
    @g_cfbtceqi (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) p0000
  have p0002 :=
    @g_cfbtceqi (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) p0001
  exact p0002

noncomputable def g_cfbtarget3step3tndv
     :
    Nominal.NPrf (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_cfbtarget3stepndv
  have p0001 :=
    @g_cfbtceqi (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) p0000
  have p0002 :=
    @g_cfbtceqi (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) p0001
  have p0003 :=
    @g_cfbtceqi (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) p0002
  exact p0003

noncomputable def g_cfbtarget2step4tndv
     :
    Nominal.NPrf (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_cfbtarget2stepndv
  have p0001 :=
    @g_cfbtceqi (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))) p0000
  have p0002 :=
    @g_cfbtceqi (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))) p0001
  have p0003 :=
    @g_cfbtceqi (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))))) p0002
  have p0004 :=
    @g_cfbtceqi (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))))) p0003
  exact p0004

noncomputable def g_cfbtarget6to4ndv
     :
    Nominal.NPrf (.classEq (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_cfbtarget6stepndv
  have p0001 :=
    @g_cfbtarget5step1tndv
  have p0002 :=
    @g_eqtri (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) p0000 p0001
  exact p0002

noncomputable def g_cfbtarget6to3ndv
     :
    Nominal.NPrf (.classEq (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_cfbtarget6to4ndv
  have p0001 :=
    @g_cfbtarget4step2tndv
  have p0002 :=
    @g_eqtri (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) p0000 p0001
  exact p0002

noncomputable def g_cfbtarget6to2ndv
     :
    Nominal.NPrf (.classEq (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_cfbtarget6to3ndv
  have p0001 :=
    @g_cfbtarget3step3tndv
  have p0002 :=
    @g_eqtri (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) p0000 p0001
  exact p0002

noncomputable def g_cfbtargethncardledgerndv
     :
    Nominal.NPrf (.classEq (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_cfbtarget6to2ndv
  have p0001 :=
    @g_cfbtarget2step4tndv
  have p0002 :=
    @g_eqtri (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))))))) p0000 p0001
  exact p0002

noncomputable def g_cfbtargetledgerndv
     :
    Nominal.NPrf (.classEq (syn_cnc (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_chncard] using (Nominal.classEqRefl (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))))
  have p0001 :=
    @g_eqcomi (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (syn_cnc (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) p0000
  have p0002 :=
    @g_cfbtargethncardledgerndv
  have p0003 :=
    @g_eqtri (syn_cnc (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))))))) p0001 p0002
  exact p0003

noncomputable def g_cfbfixedblockledgercmpndv
     :
    Nominal.NPrf (syn_wb (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))) (syn_clec) (syn_cnc (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_cfbsourceledgerndv
  have p0001 :=
    @g_cfbtargetledgerndv
  have p0002 :=
    @g_breq12i (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_cnc (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))))))) (syn_clec) p0000 p0001
  exact p0002

noncomputable def g_cfbfixedblockledgercmpdndv
    (hyp_cfbfixedblockledgercmpdndv_1 : Nominal.NPrf (.imp (syn_wwpp) (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))) (syn_clec) (syn_cnc (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))))) :
    Nominal.NPrf (.imp (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_cfbfixedblockledgercmpndv
  have p0001 :=
    @g_sylib (syn_wwpp) (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))) (syn_clec) (syn_cnc (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))))))) hyp_cfbfixedblockledgercmpdndv_1 p0000
  exact p0001

noncomputable def g_cfbfixedblockcancelleddndv
    (hyp_cfbfixedblockcancelleddndv_1 : Nominal.NPrf (.imp (syn_wwpp) (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))) (syn_clec) (syn_cnc (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))))) :
    Nominal.NPrf (.imp (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_cfbfixedblockledgercmpdndv hyp_cfbfixedblockcancelleddndv_1
  have p0001 :=
    @g_cfbfixedblockcancel3ndv
  have p0002 :=
    @g_syl (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))))) p0000 p0001
  exact p0002

noncomputable def g_cfbfixedblockf6pointfromnclendv
    (R : Class) (hyp_cfbfixedblockf6pointfromnclendv_1 : Nominal.NPrf (.imp (syn_wwpp) (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))) (syn_clec) (syn_cnc (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))))) (hyp_cfbfixedblockf6pointfromnclendv_2 : Nominal.NPrf (syn_wbr R (syn_cwe) (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))) :
    Nominal.NPrf (.imp (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))) := by
  let proofSupport : Finset Var := R.fv
  have p0000 :=
    @g_cfbfixedblockcancelleddndv hyp_cfbfixedblockf6pointfromnclendv_1
  have p0001 :=
    @g_cfbfixedblockpointimpndv R hyp_cfbfixedblockf6pointfromnclendv_2
  have p0002 :=
    @g_syl (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_ctc (syn_ctc (syn_chncard (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))))) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) p0000 p0001
  exact p0002

noncomputable def g_cfbpw16oneexndv
     :
    Nominal.NPrf (.classMem (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_n_1cex
  have p0001 :=
    @g_pw1ex (syn_c1c) p0000
  have p0002 :=
    @g_pw1ex (syn_cpw1 (syn_c1c)) p0001
  have p0003 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0002
  have p0004 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0003
  have p0005 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0004
  have p0006 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0005
  exact p0006

noncomputable def g_cfbfixedblocksourceexndv
     :
    Nominal.NPrf (.classMem (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_cfbpw16oneexndv
  have p0001 :=
    @g_pwex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) p0000
  have p0002 :=
    @g_hnordex (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) p0001
  have p0003 :=
    @g_pw1ex (syn_chnord (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) p0002
  have p0004 :=
    @g_pw1ex (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) p0003
  have p0005 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) p0004
  exact p0005

noncomputable def g_cfbfixedblocktargetexndv
     :
    Nominal.NPrf (.classMem (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_cfbpw16oneexndv
  have p0001 :=
    @g_hnordex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) p0000
  have p0002 :=
    @g_pwex (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) p0001
  have p0003 :=
    @g_pwex (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) p0002
  have p0004 :=
    @g_hnordex (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) p0003
  exact p0004

noncomputable def g_cfbnclefrominjimpndv
    (A : Class) (B : Class) (f : Var) (dv_A_f : f ∉ A.fv) (dv_B_f : f ∉ B.fv) (hyp_cfbnclefrominjimpndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_cfbnclefrominjimpndv_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wex f (syn_wf1 (.cv f) A B)) (syn_wbr (syn_cnc A) (syn_clec) (syn_cnc B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ ({f} : Finset Var)
  have dv_cache_0001 : f ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : f ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_f, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_nclenc A B f dv_cache_0001 dv_cache_0002 hyp_cfbnclefrominjimpndv_1 hyp_cfbnclefrominjimpndv_2
  have p0001 :=
    @g_biimpri (syn_wbr (syn_cnc A) (syn_clec) (syn_cnc B)) (syn_wex f (syn_wf1 (.cv f) A B)) p0000
  exact p0001

noncomputable def g_cfbfixedblocknclefrominjndv
    (f : Var) (hyp_cfbfixedblocknclefrominjndv_1 : Nominal.NPrf (.imp (syn_wwpp) (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))))) :
    Nominal.NPrf (.imp (syn_wwpp) (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))) (syn_clec) (syn_cnc (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))))) := by
  let proofSupport : Finset Var := ({f} : Finset Var)
  have dv_cache_0001 : f ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))).fv := by
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : f ∉ ((syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_cfbfixedblocksourceexndv
  have p0001 :=
    @g_cfbfixedblocktargetexndv
  have p0002 :=
    @g_cfbnclefrominjimpndv (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))) f dv_cache_0001 dv_cache_0002 p0000 p0001
  have p0003 :=
    @g_syl (syn_wwpp) (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))) (syn_wbr (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))) (syn_clec) (syn_cnc (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))) hyp_cfbfixedblocknclefrominjndv_1 p0002
  exact p0003

noncomputable def g_cfbfixedblockf6pointfrominjndv
    (R : Class) (f : Var) (hyp_cfbfixedblockf6pointfrominjndv_1 : Nominal.NPrf (.imp (syn_wwpp) (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))))) (hyp_cfbfixedblockf6pointfrominjndv_2 : Nominal.NPrf (syn_wbr R (syn_cwe) (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))))) :
    Nominal.NPrf (.imp (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))) := by
  let proofSupport : Finset Var := R.fv ∪ ({f} : Finset Var)
  have p0000 :=
    @g_cfbfixedblocknclefrominjndv f hyp_cfbfixedblockf6pointfrominjndv_1
  have p0001 :=
    @g_cfbfixedblockf6pointfromnclendv R p0000 hyp_cfbfixedblockf6pointfrominjndv_2
  exact p0001

#print axioms g_cfbfixedblockf6pointfrominjndv

end NFChoice.DirectNominalPrf.WPPReplay
