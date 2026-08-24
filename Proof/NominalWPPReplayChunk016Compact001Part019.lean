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
import NominalWPPReplayChunk016Compact001Part018

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

noncomputable def g_wecutisogenrawmem
    (B : Class) (C : Class) (D : Class) (R : Class) (S : Class) (f : Var) (E : Class) (r : Var) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))) (.classMem (.cv f) (syn_cwecutisogen R D S E))) := by
  let proofSupport : Finset Var := B.fv ∪ C.fv ∪ D.fv ∪ R.fv ∪ S.fv ∪ ({f} : Finset Var) ∪ E.fv ∪ ({r} : Finset Var)
  have p0000 :=
    @g_simpr (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))
  have p0001 :=
    @g_simpr (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C)))
  have p0002 :=
    @g_syl (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C)))) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))) p0000 p0001
  have p0003 :=
    @g_simpl (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))
  have p0004 :=
    @g_syl (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))) (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) p0002 p0003
  have p0005 :=
    @g_wecutisogennormbij f r
  have p0006 :=
    @g_syl (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))) (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (.classMem (.cv f) (syn_chwbij)) p0004 p0005
  have p0007 :=
    @g_simpr (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))
  have p0008 :=
    @g_simpl (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C)))
  have p0009 :=
    @g_syl (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C)))) (.classMem (.cv r) (syn_cvv)) p0007 p0008
  have p0010 :=
    @g_jca (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))) (.classMem (.cv f) (syn_chwbij)) (.classMem (.cv r) (syn_cvv)) p0006 p0009
  have p0011 :=
    @g_opelxp (.cv f) (.cv r) (syn_chwbij) (syn_cvv)
  have p0012 :=
    @g_biimpri (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_wa (.classMem (.cv f) (syn_chwbij)) (.classMem (.cv r) (syn_cvv))) p0011
  have p0013 :=
    @g_syl (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))) (syn_wa (.classMem (.cv f) (syn_chwbij)) (.classMem (.cv r) (syn_cvv))) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv))) p0010 p0012
  have p0014 :=
    @g_simpl (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))
  have p0015 :=
    @g_simpl (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))
  have p0016 :=
    @g_syl (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))) (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (.classMem B (syn_crn (syn_chnwcutrel R D))) p0014 p0015
  have p0017 :=
    @g_simpl (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))
  have p0018 :=
    @g_simpr (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))
  have p0019 :=
    @g_syl (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))) (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (.classMem C (syn_crn (syn_chnwcutrel S E))) p0017 p0018
  have p0020 :=
    @g_jca (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))) (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E))) p0016 p0019
  have p0021 :=
    @g_opelxp B C (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))
  have p0022 :=
    @g_biimpri (.classMem (syn_cop B C) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) p0021
  have p0023 :=
    @g_syl (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))) (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (.classMem (syn_cop B C) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))) p0020 p0022
  have p0024 :=
    @g_vex r
  have p0025 :=
    @g_hwgenval (.cv r) f p0024
  have p0026 :=
    @g_a1i (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))))) (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))) p0025
  have p0027 :=
    @g_simpr (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))
  have p0028 :=
    @g_simpr (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C)))
  have p0029 :=
    @g_syl (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C)))) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))) p0027 p0028
  have p0030 :=
    @g_simpr (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))
  have p0031 :=
    @g_syl (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C)) p0029 p0030
  have p0032 :=
    @g_simpl (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C)
  have p0033 :=
    @g_syl (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C)) (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) p0031 p0032
  have p0034 :=
    @g_simpr (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))
  have p0035 :=
    @g_simpr (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C)))
  have p0036 :=
    @g_syl (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C)))) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))) p0034 p0035
  have p0037 :=
    @g_simpr (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))
  have p0038 :=
    @g_syl (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C)) p0036 p0037
  have p0039 :=
    @g_simpr (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C)
  have p0040 :=
    @g_syl (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C)) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C) p0038 p0039
  have p0041 :=
    @g_opeq12d (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))) (syn_cop (.cv r) (syn_cdm (.cv f))) B (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C p0033 p0040
  have p0042 :=
    @g_eqtrd (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))) (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))) (syn_cop B C) p0026 p0041
  have p0043 :=
    @g_eleq1d (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))) (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop B C) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))) p0042
  have p0044 :=
    @g_mpbird (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))) (.classMem (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))) (.classMem (syn_cop B C) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))) p0023 p0043
  have p0045 :=
    @g_hwgenfn
  have p0046 :=
    @g_fnfun (syn_cvv) (syn_chwgen)
  have p0047 :=
    Nominal.mp p0045 p0046
  have p0048 :=
    @g_vex f
  have p0049 :=
    @g_vex r
  have p0050 :=
    @g_opex (.cv f) (.cv r) p0048 p0049
  have p0051 :=
    @g_hwgenfn
  have p0052 :=
    @g_fndm (syn_cvv) (syn_chwgen)
  have p0053 :=
    Nominal.mp p0051 p0052
  have p0054 :=
    @g_eleq2i (syn_cdm (syn_chwgen)) (syn_cvv) (syn_cop (.cv f) (.cv r)) p0053
  have p0055 :=
    @g_mpbir (.classMem (syn_cop (.cv f) (.cv r)) (syn_cdm (syn_chwgen))) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cvv)) p0050 p0054
  have p0056 :=
    @g_pm3_2i (syn_wfun (syn_chwgen)) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cdm (syn_chwgen))) p0047 p0055
  have p0057 :=
    @g_fvimacnv (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))) (syn_chwgen)
  have p0058 :=
    Nominal.mp p0056 p0057
  have p0059 :=
    @g_a1i (syn_wb (.classMem (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))) p0058
  have p0060 :=
    @g_mpbid (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))) (.classMem (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) p0044 p0059
  have p0061 :=
    @g_jca (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv))) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) p0013 p0060
  have p0062 :=
    @g_elin (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))
  have p0063 :=
    @g_biimpri (.classMem (syn_cop (.cv f) (.cv r)) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv))) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))) p0062
  have p0064 :=
    @g_syl (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))) (syn_wa (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv))) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))) p0061 p0063
  have p0065 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r))))
  have p0066 :=
    @g_biimpri (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r)) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))) p0065
  have p0067 :=
    @g_syl (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))) (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r)) p0064 p0066
  have p0068 :=
    @g_breldm (.cv f) (.cv r) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))
  have p0069 :=
    @g_syl (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))) (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r)) (.classMem (.cv f) (syn_cdm (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))))) p0067 p0068
  have p0070 :=
    (by simpa [syn_cwecutisogen] using (Nominal.classEqRefl (syn_cwecutisogen R D S E)))
  have p0071 :=
    @g_eleq2i (syn_cwecutisogen R D S E) (syn_cdm (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))) (.cv f) p0070
  have p0072 :=
    @g_a1i (syn_wb (.classMem (.cv f) (syn_cwecutisogen R D S E)) (.classMem (.cv f) (syn_cdm (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))))) (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))) p0071
  have p0073 :=
    @g_mpbird (syn_wa (syn_wa (.classMem B (syn_crn (syn_chnwcutrel R D))) (.classMem C (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) B) (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) C))))) (.classMem (.cv f) (syn_cwecutisogen R D S E)) (.classMem (.cv f) (syn_cdm (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))))) p0069 p0072
  exact p0073

noncomputable def g_wecutisogenrawout
    (D : Class) (R : Class) (S : Class) (f : Var) (E : Class) (r : Var) (dv_D_r : r ∉ D.fv) (dv_E_r : r ∉ E.fv) (dv_R_r : r ∉ R.fv) (dv_S_r : r ∉ S.fv) (dv_f_r : f ≠ r) :
    Nominal.NPrf (.imp (.classMem (.cv f) (syn_cwecutisogen R D S E)) (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ S.fv ∪ ({f} : Finset Var) ∪ E.fv ∪ ({r} : Finset Var)
  have dv_cache_0001 : r ∉ ((Class.cv f)).fv := by
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_f_r), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : r ∉ ((syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbij, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwgen, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_r, dv_R_r, dv_E_r, dv_S_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    (by simpa [syn_cwecutisogen] using (Nominal.classEqRefl (syn_cwecutisogen R D S E)))
  have p0001 :=
    @g_eleq2i (syn_cwecutisogen R D S E) (syn_cdm (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))) (.cv f) p0000
  have p0002 :=
    @g_biimpi (.classMem (.cv f) (syn_cwecutisogen R D S E)) (.classMem (.cv f) (syn_cdm (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))))) p0001
  have p0003 :=
    @g_eldm r (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) dv_cache_0001 dv_cache_0002
  have p0004 :=
    @g_biimpi (.classMem (.cv f) (syn_cdm (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))))) (syn_wex r (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r))) p0003
  have p0005 :=
    @g_syl (.classMem (.cv f) (syn_cwecutisogen R D S E)) (.classMem (.cv f) (syn_cdm (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))))) (syn_wex r (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r))) p0002 p0004
  have p0006 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r))))
  have p0007 :=
    @g_biimpi (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r)) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))) p0006
  have p0008 :=
    @g_elin (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))
  have p0009 :=
    @g_biimpi (.classMem (syn_cop (.cv f) (.cv r)) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv))) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))) p0008
  have p0010 :=
    @g_syl (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r)) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv))) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))) p0007 p0009
  have p0011 :=
    @g_simpl (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv))) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))
  have p0012 :=
    @g_syl (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r)) (syn_wa (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv))) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv))) p0010 p0011
  have p0013 :=
    @g_opelxp (.cv f) (.cv r) (syn_chwbij) (syn_cvv)
  have p0014 :=
    @g_biimpi (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_wa (.classMem (.cv f) (syn_chwbij)) (.classMem (.cv r) (syn_cvv))) p0013
  have p0015 :=
    @g_syl (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r)) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_wa (.classMem (.cv f) (syn_chwbij)) (.classMem (.cv r) (syn_cvv))) p0012 p0014
  have p0016 :=
    @g_simpr (.classMem (.cv f) (syn_chwbij)) (.classMem (.cv r) (syn_cvv))
  have p0017 :=
    @g_syl (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r)) (syn_wa (.classMem (.cv f) (syn_chwbij)) (.classMem (.cv r) (syn_cvv))) (.classMem (.cv r) (syn_cvv)) p0015 p0016
  have p0018 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r))))
  have p0019 :=
    @g_biimpi (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r)) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))) p0018
  have p0020 :=
    @g_elin (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))
  have p0021 :=
    @g_biimpi (.classMem (syn_cop (.cv f) (.cv r)) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv))) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))) p0020
  have p0022 :=
    @g_syl (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r)) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv))) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))) p0019 p0021
  have p0023 :=
    @g_simpl (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv))) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))
  have p0024 :=
    @g_syl (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r)) (syn_wa (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv))) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv))) p0022 p0023
  have p0025 :=
    @g_opelxp (.cv f) (.cv r) (syn_chwbij) (syn_cvv)
  have p0026 :=
    @g_biimpi (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_wa (.classMem (.cv f) (syn_chwbij)) (.classMem (.cv r) (syn_cvv))) p0025
  have p0027 :=
    @g_syl (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r)) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_wa (.classMem (.cv f) (syn_chwbij)) (.classMem (.cv r) (syn_cvv))) p0024 p0026
  have p0028 :=
    @g_simpl (.classMem (.cv f) (syn_chwbij)) (.classMem (.cv r) (syn_cvv))
  have p0029 :=
    @g_syl (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r)) (syn_wa (.classMem (.cv f) (syn_chwbij)) (.classMem (.cv r) (syn_cvv))) (.classMem (.cv f) (syn_chwbij)) p0027 p0028
  have p0030 :=
    @g_hwbijf1o f
  have p0031 :=
    @g_biimpi (.classMem (.cv f) (syn_chwbij)) (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) p0030
  have p0032 :=
    @g_hwtrnisob f r
  have p0033 :=
    @g_biimpi (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) p0032
  have p0034 :=
    @g_syl (.classMem (.cv f) (syn_chwbij)) (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) p0031 p0033
  have p0035 :=
    @g_syl (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r)) (.classMem (.cv f) (syn_chwbij)) (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) p0029 p0034
  have p0036 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r))))
  have p0037 :=
    @g_biimpi (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r)) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))) p0036
  have p0038 :=
    @g_elin (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))
  have p0039 :=
    @g_biimpi (.classMem (syn_cop (.cv f) (.cv r)) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv))) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))) p0038
  have p0040 :=
    @g_syl (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r)) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))) (syn_wa (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv))) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))) p0037 p0039
  have p0041 :=
    @g_simpr (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv))) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))
  have p0042 :=
    @g_syl (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r)) (syn_wa (.classMem (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_chwbij) (syn_cvv))) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))))) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) p0040 p0041
  have p0043 :=
    @g_hwgenfn
  have p0044 :=
    @g_fnfun (syn_cvv) (syn_chwgen)
  have p0045 :=
    Nominal.mp p0043 p0044
  have p0046 :=
    @g_vex f
  have p0047 :=
    @g_vex r
  have p0048 :=
    @g_opex (.cv f) (.cv r) p0046 p0047
  have p0049 :=
    @g_hwgenfn
  have p0050 :=
    @g_fndm (syn_cvv) (syn_chwgen)
  have p0051 :=
    Nominal.mp p0049 p0050
  have p0052 :=
    @g_eleq2i (syn_cdm (syn_chwgen)) (syn_cvv) (syn_cop (.cv f) (.cv r)) p0051
  have p0053 :=
    @g_mpbir (.classMem (syn_cop (.cv f) (.cv r)) (syn_cdm (syn_chwgen))) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cvv)) p0048 p0052
  have p0054 :=
    @g_pm3_2i (syn_wfun (syn_chwgen)) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cdm (syn_chwgen))) p0045 p0053
  have p0055 :=
    @g_fvimacnv (syn_cop (.cv f) (.cv r)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))) (syn_chwgen)
  have p0056 :=
    Nominal.mp p0054 p0055
  have p0057 :=
    @g_biimpri (.classMem (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) p0056
  have p0058 :=
    @g_syl (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r)) (.classMem (syn_cop (.cv f) (.cv r)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.classMem (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))) p0042 p0057
  have p0059 :=
    @g_vex r
  have p0060 :=
    @g_hwgenval (.cv r) f p0059
  have p0061 :=
    @g_a1i (.classEq (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))))) (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r)) p0060
  have p0062 :=
    @g_eleq1d (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r)) (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cop (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))) p0061
  have p0063 :=
    @g_mpbid (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r)) (.classMem (syn_cfv (syn_chwgen) (syn_cop (.cv f) (.cv r))) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))) (.classMem (syn_cop (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))) p0058 p0062
  have p0064 :=
    @g_opelxp (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))
  have p0065 :=
    @g_biimpi (.classMem (syn_cop (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))) p0064
  have p0066 :=
    @g_syl (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r)) (.classMem (syn_cop (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E)))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))) p0063 p0065
  have p0067 :=
    @g_jca (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r)) (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))) p0035 p0066
  have p0068 :=
    @g_jca (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r)) (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))) p0017 p0067
  have p0069 :=
    @g_eximi (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r)) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) r p0068
  have p0070 :=
    (by simpa [syn_wb, syn_wrex] using (Nominal.biimpRefl (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))))
  have p0071 :=
    @g_biimpri (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) (syn_wex r (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))) p0070
  have p0072 :=
    @g_syl (syn_wex r (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r))) (syn_wex r (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E))))))) (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) p0069 p0071
  have p0073 :=
    @g_syl (.classMem (.cv f) (syn_cwecutisogen R D S E)) (syn_wex r (syn_wbr (.cv f) (syn_cin (syn_cxp (syn_chwbij) (syn_cvv)) (syn_cima (syn_ccnv (syn_chwgen)) (syn_cxp (syn_crn (syn_chnwcutrel R D)) (syn_crn (syn_chnwcutrel S E))))) (.cv r))) (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wa (.classMem (syn_cop (.cv r) (syn_cdm (.cv f))) (syn_crn (syn_chnwcutrel R D))) (.classMem (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))) (syn_crn (syn_chnwcutrel S E)))))) p0005 p0072
  exact p0073

#print axioms g_wecutisogenrawout

end NFChoice.DirectNominalPrf.WPPReplay
