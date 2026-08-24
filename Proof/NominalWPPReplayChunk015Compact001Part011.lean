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
import NominalWPPReplayChunk015Compact001Part010

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

noncomputable def g_lnqordor
    (C : Class) (R : Class) (dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wbr (syn_clnqord R C) (syn_cstrict) (syn_clnquo R C))) := by
  let proofSupport : Finset Var := C.fv ∪ R.fv
  have dv_cache_0001 : Disjoint (C).fv (R).fv := by
    exact (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have p0000 :=
    @g_lnqordref C R dv_cache_0001
  have p0001 :=
    @g_lnqordtrans C R dv_cache_0001
  have p0002 :=
    @g_lnqordantisym C R dv_cache_0001
  have p0003 :=
    @g_n_3jca (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wbr (syn_clnqord R C) (syn_cref) (syn_clnquo R C)) (syn_wbr (syn_clnqord R C) (syn_ctrans) (syn_clnquo R C)) (syn_wbr (syn_clnqord R C) (syn_cantisym) (syn_clnquo R C)) p0000 p0001 p0002
  have p0004 :=
    @g_porta (syn_clnquo R C) (syn_clnqord R C)
  have p0005 :=
    @g_a1i (syn_wb (syn_wbr (syn_clnqord R C) (syn_cpartial) (syn_clnquo R C)) (syn_w3a (syn_wbr (syn_clnqord R C) (syn_cref) (syn_clnquo R C)) (syn_wbr (syn_clnqord R C) (syn_ctrans) (syn_clnquo R C)) (syn_wbr (syn_clnqord R C) (syn_cantisym) (syn_clnquo R C)))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) p0004
  have p0006 :=
    @g_mpbird (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wbr (syn_clnqord R C) (syn_cpartial) (syn_clnquo R C)) (syn_w3a (syn_wbr (syn_clnqord R C) (syn_cref) (syn_clnquo R C)) (syn_wbr (syn_clnqord R C) (syn_ctrans) (syn_clnquo R C)) (syn_wbr (syn_clnqord R C) (syn_cantisym) (syn_clnquo R C))) p0003 p0005
  have p0007 :=
    @g_lnqordconnex C R dv_cache_0001
  have p0008 :=
    @g_jca (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wbr (syn_clnqord R C) (syn_cpartial) (syn_clnquo R C)) (syn_wbr (syn_clnqord R C) (syn_cconnex) (syn_clnquo R C)) p0006 p0007
  have p0009 :=
    @g_sopc (syn_clnquo R C) (syn_clnqord R C)
  have p0010 :=
    @g_a1i (syn_wb (syn_wbr (syn_clnqord R C) (syn_cstrict) (syn_clnquo R C)) (syn_wa (syn_wbr (syn_clnqord R C) (syn_cpartial) (syn_clnquo R C)) (syn_wbr (syn_clnqord R C) (syn_cconnex) (syn_clnquo R C)))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) p0009
  have p0011 :=
    @g_mpbird (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wbr (syn_clnqord R C) (syn_cstrict) (syn_clnquo R C)) (syn_wa (syn_wbr (syn_clnqord R C) (syn_cpartial) (syn_clnquo R C)) (syn_wbr (syn_clnqord R C) (syn_cconnex) (syn_clnquo R C))) p0008 p0010
  exact p0011

noncomputable def g_lnkereceqb
    (C : Class) (R : Class) (X : Class) (Y : Class) (dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wb (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)))) := by
  let proofSupport : Finset Var := C.fv ∪ R.fv ∪ X.fv ∪ Y.fv
  have dv_cache_0001 : Disjoint (C).fv (R).fv := by
    exact (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have p0000 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)))
  have p0001 :=
    @g_simpl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0002 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0003 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))
  have p0004 :=
    @g_syl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))) (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) p0002 p0003
  have p0005 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) p0001 p0004
  have p0006 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)
  have p0007 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0005 p0006
  have p0008 :=
    @g_simpl (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)
  have p0009 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cref) C) p0007 p0008
  have p0010 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)))) (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wbr R (syn_cref) C) p0000 p0009
  have p0011 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)))
  have p0012 :=
    @g_simpr (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0013 :=
    @g_simpr (.classMem X C) (.classMem Y C)
  have p0014 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem X C) (.classMem Y C)) (.classMem Y C) p0012 p0013
  have p0015 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)))) (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.classMem Y C) p0011 p0014
  have p0016 :=
    @g_refd (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)))) C R Y p0010 p0015
  have p0017 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)))
  have p0018 :=
    @g_simpl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0019 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0020 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))
  have p0021 :=
    @g_syl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))) (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) p0019 p0020
  have p0022 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) p0018 p0021
  have p0023 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)
  have p0024 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0022 p0023
  have p0025 :=
    @g_simpl (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)
  have p0026 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cref) C) p0024 p0025
  have p0027 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)))) (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wbr R (syn_cref) C) p0017 p0026
  have p0028 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)))
  have p0029 :=
    @g_simpr (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0030 :=
    @g_simpr (.classMem X C) (.classMem Y C)
  have p0031 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem X C) (.classMem Y C)) (.classMem Y C) p0029 p0030
  have p0032 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)))) (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.classMem Y C) p0028 p0031
  have p0033 :=
    @g_refd (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)))) C R Y p0027 p0032
  have p0034 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)))) (syn_wbr Y R Y) (syn_wbr Y R Y) p0016 p0033
  have p0035 :=
    @g_ellnkerecg Y Y R
  have p0036 :=
    @g_a1i (syn_wb (.classMem Y (syn_cec Y (syn_clnker R))) (syn_wa (syn_wbr Y R Y) (syn_wbr Y R Y))) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)))) p0035
  have p0037 :=
    @g_mpbird (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)))) (.classMem Y (syn_cec Y (syn_clnker R))) (syn_wa (syn_wbr Y R Y) (syn_wbr Y R Y)) p0034 p0036
  have p0038 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)))
  have p0039 :=
    @g_eleq2d (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)))) (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)) Y p0038
  have p0040 :=
    @g_mpbird (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)))) (.classMem Y (syn_cec X (syn_clnker R))) (.classMem Y (syn_cec Y (syn_clnker R))) p0037 p0039
  have p0041 :=
    @g_ellnkerecg Y X R
  have p0042 :=
    @g_a1i (syn_wb (.classMem Y (syn_cec X (syn_clnker R))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X))) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)))) p0041
  have p0043 :=
    @g_mpbid (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)))) (.classMem Y (syn_cec X (syn_clnker R))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)) p0040 p0042
  have p0044 :=
    @g_ex (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)) p0043
  have p0045 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X))
  have p0046 :=
    @g_simpl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0047 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X))) (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) p0045 p0046
  have p0048 :=
    @g_lnqordantisym C R dv_cache_0001
  have p0049 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wbr (syn_clnqord R C) (syn_cantisym) (syn_clnquo R C)) p0047 p0048
  have p0050 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X))
  have p0051 :=
    @g_simpl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0052 :=
    @g_simpl (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0053 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) p0051 p0052
  have p0054 :=
    @g_simpl (.classMem R (syn_cvv)) (.classMem C (syn_cvv))
  have p0055 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (.classMem R (syn_cvv)) p0053 p0054
  have p0056 :=
    @g_lnkerexg R
  have p0057 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.classMem R (syn_cvv)) (.classMem (syn_clnker R) (syn_cvv)) p0055 p0056
  have p0058 :=
    @g_simpr (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0059 :=
    @g_simpl (.classMem X C) (.classMem Y C)
  have p0060 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem X C) (.classMem Y C)) (.classMem X C) p0058 p0059
  have p0061 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.classMem (syn_clnker R) (syn_cvv)) (.classMem X C) p0057 p0060
  have p0062 :=
    @g_ecelqsg C X (syn_clnker R) (syn_cvv)
  have p0063 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (syn_clnker R) (syn_cvv)) (.classMem X C)) (.classMem (syn_cec X (syn_clnker R)) (syn_cqs C (syn_clnker R))) p0061 p0062
  have p0064 :=
    (by simpa [syn_clnquo] using (Nominal.classEqRefl (syn_clnquo R C)))
  have p0065 :=
    @g_syl6eleqr (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_cec X (syn_clnker R)) (syn_cqs C (syn_clnker R)) (syn_clnquo R C) p0063 p0064
  have p0066 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X))) (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.classMem (syn_cec X (syn_clnker R)) (syn_clnquo R C)) p0050 p0065
  have p0067 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X))
  have p0068 :=
    @g_simpl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0069 :=
    @g_simpl (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0070 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) p0068 p0069
  have p0071 :=
    @g_simpl (.classMem R (syn_cvv)) (.classMem C (syn_cvv))
  have p0072 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (.classMem R (syn_cvv)) p0070 p0071
  have p0073 :=
    @g_lnkerexg R
  have p0074 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.classMem R (syn_cvv)) (.classMem (syn_clnker R) (syn_cvv)) p0072 p0073
  have p0075 :=
    @g_simpr (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0076 :=
    @g_simpr (.classMem X C) (.classMem Y C)
  have p0077 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem X C) (.classMem Y C)) (.classMem Y C) p0075 p0076
  have p0078 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.classMem (syn_clnker R) (syn_cvv)) (.classMem Y C) p0074 p0077
  have p0079 :=
    @g_ecelqsg C Y (syn_clnker R) (syn_cvv)
  have p0080 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem (syn_clnker R) (syn_cvv)) (.classMem Y C)) (.classMem (syn_cec Y (syn_clnker R)) (syn_cqs C (syn_clnker R))) p0078 p0079
  have p0081 :=
    (by simpa [syn_clnquo] using (Nominal.classEqRefl (syn_clnquo R C)))
  have p0082 :=
    @g_syl6eleqr (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_cec Y (syn_clnker R)) (syn_cqs C (syn_clnker R)) (syn_clnquo R C) p0080 p0081
  have p0083 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X))) (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.classMem (syn_cec Y (syn_clnker R)) (syn_clnquo R C)) p0067 p0082
  have p0084 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X))
  have p0085 :=
    @g_simpl (syn_wbr X R Y) (syn_wbr Y R X)
  have p0086 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)) (syn_wbr X R Y) p0084 p0085
  have p0087 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X))
  have p0088 :=
    @g_simpl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0089 :=
    @g_simpl (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0090 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) p0088 p0089
  have p0091 :=
    @g_simpl (.classMem R (syn_cvv)) (.classMem C (syn_cvv))
  have p0092 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (.classMem R (syn_cvv)) p0090 p0091
  have p0093 :=
    @g_simpl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0094 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0095 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))
  have p0096 :=
    @g_syl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))) (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) p0094 p0095
  have p0097 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) p0093 p0096
  have p0098 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)
  have p0099 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0097 p0098
  have p0100 :=
    @g_simpl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0101 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0102 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))
  have p0103 :=
    @g_syl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))) (syn_wss R (syn_cxp C C)) p0101 p0102
  have p0104 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss R (syn_cxp C C)) p0100 p0103
  have p0105 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C)) p0099 p0104
  have p0106 :=
    @g_simpr (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0107 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)) p0105 p0106
  have p0108 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) p0092 p0107
  have p0109 :=
    @g_brlnqordkern C R X Y dv_cache_0001
  have p0110 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))) (syn_wb (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqord R C) (syn_cec Y (syn_clnker R))) (syn_wbr X R Y)) p0108 p0109
  have p0111 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X))) (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wb (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqord R C) (syn_cec Y (syn_clnker R))) (syn_wbr X R Y)) p0087 p0110
  have p0112 :=
    @g_mpbird (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X))) (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqord R C) (syn_cec Y (syn_clnker R))) (syn_wbr X R Y) p0086 p0111
  have p0113 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X))
  have p0114 :=
    @g_simpr (syn_wbr X R Y) (syn_wbr Y R X)
  have p0115 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)) (syn_wbr Y R X) p0113 p0114
  have p0116 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X))
  have p0117 :=
    @g_simpl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0118 :=
    @g_simpl (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0119 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) p0117 p0118
  have p0120 :=
    @g_simpl (.classMem R (syn_cvv)) (.classMem C (syn_cvv))
  have p0121 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (.classMem R (syn_cvv)) p0119 p0120
  have p0122 :=
    @g_simpl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0123 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0124 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))
  have p0125 :=
    @g_syl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))) (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) p0123 p0124
  have p0126 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) p0122 p0125
  have p0127 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)
  have p0128 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0126 p0127
  have p0129 :=
    @g_simpl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0130 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0131 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))
  have p0132 :=
    @g_syl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))) (syn_wss R (syn_cxp C C)) p0130 p0131
  have p0133 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss R (syn_cxp C C)) p0129 p0132
  have p0134 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C)) p0128 p0133
  have p0135 :=
    @g_simpr (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0136 :=
    @g_simpr (.classMem X C) (.classMem Y C)
  have p0137 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem X C) (.classMem Y C)) (.classMem Y C) p0135 p0136
  have p0138 :=
    @g_simpr (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0139 :=
    @g_simpl (.classMem X C) (.classMem Y C)
  have p0140 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem X C) (.classMem Y C)) (.classMem X C) p0138 p0139
  have p0141 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.classMem Y C) (.classMem X C) p0137 p0140
  have p0142 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem Y C) (.classMem X C)) p0134 p0141
  have p0143 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem Y C) (.classMem X C))) p0121 p0142
  have p0144 :=
    @g_brlnqordkern C R Y X dv_cache_0001
  have p0145 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem Y C) (.classMem X C)))) (syn_wb (syn_wbr (syn_cec Y (syn_clnker R)) (syn_clnqord R C) (syn_cec X (syn_clnker R))) (syn_wbr Y R X)) p0143 p0144
  have p0146 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X))) (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wb (syn_wbr (syn_cec Y (syn_clnker R)) (syn_clnqord R C) (syn_cec X (syn_clnker R))) (syn_wbr Y R X)) p0116 p0145
  have p0147 :=
    @g_mpbird (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X))) (syn_wbr (syn_cec Y (syn_clnker R)) (syn_clnqord R C) (syn_cec X (syn_clnker R))) (syn_wbr Y R X) p0115 p0146
  have p0148 :=
    @g_antid (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X))) (syn_clnquo R C) (syn_clnqord R C) (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)) p0049 p0066 p0083 p0112 p0147
  have p0149 :=
    @g_ex (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)) (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R))) p0148
  have p0150 :=
    @g_impbid (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)) p0044 p0149
  exact p0150

#print axioms g_lnkereceqb

end NFChoice.DirectNominalPrf.WPPReplay
