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
import NominalWPPReplayChunk015Compact001Part011

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

noncomputable def g_brlnqordstrict
    (C : Class) (R : Class) (X : Class) (Y : Class) (dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wb (syn_wbr (syn_cec X (syn_clnker R)) (syn_cdif (syn_clnqord R C) (syn_cid)) (syn_cec Y (syn_clnker R))) (syn_wbr X (syn_cdif R (syn_ccnv R)) Y))) := by
  let proofSupport : Finset Var := C.fv ∪ R.fv ∪ X.fv ∪ Y.fv
  have dv_cache_0001 : Disjoint (C).fv (R).fv := by
    exact (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have p0000 :=
    @g_brdif (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)) (syn_clnqord R C) (syn_cid)
  have p0001 :=
    @g_a1i (syn_wb (syn_wbr (syn_cec X (syn_clnker R)) (syn_cdif (syn_clnqord R C) (syn_cid)) (syn_cec Y (syn_clnker R))) (syn_wa (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqord R C) (syn_cec Y (syn_clnker R))) (.neg (syn_wbr (syn_cec X (syn_clnker R)) (syn_cid) (syn_cec Y (syn_clnker R)))))) (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) p0000
  have p0002 :=
    @g_simpl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0003 :=
    @g_simpl (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0004 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) p0002 p0003
  have p0005 :=
    @g_simpl (.classMem R (syn_cvv)) (.classMem C (syn_cvv))
  have p0006 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (.classMem R (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_simpl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0008 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0009 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))
  have p0010 :=
    @g_syl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))) (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) p0008 p0009
  have p0011 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) p0007 p0010
  have p0012 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)
  have p0013 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0011 p0012
  have p0014 :=
    @g_simpl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0015 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0016 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))
  have p0017 :=
    @g_syl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))) (syn_wss R (syn_cxp C C)) p0015 p0016
  have p0018 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wss R (syn_cxp C C)) p0014 p0017
  have p0019 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C)) p0013 p0018
  have p0020 :=
    @g_simpr (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0021 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)) p0019 p0020
  have p0022 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))) p0006 p0021
  have p0023 :=
    @g_brlnqordkern C R X Y dv_cache_0001
  have p0024 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem R (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))) (syn_wb (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqord R C) (syn_cec Y (syn_clnker R))) (syn_wbr X R Y)) p0022 p0023
  have p0025 :=
    @g_simpl (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))
  have p0026 :=
    @g_simpl (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0027 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) p0025 p0026
  have p0028 :=
    @g_simpl (.classMem R (syn_cvv)) (.classMem C (syn_cvv))
  have p0029 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (.classMem R (syn_cvv)) p0027 p0028
  have p0030 :=
    @g_lnkerexg R
  have p0031 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.classMem R (syn_cvv)) (.classMem (syn_clnker R) (syn_cvv)) p0029 p0030
  have p0032 :=
    @g_ecexg Y (syn_cvv) (syn_clnker R)
  have p0033 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.classMem (syn_clnker R) (syn_cvv)) (.classMem (syn_cec Y (syn_clnker R)) (syn_cvv)) p0031 p0032
  have p0034 :=
    @g_ideqg (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)) (syn_cvv)
  have p0035 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.classMem (syn_cec Y (syn_clnker R)) (syn_cvv)) (syn_wb (syn_wbr (syn_cec X (syn_clnker R)) (syn_cid) (syn_cec Y (syn_clnker R))) (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)))) p0033 p0034
  have p0036 :=
    @g_notbid (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wbr (syn_cec X (syn_clnker R)) (syn_cid) (syn_cec Y (syn_clnker R))) (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R))) p0035
  have p0037 :=
    @g_anbi12d (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqord R C) (syn_cec Y (syn_clnker R))) (syn_wbr X R Y) (.neg (syn_wbr (syn_cec X (syn_clnker R)) (syn_cid) (syn_cec Y (syn_clnker R)))) (.neg (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)))) p0024 p0036
  have p0038 :=
    @g_bitrd (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wbr (syn_cec X (syn_clnker R)) (syn_cdif (syn_clnqord R C) (syn_cid)) (syn_cec Y (syn_clnker R))) (syn_wa (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqord R C) (syn_cec Y (syn_clnker R))) (.neg (syn_wbr (syn_cec X (syn_clnker R)) (syn_cid) (syn_cec Y (syn_clnker R))))) (syn_wa (syn_wbr X R Y) (.neg (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R))))) p0001 p0037
  have p0039 :=
    @g_lnkereceqb C R X Y dv_cache_0001
  have p0040 :=
    @g_notbid (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)) p0039
  have p0041 :=
    @g_anbi2d (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (.neg (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)))) (.neg (syn_wa (syn_wbr X R Y) (syn_wbr Y R X))) (syn_wbr X R Y) p0040
  have p0042 :=
    @g_bitrd (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wbr (syn_cec X (syn_clnker R)) (syn_cdif (syn_clnqord R C) (syn_cid)) (syn_cec Y (syn_clnker R))) (syn_wa (syn_wbr X R Y) (.neg (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R))))) (syn_wa (syn_wbr X R Y) (.neg (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)))) p0038 p0041
  have p0043 :=
    @g_id (syn_wbr X R Y)
  have p0044 :=
    @g_biantrurd (syn_wbr X R Y) (syn_wbr X R Y) (syn_wbr Y R X) p0043
  have p0045 :=
    @g_notbid (syn_wbr X R Y) (syn_wbr Y R X) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)) p0044
  have p0046 :=
    @g_pm5_32i (syn_wbr X R Y) (.neg (syn_wbr Y R X)) (.neg (syn_wa (syn_wbr X R Y) (syn_wbr Y R X))) p0045
  have p0047 :=
    @g_bicomi (syn_wa (syn_wbr X R Y) (.neg (syn_wbr Y R X))) (syn_wa (syn_wbr X R Y) (.neg (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)))) p0046
  have p0048 :=
    @g_a1i (syn_wb (syn_wa (syn_wbr X R Y) (.neg (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)))) (syn_wa (syn_wbr X R Y) (.neg (syn_wbr Y R X)))) (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) p0047
  have p0049 :=
    @g_bitrd (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wbr (syn_cec X (syn_clnker R)) (syn_cdif (syn_clnqord R C) (syn_cid)) (syn_cec Y (syn_clnker R))) (syn_wa (syn_wbr X R Y) (.neg (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)))) (syn_wa (syn_wbr X R Y) (.neg (syn_wbr Y R X))) p0042 p0048
  have p0050 :=
    @g_brdif X Y R (syn_ccnv R)
  have p0051 :=
    @g_brcnv X Y R
  have p0052 :=
    @g_notbii (syn_wbr X (syn_ccnv R) Y) (syn_wbr Y R X) p0051
  have p0053 :=
    @g_anbi2i (.neg (syn_wbr X (syn_ccnv R) Y)) (.neg (syn_wbr Y R X)) (syn_wbr X R Y) p0052
  have p0054 :=
    @g_bitri (syn_wbr X (syn_cdif R (syn_ccnv R)) Y) (syn_wa (syn_wbr X R Y) (.neg (syn_wbr X (syn_ccnv R) Y))) (syn_wa (syn_wbr X R Y) (.neg (syn_wbr Y R X))) p0050 p0053
  have p0055 :=
    @g_a1i (syn_wb (syn_wbr X (syn_cdif R (syn_ccnv R)) Y) (syn_wa (syn_wbr X R Y) (.neg (syn_wbr Y R X)))) (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) p0054
  have p0056 :=
    @g_bitr4d (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))) (syn_wa (.classMem X C) (.classMem Y C))) (syn_wbr (syn_cec X (syn_clnker R)) (syn_cdif (syn_clnqord R C) (syn_cid)) (syn_cec Y (syn_clnker R))) (syn_wa (syn_wbr X R Y) (.neg (syn_wbr Y R X))) (syn_wbr X (syn_cdif R (syn_ccnv R)) Y) p0049 p0055
  exact p0056

#print axioms g_brlnqordstrict

end NFChoice.DirectNominalPrf.WPPReplay
