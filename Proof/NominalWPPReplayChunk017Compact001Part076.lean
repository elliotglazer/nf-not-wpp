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
import NominalWPPReplayChunk017Compact001Part075

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

noncomputable def g_hncodecmpquotbrproxyimpndv
    (v : Var) (u : Var) (A : Class) (r : Var) (dv_A_r : r ∉ A.fv) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (hyp_hncodecmpquotbrproxyimpndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wb (syn_wbr (syn_cec (.cv u) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cec (.cv v) (syn_chwniso A))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)))) := by
  let proofSupport : Finset Var := ({v} : Finset Var) ∪ ({u} : Finset Var) ∪ A.fv ∪ ({r} : Finset Var)
  have dv_cache_0001 : Disjoint ((syn_chwcn A)).fv ((Class.cv r)).fv := by
    exact (show Disjoint ((syn_chwcn A)).fv ((Class.cv r)).fv from (by rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({r} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show r ∉ (A).fv from (by exact dv_A_r))))))
  have p0000 :=
    @g_a1i (.classMem A (syn_cvv)) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) hyp_hncodecmpquotbrproxyimpndv_1
  have p0001 :=
    @g_hncodecmpsetexg A
  have p0002 :=
    @g_syl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem A (syn_cvv)) (.classMem (syn_chncodecmpset A) (syn_cvv)) p0000 p0001
  have p0003 :=
    @g_simpl (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
  have p0004 :=
    @g_eleq1d (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.cv r) (syn_chncodecmpset A) (syn_cvv) p0003
  have p0005 :=
    @g_mpbird (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chncodecmpset A) (syn_cvv)) p0002 p0004
  have p0006 :=
    @g_a1i (.classMem A (syn_cvv)) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) hyp_hncodecmpquotbrproxyimpndv_1
  have p0007 :=
    @g_hncodecmpsetrefndv A
  have p0008 :=
    @g_syl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem A (syn_cvv)) (syn_wbr (syn_chncodecmpset A) (syn_cref) (syn_chwcn A)) p0006 p0007
  have p0009 :=
    @g_simpl (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
  have p0010 :=
    @g_breq1d (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.cv r) (syn_chncodecmpset A) (syn_chwcn A) (syn_cref) p0009
  have p0011 :=
    @g_mpbird (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv r) (syn_cref) (syn_chwcn A)) (syn_wbr (syn_chncodecmpset A) (syn_cref) (syn_chwcn A)) p0008 p0010
  have p0012 :=
    @g_a1i (.classMem A (syn_cvv)) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) hyp_hncodecmpquotbrproxyimpndv_1
  have p0013 :=
    @g_hncodecmpsettransndv A
  have p0014 :=
    @g_syl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem A (syn_cvv)) (syn_wbr (syn_chncodecmpset A) (syn_ctrans) (syn_chwcn A)) p0012 p0013
  have p0015 :=
    @g_simpl (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
  have p0016 :=
    @g_breq1d (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.cv r) (syn_chncodecmpset A) (syn_chwcn A) (syn_ctrans) p0015
  have p0017 :=
    @g_mpbird (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A)) (syn_wbr (syn_chncodecmpset A) (syn_ctrans) (syn_chwcn A)) p0014 p0016
  have p0018 :=
    @g_jca (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv r) (syn_cref) (syn_chwcn A)) (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A)) p0011 p0017
  have p0019 :=
    @g_hncodecmpsetssxpndv A
  have p0020 :=
    @g_a1i (syn_wss (syn_chncodecmpset A) (syn_cxp (syn_chwcn A) (syn_chwcn A))) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) p0019
  have p0021 :=
    @g_simpl (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
  have p0022 :=
    @g_sseq1d (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.cv r) (syn_chncodecmpset A) (syn_cxp (syn_chwcn A) (syn_chwcn A)) p0021
  have p0023 :=
    @g_mpbird (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wss (.cv r) (syn_cxp (syn_chwcn A) (syn_chwcn A))) (syn_wss (syn_chncodecmpset A) (syn_cxp (syn_chwcn A) (syn_chwcn A))) p0020 p0022
  have p0024 :=
    @g_jca (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (syn_wbr (.cv r) (syn_cref) (syn_chwcn A)) (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A))) (syn_wss (.cv r) (syn_cxp (syn_chwcn A) (syn_chwcn A))) p0018 p0023
  have p0025 :=
    @g_simpr (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
  have p0026 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
  have p0027 :=
    @g_syl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv u) (syn_chwcn A)) p0025 p0026
  have p0028 :=
    @g_simpr (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
  have p0029 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
  have p0030 :=
    @g_syl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (.classMem (.cv v) (syn_chwcn A)) p0028 p0029
  have p0031 :=
    @g_jca (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0027 p0030
  have p0032 :=
    @g_jca (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (syn_wa (syn_wbr (.cv r) (syn_cref) (syn_chwcn A)) (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A))) (syn_wss (.cv r) (syn_cxp (syn_chwcn A) (syn_chwcn A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0024 p0031
  have p0033 :=
    @g_jca (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr (.cv r) (syn_cref) (syn_chwcn A)) (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A))) (syn_wss (.cv r) (syn_cxp (syn_chwcn A) (syn_chwcn A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) p0005 p0032
  have p0034 :=
    @g_brlnqordkern (syn_chwcn A) (.cv r) (.cv u) (.cv v) dv_cache_0001
  have p0035 :=
    @g_syl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (syn_wa (syn_wa (syn_wa (syn_wbr (.cv r) (syn_cref) (syn_chwcn A)) (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A))) (syn_wss (.cv r) (syn_cxp (syn_chwcn A) (syn_chwcn A)))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))) (syn_wb (syn_wbr (syn_cec (.cv u) (syn_clnker (.cv r))) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cec (.cv v) (syn_clnker (.cv r)))) (syn_wbr (.cv u) (.cv r) (.cv v))) p0033 p0034
  have p0036 :=
    @g_simpl (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
  have p0037 :=
    @g_lnkereq (.cv r) (syn_chncodecmpset A)
  have p0038 :=
    @g_syl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classEq (.cv r) (syn_chncodecmpset A)) (.classEq (syn_clnker (.cv r)) (syn_clnker (syn_chncodecmpset A))) p0036 p0037
  have p0039 :=
    @g_a1i (.classMem A (syn_cvv)) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) hyp_hncodecmpquotbrproxyimpndv_1
  have p0040 :=
    @g_hncodecmplnkerndv A
  have p0041 :=
    @g_syl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem A (syn_cvv)) (.classEq (syn_clnker (syn_chncodecmpset A)) (syn_chwniso A)) p0039 p0040
  have p0042 :=
    @g_eqtrd (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_clnker (.cv r)) (syn_clnker (syn_chncodecmpset A)) (syn_chwniso A) p0038 p0041
  have p0043 :=
    @g_eceq2 (syn_clnker (.cv r)) (syn_chwniso A) (.cv u)
  have p0044 :=
    @g_syl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classEq (syn_clnker (.cv r)) (syn_chwniso A)) (.classEq (syn_cec (.cv u) (syn_clnker (.cv r))) (syn_cec (.cv u) (syn_chwniso A))) p0042 p0043
  have p0045 :=
    @g_simpl (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
  have p0046 :=
    @g_lnkereq (.cv r) (syn_chncodecmpset A)
  have p0047 :=
    @g_syl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classEq (.cv r) (syn_chncodecmpset A)) (.classEq (syn_clnker (.cv r)) (syn_clnker (syn_chncodecmpset A))) p0045 p0046
  have p0048 :=
    @g_a1i (.classMem A (syn_cvv)) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) hyp_hncodecmpquotbrproxyimpndv_1
  have p0049 :=
    @g_hncodecmplnkerndv A
  have p0050 :=
    @g_syl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classMem A (syn_cvv)) (.classEq (syn_clnker (syn_chncodecmpset A)) (syn_chwniso A)) p0048 p0049
  have p0051 :=
    @g_eqtrd (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_clnker (.cv r)) (syn_clnker (syn_chncodecmpset A)) (syn_chwniso A) p0047 p0050
  have p0052 :=
    @g_eceq2 (syn_clnker (.cv r)) (syn_chwniso A) (.cv v)
  have p0053 :=
    @g_syl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.classEq (syn_clnker (.cv r)) (syn_chwniso A)) (.classEq (syn_cec (.cv v) (syn_clnker (.cv r))) (syn_cec (.cv v) (syn_chwniso A))) p0051 p0052
  have p0054 :=
    @g_breq12d (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_cec (.cv u) (syn_clnker (.cv r))) (syn_cec (.cv u) (syn_chwniso A)) (syn_cec (.cv v) (syn_clnker (.cv r))) (syn_cec (.cv v) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A)) p0044 p0053
  have p0055 :=
    @g_bicomd (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (syn_cec (.cv u) (syn_clnker (.cv r))) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cec (.cv v) (syn_clnker (.cv r)))) (syn_wbr (syn_cec (.cv u) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cec (.cv v) (syn_chwniso A))) p0054
  have p0056 :=
    @g_simpl (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
  have p0057 :=
    @g_breqd (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (.cv r) (syn_chncodecmpset A) (.cv u) (.cv v) p0056
  have p0058 :=
    @g_bicomd (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (.cv u) (.cv r) (.cv v)) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) p0057
  have p0059 :=
    @g_n_3bitr4d (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wbr (syn_cec (.cv u) (syn_clnker (.cv r))) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cec (.cv v) (syn_clnker (.cv r)))) (syn_wbr (.cv u) (.cv r) (.cv v)) (syn_wbr (syn_cec (.cv u) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cec (.cv v) (syn_chwniso A))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) p0035 p0055 p0058
  exact p0059

noncomputable def g_hncodecmpquotbrproxyimpclndv
    (A : Class) (B : Class) (C : Class) (r : Var) (dv_A_r : r ∉ A.fv) (hyp_hncodecmpquotbrproxyimpclndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wb (syn_wbr (syn_cec B (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cec C (syn_chwniso A))) (syn_wbr B (syn_chncodecmpset A) C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ ({r} : Finset Var)
  let u : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_ne_r : u ≠ r := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_u : r ≠ u :=
    Ne.symm fresh_u_ne_r
  have fresh_v : v ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_v_not_B : v ∉ B.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_v_not_C : v ∉ C.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_ne_r : v ≠ r := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_v : r ≠ v :=
    Ne.symm fresh_v_ne_r
  have fresh_u_ne_v : u ≠ v := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_v_ne_u : v ≠ u :=
    Ne.symm fresh_u_ne_v
  have dv_cache_0001 : r ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : v ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : v ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : v ∉ ((Wff.imp (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wb (syn_wbr (syn_cec (.cv u) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cec C (syn_chwniso A))) (syn_wbr (.cv u) (syn_chncodecmpset A) C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_v_ne_r, fresh_v_not_A, fresh_v_ne_u, fresh_v_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : u ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : u ∉ ((Wff.imp (.classMem C (syn_chwcn A)) (.imp (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wb (syn_wbr (syn_cec B (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cec C (syn_chwniso A))) (syn_wbr B (syn_chncodecmpset A) C))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_C, fresh_u_not_A, fresh_u_ne_r, fresh_u_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))))
  have p0001 :=
    @g_simpr (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
  have p0002 :=
    @g_simpr (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))
  have p0003 :=
    @g_simpl (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))
  have p0004 :=
    @g_elex B (syn_chwcn A)
  have p0005 :=
    @g_syl (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (.classMem B (syn_chwcn A)) (.classMem B (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_biid (.classMem C (syn_chwcn A))
  have p0007 :=
    @g_a1i (syn_wb (.classMem C (syn_chwcn A)) (.classMem C (syn_chwcn A))) (.classEq (.cv u) B) p0006
  have p0008 :=
    @g_biid (.classEq (.cv r) (syn_chncodecmpset A))
  have p0009 :=
    @g_a1i (syn_wb (.classEq (.cv r) (syn_chncodecmpset A)) (.classEq (.cv r) (syn_chncodecmpset A))) (.classEq (.cv u) B) p0008
  have p0010 :=
    @g_id (.classEq (.cv u) B)
  have p0011 :=
    @g_eleq1d (.classEq (.cv u) B) (.cv u) B (syn_chwcn A) p0010
  have p0012 :=
    @g_biid (.classMem C (syn_chwcn A))
  have p0013 :=
    @g_a1i (syn_wb (.classMem C (syn_chwcn A)) (.classMem C (syn_chwcn A))) (.classEq (.cv u) B) p0012
  have p0014 :=
    @g_anbi12d (.classEq (.cv u) B) (.classMem (.cv u) (syn_chwcn A)) (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)) (.classMem C (syn_chwcn A)) p0011 p0013
  have p0015 :=
    @g_anbi12d (.classEq (.cv u) B) (.classEq (.cv r) (syn_chncodecmpset A)) (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem C (syn_chwcn A))) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) p0009 p0014
  have p0016 :=
    @g_eceq1 (.cv u) B (syn_chwniso A)
  have p0017 :=
    @g_breq1d (.classEq (.cv u) B) (syn_cec (.cv u) (syn_chwniso A)) (syn_cec B (syn_chwniso A)) (syn_cec C (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A)) p0016
  have p0018 :=
    @g_id (.classEq (.cv u) B)
  have p0019 :=
    @g_breq1d (.classEq (.cv u) B) (.cv u) B C (syn_chncodecmpset A) p0018
  have p0020 :=
    @g_bibi12d (.classEq (.cv u) B) (syn_wbr (syn_cec (.cv u) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cec C (syn_chwniso A))) (syn_wbr (syn_cec B (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cec C (syn_chwniso A))) (syn_wbr (.cv u) (syn_chncodecmpset A) C) (syn_wbr B (syn_chncodecmpset A) C) p0017 p0019
  have p0021 :=
    @g_imbi12d (.classEq (.cv u) B) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wb (syn_wbr (syn_cec (.cv u) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cec C (syn_chwniso A))) (syn_wbr (.cv u) (syn_chncodecmpset A) C)) (syn_wb (syn_wbr (syn_cec B (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cec C (syn_chwniso A))) (syn_wbr B (syn_chncodecmpset A) C)) p0015 p0020
  have p0022 :=
    @g_imbi12d (.classEq (.cv u) B) (.classMem C (syn_chwcn A)) (.classMem C (syn_chwcn A)) (.imp (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wb (syn_wbr (syn_cec (.cv u) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cec C (syn_chwniso A))) (syn_wbr (.cv u) (syn_chncodecmpset A) C))) (.imp (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wb (syn_wbr (syn_cec B (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cec C (syn_chwniso A))) (syn_wbr B (syn_chncodecmpset A) C))) p0007 p0021
  have p0023 :=
    @g_elex C (syn_chwcn A)
  have p0024 :=
    @g_biid (.classEq (.cv r) (syn_chncodecmpset A))
  have p0025 :=
    @g_a1i (syn_wb (.classEq (.cv r) (syn_chncodecmpset A)) (.classEq (.cv r) (syn_chncodecmpset A))) (.classEq (.cv v) C) p0024
  have p0026 :=
    @g_biid (.classMem (.cv u) (syn_chwcn A))
  have p0027 :=
    @g_a1i (syn_wb (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) (.classEq (.cv v) C) p0026
  have p0028 :=
    @g_id (.classEq (.cv v) C)
  have p0029 :=
    @g_eleq1d (.classEq (.cv v) C) (.cv v) C (syn_chwcn A) p0028
  have p0030 :=
    @g_anbi12d (.classEq (.cv v) C) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) (.classMem C (syn_chwcn A)) p0027 p0029
  have p0031 :=
    @g_anbi12d (.classEq (.cv v) C) (.classEq (.cv r) (syn_chncodecmpset A)) (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem C (syn_chwcn A))) p0025 p0030
  have p0032 :=
    @g_eceq1 (.cv v) C (syn_chwniso A)
  have p0033 :=
    @g_breq2d (.classEq (.cv v) C) (syn_cec (.cv v) (syn_chwniso A)) (syn_cec C (syn_chwniso A)) (syn_cec (.cv u) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A)) p0032
  have p0034 :=
    @g_id (.classEq (.cv v) C)
  have p0035 :=
    @g_breq2d (.classEq (.cv v) C) (.cv v) C (.cv u) (syn_chncodecmpset A) p0034
  have p0036 :=
    @g_bibi12d (.classEq (.cv v) C) (syn_wbr (syn_cec (.cv u) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cec (.cv v) (syn_chwniso A))) (syn_wbr (syn_cec (.cv u) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cec C (syn_chwniso A))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)) (syn_wbr (.cv u) (syn_chncodecmpset A) C) p0033 p0035
  have p0037 :=
    @g_imbi12d (.classEq (.cv v) C) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wb (syn_wbr (syn_cec (.cv u) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cec (.cv v) (syn_chwniso A))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))) (syn_wb (syn_wbr (syn_cec (.cv u) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cec C (syn_chwniso A))) (syn_wbr (.cv u) (syn_chncodecmpset A) C)) p0031 p0036
  have p0038 :=
    @g_hncodecmpquotbrproxyimpndv v u A r dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_hncodecmpquotbrproxyimpclndv_1
  have p0039 :=
    @g_vtoclg (.imp (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wb (syn_wbr (syn_cec (.cv u) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cec (.cv v) (syn_chwniso A))) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)))) (.imp (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wb (syn_wbr (syn_cec (.cv u) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cec C (syn_chwniso A))) (syn_wbr (.cv u) (syn_chncodecmpset A) C))) v C (syn_cvv) dv_cache_0004 dv_cache_0005 p0037 p0038
  have p0040 :=
    @g_syl (.classMem C (syn_chwcn A)) (.classMem C (syn_cvv)) (.imp (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wb (syn_wbr (syn_cec (.cv u) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cec C (syn_chwniso A))) (syn_wbr (.cv u) (syn_chncodecmpset A) C))) p0023 p0039
  have p0041 :=
    @g_vtoclg (.imp (.classMem C (syn_chwcn A)) (.imp (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wb (syn_wbr (syn_cec (.cv u) (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cec C (syn_chwniso A))) (syn_wbr (.cv u) (syn_chncodecmpset A) C)))) (.imp (.classMem C (syn_chwcn A)) (.imp (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wb (syn_wbr (syn_cec B (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cec C (syn_chwniso A))) (syn_wbr B (syn_chncodecmpset A) C)))) u B (syn_cvv) dv_cache_0006 dv_cache_0007 p0022 p0040
  have p0042 :=
    @g_syl (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (.classMem B (syn_cvv)) (.imp (.classMem C (syn_chwcn A)) (.imp (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wb (syn_wbr (syn_cec B (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cec C (syn_chwniso A))) (syn_wbr B (syn_chncodecmpset A) C)))) p0005 p0041
  have p0043 :=
    @g_mpd (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (.classMem C (syn_chwcn A)) (.imp (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wb (syn_wbr (syn_cec B (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cec C (syn_chwniso A))) (syn_wbr B (syn_chncodecmpset A) C))) p0002 p0042
  have p0044 :=
    @g_syl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (.imp (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wb (syn_wbr (syn_cec B (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cec C (syn_chwniso A))) (syn_wbr B (syn_chncodecmpset A) C))) p0001 p0043
  have p0045 :=
    @g_mpd (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wb (syn_wbr (syn_cec B (syn_chwniso A)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cec C (syn_chwniso A))) (syn_wbr B (syn_chncodecmpset A) C)) p0000 p0044
  exact p0045

noncomputable def g_hncodecmpquotstrictbrproxyimpclndv
    (A : Class) (B : Class) (C : Class) (r : Var) (dv_A_r : r ∉ A.fv) (hyp_hncodecmpquotstrictbrproxyimpclndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wb (syn_wbr (syn_cec B (syn_chwniso A)) (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)) (syn_cec C (syn_chwniso A))) (syn_wbr B (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ ({r} : Finset Var)
  have dv_cache_0001 : Disjoint ((syn_chwcn A)).fv ((Class.cv r)).fv := by
    exact (show Disjoint ((syn_chwcn A)).fv ((Class.cv r)).fv from (by rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CoreFVSimp.fv_class_cv]; exact (show Disjoint ((A).fv) (({r} : Finset Var)) from (Finset.disjoint_singleton_right.mpr (show r ∉ (A).fv from (by exact dv_A_r))))))
  have p0000 :=
    @g_a1i (.classMem A (syn_cvv)) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) hyp_hncodecmpquotstrictbrproxyimpclndv_1
  have p0001 :=
    @g_hncodecmpsetexg A
  have p0002 :=
    @g_syl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (.classMem A (syn_cvv)) (.classMem (syn_chncodecmpset A) (syn_cvv)) p0000 p0001
  have p0003 :=
    @g_simpl (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
  have p0004 :=
    @g_eleq1d (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (.cv r) (syn_chncodecmpset A) (syn_cvv) p0003
  have p0005 :=
    @g_mpbird (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chncodecmpset A) (syn_cvv)) p0002 p0004
  have p0006 :=
    @g_a1i (.classMem A (syn_cvv)) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) hyp_hncodecmpquotstrictbrproxyimpclndv_1
  have p0007 :=
    @g_hwcnexg A
  have p0008 :=
    @g_syl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (.classMem A (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)) p0006 p0007
  have p0009 :=
    @g_jca (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)) p0005 p0008
  have p0010 :=
    @g_a1i (.classMem A (syn_cvv)) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) hyp_hncodecmpquotstrictbrproxyimpclndv_1
  have p0011 :=
    @g_hncodecmpsetrefndv A
  have p0012 :=
    @g_syl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (.classMem A (syn_cvv)) (syn_wbr (syn_chncodecmpset A) (syn_cref) (syn_chwcn A)) p0010 p0011
  have p0013 :=
    @g_simpl (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
  have p0014 :=
    @g_breq1d (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (.cv r) (syn_chncodecmpset A) (syn_chwcn A) (syn_cref) p0013
  have p0015 :=
    @g_mpbird (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wbr (.cv r) (syn_cref) (syn_chwcn A)) (syn_wbr (syn_chncodecmpset A) (syn_cref) (syn_chwcn A)) p0012 p0014
  have p0016 :=
    @g_a1i (.classMem A (syn_cvv)) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) hyp_hncodecmpquotstrictbrproxyimpclndv_1
  have p0017 :=
    @g_hncodecmpsettransndv A
  have p0018 :=
    @g_syl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (.classMem A (syn_cvv)) (syn_wbr (syn_chncodecmpset A) (syn_ctrans) (syn_chwcn A)) p0016 p0017
  have p0019 :=
    @g_simpl (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
  have p0020 :=
    @g_breq1d (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (.cv r) (syn_chncodecmpset A) (syn_chwcn A) (syn_ctrans) p0019
  have p0021 :=
    @g_mpbird (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A)) (syn_wbr (syn_chncodecmpset A) (syn_ctrans) (syn_chwcn A)) p0018 p0020
  have p0022 :=
    @g_jca (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wbr (.cv r) (syn_cref) (syn_chwcn A)) (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A)) p0015 p0021
  have p0023 :=
    @g_a1i (.classMem A (syn_cvv)) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) hyp_hncodecmpquotstrictbrproxyimpclndv_1
  have p0024 :=
    @g_hncodecmpsetconnexndv A
  have p0025 :=
    @g_syl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (.classMem A (syn_cvv)) (syn_wbr (syn_chncodecmpset A) (syn_cconnex) (syn_chwcn A)) p0023 p0024
  have p0026 :=
    @g_simpl (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
  have p0027 :=
    @g_breq1d (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (.cv r) (syn_chncodecmpset A) (syn_chwcn A) (syn_cconnex) p0026
  have p0028 :=
    @g_mpbird (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wbr (.cv r) (syn_cconnex) (syn_chwcn A)) (syn_wbr (syn_chncodecmpset A) (syn_cconnex) (syn_chwcn A)) p0025 p0027
  have p0029 :=
    @g_jca (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wa (syn_wbr (.cv r) (syn_cref) (syn_chwcn A)) (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A))) (syn_wbr (.cv r) (syn_cconnex) (syn_chwcn A)) p0022 p0028
  have p0030 :=
    @g_hncodecmpsetssxpndv A
  have p0031 :=
    @g_a1i (syn_wss (syn_chncodecmpset A) (syn_cxp (syn_chwcn A) (syn_chwcn A))) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) p0030
  have p0032 :=
    @g_simpl (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
  have p0033 :=
    @g_sseq1d (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (.cv r) (syn_chncodecmpset A) (syn_cxp (syn_chwcn A) (syn_chwcn A)) p0032
  have p0034 :=
    @g_mpbird (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wss (.cv r) (syn_cxp (syn_chwcn A) (syn_chwcn A))) (syn_wss (syn_chncodecmpset A) (syn_cxp (syn_chwcn A) (syn_chwcn A))) p0031 p0033
  have p0035 :=
    @g_jca (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wa (syn_wa (syn_wbr (.cv r) (syn_cref) (syn_chwcn A)) (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A))) (syn_wbr (.cv r) (syn_cconnex) (syn_chwcn A))) (syn_wss (.cv r) (syn_cxp (syn_chwcn A) (syn_chwcn A))) p0029 p0034
  have p0036 :=
    @g_jca (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wa (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr (.cv r) (syn_cref) (syn_chwcn A)) (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A))) (syn_wbr (.cv r) (syn_cconnex) (syn_chwcn A))) (syn_wss (.cv r) (syn_cxp (syn_chwcn A) (syn_chwcn A)))) p0009 p0035
  have p0037 :=
    @g_simpr (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
  have p0038 :=
    @g_simpl (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))
  have p0039 :=
    @g_syl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (.classMem B (syn_chwcn A)) p0037 p0038
  have p0040 :=
    @g_simpr (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
  have p0041 :=
    @g_simpr (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))
  have p0042 :=
    @g_syl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) (.classMem C (syn_chwcn A)) p0040 p0041
  have p0043 :=
    @g_jca (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)) p0039 p0042
  have p0044 :=
    @g_jca (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr (.cv r) (syn_cref) (syn_chwcn A)) (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A))) (syn_wbr (.cv r) (syn_cconnex) (syn_chwcn A))) (syn_wss (.cv r) (syn_cxp (syn_chwcn A) (syn_chwcn A))))) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))) p0036 p0043
  have p0045 :=
    @g_brlnqordstrict (syn_chwcn A) (.cv r) B C dv_cache_0001
  have p0046 :=
    @g_syl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wa (syn_wa (syn_wa (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr (.cv r) (syn_cref) (syn_chwcn A)) (syn_wbr (.cv r) (syn_ctrans) (syn_chwcn A))) (syn_wbr (.cv r) (syn_cconnex) (syn_chwcn A))) (syn_wss (.cv r) (syn_cxp (syn_chwcn A) (syn_chwcn A))))) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wb (syn_wbr (syn_cec B (syn_clnker (.cv r))) (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)) (syn_cec C (syn_clnker (.cv r)))) (syn_wbr B (syn_cdif (.cv r) (syn_ccnv (.cv r))) C)) p0044 p0045
  have p0047 :=
    @g_simpl (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
  have p0048 :=
    @g_lnkereq (.cv r) (syn_chncodecmpset A)
  have p0049 :=
    @g_syl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (.classEq (.cv r) (syn_chncodecmpset A)) (.classEq (syn_clnker (.cv r)) (syn_clnker (syn_chncodecmpset A))) p0047 p0048
  have p0050 :=
    @g_a1i (.classMem A (syn_cvv)) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) hyp_hncodecmpquotstrictbrproxyimpclndv_1
  have p0051 :=
    @g_hncodecmplnkerndv A
  have p0052 :=
    @g_syl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (.classMem A (syn_cvv)) (.classEq (syn_clnker (syn_chncodecmpset A)) (syn_chwniso A)) p0050 p0051
  have p0053 :=
    @g_eqtrd (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_clnker (.cv r)) (syn_clnker (syn_chncodecmpset A)) (syn_chwniso A) p0049 p0052
  have p0054 :=
    @g_eceq2 (syn_clnker (.cv r)) (syn_chwniso A) B
  have p0055 :=
    @g_syl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (.classEq (syn_clnker (.cv r)) (syn_chwniso A)) (.classEq (syn_cec B (syn_clnker (.cv r))) (syn_cec B (syn_chwniso A))) p0053 p0054
  have p0056 :=
    @g_simpl (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
  have p0057 :=
    @g_lnkereq (.cv r) (syn_chncodecmpset A)
  have p0058 :=
    @g_syl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (.classEq (.cv r) (syn_chncodecmpset A)) (.classEq (syn_clnker (.cv r)) (syn_clnker (syn_chncodecmpset A))) p0056 p0057
  have p0059 :=
    @g_a1i (.classMem A (syn_cvv)) (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) hyp_hncodecmpquotstrictbrproxyimpclndv_1
  have p0060 :=
    @g_hncodecmplnkerndv A
  have p0061 :=
    @g_syl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (.classMem A (syn_cvv)) (.classEq (syn_clnker (syn_chncodecmpset A)) (syn_chwniso A)) p0059 p0060
  have p0062 :=
    @g_eqtrd (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_clnker (.cv r)) (syn_clnker (syn_chncodecmpset A)) (syn_chwniso A) p0058 p0061
  have p0063 :=
    @g_eceq2 (syn_clnker (.cv r)) (syn_chwniso A) C
  have p0064 :=
    @g_syl (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (.classEq (syn_clnker (.cv r)) (syn_chwniso A)) (.classEq (syn_cec C (syn_clnker (.cv r))) (syn_cec C (syn_chwniso A))) p0062 p0063
  have p0065 :=
    @g_breq12d (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_cec B (syn_clnker (.cv r))) (syn_cec B (syn_chwniso A)) (syn_cec C (syn_clnker (.cv r))) (syn_cec C (syn_chwniso A)) (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)) p0055 p0064
  have p0066 :=
    @g_bicomd (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wbr (syn_cec B (syn_clnker (.cv r))) (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)) (syn_cec C (syn_clnker (.cv r)))) (syn_wbr (syn_cec B (syn_chwniso A)) (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)) (syn_cec C (syn_chwniso A))) p0065
  have p0067 :=
    @g_simpl (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
  have p0068 :=
    @g_simpl (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
  have p0069 :=
    @g_cnveqd (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (.cv r) (syn_chncodecmpset A) p0068
  have p0070 :=
    @g_difeq12d (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (.cv r) (syn_chncodecmpset A) (syn_ccnv (.cv r)) (syn_ccnv (syn_chncodecmpset A)) p0067 p0069
  have p0071 :=
    @g_breqd (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_cdif (.cv r) (syn_ccnv (.cv r))) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) B C p0070
  have p0072 :=
    @g_bicomd (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wbr B (syn_cdif (.cv r) (syn_ccnv (.cv r))) C) (syn_wbr B (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) C) p0071
  have p0073 :=
    @g_n_3bitr4d (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))) (syn_wbr (syn_cec B (syn_clnker (.cv r))) (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)) (syn_cec C (syn_clnker (.cv r)))) (syn_wbr B (syn_cdif (.cv r) (syn_ccnv (.cv r))) C) (syn_wbr (syn_cec B (syn_chwniso A)) (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)) (syn_cec C (syn_chwniso A))) (syn_wbr B (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) C) p0046 p0066 p0072
  exact p0073

noncomputable def g_hnwcutrelambfnnoarndv
    (A : Class) (D : Class) (R : Class) (hyp_hnwcutrelambfnnoarndv_1 : Nominal.NPrf (syn_wss D A)) (hyp_hnwcutrelambfnnoarndv_2 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf (syn_wf (syn_chnwcutrel R D) (syn_cpw1 D) (syn_chwcn A)) := by
  let proofSupport : Finset Var := A.fv ∪ D.fv ∪ R.fv
  have p0000 :=
    @g_hnwcutrelfndv D R hyp_hnwcutrelambfnnoarndv_2
  have p0001 :=
    @g_hwcnssbase A D hyp_hnwcutrelambfnnoarndv_1
  have p0002 :=
    @g_pm3_2i (syn_wf (syn_chnwcutrel R D) (syn_cpw1 D) (syn_chwcn D)) (syn_wss (syn_chwcn D) (syn_chwcn A)) p0000 p0001
  have p0003 :=
    @g_fss (syn_cpw1 D) (syn_chwcn D) (syn_chwcn A) (syn_chnwcutrel R D)
  have p0004 :=
    Nominal.mp p0002 p0003
  exact p0004

noncomputable def g_hnwcutambfactorvalnoarndv
    (A : Class) (D : Class) (R : Class) (q : Var) (dv_D_q : q ∉ D.fv) (dv_R_q : q ∉ R.fv) (hyp_hnwcutambfactorvalnoarndv_1 : Nominal.NPrf (syn_wss D A)) (hyp_hnwcutambfactorvalnoarndv_2 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) (hyp_hnwcutambfactorvalnoarndv_3 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel R D))) (.cv q)) (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A)))) := by
  let proofSupport : Finset Var := A.fv ∪ D.fv ∪ R.fv ∪ ({q} : Finset Var)
  have p0000 :=
    @g_hnwcutrelambfnnoarndv A D R hyp_hnwcutambfactorvalnoarndv_1 hyp_hnwcutambfactorvalnoarndv_2
  have p0001 :=
    @g_sifmap (syn_cpw1 D) (syn_chwcn A) (syn_chnwcutrel R D)
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_id (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
  have p0004 :=
    @g_hnwcutsirelvalndv D R q hyp_hnwcutambfactorvalnoarndv_2
  have p0005 :=
    @g_hwcnssbase A D hyp_hnwcutambfactorvalnoarndv_1
  have p0006 :=
    @g_pw12argcl (.cv q) D
  have p0007 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (syn_cuni (syn_cuni (.cv q))) D) (.classEq (.cv q) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv q)))))) p0006
  have p0008 :=
    @g_hnwcutcodecnclndv (syn_cuni (syn_cuni (.cv q))) D R hyp_hnwcutambfactorvalnoarndv_2
  have p0009 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classMem (syn_cuni (syn_cuni (.cv q))) D) (.classMem (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_chwcn D)) p0007 p0008
  have p0010 :=
    @g_sseldi (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (syn_chwcn D) (syn_chwcn A) (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) p0005 p0009
  have p0011 :=
    @g_qmapcompvald (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) A (syn_chnwcutcode R D (syn_cuni (syn_cuni (.cv q)))) (syn_csi (syn_chnwcutrel R D)) (syn_cpw1 (syn_cpw1 D)) q hyp_hnwcutambfactorvalnoarndv_3 p0002 p0003 p0004 p0010
  exact p0011

noncomputable def g_hnwcutambfactorvalcodendv
    (A : Class) (B : Class) (q : Var) (dv_B_q : q ∉ B.fv) (hyp_hnwcutambfactorvalcodendv_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_hnwcutambfactorvalcodendv_2 : Nominal.NPrf (.classMem B (syn_chwcn A))) :
    Nominal.NPrf (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) B)))) (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B)))) (.cv q)) (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) B) (syn_cfv (syn_c2nd) B) (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ ({q} : Finset Var)
  have dv_cache_0001 : q ∉ ((syn_cfv (syn_c2nd) B)).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ ((syn_cfv (syn_c1st) B)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_hwcnbaseclndv A B
  have p0001 :=
    Nominal.mp hyp_hnwcutambfactorvalcodendv_2 p0000
  have p0002 :=
    @g_hwcnweclndv A B
  have p0003 :=
    Nominal.mp hyp_hnwcutambfactorvalcodendv_2 p0002
  have p0004 :=
    @g_hnwcutambfactorvalnoarndv A (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c1st) B) q dv_cache_0001 dv_cache_0002 p0001 p0003 hyp_hnwcutambfactorvalcodendv_1
  exact p0004

noncomputable def g_hnwcuttxpeq1dndv
    (ph : Wff) (A : Class) (B : Class) (C : Class) (hyp_hnwcuttxpeq1dndv_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_ctxp A C) (syn_ctxp B C))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv ∪ C.fv
  have p0000 :=
    @g_coeq2d ph A B (syn_ccnv (syn_c1st)) hyp_hnwcuttxpeq1dndv_1
  have p0001 :=
    @g_ineq1d ph (syn_ccom (syn_ccnv (syn_c1st)) A) (syn_ccom (syn_ccnv (syn_c1st)) B) (syn_ccom (syn_ccnv (syn_c2nd)) C) p0000
  have p0002 :=
    (by simpa [syn_ctxp] using (Nominal.classEqRefl (syn_ctxp A C)))
  have p0003 :=
    (by simpa [syn_ctxp] using (Nominal.classEqRefl (syn_ctxp B C)))
  have p0004 :=
    @g_n_3eqtr4g ph (syn_cin (syn_ccom (syn_ccnv (syn_c1st)) A) (syn_ccom (syn_ccnv (syn_c2nd)) C)) (syn_cin (syn_ccom (syn_ccnv (syn_c1st)) B) (syn_ccom (syn_ccnv (syn_c2nd)) C)) (syn_ctxp A C) (syn_ctxp B C) p0001 p0002 p0003
  exact p0004

noncomputable def g_hnwcutimageeqdndv
    (ph : Wff) (A : Class) (B : Class) (hyp_hnwcutimageeqdndv_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cimage A) (syn_cimage B))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_sieqdndv ph A B hyp_hnwcutimageeqdndv_1
  have p0001 :=
    @g_cnveqd ph (syn_csi A) (syn_csi B) p0000
  have p0002 :=
    @g_coeq2d ph (syn_ccnv (syn_csi A)) (syn_ccnv (syn_csi B)) (syn_csset) p0001
  have p0003 :=
    @g_hnwcuttxpeq1dndv ph (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))) (syn_ccom (syn_csset) (syn_ccnv (syn_csi B))) (syn_cvv) p0002
  have p0004 :=
    (by simpa [syn_cins3] using (Nominal.classEqRefl (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))))))
  have p0005 :=
    (by simpa [syn_cins3] using (Nominal.classEqRefl (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi B))))))
  have p0006 :=
    @g_n_3eqtr4g ph (syn_ctxp (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))) (syn_cvv)) (syn_ctxp (syn_ccom (syn_csset) (syn_ccnv (syn_csi B))) (syn_cvv)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A)))) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi B)))) p0003 p0004 p0005
  have p0007 :=
    @g_difeq2d ph (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A)))) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi B)))) (syn_cins2 (syn_csset)) p0006
  have p0008 :=
    @g_sieqdndv ph A B hyp_hnwcutimageeqdndv_1
  have p0009 :=
    @g_cnveqd ph (syn_csi A) (syn_csi B) p0008
  have p0010 :=
    @g_coeq2d ph (syn_ccnv (syn_csi A)) (syn_ccnv (syn_csi B)) (syn_csset) p0009
  have p0011 :=
    @g_hnwcuttxpeq1dndv ph (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))) (syn_ccom (syn_csset) (syn_ccnv (syn_csi B))) (syn_cvv) p0010
  have p0012 :=
    (by simpa [syn_cins3] using (Nominal.classEqRefl (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))))))
  have p0013 :=
    (by simpa [syn_cins3] using (Nominal.classEqRefl (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi B))))))
  have p0014 :=
    @g_n_3eqtr4g ph (syn_ctxp (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))) (syn_cvv)) (syn_ctxp (syn_ccom (syn_csset) (syn_ccnv (syn_csi B))) (syn_cvv)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A)))) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi B)))) p0011 p0012 p0013
  have p0015 :=
    @g_difeq1d ph (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A)))) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi B)))) (syn_cins2 (syn_csset)) p0014
  have p0016 :=
    @g_uneq12d ph (syn_cdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))))) (syn_cdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi B))))) (syn_cdif (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A)))) (syn_cins2 (syn_csset))) (syn_cdif (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi B)))) (syn_cins2 (syn_csset))) p0007 p0015
  have p0017 :=
    (by simpa [syn_csymdif] using (Nominal.classEqRefl (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A)))))))
  have p0018 :=
    (by simpa [syn_csymdif] using (Nominal.classEqRefl (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi B)))))))
  have p0019 :=
    @g_n_3eqtr4g ph (syn_cun (syn_cdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))))) (syn_cdif (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A)))) (syn_cins2 (syn_csset)))) (syn_cun (syn_cdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi B))))) (syn_cdif (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi B)))) (syn_cins2 (syn_csset)))) (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))))) (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi B))))) p0016 p0017 p0018
  have p0020 :=
    @g_imaeq1d ph (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))))) (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi B))))) (syn_c1c) p0019
  have p0021 :=
    @g_compleqd ph (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))))) (syn_c1c)) (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi B))))) (syn_c1c)) p0020
  have p0022 :=
    (by simpa [syn_cimage] using (Nominal.classEqRefl (syn_cimage A)))
  have p0023 :=
    (by simpa [syn_cimage] using (Nominal.classEqRefl (syn_cimage B)))
  have p0024 :=
    @g_n_3eqtr4g ph (syn_ccompl (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi A))))) (syn_c1c))) (syn_ccompl (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset) (syn_ccnv (syn_csi B))))) (syn_c1c))) (syn_cimage A) (syn_cimage B) p0021 p0022 p0023
  exact p0024

#print axioms g_hnwcutimageeqdndv

end NFChoice.DirectNominalPrf.WPPReplay
