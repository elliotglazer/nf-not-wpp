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
import NominalWPPReplayChunk014Compact001Part013

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

noncomputable def g_wppstrictcomplement
    (A : Class) (R : Class) (e : Var) (c : Var) (dv_A_R : Disjoint A.fv R.fv) (dv_A_c : c ∉ A.fv) (dv_A_e : e ∉ A.fv) (dv_R_c : c ∉ R.fv) (dv_R_e : e ∉ R.fv) (dv_c_e : c ≠ e) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (syn_wb (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))) (syn_wbr (.cv e) R (.cv c)))) := by
  let proofSupport : Finset Var := A.fv ∪ R.fv ∪ ({e} : Finset Var) ∪ ({c} : Finset Var)
  have p0000 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))
  have p0001 :=
    @g_simpll (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A) (.classMem (.cv c) A)
  have p0002 :=
    @g_wppweconnex A R
  have p0003 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cconnex) A) p0001 p0002
  have p0004 :=
    @g_simpr (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)
  have p0005 :=
    @g_simplr (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A) (.classMem (.cv c) A)
  have p0006 :=
    @g_connexd (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) A R (.cv c) (.cv e) p0003 p0004 p0005
  have p0007 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (syn_wo (syn_wbr (.cv c) R (.cv e)) (syn_wbr (.cv e) R (.cv c))) p0000 p0006
  have p0008 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))) (syn_wbr (.cv c) R (.cv e))
  have p0009 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))
  have p0010 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))) (syn_wbr (.cv c) R (.cv e))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) p0008 p0009
  have p0011 :=
    @g_simpll (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A) (.classMem (.cv c) A)
  have p0012 :=
    @g_wppweref A R
  have p0013 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cref) A) p0011 p0012
  have p0014 :=
    @g_simplr (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A) (.classMem (.cv c) A)
  have p0015 :=
    @g_refd (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) A R (.cv e) p0013 p0014
  have p0016 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))) (syn_wbr (.cv c) R (.cv e))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv e)) p0010 p0015
  have p0017 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))) (syn_wbr (.cv c) R (.cv e))
  have p0018 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))
  have p0019 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))) (syn_wbr (.cv c) R (.cv e))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))) p0017 p0018
  have p0020 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))) (syn_wbr (.cv c) R (.cv e))) (syn_wne (.cv c) (.cv e))
  have p0021 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))) (syn_wbr (.cv c) R (.cv e))
  have p0022 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))) (syn_wbr (.cv c) R (.cv e))) (syn_wne (.cv c) (.cv e))) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))) (syn_wbr (.cv c) R (.cv e))) (syn_wbr (.cv c) R (.cv e)) p0020 p0021
  have p0023 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))) (syn_wbr (.cv c) R (.cv e))) (syn_wne (.cv c) (.cv e))
  have p0024 :=
    @g_jca (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))) (syn_wbr (.cv c) R (.cv e))) (syn_wne (.cv c) (.cv e))) (syn_wbr (.cv c) R (.cv e)) (syn_wne (.cv c) (.cv e)) p0022 p0023
  have p0025 :=
    @g_strictbr R e c
  have p0026 :=
    @g_biimpri (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (syn_wa (syn_wbr (.cv c) R (.cv e)) (syn_wne (.cv c) (.cv e))) p0025
  have p0027 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))) (syn_wbr (.cv c) R (.cv e))) (syn_wne (.cv c) (.cv e))) (syn_wa (syn_wbr (.cv c) R (.cv e)) (syn_wne (.cv c) (.cv e))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) p0024 p0026
  have p0028 :=
    @g_mtand (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))) (syn_wbr (.cv c) R (.cv e))) (syn_wne (.cv c) (.cv e)) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) p0019 p0027
  have p0029 :=
    @g_id (syn_wne (.cv c) (.cv e))
  have p0030 :=
    @g_necon1bi (syn_wne (.cv c) (.cv e)) (.cv c) (.cv e) p0029
  have p0031 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))) (syn_wbr (.cv c) R (.cv e))) (.neg (syn_wne (.cv c) (.cv e))) (.classEq (.cv c) (.cv e)) p0028 p0030
  have p0032 :=
    @g_breq2d (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))) (syn_wbr (.cv c) R (.cv e))) (.cv c) (.cv e) (.cv e) R p0031
  have p0033 :=
    @g_mpbird (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))) (syn_wbr (.cv c) R (.cv e))) (syn_wbr (.cv e) R (.cv c)) (syn_wbr (.cv e) R (.cv e)) p0016 p0032
  have p0034 :=
    @g_ex (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))) (syn_wbr (.cv c) R (.cv e)) (syn_wbr (.cv e) R (.cv c)) p0033
  have p0035 :=
    @g_idd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))) (syn_wbr (.cv e) R (.cv c))
  have p0036 :=
    @g_jaod (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))) (syn_wbr (.cv c) R (.cv e)) (syn_wbr (.cv e) R (.cv c)) (syn_wbr (.cv e) R (.cv c)) p0034 p0035
  have p0037 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))) (syn_wo (syn_wbr (.cv c) R (.cv e)) (syn_wbr (.cv e) R (.cv c))) (syn_wbr (.cv e) R (.cv c)) p0007 p0036
  have p0038 :=
    @g_ex (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))) (syn_wbr (.cv e) R (.cv c)) p0037
  have p0039 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
  have p0040 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c))
  have p0041 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) p0039 p0040
  have p0042 :=
    @g_simpll (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A) (.classMem (.cv c) A)
  have p0043 :=
    @g_wppweantisym A R
  have p0044 :=
    @g_syl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cantisym) A) p0042 p0043
  have p0045 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (syn_wbr R (syn_cantisym) A) p0041 p0044
  have p0046 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
  have p0047 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c))
  have p0048 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) p0046 p0047
  have p0049 :=
    @g_simpr (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)
  have p0050 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (.classMem (.cv c) A) p0048 p0049
  have p0051 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
  have p0052 :=
    @g_simpl (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c))
  have p0053 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) p0051 p0052
  have p0054 :=
    @g_simplr (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A) (.classMem (.cv c) A)
  have p0055 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))) (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (.classMem (.cv e) A) p0053 p0054
  have p0056 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
  have p0057 :=
    @g_strictbr R e c
  have p0058 :=
    @g_biimpi (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (syn_wa (syn_wbr (.cv c) R (.cv e)) (syn_wne (.cv c) (.cv e))) p0057
  have p0059 :=
    @g_simpl (syn_wbr (.cv c) R (.cv e)) (syn_wne (.cv c) (.cv e))
  have p0060 :=
    @g_syl (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (syn_wa (syn_wbr (.cv c) R (.cv e)) (syn_wne (.cv c) (.cv e))) (syn_wbr (.cv c) R (.cv e)) p0058 p0059
  have p0061 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (syn_wbr (.cv c) R (.cv e)) p0056 p0060
  have p0062 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
  have p0063 :=
    @g_simpr (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c))
  have p0064 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c))) (syn_wbr (.cv e) R (.cv c)) p0062 p0063
  have p0065 :=
    @g_antid (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))) A R (.cv c) (.cv e) p0045 p0050 p0055 p0061 p0064
  have p0066 :=
    @g_simpr (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))
  have p0067 :=
    @g_strictbr R e c
  have p0068 :=
    @g_biimpi (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (syn_wa (syn_wbr (.cv c) R (.cv e)) (syn_wne (.cv c) (.cv e))) p0067
  have p0069 :=
    @g_simpr (syn_wbr (.cv c) R (.cv e)) (syn_wne (.cv c) (.cv e))
  have p0070 :=
    @g_syl (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (syn_wa (syn_wbr (.cv c) R (.cv e)) (syn_wne (.cv c) (.cv e))) (syn_wne (.cv c) (.cv e)) p0068 p0069
  have p0071 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (syn_wne (.cv c) (.cv e)) p0066 p0070
  have p0072 :=
    @g_pm2_21ddne (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))) (.cv c) (.cv e) p0065 p0071
  have p0073 :=
    @g_pm2_01da (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c))) (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) p0072
  have p0074 :=
    @g_ex (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (syn_wbr (.cv e) R (.cv c)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))) p0073
  have p0075 :=
    @g_impbid (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))) (syn_wbr (.cv e) R (.cv c)) p0038 p0074
  exact p0075

noncomputable def g_wppstrictleastbridge
    (ph : Wff) (A : Class) (R : Class) (e : Var) (c : Var) (dv_A_R : Disjoint A.fv R.fv) (dv_A_c : c ∉ A.fv) (dv_A_e : e ∉ A.fv) (dv_R_c : c ∉ R.fv) (dv_R_e : e ∉ R.fv) (dv_c_e : c ≠ e) :
    Nominal.NPrf (.imp (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (syn_wb (syn_wral c A (.imp (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.neg ph))) (syn_wral c A (.imp ph (syn_wbr (.cv e) R (.cv c)))))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ R.fv ∪ ({e} : Finset Var) ∪ ({c} : Finset Var)
  have dv_cache_0001 : Disjoint (A).fv (R).fv := by
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0002 : c ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : e ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_e, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : c ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_c, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : e ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_e, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : c ≠ e := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show c ≠ e from (by exact dv_c_e))
  have dv_cache_0007 : c ∉ ((syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_c, dv_A_c, dv_c_e, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_wppstrictcomplement A R e c dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_imbi2d (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e))) (syn_wbr (.cv e) R (.cv c)) ph p0000
  have p0002 :=
    @g_con2b (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) ph
  have p0003 :=
    @g_biid (.imp ph (syn_wbr (.cv e) R (.cv c)))
  have p0004 :=
    @g_n_3bitr4g (syn_wa (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.classMem (.cv c) A)) (.imp ph (.neg (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)))) (.imp ph (syn_wbr (.cv e) R (.cv c))) (.imp (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.neg ph)) (.imp ph (syn_wbr (.cv e) R (.cv c))) p0001 p0002 p0003
  have p0005 :=
    @g_ralbidva (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (.imp (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.neg ph)) (.imp ph (syn_wbr (.cv e) R (.cv c))) c A dv_cache_0007 p0004
  exact p0005

noncomputable def g_fdminsepfpivred
    (A : Class) (B : Class) (C : Class) (D : Class) (R : Class) (e : Var) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv) (dv_A_D : Disjoint A.fv D.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_A_e : e ∉ A.fv) (dv_B_C : Disjoint B.fv C.fv) (dv_B_D : Disjoint B.fv D.fv) (dv_B_R : Disjoint B.fv R.fv) (dv_B_e : e ∉ B.fv) (dv_C_D : Disjoint C.fv D.fv) (dv_C_R : Disjoint C.fv R.fv) (dv_C_e : e ∉ C.fv) (dv_D_R : Disjoint D.fv R.fv) (dv_D_e : e ∉ D.fv) (dv_R_e : e ∉ R.fv) :
    Nominal.NPrf (.imp (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))) (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdminsep R A B)) (.classMem (.cv e) (syn_cfpiv R A C D)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv ∪ ({e} : Finset Var)
  let c : Var := freshVar proofSupport 0
  have fresh_c : c ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_c_not_A : c ∉ A.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_c_not_B : c ∉ B.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_c_not_C : c ∉ C.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_c_not_D : c ∉ D.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_c_not_R : c ∉ R.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_c_ne_e : c ≠ e := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_e_ne_c : e ≠ c :=
    Ne.symm fresh_c_ne_e
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (C).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0003 : Disjoint (A).fv (D).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint (A).fv (D).fv from (show Disjoint (A).fv (D).fv from (by exact dv_A_D)))
  have dv_cache_0004 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0005 : c ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : e ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_e, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : Disjoint (B).fv (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0008 : Disjoint (B).fv (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show Disjoint (B).fv (D).fv from (show Disjoint (B).fv (D).fv from (by exact dv_B_D)))
  have dv_cache_0009 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0010 : c ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : e ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_e, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : Disjoint (C).fv (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show Disjoint (C).fv (D).fv from (show Disjoint (C).fv (D).fv from (by exact dv_C_D)))
  have dv_cache_0013 : Disjoint (C).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0014 : c ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : e ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_e, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : Disjoint (D).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have dv_cache_0017 : c ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : e ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_D_e, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : c ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_c_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : e ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_e, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : c ≠ e := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show c ≠ e from (by exact fresh_c_ne_e))
  have p0000 :=
    @g_simpr (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))
  have p0001 :=
    @g_fdminsepval0J A B C D R e c dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
  have p0002 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))) (syn_wa (.classMem C B) (.classMem D B)) (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdminsep R A B)) (syn_wa (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D))) (.neg (syn_wrex c A (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (.cv c) (syn_csep2 C D))))))) p0000 p0001
  have p0003 :=
    @g_simpl (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))
  have p0004 :=
    @g_imnan (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (.cv c) (syn_csep2 C D))
  have p0005 :=
    @g_ralbii (.imp (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.neg (.classMem (.cv c) (syn_csep2 C D)))) (.neg (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (.cv c) (syn_csep2 C D)))) c A p0004
  have p0006 :=
    @g_ralnex (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (.cv c) (syn_csep2 C D))) c A
  have p0007 :=
    @g_bitri (syn_wral c A (.imp (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.neg (.classMem (.cv c) (syn_csep2 C D))))) (syn_wral c A (.neg (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (.cv c) (syn_csep2 C D))))) (.neg (syn_wrex c A (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (.cv c) (syn_csep2 C D))))) p0005 p0006
  have p0008 :=
    @g_bicomi (syn_wral c A (.imp (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.neg (.classMem (.cv c) (syn_csep2 C D))))) (.neg (syn_wrex c A (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (.cv c) (syn_csep2 C D))))) p0007
  have p0009 :=
    @g_a1i (syn_wb (.neg (syn_wrex c A (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (.cv c) (syn_csep2 C D))))) (syn_wral c A (.imp (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.neg (.classMem (.cv c) (syn_csep2 C D)))))) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D)))) p0008
  have p0010 :=
    @g_simpl (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D)))
  have p0011 :=
    @g_simpr (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D)))
  have p0012 :=
    @g_simpl (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D))
  have p0013 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D)))) (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D))) (.classMem (.cv e) A) p0011 p0012
  have p0014 :=
    @g_jca (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D)))) (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A) p0010 p0013
  have p0015 :=
    @g_wppstrictleastbridge (.classMem (.cv c) (syn_csep2 C D)) A R e c dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0019 dv_cache_0020 dv_cache_0021
  have p0016 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D)))) (syn_wa (syn_wbr R (syn_cwe) A) (.classMem (.cv e) A)) (syn_wb (syn_wral c A (.imp (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.neg (.classMem (.cv c) (syn_csep2 C D))))) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 C D)) (syn_wbr (.cv e) R (.cv c))))) p0014 p0015
  have p0017 :=
    @g_bitrd (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D)))) (.neg (syn_wrex c A (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (.cv c) (syn_csep2 C D))))) (syn_wral c A (.imp (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.neg (.classMem (.cv c) (syn_csep2 C D))))) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 C D)) (syn_wbr (.cv e) R (.cv c)))) p0009 p0016
  have p0018 :=
    @g_pm5_32da (syn_wbr R (syn_cwe) A) (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D))) (.neg (syn_wrex c A (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (.cv c) (syn_csep2 C D))))) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 C D)) (syn_wbr (.cv e) R (.cv c)))) p0017
  have p0019 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))) (syn_wbr R (syn_cwe) A) (syn_wb (syn_wa (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D))) (.neg (syn_wrex c A (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (.cv c) (syn_csep2 C D)))))) (syn_wa (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D))) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 C D)) (syn_wbr (.cv e) R (.cv c)))))) p0003 p0018
  have p0020 :=
    @g_bitrd (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdminsep R A B)) (syn_wa (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D))) (.neg (syn_wrex c A (syn_wa (syn_wbr (.cv c) (syn_cdif R (syn_cid)) (.cv e)) (.classMem (.cv c) (syn_csep2 C D)))))) (syn_wa (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D))) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 C D)) (syn_wbr (.cv e) R (.cv c))))) p0002 p0019
  have p0021 :=
    @g_elfpiv A C D R e c dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
  have p0022 :=
    @g_bicomi (.classMem (.cv e) (syn_cfpiv R A C D)) (syn_wa (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D))) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 C D)) (syn_wbr (.cv e) R (.cv c))))) p0021
  have p0023 :=
    @g_a1i (syn_wb (syn_wa (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D))) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 C D)) (syn_wbr (.cv e) R (.cv c))))) (.classMem (.cv e) (syn_cfpiv R A C D))) (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))) p0022
  have p0024 :=
    @g_bitrd (syn_wa (syn_wbr R (syn_cwe) A) (syn_wa (.classMem C B) (.classMem D B))) (.classMem (syn_copk (syn_csn (.cv e)) (syn_copk C D)) (syn_cfdminsep R A B)) (syn_wa (syn_wa (.classMem (.cv e) A) (.classMem (.cv e) (syn_csep2 C D))) (syn_wral c A (.imp (.classMem (.cv c) (syn_csep2 C D)) (syn_wbr (.cv e) R (.cv c))))) (.classMem (.cv e) (syn_cfpiv R A C D)) p0020 p0023
  exact p0024

noncomputable def g_elfdminvalp
    (A : Class) (B : Class) (C : Class) (R : Class) (d : Var) (dv_A_B : Disjoint A.fv B.fv) (dv_A_C : Disjoint A.fv C.fv) (dv_A_R : Disjoint A.fv R.fv) (dv_A_d : d ∉ A.fv) (dv_B_C : Disjoint B.fv C.fv) (dv_B_R : Disjoint B.fv R.fv) (dv_B_d : d ∉ B.fv) (dv_C_R : Disjoint C.fv R.fv) (dv_C_d : d ∉ C.fv) (dv_R_d : d ∉ R.fv) (hyp_elfdminvalp_1 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem (.cv d) (syn_cfdminvalp R A B C)) (syn_wa (.classMem (.cv d) A) (.classMem (syn_copk (syn_csn (.cv d)) C) (syn_cfdminsep R A B)))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ R.fv ∪ ({d} : Finset Var)
  have dv_cache_0001 : Disjoint (A).fv (B).fv := by
    exact (show Disjoint (A).fv (B).fv from (show Disjoint (A).fv (B).fv from (by exact dv_A_B)))
  have dv_cache_0002 : Disjoint (A).fv (C).fv := by
    clear dv_cache_0001
    exact (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
  have dv_cache_0003 : Disjoint (A).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have dv_cache_0004 : Disjoint (B).fv (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show Disjoint (B).fv (C).fv from (show Disjoint (B).fv (C).fv from (by exact dv_B_C)))
  have dv_cache_0005 : Disjoint (B).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show Disjoint (B).fv (R).fv from (show Disjoint (B).fv (R).fv from (by exact dv_B_R)))
  have dv_cache_0006 : Disjoint (C).fv (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0007 : d ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : d ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : d ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : d ∉ (R).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_R_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_fdminvalpss A B C R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 hyp_elfdminvalp_1
  have p0001 :=
    @g_sseli (syn_cfdminvalp R A B C) A (.cv d) p0000
  have p0002 :=
    @g_fdminvalpbr d A B C R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0007 dv_cache_0004 dv_cache_0005 dv_cache_0008 dv_cache_0006 dv_cache_0009 dv_cache_0010 hyp_elfdminvalp_1
  have p0003 :=
    @g_biimpi (.classMem (.cv d) (syn_cfdminvalp R A B C)) (.classMem (syn_copk (syn_csn (.cv d)) C) (syn_cfdminsep R A B)) p0002
  have p0004 :=
    @g_jca (.classMem (.cv d) (syn_cfdminvalp R A B C)) (.classMem (.cv d) A) (.classMem (syn_copk (syn_csn (.cv d)) C) (syn_cfdminsep R A B)) p0001 p0003
  have p0005 :=
    @g_simpr (.classMem (.cv d) A) (.classMem (syn_copk (syn_csn (.cv d)) C) (syn_cfdminsep R A B))
  have p0006 :=
    @g_fdminvalpbr d A B C R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0007 dv_cache_0004 dv_cache_0005 dv_cache_0008 dv_cache_0006 dv_cache_0009 dv_cache_0010 hyp_elfdminvalp_1
  have p0007 :=
    @g_biimpri (.classMem (.cv d) (syn_cfdminvalp R A B C)) (.classMem (syn_copk (syn_csn (.cv d)) C) (syn_cfdminsep R A B)) p0006
  have p0008 :=
    @g_syl (syn_wa (.classMem (.cv d) A) (.classMem (syn_copk (syn_csn (.cv d)) C) (syn_cfdminsep R A B))) (.classMem (syn_copk (syn_csn (.cv d)) C) (syn_cfdminsep R A B)) (.classMem (.cv d) (syn_cfdminvalp R A B C)) p0005 p0007
  have p0009 :=
    @g_impbii (.classMem (.cv d) (syn_cfdminvalp R A B C)) (syn_wa (.classMem (.cv d) A) (.classMem (syn_copk (syn_csn (.cv d)) C) (syn_cfdminsep R A B))) p0004 p0008
  exact p0009

#print axioms g_elfdminvalp

end NFChoice.DirectNominalPrf.WPPReplay
