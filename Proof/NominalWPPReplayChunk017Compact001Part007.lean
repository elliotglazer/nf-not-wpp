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
import NominalWPPReplayChunk017Compact001Part006

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

noncomputable def g_hnsicodemapclassimdndv
    (A : Class) (q : Var) (dv_A_q : q ∉ A.fv) (hyp_hnsicodemapclassimdndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classEq (syn_cima (syn_chnsicodemap A) (syn_cec (.cv q) (syn_csi (syn_chwniso A)))) (syn_cec (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwniso (syn_cpw1 A))))) := by
  let proofSupport : Finset Var := A.fv ∪ ({q} : Finset Var)
  have dv_cache_0001 : Disjoint (A).fv ((syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))).fv := by
    exact (show Disjoint (A).fv ((syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin]; exact (show Disjoint ((A).fv) ((((syn_ckqrel (syn_clefin))).fv) ∪ (((syn_cxp (syn_c0) (syn_c0))).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint ((A).fv) (((syn_ckqrel (syn_clefin))).fv) from (by rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel]; exact (show Disjoint ((A).fv) (((syn_clefin)).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin]; exact (show Disjoint ((A).fv) ((∅ : Finset Var)) from (by simp)))))), (show Disjoint ((A).fv) (((syn_cxp (syn_c0) (syn_c0))).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp]; exact (show Disjoint ((A).fv) ((((syn_c0)).fv) ∪ (((syn_c0)).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint ((A).fv) (((syn_c0)).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show Disjoint ((A).fv) ((∅ : Finset Var)) from (by simp)))), (show Disjoint ((A).fv) (((syn_c0)).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0]; exact (show Disjoint ((A).fv) ((∅ : Finset Var)) from (by simp))))⟩))))⟩))))
  have p0000 :=
    @g_eceq1 (.cv q) (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q) (syn_csn (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_csi (syn_chwniso A))
  have p0001 :=
    @g_imaeq2d (.classEq (.cv q) (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q) (syn_csn (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))) (syn_cec (.cv q) (syn_csi (syn_chwniso A))) (syn_cec (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q) (syn_csn (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_csi (syn_chwniso A))) (syn_chnsicodemap A) p0000
  have p0002 :=
    @g_id (.classEq (.cv q) (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q) (syn_csn (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))))
  have p0003 :=
    @g_fveq2d (.classEq (.cv q) (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q) (syn_csn (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))) (.cv q) (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q) (syn_csn (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_chnsicodemap A) p0002
  have p0004 :=
    @g_eceq1 (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q) (syn_csn (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))) (syn_chwniso (syn_cpw1 A))
  have p0005 :=
    @g_syl (.classEq (.cv q) (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q) (syn_csn (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q) (syn_csn (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))))) (.classEq (syn_cec (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwniso (syn_cpw1 A))) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q) (syn_csn (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))) (syn_chwniso (syn_cpw1 A)))) p0003 p0004
  have p0006 :=
    @g_eqeq12d (.classEq (.cv q) (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q) (syn_csn (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))) (syn_cima (syn_chnsicodemap A) (syn_cec (.cv q) (syn_csi (syn_chwniso A)))) (syn_cima (syn_chnsicodemap A) (syn_cec (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q) (syn_csn (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_csi (syn_chwniso A)))) (syn_cec (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwniso (syn_cpw1 A))) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q) (syn_csn (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))) (syn_chwniso (syn_cpw1 A))) p0001 p0005
  have p0007 :=
    @g_eqid (syn_c0)
  have p0008 :=
    @g_simpr (.classEq (syn_c0) (syn_c0)) (.classMem (.cv q) (syn_cpw1 (syn_chwcn A)))
  have p0009 :=
    @g_wecomparisondefaultemptywe
  have p0010 :=
    @g_n_0ss A
  have p0011 :=
    @g_pm3_2i (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe) (syn_c0)) (syn_wss (syn_c0) A) p0009 p0010
  have p0012 :=
    @g_wecomparisondefaultemptywe
  have p0013 :=
    @g_brex (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0) (syn_cwe)
  have p0014 :=
    Nominal.mp p0012 p0013
  have p0015 :=
    @g_simpl (.classMem (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cvv)) (.classMem (syn_c0) (syn_cvv))
  have p0016 :=
    Nominal.mp p0014 p0015
  have p0017 :=
    @g_n_0ex
  have p0018 :=
    @g_elhwcodes A (syn_c0) (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) dv_cache_0001 p0016 p0017
  have p0019 :=
    @g_mpbir (.classMem (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)) (syn_chwcodes A)) (syn_wa (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe) (syn_c0)) (syn_wss (syn_c0) A)) p0011 p0018
  have p0020 :=
    @g_inss2 (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))
  have p0021 :=
    @g_wecomparisondefaultemptywe
  have p0022 :=
    @g_brex (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0) (syn_cwe)
  have p0023 :=
    Nominal.mp p0021 p0022
  have p0024 :=
    @g_simpl (.classMem (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cvv)) (.classMem (syn_c0) (syn_cvv))
  have p0025 :=
    Nominal.mp p0023 p0024
  have p0026 :=
    @g_n_0ex
  have p0027 :=
    @g_opfv1st (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0) p0025 p0026
  have p0028 :=
    @g_wecomparisondefaultemptywe
  have p0029 :=
    @g_brex (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0) (syn_cwe)
  have p0030 :=
    Nominal.mp p0028 p0029
  have p0031 :=
    @g_simpl (.classMem (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cvv)) (.classMem (syn_c0) (syn_cvv))
  have p0032 :=
    Nominal.mp p0030 p0031
  have p0033 :=
    @g_n_0ex
  have p0034 :=
    @g_opfv2nd (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0) p0032 p0033
  have p0035 :=
    @g_wecomparisondefaultemptywe
  have p0036 :=
    @g_brex (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0) (syn_cwe)
  have p0037 :=
    Nominal.mp p0035 p0036
  have p0038 :=
    @g_simpl (.classMem (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cvv)) (.classMem (syn_c0) (syn_cvv))
  have p0039 :=
    Nominal.mp p0037 p0038
  have p0040 :=
    @g_n_0ex
  have p0041 :=
    @g_opfv2nd (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0) p0039 p0040
  have p0042 :=
    @g_xpeq12i (syn_cfv (syn_c2nd) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (syn_c0) (syn_cfv (syn_c2nd) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (syn_c0) p0034 p0041
  have p0043 :=
    @g_sseq12i (syn_cfv (syn_c1st) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_cxp (syn_c0) (syn_c0)) p0027 p0042
  have p0044 :=
    @g_mpbir (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))) (syn_wss (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cxp (syn_c0) (syn_c0))) p0020 p0043
  have p0045 :=
    @g_pm3_2i (.classMem (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)) (syn_chwcodes A)) (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))) p0019 p0044
  have p0046 :=
    @g_wecomparisondefaultemptywe
  have p0047 :=
    @g_brex (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0) (syn_cwe)
  have p0048 :=
    Nominal.mp p0046 p0047
  have p0049 :=
    @g_simpl (.classMem (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cvv)) (.classMem (syn_c0) (syn_cvv))
  have p0050 :=
    Nominal.mp p0048 p0049
  have p0051 :=
    @g_n_0ex
  have p0052 :=
    @g_opex (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0) p0050 p0051
  have p0053 :=
    @g_elhwcncl A (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
  have p0054 :=
    Nominal.mp p0052 p0053
  have p0055 :=
    @g_mpbir (.classMem (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)) (syn_chwcn A)) (syn_wa (.classMem (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)) (syn_chwcodes A)) (syn_wss (syn_cfv (syn_c1st) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (syn_cxp (syn_cfv (syn_c2nd) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (syn_cfv (syn_c2nd) (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))))) p0045 p0054
  have p0056 :=
    @g_snelpw1 (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)) (syn_chwcn A)
  have p0057 :=
    @g_mpbir (.classMem (syn_csn (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (syn_cpw1 (syn_chwcn A))) (.classMem (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)) (syn_chwcn A)) p0055 p0056
  have p0058 :=
    @g_a1i (.classMem (syn_csn (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (syn_cpw1 (syn_chwcn A))) (syn_wa (.classEq (syn_c0) (syn_c0)) (.neg (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))))) p0057
  have p0059 :=
    @g_ifclda (.classEq (syn_c0) (syn_c0)) (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q) (syn_csn (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) (syn_cpw1 (syn_chwcn A)) p0008 p0058
  have p0060 :=
    Nominal.mp p0007 p0059
  have p0061 :=
    @g_hnsicodemapclassimclndv A (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q) (syn_csn (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) hyp_hnsicodemapclassimdndv_1 p0060
  have p0062 :=
    @g_dedth (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.classEq (syn_cima (syn_chnsicodemap A) (syn_cec (.cv q) (syn_csi (syn_chwniso A)))) (syn_cec (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwniso (syn_cpw1 A)))) (.classEq (syn_cima (syn_chnsicodemap A) (syn_cec (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q) (syn_csn (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))) (syn_csi (syn_chwniso A)))) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_cif (.classMem (.cv q) (syn_cpw1 (syn_chwcn A))) (.cv q) (syn_csn (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))) (syn_chwniso (syn_cpw1 A)))) (.cv q) (syn_csn (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))) p0006 p0061
  exact p0062

noncomputable def g_hnsicodemapclassimcldndv
    (A : Class) (Q : Class) (hyp_hnsicodemapclassimcldndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem Q (syn_cpw1 (syn_chwcn A))) (.classEq (syn_cima (syn_chnsicodemap A) (syn_cec Q (syn_csi (syn_chwniso A)))) (syn_cec (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A))))) := by
  let proofSupport : Finset Var := A.fv ∪ Q.fv
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (h))
  have fresh_q_not_Q : q ∉ Q.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have dv_cache_0001 : q ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ (Q).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_Q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((syn_cpw1 (syn_chwcn A))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((Wff.classEq (syn_cima (syn_chnsicodemap A) (syn_cec Q (syn_csi (syn_chwniso A)))) (syn_cec (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, fresh_q_not_Q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eceq1 (.cv q) Q (syn_csi (syn_chwniso A))
  have p0001 :=
    @g_imaeq2d (.classEq (.cv q) Q) (syn_cec (.cv q) (syn_csi (syn_chwniso A))) (syn_cec Q (syn_csi (syn_chwniso A))) (syn_chnsicodemap A) p0000
  have p0002 :=
    @g_id (.classEq (.cv q) Q)
  have p0003 :=
    @g_fveq2d (.classEq (.cv q) Q) (.cv q) Q (syn_chnsicodemap A) p0002
  have p0004 :=
    @g_eceq1 (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A))
  have p0005 :=
    @g_syl (.classEq (.cv q) Q) (.classEq (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_cfv (syn_chnsicodemap A) Q)) (.classEq (syn_cec (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwniso (syn_cpw1 A))) (syn_cec (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A)))) p0003 p0004
  have p0006 :=
    @g_eqeq12d (.classEq (.cv q) Q) (syn_cima (syn_chnsicodemap A) (syn_cec (.cv q) (syn_csi (syn_chwniso A)))) (syn_cima (syn_chnsicodemap A) (syn_cec Q (syn_csi (syn_chwniso A)))) (syn_cec (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwniso (syn_cpw1 A))) (syn_cec (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A))) p0001 p0005
  have p0007 :=
    @g_hnsicodemapclassimdndv A q dv_cache_0001 hyp_hnsicodemapclassimcldndv_1
  have p0008 :=
    @g_vtoclga (.classEq (syn_cima (syn_chnsicodemap A) (syn_cec (.cv q) (syn_csi (syn_chwniso A)))) (syn_cec (syn_cfv (syn_chnsicodemap A) (.cv q)) (syn_chwniso (syn_cpw1 A)))) (.classEq (syn_cima (syn_chnsicodemap A) (syn_cec Q (syn_csi (syn_chwniso A)))) (syn_cec (syn_cfv (syn_chnsicodemap A) Q) (syn_chwniso (syn_cpw1 A)))) q Q (syn_cpw1 (syn_chwcn A)) dv_cache_0002 dv_cache_0003 dv_cache_0004 p0006 p0007
  exact p0008

noncomputable def g_elhnordclndv
    (u : Var) (A : Class) (X : Class) (dv_A_u : u ∉ A.fv) (dv_X_u : u ∉ X.fv) :
    Nominal.NPrf (.imp (.classMem X (syn_cvv)) (syn_wb (.classMem X (syn_chnord A)) (syn_wrex u (syn_chwcn A) (.classEq X (syn_cec (.cv u) (syn_chwniso A)))))) := by
  let proofSupport : Finset Var := ({u} : Finset Var) ∪ A.fv ∪ X.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_u : x ≠ u := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_x : u ≠ x :=
    Ne.symm fresh_x_ne_u
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_X : x ∉ X.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : u ∉ ((Wff.classEq (.cv x) X)).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_x, dv_X_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : u ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0005 : x ∉ (X).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_wb (.classMem X (syn_chnord A)) (syn_wrex u (syn_chwcn A) (.classEq X (syn_cec (.cv u) (syn_chwniso A)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_X, fresh_x_not_A, fresh_x_ne_u, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Wff.classMem X (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_X, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classMem X (syn_cvv))
  have p0001 :=
    @g_simpr (.classMem X (syn_cvv)) (.classEq (.cv x) X)
  have p0002 :=
    @g_eleq1 (.cv x) X (syn_chnord A)
  have p0003 :=
    @g_id (.classEq (.cv x) X)
  have p0004 :=
    @g_eqeq1d (.classEq (.cv x) X) (.cv x) X (syn_cec (.cv u) (syn_chwniso A)) p0003
  have p0005 :=
    @g_rexbidv (.classEq (.cv x) X) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso A))) (.classEq X (syn_cec (.cv u) (syn_chwniso A))) u (syn_chwcn A) dv_cache_0001 p0004
  have p0006 :=
    @g_bibi12d (.classEq (.cv x) X) (.classMem (.cv x) (syn_chnord A)) (.classMem X (syn_chnord A)) (syn_wrex u (syn_chwcn A) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso A)))) (syn_wrex u (syn_chwcn A) (.classEq X (syn_cec (.cv u) (syn_chwniso A)))) p0002 p0005
  have p0007 :=
    @g_syl (syn_wa (.classMem X (syn_cvv)) (.classEq (.cv x) X)) (.classEq (.cv x) X) (syn_wb (syn_wb (.classMem (.cv x) (syn_chnord A)) (syn_wrex u (syn_chwcn A) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wb (.classMem X (syn_chnord A)) (syn_wrex u (syn_chwcn A) (.classEq X (syn_cec (.cv u) (syn_chwniso A)))))) p0001 p0006
  have p0008 :=
    @g_vex x
  have p0009 :=
    @g_elhnord x u A dv_cache_0002 dv_cache_0003 dv_cache_0004 p0008
  have p0010 :=
    @g_a1i (syn_wb (.classMem (.cv x) (syn_chnord A)) (syn_wrex u (syn_chwcn A) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso A))))) (.classMem X (syn_cvv)) p0009
  have p0011 :=
    @g_vtocld (.classMem X (syn_cvv)) (syn_wb (.classMem (.cv x) (syn_chnord A)) (syn_wrex u (syn_chwcn A) (.classEq (.cv x) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wb (.classMem X (syn_chnord A)) (syn_wrex u (syn_chwcn A) (.classEq X (syn_cec (.cv u) (syn_chwniso A))))) x X (syn_cvv) dv_cache_0005 dv_cache_0006 dv_cache_0007 p0000 p0007 p0010
  exact p0011

noncomputable def g_hnsiquomapfvhnordndv
    (A : Class) (q : Var) (dv_A_q : q ∉ A.fv) (hyp_hnsiquomapfvhnordndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_chnord (syn_cpw1 A)))) := by
  let proofSupport : Finset Var := A.fv ∪ ({q} : Finset Var)
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_ne_q : u ≠ q := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_u : q ≠ u :=
    Ne.symm fresh_u_ne_q
  have dv_cache_0001 : u ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : u ∉ ((syn_cuni (.cv q))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : u ∉ ((syn_chwniso A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : u ∉ ((Wff.classMem (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_chnord (syn_cpw1 A)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_q, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : u ∉ ((Wff.classMem (.cv q) (syn_cpw1 (syn_chnord A)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_ne_q, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_pw1argclcl (syn_chnord A) (.cv q)
  have p0001 :=
    @g_simpl (.classMem (syn_cuni (.cv q)) (syn_chnord A)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0002 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_chnord A)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) (.classMem (syn_cuni (.cv q)) (syn_chnord A)) p0000 p0001
  have p0003 :=
    @g_pw1argclcl (syn_chnord A) (.cv q)
  have p0004 :=
    @g_simpl (.classMem (syn_cuni (.cv q)) (syn_chnord A)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))
  have p0005 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (syn_cuni (.cv q)) (syn_chnord A)) (.classEq (.cv q) (syn_csn (syn_cuni (.cv q))))) (.classMem (syn_cuni (.cv q)) (syn_chnord A)) p0003 p0004
  have p0006 :=
    @g_elex (syn_cuni (.cv q)) (syn_chnord A)
  have p0007 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (syn_cuni (.cv q)) (syn_chnord A)) (.classMem (syn_cuni (.cv q)) (syn_cvv)) p0005 p0006
  have p0008 :=
    @g_elhnordclndv u A (syn_cuni (.cv q)) dv_cache_0001 dv_cache_0002
  have p0009 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (syn_cuni (.cv q)) (syn_cvv)) (syn_wb (.classMem (syn_cuni (.cv q)) (syn_chnord A)) (syn_wrex u (syn_chwcn A) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) p0007 p0008
  have p0010 :=
    @g_mpbid (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classMem (syn_cuni (.cv q)) (syn_chnord A)) (syn_wrex u (syn_chwcn A) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))) p0002 p0009
  have p0011 :=
    @g_simpl (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
  have p0012 :=
    @g_hnsiquomapvalndv A q dv_cache_0003 hyp_hnsiquomapfvhnordndv_1
  have p0013 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cima (syn_chnsicodemap A) (syn_cpw1 (syn_cuni (.cv q))))) p0011 p0012
  have p0014 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
  have p0015 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))
  have p0016 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))) p0014 p0015
  have p0017 :=
    @g_pw1eq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))
  have p0018 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))) (.classEq (syn_cpw1 (syn_cuni (.cv q))) (syn_cpw1 (syn_cec (.cv u) (syn_chwniso A)))) p0016 p0017
  have p0019 :=
    @g_siecsnndv u (syn_chwniso A) dv_cache_0004
  have p0020 :=
    @g_eqcomi (syn_cec (syn_csn (.cv u)) (syn_csi (syn_chwniso A))) (syn_cpw1 (syn_cec (.cv u) (syn_chwniso A))) p0019
  have p0021 :=
    @g_a1i (.classEq (syn_cpw1 (syn_cec (.cv u) (syn_chwniso A))) (syn_cec (syn_csn (.cv u)) (syn_csi (syn_chwniso A)))) (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) p0020
  have p0022 :=
    @g_eqtrd (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_cpw1 (syn_cuni (.cv q))) (syn_cpw1 (syn_cec (.cv u) (syn_chwniso A))) (syn_cec (syn_csn (.cv u)) (syn_csi (syn_chwniso A))) p0018 p0021
  have p0023 :=
    @g_imaeq2d (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_cpw1 (syn_cuni (.cv q))) (syn_cec (syn_csn (.cv u)) (syn_csi (syn_chwniso A))) (syn_chnsicodemap A) p0022
  have p0024 :=
    @g_eqtrd (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cima (syn_chnsicodemap A) (syn_cpw1 (syn_cuni (.cv q)))) (syn_cima (syn_chnsicodemap A) (syn_cec (syn_csn (.cv u)) (syn_csi (syn_chwniso A)))) p0013 p0023
  have p0025 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
  have p0026 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))
  have p0027 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))) (.classMem (.cv u) (syn_chwcn A)) p0025 p0026
  have p0028 :=
    @g_snelpw1 (.cv u) (syn_chwcn A)
  have p0029 :=
    @g_sylibr (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A))) p0027 p0028
  have p0030 :=
    @g_hnsicodemapclassimcldndv A (syn_csn (.cv u)) hyp_hnsiquomapfvhnordndv_1
  have p0031 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A))) (.classEq (syn_cima (syn_chnsicodemap A) (syn_cec (syn_csn (.cv u)) (syn_csi (syn_chwniso A)))) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwniso (syn_cpw1 A)))) p0029 p0030
  have p0032 :=
    @g_eqtrd (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cima (syn_chnsicodemap A) (syn_cec (syn_csn (.cv u)) (syn_csi (syn_chwniso A)))) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwniso (syn_cpw1 A))) p0024 p0031
  have p0033 :=
    @g_simpr (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))
  have p0034 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))
  have p0035 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A)))) (.classMem (.cv u) (syn_chwcn A)) p0033 p0034
  have p0036 :=
    @g_snelpw1 (.cv u) (syn_chwcn A)
  have p0037 :=
    @g_sylibr (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (.classMem (.cv u) (syn_chwcn A)) (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A))) p0035 p0036
  have p0038 :=
    @g_hnsicodemapfndv A
  have p0039 :=
    @g_ffvelrni (syn_cpw1 (syn_chwcn A)) (syn_chwcn (syn_cpw1 A)) (syn_csn (.cv u)) (syn_chnsicodemap A) p0038
  have p0040 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn A))) (.classMem (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwcn (syn_cpw1 A))) p0037 p0039
  have p0041 :=
    @g_pw1exg A (syn_cvv)
  have p0042 :=
    Nominal.mp hyp_hnsiquomapfvhnordndv_1 p0041
  have p0043 :=
    @g_hwnisoclasselhnordcl (syn_cpw1 A) (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) p0042
  have p0044 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (.classMem (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwcn (syn_cpw1 A))) (.classMem (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwniso (syn_cpw1 A))) (syn_chnord (syn_cpw1 A))) p0040 p0043
  have p0045 :=
    @g_eqeltrd (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))))) (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn (.cv u))) (syn_chwniso (syn_cpw1 A))) (syn_chnord (syn_cpw1 A)) p0032 p0044
  have p0046 :=
    @g_rexlimddv (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (.classEq (syn_cuni (.cv q)) (syn_cec (.cv u) (syn_chwniso A))) (.classMem (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_chnord (syn_cpw1 A))) u (syn_chwcn A) dv_cache_0005 dv_cache_0006 p0010 p0045
  exact p0046

noncomputable def g_hnsiquomapvalclndv
    (A : Class) (Q : Class) (hyp_hnsiquomapvalclndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem Q (syn_cpw1 (syn_chnord A))) (.classEq (syn_cfv (syn_chnsiquomap A) Q) (syn_cima (syn_chnsicodemap A) (syn_cpw1 (syn_cuni Q))))) := by
  let proofSupport : Finset Var := A.fv ∪ Q.fv
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (h))
  have fresh_q_not_Q : q ∉ Q.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have dv_cache_0001 : q ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ (Q).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_Q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((syn_cpw1 (syn_chnord A))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((Wff.classEq (syn_cfv (syn_chnsiquomap A) Q) (syn_cima (syn_chnsicodemap A) (syn_cpw1 (syn_cuni Q))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_Q, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classEq (.cv q) Q)
  have p0001 :=
    @g_fveq2d (.classEq (.cv q) Q) (.cv q) Q (syn_chnsiquomap A) p0000
  have p0002 :=
    @g_id (.classEq (.cv q) Q)
  have p0003 :=
    @g_unieqd (.classEq (.cv q) Q) (.cv q) Q p0002
  have p0004 :=
    @g_pw1eq (syn_cuni (.cv q)) (syn_cuni Q)
  have p0005 :=
    @g_syl (.classEq (.cv q) Q) (.classEq (syn_cuni (.cv q)) (syn_cuni Q)) (.classEq (syn_cpw1 (syn_cuni (.cv q))) (syn_cpw1 (syn_cuni Q))) p0003 p0004
  have p0006 :=
    @g_imaeq2d (.classEq (.cv q) Q) (syn_cpw1 (syn_cuni (.cv q))) (syn_cpw1 (syn_cuni Q)) (syn_chnsicodemap A) p0005
  have p0007 :=
    @g_eqeq12d (.classEq (.cv q) Q) (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cfv (syn_chnsiquomap A) Q) (syn_cima (syn_chnsicodemap A) (syn_cpw1 (syn_cuni (.cv q)))) (syn_cima (syn_chnsicodemap A) (syn_cpw1 (syn_cuni Q))) p0001 p0006
  have p0008 :=
    @g_hnsiquomapvalndv A q dv_cache_0001 hyp_hnsiquomapvalclndv_1
  have p0009 :=
    @g_vtoclga (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_cima (syn_chnsicodemap A) (syn_cpw1 (syn_cuni (.cv q))))) (.classEq (syn_cfv (syn_chnsiquomap A) Q) (syn_cima (syn_chnsicodemap A) (syn_cpw1 (syn_cuni Q)))) q Q (syn_cpw1 (syn_chnord A)) dv_cache_0002 dv_cache_0003 dv_cache_0004 p0007 p0008
  exact p0009

noncomputable def g_hnsiquomapfndv
    (A : Class) (hyp_hnsiquomapfndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wf (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A))) := by
  let proofSupport : Finset Var := A.fv
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (h)
  have dv_cache_0001 : q ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ ((syn_cpw1 (syn_chnord A))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((syn_chnord (syn_cpw1 A))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((syn_chnsiquomap A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_hnsiquomapfnndv A hyp_hnsiquomapfndv_1
  have p0001 :=
    @g_hnsiquomapfvhnordndv A q dv_cache_0001 hyp_hnsiquomapfndv_1
  have p0002 :=
    @g_rgen (.classMem (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_chnord (syn_cpw1 A))) q (syn_cpw1 (syn_chnord A)) p0001
  have p0003 :=
    @g_pm3_2i (syn_wfn (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A))) (syn_wral q (syn_cpw1 (syn_chnord A)) (.classMem (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_chnord (syn_cpw1 A)))) p0000 p0002
  have p0004 :=
    @g_ffnfv q (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A)) (syn_chnsiquomap A) dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0005 :=
    @g_mpbir (syn_wf (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A))) (syn_wa (syn_wfn (syn_chnsiquomap A) (syn_cpw1 (syn_chnord A))) (syn_wral q (syn_cpw1 (syn_chnord A)) (.classMem (syn_cfv (syn_chnsiquomap A) (.cv q)) (syn_chnord (syn_cpw1 A))))) p0003 p0004
  exact p0005

#print axioms g_hnsiquomapfndv

end NFChoice.DirectNominalPrf.WPPReplay
