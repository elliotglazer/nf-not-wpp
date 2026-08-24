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
import NominalWPPReplayChunk018Compact001Part001

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

noncomputable def g_cfbfixedblockf6pointfrominjnowendv
    (f : Var) (hyp_cfbfixedblockf6pointfrominjnowendv_1 : Nominal.NPrf (.imp (syn_wwpp) (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))))) :
    Nominal.NPrf (.imp (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))) := by
  let proofSupport : Finset Var := ({f} : Finset Var)
  have dv_cache_0001 : Disjoint ((syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))).fv ((syn_chncodecmpset (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))).fv := by
    exact (show Disjoint ((syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))).fv ((syn_chncodecmpset (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset]; exact (show Disjoint (((syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))).fv) (((syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw]; exact (show Disjoint (((syn_chnord (syn_cpw1 (syn_c1c)))).fv) (((syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))).fv) from (by rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord]; exact (show Disjoint (((syn_cpw1 (syn_c1c))).fv) (((syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1]; exact (show Disjoint (((syn_c1c)).fv) (((syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]; exact (show Disjoint ((∅ : Finset Var)) (((syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))).fv) from (by simp))))))))))))
  have p0000 :=
    @g_cfbtargetqbaseexndv
  have p0001 :=
    @g_cfbtargetqbaseexndv
  have p0002 :=
    @g_hncodecmpsetexg (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    @g_cfbtargetqbaseexndv
  have p0005 :=
    @g_hncodecmplnpwcndv (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_cfbtargetqbaseexndv
  have p0008 :=
    @g_hncodecmplnkerndv (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_hnordwefromcmp (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))) (syn_chncodecmpset (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))) dv_cache_0001 p0000 p0003 p0006 p0009
  have p0011 :=
    @g_cfbfixedblockf6pointfrominjndv (syn_clnqord (syn_chncodecmpset (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c)))))) (syn_chwcn (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_c1c))))))) f hyp_cfbfixedblockf6pointfrominjnowendv_1 p0010
  exact p0011

noncomputable def g_cfbfixedblocknotwppfrominjndv
    (f : Var) (hyp_cfbfixedblocknotwppfrominjndv_1 : Nominal.NPrf (.imp (syn_wwpp) (syn_wex f (syn_wf1 (.cv f) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) (syn_chnord (syn_cpw (syn_cpw (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))))) :
    Nominal.NPrf (.neg (syn_wwpp)) := by
  let proofSupport : Finset Var := ({f} : Finset Var)
  have p0000 :=
    @g_cfbfixedblockf6pointfrominjnowendv f hyp_cfbfixedblocknotwppfrominjndv_1
  have p0001 :=
    @g_wppconcrete6notwppfrompointndv p0000
  exact p0001

noncomputable def g_cfbthresholdnn2lencndv
    (X : Class) (hyp_cfbthresholdnn2lencndv_1 : Nominal.NPrf (.classMem X (syn_cvv))) (hyp_cfbthresholdnn2lencndv_2 : Nominal.NPrf (syn_wbr (syn_cnc (syn_cnnc)) (syn_clec) (syn_cnc X))) :
    Nominal.NPrf (syn_wbr (syn_cnc (syn_cnnc)) (syn_clec) (syn_cnc (syn_cpw1 (syn_cpw1 X)))) := by
  let proofSupport : Finset Var := X.fv
  have p0000 :=
    @g_nncex
  have p0001 :=
    @g_ncelncsi (syn_cnnc) p0000
  have p0002 :=
    @g_ncelncsi X hyp_cfbthresholdnn2lencndv_1
  have p0003 :=
    @g_pm3_2i (.classMem (syn_cnc (syn_cnnc)) (syn_cncs)) (.classMem (syn_cnc X) (syn_cncs)) p0001 p0002
  have p0004 :=
    @g_tlecg (syn_cnc (syn_cnnc)) (syn_cnc X)
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_mpbi (syn_wbr (syn_cnc (syn_cnnc)) (syn_clec) (syn_cnc X)) (syn_wbr (syn_ctc (syn_cnc (syn_cnnc))) (syn_clec) (syn_ctc (syn_cnc X))) hyp_cfbthresholdnn2lencndv_2 p0005
  have p0007 :=
    @g_nncex
  have p0008 :=
    @g_ncelncsi (syn_cnnc) p0007
  have p0009 :=
    @g_tccl (syn_cnc (syn_cnnc))
  have p0010 :=
    Nominal.mp p0008 p0009
  have p0011 :=
    @g_ncelncsi X hyp_cfbthresholdnn2lencndv_1
  have p0012 :=
    @g_tccl (syn_cnc X)
  have p0013 :=
    Nominal.mp p0011 p0012
  have p0014 :=
    @g_pm3_2i (.classMem (syn_ctc (syn_cnc (syn_cnnc))) (syn_cncs)) (.classMem (syn_ctc (syn_cnc X)) (syn_cncs)) p0010 p0013
  have p0015 :=
    @g_tlecg (syn_ctc (syn_cnc (syn_cnnc))) (syn_ctc (syn_cnc X))
  have p0016 :=
    Nominal.mp p0014 p0015
  have p0017 :=
    @g_mpbi (syn_wbr (syn_ctc (syn_cnc (syn_cnnc))) (syn_clec) (syn_ctc (syn_cnc X))) (syn_wbr (syn_ctc (syn_ctc (syn_cnc (syn_cnnc)))) (syn_clec) (syn_ctc (syn_ctc (syn_cnc X)))) p0006 p0016
  have p0018 :=
    @g_nncex
  have p0019 :=
    @g_tc2nc (syn_cnnc) p0018
  have p0020 :=
    @g_tcnnf1o
  have p0021 :=
    @g_tcfnex
  have p0022 :=
    @g_nncex
  have p0023 :=
    @g_pw1ex (syn_cnnc) p0022
  have p0024 :=
    @g_resex (syn_ctcfn) (syn_cpw1 (syn_cnnc)) p0021 p0023
  have p0025 :=
    @g_f1oen (syn_cpw1 (syn_cnnc)) (syn_cnnc) (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) p0024
  have p0026 :=
    Nominal.mp p0020 p0025
  have p0027 :=
    @g_enpw1 (syn_cpw1 (syn_cnnc)) (syn_cnnc)
  have p0028 :=
    @g_mpbi (syn_wbr (syn_cpw1 (syn_cnnc)) (syn_cen) (syn_cnnc)) (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_cen) (syn_cpw1 (syn_cnnc))) p0026 p0027
  have p0029 :=
    @g_tcnnf1o
  have p0030 :=
    @g_tcfnex
  have p0031 :=
    @g_nncex
  have p0032 :=
    @g_pw1ex (syn_cnnc) p0031
  have p0033 :=
    @g_resex (syn_ctcfn) (syn_cpw1 (syn_cnnc)) p0030 p0032
  have p0034 :=
    @g_f1oen (syn_cpw1 (syn_cnnc)) (syn_cnnc) (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cnnc))) p0033
  have p0035 :=
    Nominal.mp p0029 p0034
  have p0036 :=
    @g_pm3_2i (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_cen) (syn_cpw1 (syn_cnnc))) (syn_wbr (syn_cpw1 (syn_cnnc)) (syn_cen) (syn_cnnc)) p0028 p0035
  have p0037 :=
    @g_entr (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_cpw1 (syn_cnnc)) (syn_cnnc)
  have p0038 :=
    Nominal.mp p0036 p0037
  have p0039 :=
    @g_nncex
  have p0040 :=
    @g_pw1ex (syn_cnnc) p0039
  have p0041 :=
    @g_pw1ex (syn_cpw1 (syn_cnnc)) p0040
  have p0042 :=
    @g_eqnc (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_cnnc) p0041
  have p0043 :=
    @g_mpbir (.classEq (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cnnc)))) (syn_cnc (syn_cnnc))) (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cnnc))) (syn_cen) (syn_cnnc)) p0038 p0042
  have p0044 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_cnc (syn_cnnc)))) (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cnnc)))) (syn_cnc (syn_cnnc)) p0019 p0043
  have p0045 :=
    @g_tc2nc X hyp_cfbthresholdnn2lencndv_1
  have p0046 :=
    @g_breq12i (syn_ctc (syn_ctc (syn_cnc (syn_cnnc)))) (syn_cnc (syn_cnnc)) (syn_ctc (syn_ctc (syn_cnc X))) (syn_cnc (syn_cpw1 (syn_cpw1 X))) (syn_clec) p0044 p0045
  have p0047 :=
    @g_mpbi (syn_wbr (syn_ctc (syn_ctc (syn_cnc (syn_cnnc)))) (syn_clec) (syn_ctc (syn_ctc (syn_cnc X)))) (syn_wbr (syn_cnc (syn_cnnc)) (syn_clec) (syn_cnc (syn_cpw1 (syn_cpw1 X)))) p0017 p0046
  exact p0047

noncomputable def g_cfbliteralunivhncardboundndv
     :
    Nominal.NPrf (syn_wbr (syn_chncard (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc))) (syn_clec) (syn_chncard (syn_cpw1 (syn_cpw1 (syn_cvv))))) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    @g_vvex
  have p0001 :=
    @g_pw1ex (syn_cvv) p0000
  have p0002 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0001
  have p0003 :=
    @g_ncelncsi (syn_cpw1 (syn_cpw1 (syn_cvv))) p0002
  have p0004 :=
    @g_nncex
  have p0005 :=
    @g_ncelncsi (syn_cnnc) p0004
  have p0006 :=
    @g_vvex
  have p0007 :=
    @g_pw1ex (syn_cvv) p0006
  have p0008 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0007
  have p0009 :=
    @g_ncelncsi (syn_cpw1 (syn_cpw1 (syn_cvv))) p0008
  have p0010 :=
    @g_n_3pm3_2i (.classMem (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cncs)) (.classMem (syn_cnc (syn_cnnc)) (syn_cncs)) (.classMem (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cncs)) p0003 p0005 p0009
  have p0011 :=
    @g_vvex
  have p0012 :=
    @g_ssv (syn_cnnc)
  have p0013 :=
    @g_nncex
  have p0014 :=
    @g_vvex
  have p0015 :=
    @g_nclec (syn_cnnc) (syn_cvv) p0013 p0014
  have p0016 :=
    Nominal.mp p0012 p0015
  have p0017 :=
    @g_cfbthresholdnn2lencndv (syn_cvv) p0011 p0016
  have p0018 :=
    @g_pm3_2i (syn_w3a (.classMem (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cncs)) (.classMem (syn_cnc (syn_cnnc)) (syn_cncs)) (.classMem (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cncs))) (syn_wbr (syn_cnc (syn_cnnc)) (syn_clec) (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0010 p0017
  have p0019 :=
    @g_lemuc2 (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cnc (syn_cnnc)) (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv))))
  have p0020 :=
    Nominal.mp p0018 p0019
  have p0021 :=
    @g_vvex
  have p0022 :=
    @g_wppqkrelliteralnceqndv (syn_cvv) p0021
  have p0023 :=
    @g_xpvv
  have p0024 :=
    @g_pw1eq (syn_cxp (syn_cvv) (syn_cvv)) (syn_cvv)
  have p0025 :=
    Nominal.mp p0023 p0024
  have p0026 :=
    @g_pw1eq (syn_cpw1 (syn_cxp (syn_cvv) (syn_cvv))) (syn_cpw1 (syn_cvv))
  have p0027 :=
    Nominal.mp p0025 p0026
  have p0028 :=
    @g_xpeq1i (syn_cpw1 (syn_cpw1 (syn_cxp (syn_cvv) (syn_cvv)))) (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cnnc) p0027
  have p0029 :=
    @g_nceqi (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cxp (syn_cvv) (syn_cvv)))) (syn_cnnc)) (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cnnc)) p0028
  have p0030 :=
    @g_eqtri (syn_cnc (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc))) (syn_cnc (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cxp (syn_cvv) (syn_cvv)))) (syn_cnnc))) (syn_cnc (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cnnc))) p0022 p0029
  have p0031 :=
    @g_vvex
  have p0032 :=
    @g_pw1ex (syn_cvv) p0031
  have p0033 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0032
  have p0034 :=
    @g_nncex
  have p0035 :=
    @g_mucnc (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cnnc) p0033 p0034
  have p0036 :=
    @g_eqcomi (syn_co (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cmuc) (syn_cnc (syn_cnnc))) (syn_cnc (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cnnc))) p0035
  have p0037 :=
    @g_eqtri (syn_cnc (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc))) (syn_cnc (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cnnc))) (syn_co (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cmuc) (syn_cnc (syn_cnnc))) p0030 p0036
  have p0038 :=
    @g_vvex
  have p0039 :=
    @g_pw1ex (syn_cvv) p0038
  have p0040 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0039
  have p0041 :=
    @g_vvex
  have p0042 :=
    @g_pw1ex (syn_cvv) p0041
  have p0043 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0042
  have p0044 :=
    @g_mucnc (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))) p0040 p0043
  have p0045 :=
    @g_vvex
  have p0046 :=
    @g_vvex
  have p0047 :=
    @g_pw1xpshiftenndv (syn_cvv) (syn_cvv) p0045 p0046
  have p0048 :=
    @g_enpw1 (syn_cpw1 (syn_cxp (syn_cvv) (syn_cvv))) (syn_cxp (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)))
  have p0049 :=
    @g_mpbi (syn_wbr (syn_cpw1 (syn_cxp (syn_cvv) (syn_cvv))) (syn_cen) (syn_cxp (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)))) (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cxp (syn_cvv) (syn_cvv)))) (syn_cen) (syn_cpw1 (syn_cxp (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))))) p0047 p0048
  have p0050 :=
    @g_vvex
  have p0051 :=
    @g_pw1ex (syn_cvv) p0050
  have p0052 :=
    @g_vvex
  have p0053 :=
    @g_pw1ex (syn_cvv) p0052
  have p0054 :=
    @g_pw1xpshiftenndv (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)) p0051 p0053
  have p0055 :=
    @g_pm3_2i (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cxp (syn_cvv) (syn_cvv)))) (syn_cen) (syn_cpw1 (syn_cxp (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv))))) (syn_wbr (syn_cpw1 (syn_cxp (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)))) (syn_cen) (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))))) p0049 p0054
  have p0056 :=
    @g_entr (syn_cpw1 (syn_cpw1 (syn_cxp (syn_cvv) (syn_cvv)))) (syn_cpw1 (syn_cxp (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cvv)))) (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))))
  have p0057 :=
    Nominal.mp p0055 p0056
  have p0058 :=
    @g_ensym (syn_cpw1 (syn_cpw1 (syn_cxp (syn_cvv) (syn_cvv)))) (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))))
  have p0059 :=
    @g_mpbi (syn_wbr (syn_cpw1 (syn_cpw1 (syn_cxp (syn_cvv) (syn_cvv)))) (syn_cen) (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_wbr (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cen) (syn_cpw1 (syn_cpw1 (syn_cxp (syn_cvv) (syn_cvv))))) p0057 p0058
  have p0060 :=
    @g_xpvv
  have p0061 :=
    @g_pw1eq (syn_cxp (syn_cvv) (syn_cvv)) (syn_cvv)
  have p0062 :=
    Nominal.mp p0060 p0061
  have p0063 :=
    @g_pw1eq (syn_cpw1 (syn_cxp (syn_cvv) (syn_cvv))) (syn_cpw1 (syn_cvv))
  have p0064 :=
    Nominal.mp p0062 p0063
  have p0065 :=
    @g_breq2i (syn_cpw1 (syn_cpw1 (syn_cxp (syn_cvv) (syn_cvv)))) (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cen) p0064
  have p0066 :=
    @g_mpbi (syn_wbr (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cen) (syn_cpw1 (syn_cpw1 (syn_cxp (syn_cvv) (syn_cvv))))) (syn_wbr (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cen) (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0059 p0065
  have p0067 :=
    @g_vvex
  have p0068 :=
    @g_pw1ex (syn_cvv) p0067
  have p0069 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0068
  have p0070 :=
    @g_vvex
  have p0071 :=
    @g_pw1ex (syn_cvv) p0070
  have p0072 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0071
  have p0073 :=
    @g_xpex (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))) p0069 p0072
  have p0074 :=
    @g_eqnc (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cpw1 (syn_cpw1 (syn_cvv))) p0073
  have p0075 :=
    @g_mpbir (.classEq (syn_cnc (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_wbr (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cen) (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0066 p0074
  have p0076 :=
    @g_eqtri (syn_co (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cmuc) (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnc (syn_cxp (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0044 p0075
  have p0077 :=
    @g_eqcomi (syn_co (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cmuc) (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))) p0076
  have p0078 :=
    @g_breq12i (syn_cnc (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc))) (syn_co (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cmuc) (syn_cnc (syn_cnnc))) (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_co (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cmuc) (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_clec) p0037 p0077
  have p0079 :=
    @g_mpbir (syn_wbr (syn_cnc (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc))) (syn_clec) (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv))))) (syn_wbr (syn_co (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cmuc) (syn_cnc (syn_cnnc))) (syn_clec) (syn_co (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))) (syn_cmuc) (syn_cnc (syn_cpw1 (syn_cpw1 (syn_cvv)))))) p0020 p0078
  have p0080 :=
    @g_vvex
  have p0081 :=
    @g_vvex
  have p0082 :=
    @g_xpkex (syn_cvv) (syn_cvv) p0080 p0081
  have p0083 :=
    @g_nncex
  have p0084 :=
    @g_xpex (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc) p0082 p0083
  have p0085 :=
    @g_vvex
  have p0086 :=
    @g_pw1ex (syn_cvv) p0085
  have p0087 :=
    @g_pw1ex (syn_cpw1 (syn_cvv)) p0086
  have p0088 :=
    @g_hncardnclecndv (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cxp (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cnnc)) p0084 p0087
  have p0089 :=
    Nominal.mp p0079 p0088
  exact p0089

#print axioms g_cfbliteralunivhncardboundndv

end NFChoice.DirectNominalPrf.WPPReplay
