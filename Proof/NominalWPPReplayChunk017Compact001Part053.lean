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
import NominalWPPReplayChunk017Compact001Part052

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

noncomputable def g_wppconcrete6tchomdmndv
    (x : Var) :
    Nominal.NPrf (.imp (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn))) (.classEq (syn_ctc (syn_cfv (syn_cwppconcrete6fn) (.cv x))) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (.cv x))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_singleton.mpr h)
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have dv_cache_0001 : x ≠ z := by
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0002 : z ∉ ((Wff.classEq (syn_ctc (syn_cfv (syn_cwppconcrete6fn) (.cv x))) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (.cv x))))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppconcrete6fn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_wppconcrete6dmrepdndv x z dv_cache_0001
  have p0001 :=
    @g_id (.classEq (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
  have p0002 :=
    @g_fveq2 (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))) (syn_cwppconcrete6fn)
  have p0003 :=
    @g_syl (.classEq (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) (.classEq (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) (.classEq (syn_cfv (syn_cwppconcrete6fn) (.cv x)) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))) p0001 p0002
  have p0004 :=
    @g_tceq (syn_cfv (syn_cwppconcrete6fn) (.cv x)) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
  have p0005 :=
    @g_syl (.classEq (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) (.classEq (syn_cfv (syn_cwppconcrete6fn) (.cv x)) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))) (.classEq (syn_ctc (syn_cfv (syn_cwppconcrete6fn) (.cv x))) (syn_ctc (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))) p0003 p0004
  have p0006 :=
    @g_vex z
  have p0007 :=
    @g_wppconcrete6canonicaltchomndv (.cv z) p0006
  have p0008 :=
    @g_a1i (.classEq (syn_ctc (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))) (.classEq (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) p0007
  have p0009 :=
    @g_id (.classEq (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
  have p0010 :=
    @g_tceq (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))
  have p0011 :=
    @g_syl (.classEq (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) (.classEq (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) (.classEq (syn_ctc (.cv x)) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))) p0009 p0010
  have p0012 :=
    @g_fveq2 (syn_ctc (.cv x)) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) (syn_cwppconcrete6fn)
  have p0013 :=
    @g_syl (.classEq (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) (.classEq (syn_ctc (.cv x)) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))) (.classEq (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (.cv x))) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))) p0011 p0012
  have p0014 :=
    @g_eqcomd (.classEq (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (.cv x))) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))) p0013
  have p0015 :=
    @g_n_3eqtrd (.classEq (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) (syn_ctc (syn_cfv (syn_cwppconcrete6fn) (.cv x))) (syn_ctc (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (.cv x))) p0005 p0008 p0014
  have p0016 :=
    @g_exlimiv (.classEq (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))) (.classEq (syn_ctc (syn_cfv (syn_cwppconcrete6fn) (.cv x))) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (.cv x)))) z dv_cache_0002 p0015
  have p0017 :=
    @g_syl (.classMem (.cv x) (syn_cdm (syn_cwppconcrete6fn))) (syn_wex z (.classEq (.cv x) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))) (.classEq (syn_ctc (syn_cfv (syn_cwppconcrete6fn) (.cv x))) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (.cv x)))) p0000 p0016
  exact p0017

noncomputable def g_wppstopstepexndv
    (C : Class) (F : Class) (hyp_wppstopstepexndv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) :
    Nominal.NPrf (.classMem (syn_cwppstopstep F C) (syn_cvv)) := by
  let proofSupport : Finset Var := C.fv ∪ F.fv
  have p0000 :=
    (by simpa [syn_cwppstopstep] using (Nominal.classEqRefl (syn_cwppstopstep F C)))
  have p0001 :=
    @g_elex F (syn_cfuns)
  have p0002 :=
    Nominal.mp hyp_wppstopstepexndv_1 p0001
  have p0003 :=
    (by simpa [syn_cwppstopact] using (Nominal.classEqRefl (syn_cwppstopact F C)))
  have p0004 :=
    @g_elex F (syn_cfuns)
  have p0005 :=
    Nominal.mp hyp_wppstopstepexndv_1 p0004
  have p0006 :=
    @g_dmex F p0005
  have p0007 :=
    @g_vvex
  have p0008 :=
    @g_hwcardsexg (syn_cvv)
  have p0009 :=
    Nominal.mp p0007 p0008
  have p0010 :=
    @g_lecex
  have p0011 :=
    @g_cnvex (syn_clec) p0010
  have p0012 :=
    @g_snex C
  have p0013 :=
    @g_imaex (syn_ccnv (syn_clec)) (syn_csn C) p0011 p0012
  have p0014 :=
    @g_inex (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)) p0009 p0013
  have p0015 :=
    @g_inex (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))) p0006 p0014
  have p0016 :=
    @g_eqeltri (syn_cwppstopact F C) (syn_cin (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))) (syn_cvv) p0003 p0015
  have p0017 :=
    @g_resex F (syn_cwppstopact F C) p0002 p0016
  have p0018 :=
    @g_idex
  have p0019 :=
    @g_vvex
  have p0020 :=
    @g_hwcardsexg (syn_cvv)
  have p0021 :=
    Nominal.mp p0019 p0020
  have p0022 :=
    (by simpa [syn_cwppstopact] using (Nominal.classEqRefl (syn_cwppstopact F C)))
  have p0023 :=
    @g_elex F (syn_cfuns)
  have p0024 :=
    Nominal.mp hyp_wppstopstepexndv_1 p0023
  have p0025 :=
    @g_dmex F p0024
  have p0026 :=
    @g_vvex
  have p0027 :=
    @g_hwcardsexg (syn_cvv)
  have p0028 :=
    Nominal.mp p0026 p0027
  have p0029 :=
    @g_lecex
  have p0030 :=
    @g_cnvex (syn_clec) p0029
  have p0031 :=
    @g_snex C
  have p0032 :=
    @g_imaex (syn_ccnv (syn_clec)) (syn_csn C) p0030 p0031
  have p0033 :=
    @g_inex (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)) p0028 p0032
  have p0034 :=
    @g_inex (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))) p0025 p0033
  have p0035 :=
    @g_eqeltri (syn_cwppstopact F C) (syn_cin (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))) (syn_cvv) p0022 p0034
  have p0036 :=
    @g_difex (syn_chwcards (syn_cvv)) (syn_cwppstopact F C) p0021 p0035
  have p0037 :=
    @g_resex (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) p0018 p0036
  have p0038 :=
    @g_unex (syn_cres F (syn_cwppstopact F C)) (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) p0017 p0037
  have p0039 :=
    @g_eqeltri (syn_cwppstopstep F C) (syn_cun (syn_cres F (syn_cwppstopact F C)) (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))) (syn_cvv) p0000 p0038
  exact p0039

noncomputable def g_wppstopstepmapndv
    (C : Class) (F : Class) (hyp_wppstopstepmapndv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppstopstepmapndv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf (syn_wf (syn_cwppstopstep F C) (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))) := by
  let proofSupport : Finset Var := C.fv ∪ F.fv
  have p0000 :=
    @g_elfunsi F
  have p0001 :=
    Nominal.mp hyp_wppstopstepmapndv_1 p0000
  have p0002 :=
    @g_funfn F
  have p0003 :=
    @g_mpbi (syn_wfun F) (syn_wfn F (syn_cdm F)) p0001 p0002
  have p0004 :=
    @g_dffn3 (syn_cdm F) F
  have p0005 :=
    @g_mpbi (syn_wfn F (syn_cdm F)) (syn_wf F (syn_cdm F) (syn_crn F)) p0003 p0004
  have p0006 :=
    @g_pm3_2i (syn_wf F (syn_cdm F) (syn_crn F)) (syn_wss (syn_crn F) (syn_chwcards (syn_cvv))) p0005 hyp_wppstopstepmapndv_2
  have p0007 :=
    @g_fss (syn_cdm F) (syn_crn F) (syn_chwcards (syn_cvv)) F
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_inss1 (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
  have p0010 :=
    (by simpa [syn_cwppstopact] using (Nominal.classEqRefl (syn_cwppstopact F C)))
  have p0011 :=
    @g_sseq1i (syn_cwppstopact F C) (syn_cin (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))) (syn_cdm F) p0010
  have p0012 :=
    @g_mpbir (syn_wss (syn_cwppstopact F C) (syn_cdm F)) (syn_wss (syn_cin (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))) (syn_cdm F)) p0009 p0011
  have p0013 :=
    @g_pm3_2i (syn_wf F (syn_cdm F) (syn_chwcards (syn_cvv))) (syn_wss (syn_cwppstopact F C) (syn_cdm F)) p0008 p0012
  have p0014 :=
    @g_fssres (syn_cdm F) (syn_chwcards (syn_cvv)) (syn_cwppstopact F C) F
  have p0015 :=
    Nominal.mp p0013 p0014
  have p0016 :=
    @g_f1oi (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))
  have p0017 :=
    @g_f1of (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
  have p0018 :=
    Nominal.mp p0016 p0017
  have p0019 :=
    @g_difss (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)
  have p0020 :=
    @g_pm3_2i (syn_wf (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_wss (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_chwcards (syn_cvv))) p0018 p0019
  have p0021 :=
    @g_fss (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_chwcards (syn_cvv)) (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
  have p0022 :=
    Nominal.mp p0020 p0021
  have p0023 :=
    @g_pm3_2i (syn_wf (syn_cres F (syn_cwppstopact F C)) (syn_cwppstopact F C) (syn_chwcards (syn_cvv))) (syn_wf (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_chwcards (syn_cvv))) p0015 p0022
  have p0024 :=
    @g_disjdif (syn_cwppstopact F C) (syn_chwcards (syn_cvv))
  have p0025 :=
    @g_pm3_2i (syn_wa (syn_wf (syn_cres F (syn_cwppstopact F C)) (syn_cwppstopact F C) (syn_chwcards (syn_cvv))) (syn_wf (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_chwcards (syn_cvv)))) (.classEq (syn_cin (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_c0)) p0023 p0024
  have p0026 :=
    @g_fun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)) (syn_cres F (syn_cwppstopact F C)) (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
  have p0027 :=
    Nominal.mp p0025 p0026
  have p0028 :=
    (by simpa [syn_cwppstopstep] using (Nominal.classEqRefl (syn_cwppstopstep F C)))
  have p0029 :=
    @g_feq1i (syn_cun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))) (syn_cwppstopstep F C) (syn_cun (syn_cres F (syn_cwppstopact F C)) (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))) p0028
  have p0030 :=
    @g_mpbir (syn_wf (syn_cwppstopstep F C) (syn_cun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)))) (syn_wf (syn_cun (syn_cres F (syn_cwppstopact F C)) (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))) (syn_cun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)))) p0027 p0029
  have p0031 :=
    @g_inss2 (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
  have p0032 :=
    @g_inss1 (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))
  have p0033 :=
    @g_sstri (syn_cin (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))) (syn_chwcards (syn_cvv)) p0031 p0032
  have p0034 :=
    (by simpa [syn_cwppstopact] using (Nominal.classEqRefl (syn_cwppstopact F C)))
  have p0035 :=
    @g_sseq1i (syn_cwppstopact F C) (syn_cin (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))) (syn_chwcards (syn_cvv)) p0034
  have p0036 :=
    @g_mpbir (syn_wss (syn_cwppstopact F C) (syn_chwcards (syn_cvv))) (syn_wss (syn_cin (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))) (syn_chwcards (syn_cvv))) p0033 p0035
  have p0037 :=
    @g_undif (syn_cwppstopact F C) (syn_chwcards (syn_cvv))
  have p0038 :=
    @g_mpbi (syn_wss (syn_cwppstopact F C) (syn_chwcards (syn_cvv))) (.classEq (syn_cun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_chwcards (syn_cvv))) p0036 p0037
  have p0039 :=
    @g_feq2i (syn_cun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_chwcards (syn_cvv)) (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))) (syn_cwppstopstep F C) p0038
  have p0040 :=
    @g_mpbi (syn_wf (syn_cwppstopstep F C) (syn_cun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)))) (syn_wf (syn_cwppstopstep F C) (syn_chwcards (syn_cvv)) (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)))) p0030 p0039
  have p0041 :=
    @g_unidm (syn_chwcards (syn_cvv))
  have p0042 :=
    @g_feq3 (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))) (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)) (syn_cwppstopstep F C)
  have p0043 :=
    Nominal.mp p0041 p0042
  have p0044 :=
    @g_mpbi (syn_wf (syn_cwppstopstep F C) (syn_chwcards (syn_cvv)) (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)))) (syn_wf (syn_cwppstopstep F C) (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))) p0040 p0043
  exact p0044

noncomputable def g_wppstopstepfunsndv
    (C : Class) (F : Class) (hyp_wppstopstepfunsndv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppstopstepfunsndv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf (.classMem (syn_cwppstopstep F C) (syn_cfuns)) := by
  let proofSupport : Finset Var := C.fv ∪ F.fv
  have p0000 :=
    @g_elfunsi F
  have p0001 :=
    Nominal.mp hyp_wppstopstepfunsndv_1 p0000
  have p0002 :=
    @g_funfn F
  have p0003 :=
    @g_mpbi (syn_wfun F) (syn_wfn F (syn_cdm F)) p0001 p0002
  have p0004 :=
    @g_dffn3 (syn_cdm F) F
  have p0005 :=
    @g_mpbi (syn_wfn F (syn_cdm F)) (syn_wf F (syn_cdm F) (syn_crn F)) p0003 p0004
  have p0006 :=
    @g_pm3_2i (syn_wf F (syn_cdm F) (syn_crn F)) (syn_wss (syn_crn F) (syn_chwcards (syn_cvv))) p0005 hyp_wppstopstepfunsndv_2
  have p0007 :=
    @g_fss (syn_cdm F) (syn_crn F) (syn_chwcards (syn_cvv)) F
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_inss1 (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
  have p0010 :=
    (by simpa [syn_cwppstopact] using (Nominal.classEqRefl (syn_cwppstopact F C)))
  have p0011 :=
    @g_sseq1i (syn_cwppstopact F C) (syn_cin (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))) (syn_cdm F) p0010
  have p0012 :=
    @g_mpbir (syn_wss (syn_cwppstopact F C) (syn_cdm F)) (syn_wss (syn_cin (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))) (syn_cdm F)) p0009 p0011
  have p0013 :=
    @g_pm3_2i (syn_wf F (syn_cdm F) (syn_chwcards (syn_cvv))) (syn_wss (syn_cwppstopact F C) (syn_cdm F)) p0008 p0012
  have p0014 :=
    @g_fssres (syn_cdm F) (syn_chwcards (syn_cvv)) (syn_cwppstopact F C) F
  have p0015 :=
    Nominal.mp p0013 p0014
  have p0016 :=
    @g_f1oi (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))
  have p0017 :=
    @g_f1of (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
  have p0018 :=
    Nominal.mp p0016 p0017
  have p0019 :=
    @g_difss (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)
  have p0020 :=
    @g_pm3_2i (syn_wf (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_wss (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_chwcards (syn_cvv))) p0018 p0019
  have p0021 :=
    @g_fss (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_chwcards (syn_cvv)) (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
  have p0022 :=
    Nominal.mp p0020 p0021
  have p0023 :=
    @g_pm3_2i (syn_wf (syn_cres F (syn_cwppstopact F C)) (syn_cwppstopact F C) (syn_chwcards (syn_cvv))) (syn_wf (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_chwcards (syn_cvv))) p0015 p0022
  have p0024 :=
    @g_disjdif (syn_cwppstopact F C) (syn_chwcards (syn_cvv))
  have p0025 :=
    @g_pm3_2i (syn_wa (syn_wf (syn_cres F (syn_cwppstopact F C)) (syn_cwppstopact F C) (syn_chwcards (syn_cvv))) (syn_wf (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_chwcards (syn_cvv)))) (.classEq (syn_cin (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_c0)) p0023 p0024
  have p0026 :=
    @g_fun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)) (syn_cres F (syn_cwppstopact F C)) (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
  have p0027 :=
    Nominal.mp p0025 p0026
  have p0028 :=
    (by simpa [syn_cwppstopstep] using (Nominal.classEqRefl (syn_cwppstopstep F C)))
  have p0029 :=
    @g_feq1i (syn_cun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))) (syn_cwppstopstep F C) (syn_cun (syn_cres F (syn_cwppstopact F C)) (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))) p0028
  have p0030 :=
    @g_mpbir (syn_wf (syn_cwppstopstep F C) (syn_cun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)))) (syn_wf (syn_cun (syn_cres F (syn_cwppstopact F C)) (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))) (syn_cun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)))) p0027 p0029
  have p0031 :=
    @g_inss2 (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
  have p0032 :=
    @g_inss1 (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))
  have p0033 :=
    @g_sstri (syn_cin (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))) (syn_chwcards (syn_cvv)) p0031 p0032
  have p0034 :=
    (by simpa [syn_cwppstopact] using (Nominal.classEqRefl (syn_cwppstopact F C)))
  have p0035 :=
    @g_sseq1i (syn_cwppstopact F C) (syn_cin (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))) (syn_chwcards (syn_cvv)) p0034
  have p0036 :=
    @g_mpbir (syn_wss (syn_cwppstopact F C) (syn_chwcards (syn_cvv))) (syn_wss (syn_cin (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))) (syn_chwcards (syn_cvv))) p0033 p0035
  have p0037 :=
    @g_undif (syn_cwppstopact F C) (syn_chwcards (syn_cvv))
  have p0038 :=
    @g_mpbi (syn_wss (syn_cwppstopact F C) (syn_chwcards (syn_cvv))) (.classEq (syn_cun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_chwcards (syn_cvv))) p0036 p0037
  have p0039 :=
    @g_feq2i (syn_cun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_chwcards (syn_cvv)) (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))) (syn_cwppstopstep F C) p0038
  have p0040 :=
    @g_mpbi (syn_wf (syn_cwppstopstep F C) (syn_cun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)))) (syn_wf (syn_cwppstopstep F C) (syn_chwcards (syn_cvv)) (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)))) p0030 p0039
  have p0041 :=
    @g_unidm (syn_chwcards (syn_cvv))
  have p0042 :=
    @g_feq3 (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))) (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)) (syn_cwppstopstep F C)
  have p0043 :=
    Nominal.mp p0041 p0042
  have p0044 :=
    @g_mpbi (syn_wf (syn_cwppstopstep F C) (syn_chwcards (syn_cvv)) (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)))) (syn_wf (syn_cwppstopstep F C) (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))) p0040 p0043
  have p0045 :=
    @g_ffun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)) (syn_cwppstopstep F C)
  have p0046 :=
    Nominal.mp p0044 p0045
  have p0047 :=
    @g_wppstopstepexndv C F hyp_wppstopstepfunsndv_1
  have p0048 :=
    @g_elfuns (syn_cwppstopstep F C) p0047
  have p0049 :=
    @g_mpbir (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (syn_wfun (syn_cwppstopstep F C)) p0046 p0048
  exact p0049

noncomputable def g_wppstopstepdmndv
    (C : Class) (F : Class) (hyp_wppstopstepdmndv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppstopstepdmndv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf (.classEq (syn_cdm (syn_cwppstopstep F C)) (syn_chwcards (syn_cvv))) := by
  let proofSupport : Finset Var := C.fv ∪ F.fv
  have p0000 :=
    @g_elfunsi F
  have p0001 :=
    Nominal.mp hyp_wppstopstepdmndv_1 p0000
  have p0002 :=
    @g_funfn F
  have p0003 :=
    @g_mpbi (syn_wfun F) (syn_wfn F (syn_cdm F)) p0001 p0002
  have p0004 :=
    @g_dffn3 (syn_cdm F) F
  have p0005 :=
    @g_mpbi (syn_wfn F (syn_cdm F)) (syn_wf F (syn_cdm F) (syn_crn F)) p0003 p0004
  have p0006 :=
    @g_pm3_2i (syn_wf F (syn_cdm F) (syn_crn F)) (syn_wss (syn_crn F) (syn_chwcards (syn_cvv))) p0005 hyp_wppstopstepdmndv_2
  have p0007 :=
    @g_fss (syn_cdm F) (syn_crn F) (syn_chwcards (syn_cvv)) F
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_inss1 (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
  have p0010 :=
    (by simpa [syn_cwppstopact] using (Nominal.classEqRefl (syn_cwppstopact F C)))
  have p0011 :=
    @g_sseq1i (syn_cwppstopact F C) (syn_cin (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))) (syn_cdm F) p0010
  have p0012 :=
    @g_mpbir (syn_wss (syn_cwppstopact F C) (syn_cdm F)) (syn_wss (syn_cin (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))) (syn_cdm F)) p0009 p0011
  have p0013 :=
    @g_pm3_2i (syn_wf F (syn_cdm F) (syn_chwcards (syn_cvv))) (syn_wss (syn_cwppstopact F C) (syn_cdm F)) p0008 p0012
  have p0014 :=
    @g_fssres (syn_cdm F) (syn_chwcards (syn_cvv)) (syn_cwppstopact F C) F
  have p0015 :=
    Nominal.mp p0013 p0014
  have p0016 :=
    @g_f1oi (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))
  have p0017 :=
    @g_f1of (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
  have p0018 :=
    Nominal.mp p0016 p0017
  have p0019 :=
    @g_difss (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)
  have p0020 :=
    @g_pm3_2i (syn_wf (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_wss (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_chwcards (syn_cvv))) p0018 p0019
  have p0021 :=
    @g_fss (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_chwcards (syn_cvv)) (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
  have p0022 :=
    Nominal.mp p0020 p0021
  have p0023 :=
    @g_pm3_2i (syn_wf (syn_cres F (syn_cwppstopact F C)) (syn_cwppstopact F C) (syn_chwcards (syn_cvv))) (syn_wf (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_chwcards (syn_cvv))) p0015 p0022
  have p0024 :=
    @g_disjdif (syn_cwppstopact F C) (syn_chwcards (syn_cvv))
  have p0025 :=
    @g_pm3_2i (syn_wa (syn_wf (syn_cres F (syn_cwppstopact F C)) (syn_cwppstopact F C) (syn_chwcards (syn_cvv))) (syn_wf (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_chwcards (syn_cvv)))) (.classEq (syn_cin (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_c0)) p0023 p0024
  have p0026 :=
    @g_fun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)) (syn_cres F (syn_cwppstopact F C)) (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
  have p0027 :=
    Nominal.mp p0025 p0026
  have p0028 :=
    (by simpa [syn_cwppstopstep] using (Nominal.classEqRefl (syn_cwppstopstep F C)))
  have p0029 :=
    @g_feq1i (syn_cun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))) (syn_cwppstopstep F C) (syn_cun (syn_cres F (syn_cwppstopact F C)) (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))) p0028
  have p0030 :=
    @g_mpbir (syn_wf (syn_cwppstopstep F C) (syn_cun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)))) (syn_wf (syn_cun (syn_cres F (syn_cwppstopact F C)) (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))) (syn_cun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)))) p0027 p0029
  have p0031 :=
    @g_inss2 (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
  have p0032 :=
    @g_inss1 (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))
  have p0033 :=
    @g_sstri (syn_cin (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))) (syn_chwcards (syn_cvv)) p0031 p0032
  have p0034 :=
    (by simpa [syn_cwppstopact] using (Nominal.classEqRefl (syn_cwppstopact F C)))
  have p0035 :=
    @g_sseq1i (syn_cwppstopact F C) (syn_cin (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))) (syn_chwcards (syn_cvv)) p0034
  have p0036 :=
    @g_mpbir (syn_wss (syn_cwppstopact F C) (syn_chwcards (syn_cvv))) (syn_wss (syn_cin (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))) (syn_chwcards (syn_cvv))) p0033 p0035
  have p0037 :=
    @g_undif (syn_cwppstopact F C) (syn_chwcards (syn_cvv))
  have p0038 :=
    @g_mpbi (syn_wss (syn_cwppstopact F C) (syn_chwcards (syn_cvv))) (.classEq (syn_cun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_chwcards (syn_cvv))) p0036 p0037
  have p0039 :=
    @g_feq2i (syn_cun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_chwcards (syn_cvv)) (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))) (syn_cwppstopstep F C) p0038
  have p0040 :=
    @g_mpbi (syn_wf (syn_cwppstopstep F C) (syn_cun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)))) (syn_wf (syn_cwppstopstep F C) (syn_chwcards (syn_cvv)) (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)))) p0030 p0039
  have p0041 :=
    @g_unidm (syn_chwcards (syn_cvv))
  have p0042 :=
    @g_feq3 (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))) (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)) (syn_cwppstopstep F C)
  have p0043 :=
    Nominal.mp p0041 p0042
  have p0044 :=
    @g_mpbi (syn_wf (syn_cwppstopstep F C) (syn_chwcards (syn_cvv)) (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)))) (syn_wf (syn_cwppstopstep F C) (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))) p0040 p0043
  have p0045 :=
    @g_fdm (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)) (syn_cwppstopstep F C)
  have p0046 :=
    Nominal.mp p0044 p0045
  exact p0046

noncomputable def g_wppstopsteprndmndv
    (C : Class) (F : Class) (hyp_wppstopstepdmndv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppstopstepdmndv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))) := by
  let proofSupport : Finset Var := C.fv ∪ F.fv
  have p0000 :=
    @g_elfunsi F
  have p0001 :=
    Nominal.mp hyp_wppstopstepdmndv_1 p0000
  have p0002 :=
    @g_funfn F
  have p0003 :=
    @g_mpbi (syn_wfun F) (syn_wfn F (syn_cdm F)) p0001 p0002
  have p0004 :=
    @g_dffn3 (syn_cdm F) F
  have p0005 :=
    @g_mpbi (syn_wfn F (syn_cdm F)) (syn_wf F (syn_cdm F) (syn_crn F)) p0003 p0004
  have p0006 :=
    @g_pm3_2i (syn_wf F (syn_cdm F) (syn_crn F)) (syn_wss (syn_crn F) (syn_chwcards (syn_cvv))) p0005 hyp_wppstopstepdmndv_2
  have p0007 :=
    @g_fss (syn_cdm F) (syn_crn F) (syn_chwcards (syn_cvv)) F
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_inss1 (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
  have p0010 :=
    (by simpa [syn_cwppstopact] using (Nominal.classEqRefl (syn_cwppstopact F C)))
  have p0011 :=
    @g_sseq1i (syn_cwppstopact F C) (syn_cin (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))) (syn_cdm F) p0010
  have p0012 :=
    @g_mpbir (syn_wss (syn_cwppstopact F C) (syn_cdm F)) (syn_wss (syn_cin (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))) (syn_cdm F)) p0009 p0011
  have p0013 :=
    @g_pm3_2i (syn_wf F (syn_cdm F) (syn_chwcards (syn_cvv))) (syn_wss (syn_cwppstopact F C) (syn_cdm F)) p0008 p0012
  have p0014 :=
    @g_fssres (syn_cdm F) (syn_chwcards (syn_cvv)) (syn_cwppstopact F C) F
  have p0015 :=
    Nominal.mp p0013 p0014
  have p0016 :=
    @g_f1oi (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))
  have p0017 :=
    @g_f1of (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
  have p0018 :=
    Nominal.mp p0016 p0017
  have p0019 :=
    @g_difss (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)
  have p0020 :=
    @g_pm3_2i (syn_wf (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_wss (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_chwcards (syn_cvv))) p0018 p0019
  have p0021 :=
    @g_fss (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_chwcards (syn_cvv)) (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
  have p0022 :=
    Nominal.mp p0020 p0021
  have p0023 :=
    @g_pm3_2i (syn_wf (syn_cres F (syn_cwppstopact F C)) (syn_cwppstopact F C) (syn_chwcards (syn_cvv))) (syn_wf (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_chwcards (syn_cvv))) p0015 p0022
  have p0024 :=
    @g_disjdif (syn_cwppstopact F C) (syn_chwcards (syn_cvv))
  have p0025 :=
    @g_pm3_2i (syn_wa (syn_wf (syn_cres F (syn_cwppstopact F C)) (syn_cwppstopact F C) (syn_chwcards (syn_cvv))) (syn_wf (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_chwcards (syn_cvv)))) (.classEq (syn_cin (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_c0)) p0023 p0024
  have p0026 :=
    @g_fun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)) (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)) (syn_cres F (syn_cwppstopact F C)) (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
  have p0027 :=
    Nominal.mp p0025 p0026
  have p0028 :=
    (by simpa [syn_cwppstopstep] using (Nominal.classEqRefl (syn_cwppstopstep F C)))
  have p0029 :=
    @g_feq1i (syn_cun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))) (syn_cwppstopstep F C) (syn_cun (syn_cres F (syn_cwppstopact F C)) (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))) p0028
  have p0030 :=
    @g_mpbir (syn_wf (syn_cwppstopstep F C) (syn_cun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)))) (syn_wf (syn_cun (syn_cres F (syn_cwppstopact F C)) (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))) (syn_cun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)))) p0027 p0029
  have p0031 :=
    @g_inss2 (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
  have p0032 :=
    @g_inss1 (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))
  have p0033 :=
    @g_sstri (syn_cin (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))) (syn_chwcards (syn_cvv)) p0031 p0032
  have p0034 :=
    (by simpa [syn_cwppstopact] using (Nominal.classEqRefl (syn_cwppstopact F C)))
  have p0035 :=
    @g_sseq1i (syn_cwppstopact F C) (syn_cin (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))) (syn_chwcards (syn_cvv)) p0034
  have p0036 :=
    @g_mpbir (syn_wss (syn_cwppstopact F C) (syn_chwcards (syn_cvv))) (syn_wss (syn_cin (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))) (syn_chwcards (syn_cvv))) p0033 p0035
  have p0037 :=
    @g_undif (syn_cwppstopact F C) (syn_chwcards (syn_cvv))
  have p0038 :=
    @g_mpbi (syn_wss (syn_cwppstopact F C) (syn_chwcards (syn_cvv))) (.classEq (syn_cun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_chwcards (syn_cvv))) p0036 p0037
  have p0039 :=
    @g_feq2i (syn_cun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_chwcards (syn_cvv)) (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))) (syn_cwppstopstep F C) p0038
  have p0040 :=
    @g_mpbi (syn_wf (syn_cwppstopstep F C) (syn_cun (syn_cwppstopact F C) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)))) (syn_wf (syn_cwppstopstep F C) (syn_chwcards (syn_cvv)) (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)))) p0030 p0039
  have p0041 :=
    @g_unidm (syn_chwcards (syn_cvv))
  have p0042 :=
    @g_feq3 (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))) (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)) (syn_cwppstopstep F C)
  have p0043 :=
    Nominal.mp p0041 p0042
  have p0044 :=
    @g_mpbi (syn_wf (syn_cwppstopstep F C) (syn_chwcards (syn_cvv)) (syn_cun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)))) (syn_wf (syn_cwppstopstep F C) (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv))) p0040 p0043
  have p0045 :=
    @g_frn (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)) (syn_cwppstopstep F C)
  have p0046 :=
    Nominal.mp p0044 p0045
  have p0047 :=
    @g_wppstopstepdmndv C F hyp_wppstopstepdmndv_1 hyp_wppstopstepdmndv_2
  have p0048 :=
    @g_eqcomi (syn_cdm (syn_cwppstopstep F C)) (syn_chwcards (syn_cvv)) p0047
  have p0049 :=
    @g_sseq2i (syn_chwcards (syn_cvv)) (syn_cdm (syn_cwppstopstep F C)) (syn_crn (syn_cwppstopstep F C)) p0048
  have p0050 :=
    @g_mpbi (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_chwcards (syn_cvv))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))) p0046 p0049
  exact p0050

noncomputable def g_wppstopstepfvactclndv
    (A : Class) (C : Class) (F : Class) (hyp_wppstopstepfvactclndv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppstopstepfvactclndv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf (.imp (.classMem A (syn_cwppstopact F C)) (.classEq (syn_cfv (syn_cwppstopstep F C) A) (syn_cfv F A))) := by
  let proofSupport : Finset Var := A.fv ∪ C.fv ∪ F.fv
  have p0000 :=
    @g_inss1 (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
  have p0001 :=
    (by simpa [syn_cwppstopact] using (Nominal.classEqRefl (syn_cwppstopact F C)))
  have p0002 :=
    @g_sseq1i (syn_cwppstopact F C) (syn_cin (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))) (syn_cdm F) p0001
  have p0003 :=
    @g_mpbir (syn_wss (syn_cwppstopact F C) (syn_cdm F)) (syn_wss (syn_cin (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))) (syn_cdm F)) p0000 p0002
  have p0004 :=
    @g_sseli (syn_cwppstopact F C) (syn_cdm F) A p0003
  have p0005 :=
    @g_elfunsi F
  have p0006 :=
    Nominal.mp hyp_wppstopstepfvactclndv_1 p0005
  have p0007 :=
    @g_funfvbrb A F
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_biimpi (.classMem A (syn_cdm F)) (syn_wbr A F (syn_cfv F A)) p0008
  have p0010 :=
    @g_syl (.classMem A (syn_cwppstopact F C)) (.classMem A (syn_cdm F)) (syn_wbr A F (syn_cfv F A)) p0004 p0009
  have p0011 :=
    @g_id (.classMem A (syn_cwppstopact F C))
  have p0012 :=
    @g_jca (.classMem A (syn_cwppstopact F C)) (syn_wbr A F (syn_cfv F A)) (.classMem A (syn_cwppstopact F C)) p0010 p0011
  have p0013 :=
    @g_brres A (syn_cfv F A) F (syn_cwppstopact F C)
  have p0014 :=
    @g_biimpri (syn_wbr A (syn_cres F (syn_cwppstopact F C)) (syn_cfv F A)) (syn_wa (syn_wbr A F (syn_cfv F A)) (.classMem A (syn_cwppstopact F C))) p0013
  have p0015 :=
    @g_syl (.classMem A (syn_cwppstopact F C)) (syn_wa (syn_wbr A F (syn_cfv F A)) (.classMem A (syn_cwppstopact F C))) (syn_wbr A (syn_cres F (syn_cwppstopact F C)) (syn_cfv F A)) p0012 p0014
  have p0016 :=
    @g_orc (syn_wbr A (syn_cres F (syn_cwppstopact F C)) (syn_cfv F A)) (syn_wbr A (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_cfv F A))
  have p0017 :=
    @g_syl (.classMem A (syn_cwppstopact F C)) (syn_wbr A (syn_cres F (syn_cwppstopact F C)) (syn_cfv F A)) (syn_wo (syn_wbr A (syn_cres F (syn_cwppstopact F C)) (syn_cfv F A)) (syn_wbr A (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_cfv F A))) p0015 p0016
  have p0018 :=
    @g_brun A (syn_cfv F A) (syn_cres F (syn_cwppstopact F C)) (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
  have p0019 :=
    @g_biimpri (syn_wbr A (syn_cun (syn_cres F (syn_cwppstopact F C)) (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))) (syn_cfv F A)) (syn_wo (syn_wbr A (syn_cres F (syn_cwppstopact F C)) (syn_cfv F A)) (syn_wbr A (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_cfv F A))) p0018
  have p0020 :=
    @g_syl (.classMem A (syn_cwppstopact F C)) (syn_wo (syn_wbr A (syn_cres F (syn_cwppstopact F C)) (syn_cfv F A)) (syn_wbr A (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_cfv F A))) (syn_wbr A (syn_cun (syn_cres F (syn_cwppstopact F C)) (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))) (syn_cfv F A)) p0017 p0019
  have p0021 :=
    (by simpa [syn_cwppstopstep] using (Nominal.classEqRefl (syn_cwppstopstep F C)))
  have p0022 :=
    @g_breqi A (syn_cfv F A) (syn_cwppstopstep F C) (syn_cun (syn_cres F (syn_cwppstopact F C)) (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))) p0021
  have p0023 :=
    @g_biimpri (syn_wbr A (syn_cwppstopstep F C) (syn_cfv F A)) (syn_wbr A (syn_cun (syn_cres F (syn_cwppstopact F C)) (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))) (syn_cfv F A)) p0022
  have p0024 :=
    @g_syl (.classMem A (syn_cwppstopact F C)) (syn_wbr A (syn_cun (syn_cres F (syn_cwppstopact F C)) (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))) (syn_cfv F A)) (syn_wbr A (syn_cwppstopstep F C) (syn_cfv F A)) p0020 p0023
  have p0025 :=
    @g_wppstopstepmapndv C F hyp_wppstopstepfvactclndv_1 hyp_wppstopstepfvactclndv_2
  have p0026 :=
    @g_ffun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)) (syn_cwppstopstep F C)
  have p0027 :=
    Nominal.mp p0025 p0026
  have p0028 :=
    @g_funbrfv A (syn_cfv F A) (syn_cwppstopstep F C)
  have p0029 :=
    Nominal.mp p0027 p0028
  have p0030 :=
    @g_syl (.classMem A (syn_cwppstopact F C)) (syn_wbr A (syn_cwppstopstep F C) (syn_cfv F A)) (.classEq (syn_cfv (syn_cwppstopstep F C) A) (syn_cfv F A)) p0024 p0029
  exact p0030

noncomputable def g_wppstopstepfvidleclndv
    (A : Class) (C : Class) (F : Class) (hyp_wppstopstepfvidleclndv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppstopstepfvidleclndv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.neg (.classMem A (syn_cwppstopact F C)))) (.classEq (syn_cfv (syn_cwppstopstep F C) A) A)) := by
  let proofSupport : Finset Var := A.fv ∪ C.fv ∪ F.fv
  have p0000 :=
    @g_eldif A (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)
  have p0001 :=
    @g_biimpri (.classMem A (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.neg (.classMem A (syn_cwppstopact F C)))) p0000
  have p0002 :=
    @g_ididg A (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))
  have p0003 :=
    @g_syl (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.neg (.classMem A (syn_cwppstopact F C)))) (.classMem A (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_wbr A (syn_cid) A) p0001 p0002
  have p0004 :=
    @g_eldif A (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)
  have p0005 :=
    @g_biimpri (.classMem A (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.neg (.classMem A (syn_cwppstopact F C)))) p0004
  have p0006 :=
    @g_jca (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.neg (.classMem A (syn_cwppstopact F C)))) (syn_wbr A (syn_cid) A) (.classMem A (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) p0003 p0005
  have p0007 :=
    @g_brres A A (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))
  have p0008 :=
    @g_biimpri (syn_wbr A (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) A) (syn_wa (syn_wbr A (syn_cid) A) (.classMem A (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))) p0007
  have p0009 :=
    @g_syl (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.neg (.classMem A (syn_cwppstopact F C)))) (syn_wa (syn_wbr A (syn_cid) A) (.classMem A (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))) (syn_wbr A (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) A) p0006 p0008
  have p0010 :=
    @g_olc (syn_wbr A (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) A) (syn_wbr A (syn_cres F (syn_cwppstopact F C)) A)
  have p0011 :=
    @g_syl (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.neg (.classMem A (syn_cwppstopact F C)))) (syn_wbr A (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) A) (syn_wo (syn_wbr A (syn_cres F (syn_cwppstopact F C)) A) (syn_wbr A (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) A)) p0009 p0010
  have p0012 :=
    @g_brun A A (syn_cres F (syn_cwppstopact F C)) (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))
  have p0013 :=
    @g_biimpri (syn_wbr A (syn_cun (syn_cres F (syn_cwppstopact F C)) (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))) A) (syn_wo (syn_wbr A (syn_cres F (syn_cwppstopact F C)) A) (syn_wbr A (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) A)) p0012
  have p0014 :=
    @g_syl (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.neg (.classMem A (syn_cwppstopact F C)))) (syn_wo (syn_wbr A (syn_cres F (syn_cwppstopact F C)) A) (syn_wbr A (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C))) A)) (syn_wbr A (syn_cun (syn_cres F (syn_cwppstopact F C)) (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))) A) p0011 p0013
  have p0015 :=
    (by simpa [syn_cwppstopstep] using (Nominal.classEqRefl (syn_cwppstopstep F C)))
  have p0016 :=
    @g_breqi A A (syn_cwppstopstep F C) (syn_cun (syn_cres F (syn_cwppstopact F C)) (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))) p0015
  have p0017 :=
    @g_biimpri (syn_wbr A (syn_cwppstopstep F C) A) (syn_wbr A (syn_cun (syn_cres F (syn_cwppstopact F C)) (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))) A) p0016
  have p0018 :=
    @g_syl (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.neg (.classMem A (syn_cwppstopact F C)))) (syn_wbr A (syn_cun (syn_cres F (syn_cwppstopact F C)) (syn_cres (syn_cid) (syn_cdif (syn_chwcards (syn_cvv)) (syn_cwppstopact F C)))) A) (syn_wbr A (syn_cwppstopstep F C) A) p0014 p0017
  have p0019 :=
    @g_wppstopstepmapndv C F hyp_wppstopstepfvidleclndv_1 hyp_wppstopstepfvidleclndv_2
  have p0020 :=
    @g_ffun (syn_chwcards (syn_cvv)) (syn_chwcards (syn_cvv)) (syn_cwppstopstep F C)
  have p0021 :=
    Nominal.mp p0019 p0020
  have p0022 :=
    @g_funbrfv A A (syn_cwppstopstep F C)
  have p0023 :=
    Nominal.mp p0021 p0022
  have p0024 :=
    @g_syl (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.neg (.classMem A (syn_cwppstopact F C)))) (syn_wbr A (syn_cwppstopstep F C) A) (.classEq (syn_cfv (syn_cwppstopstep F C) A) A) p0018 p0023
  exact p0024

noncomputable def g_wppstopactlecbindv
    (A : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F)))) (syn_wb (.classMem A (syn_cwppstopact F C)) (syn_wbr A (syn_clec) C))) := by
  let proofSupport : Finset Var := A.fv ∪ C.fv ∪ F.fv
  have p0000 :=
    (by simpa [syn_cwppstopact] using (Nominal.classEqRefl (syn_cwppstopact F C)))
  have p0001 :=
    @g_eleq2i (syn_cwppstopact F C) (syn_cin (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))) A p0000
  have p0002 :=
    @g_elin A (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
  have p0003 :=
    @g_elin A (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))
  have p0004 :=
    @g_elimasn (syn_ccnv (syn_clec)) C A
  have p0005 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr C (syn_ccnv (syn_clec)) A)))
  have p0006 :=
    @g_bicomi (syn_wbr C (syn_ccnv (syn_clec)) A) (.classMem (syn_cop C A) (syn_ccnv (syn_clec))) p0005
  have p0007 :=
    @g_bitri (.classMem A (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))) (.classMem (syn_cop C A) (syn_ccnv (syn_clec))) (syn_wbr C (syn_ccnv (syn_clec)) A) p0004 p0006
  have p0008 :=
    @g_brcnv C A (syn_clec)
  have p0009 :=
    @g_bitri (.classMem A (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))) (syn_wbr C (syn_ccnv (syn_clec)) A) (syn_wbr A (syn_clec) C) p0007 p0008
  have p0010 :=
    @g_anbi2i (.classMem A (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))) (syn_wbr A (syn_clec) C) (.classMem A (syn_chwcards (syn_cvv))) p0009
  have p0011 :=
    @g_bitri (.classMem A (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))) (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.classMem A (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))) (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C)) p0003 p0010
  have p0012 :=
    @g_anbi2i (.classMem A (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))) (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C)) (.classMem A (syn_cdm F)) p0011
  have p0013 :=
    @g_bitri (.classMem A (syn_cin (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))) (syn_wa (.classMem A (syn_cdm F)) (.classMem A (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))) (syn_wa (.classMem A (syn_cdm F)) (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C))) p0002 p0012
  have p0014 :=
    @g_bitri (.classMem A (syn_cwppstopact F C)) (.classMem A (syn_cin (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))) (syn_wa (.classMem A (syn_cdm F)) (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C))) p0001 p0013
  have p0015 :=
    @g_biimpi (.classMem A (syn_cwppstopact F C)) (syn_wa (.classMem A (syn_cdm F)) (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C))) p0014
  have p0016 :=
    @g_simpr (.classMem A (syn_cdm F)) (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C))
  have p0017 :=
    @g_syl (.classMem A (syn_cwppstopact F C)) (syn_wa (.classMem A (syn_cdm F)) (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C))) (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C)) p0015 p0016
  have p0018 :=
    @g_simpr (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C)
  have p0019 :=
    @g_syl (.classMem A (syn_cwppstopact F C)) (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C)) (syn_wbr A (syn_clec) C) p0017 p0018
  have p0020 :=
    @g_a1i (.imp (.classMem A (syn_cwppstopact F C)) (syn_wbr A (syn_clec) C)) (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F)))) p0019
  have p0021 :=
    @g_simpr (.classMem A (syn_chwcards (syn_cvv))) (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F)))
  have p0022 :=
    @g_simpl (.classMem A (syn_chwcards (syn_cvv))) (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F)))
  have p0023 :=
    @g_a1d (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F)))) (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C) p0022
  have p0024 :=
    @g_id (syn_wbr A (syn_clec) C)
  have p0025 :=
    @g_a1i (.imp (syn_wbr A (syn_clec) C) (syn_wbr A (syn_clec) C)) (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F)))) p0024
  have p0026 :=
    @g_jcad (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F)))) (syn_wbr A (syn_clec) C) (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C) p0023 p0025
  have p0027 :=
    @g_jcad (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F)))) (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F)) (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C)) p0021 p0026
  have p0028 :=
    (by simpa [syn_cwppstopact] using (Nominal.classEqRefl (syn_cwppstopact F C)))
  have p0029 :=
    @g_eleq2i (syn_cwppstopact F C) (syn_cin (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))) A p0028
  have p0030 :=
    @g_elin A (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
  have p0031 :=
    @g_elin A (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))
  have p0032 :=
    @g_elimasn (syn_ccnv (syn_clec)) C A
  have p0033 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr C (syn_ccnv (syn_clec)) A)))
  have p0034 :=
    @g_bicomi (syn_wbr C (syn_ccnv (syn_clec)) A) (.classMem (syn_cop C A) (syn_ccnv (syn_clec))) p0033
  have p0035 :=
    @g_bitri (.classMem A (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))) (.classMem (syn_cop C A) (syn_ccnv (syn_clec))) (syn_wbr C (syn_ccnv (syn_clec)) A) p0032 p0034
  have p0036 :=
    @g_brcnv C A (syn_clec)
  have p0037 :=
    @g_bitri (.classMem A (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))) (syn_wbr C (syn_ccnv (syn_clec)) A) (syn_wbr A (syn_clec) C) p0035 p0036
  have p0038 :=
    @g_anbi2i (.classMem A (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))) (syn_wbr A (syn_clec) C) (.classMem A (syn_chwcards (syn_cvv))) p0037
  have p0039 :=
    @g_bitri (.classMem A (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))) (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.classMem A (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))) (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C)) p0031 p0038
  have p0040 :=
    @g_anbi2i (.classMem A (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))) (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C)) (.classMem A (syn_cdm F)) p0039
  have p0041 :=
    @g_bitri (.classMem A (syn_cin (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))) (syn_wa (.classMem A (syn_cdm F)) (.classMem A (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))) (syn_wa (.classMem A (syn_cdm F)) (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C))) p0030 p0040
  have p0042 :=
    @g_bitri (.classMem A (syn_cwppstopact F C)) (.classMem A (syn_cin (syn_cdm F) (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C))))) (syn_wa (.classMem A (syn_cdm F)) (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C))) p0029 p0041
  have p0043 :=
    @g_biimpri (.classMem A (syn_cwppstopact F C)) (syn_wa (.classMem A (syn_cdm F)) (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C))) p0042
  have p0044 :=
    @g_syl6 (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F)))) (syn_wbr A (syn_clec) C) (syn_wa (.classMem A (syn_cdm F)) (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (syn_wbr A (syn_clec) C))) (.classMem A (syn_cwppstopact F C)) p0027 p0043
  have p0045 :=
    @g_impbid (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F)))) (.classMem A (syn_cwppstopact F C)) (syn_wbr A (syn_clec) C) p0020 p0044
  exact p0045

noncomputable def g_wppstopstepfvlecdndv
    (A : Class) (C : Class) (F : Class) (hyp_wppstopstepfvlecdndv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppstopstepfvlecdndv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F)))) (.imp (syn_wbr A (syn_clec) C) (.classEq (syn_cfv (syn_cwppstopstep F C) A) (syn_cfv F A)))) := by
  let proofSupport : Finset Var := A.fv ∪ C.fv ∪ F.fv
  have p0000 :=
    @g_wppstopactlecbindv A C F
  have p0001 :=
    @g_biimprd (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F)))) (.classMem A (syn_cwppstopact F C)) (syn_wbr A (syn_clec) C) p0000
  have p0002 :=
    @g_wppstopstepfvactclndv A C F hyp_wppstopstepfvlecdndv_1 hyp_wppstopstepfvlecdndv_2
  have p0003 :=
    @g_syl6 (syn_wa (.classMem A (syn_chwcards (syn_cvv))) (.imp (syn_wbr A (syn_clec) C) (.classMem A (syn_cdm F)))) (syn_wbr A (syn_clec) C) (.classMem A (syn_cwppstopact F C)) (.classEq (syn_cfv (syn_cwppstopstep F C) A) (syn_cfv F A)) p0001 p0002
  exact p0003

#print axioms g_wppstopstepfvlecdndv

end NFChoice.DirectNominalPrf.WPPReplay
