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
import NominalWPPReplayChunk015Compact001Part030

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

noncomputable def g_hwcardslecanti
    (k : Var) (m : Var) :
    Nominal.NPrf (.imp (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (.classMem (.cv m) (syn_chwcards (syn_cvv)))) (.imp (syn_wa (syn_wbr (.cv k) (syn_clec) (.cv m)) (syn_wbr (.cv m) (syn_clec) (.cv k))) (.classEq (.cv k) (.cv m)))) := by
  let proofSupport : Finset Var := ({k} : Finset Var) ∪ ({m} : Finset Var)
  have p0000 :=
    @g_simpl (.classMem (.cv k) (syn_chwcards (syn_cvv))) (.classMem (.cv m) (syn_chwcards (syn_cvv)))
  have p0001 :=
    @g_hwcardssnc (syn_cvv)
  have p0002 :=
    @g_ssel (syn_chwcards (syn_cvv)) (syn_cncs) (.cv k)
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (.classMem (.cv m) (syn_chwcards (syn_cvv)))) (.classMem (.cv k) (syn_chwcards (syn_cvv))) (.classMem (.cv k) (syn_cncs)) p0000 p0003
  have p0005 :=
    @g_simpr (.classMem (.cv k) (syn_chwcards (syn_cvv))) (.classMem (.cv m) (syn_chwcards (syn_cvv)))
  have p0006 :=
    @g_hwcardssnc (syn_cvv)
  have p0007 :=
    @g_ssel (syn_chwcards (syn_cvv)) (syn_cncs) (.cv m)
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (.classMem (.cv m) (syn_chwcards (syn_cvv)))) (.classMem (.cv m) (syn_chwcards (syn_cvv))) (.classMem (.cv m) (syn_cncs)) p0005 p0008
  have p0010 :=
    @g_jca (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (.classMem (.cv m) (syn_chwcards (syn_cvv)))) (.classMem (.cv k) (syn_cncs)) (.classMem (.cv m) (syn_cncs)) p0004 p0009
  have p0011 :=
    @g_sbth (.cv k) (.cv m)
  have p0012 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (.classMem (.cv m) (syn_chwcards (syn_cvv)))) (syn_wa (.classMem (.cv k) (syn_cncs)) (.classMem (.cv m) (syn_cncs))) (.imp (syn_wa (syn_wbr (.cv k) (syn_clec) (.cv m)) (syn_wbr (.cv m) (syn_clec) (.cv k))) (.classEq (.cv k) (.cv m))) p0010 p0011
  exact p0012

noncomputable def g_wpporbitfnndv
    (F : Class) (I : Class) :
    Nominal.NPrf (.imp (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_wfn (syn_cfrec F I) (syn_cnnc))) := by
  let proofSupport : Finset Var := F.fv ∪ I.fv
  have p0000 :=
    @g_eqid (syn_cfrec F I)
  have p0001 :=
    @g_simp1 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0002 :=
    @g_simp2 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0003 :=
    @g_simp3 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0004 :=
    @g_fnfrec (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_cfrec F I) F I p0000 p0001 p0002 p0003
  exact p0004

noncomputable def g_wpporbit0ndv
    (F : Class) (I : Class) :
    Nominal.NPrf (.imp (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classEq (syn_cfv (syn_cfrec F I) (syn_c0c)) I)) := by
  let proofSupport : Finset Var := F.fv ∪ I.fv
  have p0000 :=
    @g_eqid (syn_cfrec F I)
  have p0001 :=
    @g_simp1 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0002 :=
    @g_simp2 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0003 :=
    @g_simp3 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0004 :=
    @g_frec0 (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_cfrec F I) F I p0000 p0001 p0002 p0003
  exact p0004

noncomputable def g_wpporbitsucndv
    (F : Class) (I : Class) (N : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc N (syn_c1c))) (syn_cfv F (syn_cfv (syn_cfrec F I) N)))) := by
  let proofSupport : Finset Var := F.fv ∪ I.fv ∪ N.fv
  have p0000 :=
    @g_eqid (syn_cfrec F I)
  have p0001 :=
    @g_simpl (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))
  have p0002 :=
    @g_simp1 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0003 :=
    @g_syl (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem F (syn_cfuns)) p0001 p0002
  have p0004 :=
    @g_simpl (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))
  have p0005 :=
    @g_simp2 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0006 :=
    @g_syl (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem I (syn_cdm F)) p0004 p0005
  have p0007 :=
    @g_simpl (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))
  have p0008 :=
    @g_simp3 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))
  have p0009 :=
    @g_syl (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (syn_wss (syn_crn F) (syn_cdm F)) p0007 p0008
  have p0010 :=
    @g_simpr (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))
  have p0011 :=
    @g_frecsuc (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F)) (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_cfrec F I) F I N p0000 p0003 p0006 p0009 p0010
  exact p0011

noncomputable def g_lnwpwccore
    (A : Class) (R : Class) (dv_A_R : Disjoint A.fv R.fv) (hyp_lnwpwccore_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_lnwpwccore_2 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_lnwpwccore_3 : Nominal.NPrf (.classMem (syn_cop R A) (syn_clnpwc A))) :
    Nominal.NPrf (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) A) (syn_wbr R (syn_ctrans) A)) (syn_wbr R (syn_cconnex) A)) (syn_wss R (syn_cxp A A))) := by
  let proofSupport : Finset Var := A.fv ∪ R.fv
  have dv_cache_0001 : Disjoint (A).fv (R).fv := by
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have p0000 :=
    @g_ellnpwcndv A A R dv_cache_0001 dv_cache_0001 hyp_lnwpwccore_2 hyp_lnwpwccore_1
  have p0001 :=
    @g_mpbi (.classMem (syn_cop R A) (syn_clnpwc A)) (syn_wa (.classMem (syn_cop R A) (syn_clntpc A)) (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) A)) hyp_lnwpwccore_3 p0000
  have p0002 :=
    @g_simpl (.classMem (syn_cop R A) (syn_clntpc A)) (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) A)
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    @g_ellntpcndv A A R dv_cache_0001 dv_cache_0001 hyp_lnwpwccore_1 hyp_lnwpwccore_2 hyp_lnwpwccore_1
  have p0005 :=
    @g_mpbi (.classMem (syn_cop R A) (syn_clntpc A)) (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) A) (syn_wbr R (syn_ctrans) A)) (syn_wbr R (syn_cconnex) A)) (syn_wss R (syn_cxp A A))) (.classEq A A)) p0003 p0004
  have p0006 :=
    @g_simpl (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) A) (syn_wbr R (syn_ctrans) A)) (syn_wbr R (syn_cconnex) A)) (syn_wss R (syn_cxp A A))) (.classEq A A)
  have p0007 :=
    Nominal.mp p0005 p0006
  exact p0007

noncomputable def g_lnworigqordwe
    (A : Class) (R : Class) (dv_A_R : Disjoint A.fv R.fv) (hyp_lnworigqordwe_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_lnworigqordwe_2 : Nominal.NPrf (.classMem R (syn_cvv))) (hyp_lnworigqordwe_3 : Nominal.NPrf (.classMem (syn_cop R A) (syn_clnpwc A))) :
    Nominal.NPrf (syn_wbr (syn_clnqord R A) (syn_cwe) (syn_clnquo R A)) := by
  let proofSupport : Finset Var := A.fv ∪ R.fv
  have dv_cache_0001 : Disjoint (A).fv (R).fv := by
    exact (show Disjoint (A).fv (R).fv from (show Disjoint (A).fv (R).fv from (by exact dv_A_R)))
  have p0000 :=
    @g_pm3_2i (.classMem R (syn_cvv)) (.classMem A (syn_cvv)) hyp_lnworigqordwe_2 hyp_lnworigqordwe_1
  have p0001 :=
    @g_lnwpwccore A R dv_cache_0001 hyp_lnworigqordwe_1 hyp_lnworigqordwe_2 hyp_lnworigqordwe_3
  have p0002 :=
    @g_pm3_2i (syn_wa (.classMem R (syn_cvv)) (.classMem A (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) A) (syn_wbr R (syn_ctrans) A)) (syn_wbr R (syn_cconnex) A)) (syn_wss R (syn_cxp A A))) p0000 p0001
  have p0003 :=
    @g_ellnpwcndv A A R dv_cache_0001 dv_cache_0001 hyp_lnworigqordwe_2 hyp_lnworigqordwe_1
  have p0004 :=
    @g_biimpi (.classMem (syn_cop R A) (syn_clnpwc A)) (syn_wa (.classMem (syn_cop R A) (syn_clntpc A)) (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) A)) p0003
  have p0005 :=
    Nominal.mp hyp_lnworigqordwe_3 p0004
  have p0006 :=
    @g_simpr (.classMem (syn_cop R A) (syn_clntpc A)) (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) A)
  have p0007 :=
    Nominal.mp p0005 p0006
  have p0008 :=
    @g_pm3_2i (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem A (syn_cvv))) (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) A) (syn_wbr R (syn_ctrans) A)) (syn_wbr R (syn_cconnex) A)) (syn_wss R (syn_cxp A A)))) (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) A) p0002 p0007
  have p0009 :=
    @g_lnqordwe A R dv_cache_0001
  have p0010 :=
    Nominal.mp p0008 p0009
  exact p0010

noncomputable def g_wppreachsucndv
    (C : Class) (F : Class) (N : Class) (dv_C_F : Disjoint C.fv F.fv) (dv_C_N : Disjoint C.fv N.fv) (dv_F_N : Disjoint F.fv N.fv) (hyp_wppreachsucndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem N (syn_cnnc)) (.classEq (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_cplc N (syn_c1c))) (syn_cima (syn_ccnv F) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) N)))) := by
  let proofSupport : Finset Var := C.fv ∪ F.fv ∪ N.fv
  have dv_cache_0001 : Disjoint ((syn_cimage (syn_ccnv F))).fv ((syn_cima (syn_clec) (syn_csn C))).fv := by
    exact (show Disjoint ((syn_cimage (syn_ccnv F))).fv ((syn_cima (syn_clec) (syn_csn C))).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima]; exact (show Disjoint (((syn_ccnv F)).fv) ((((syn_clec)).fv) ∪ (((syn_csn C)).fv)) from (Finset.disjoint_union_right.mpr ⟨(show Disjoint (((syn_ccnv F)).fv) (((syn_clec)).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv]; exact (show Disjoint ((F).fv) (((syn_clec)).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec]; exact (show Disjoint ((F).fv) ((∅ : Finset Var)) from (by simp)))))), (show Disjoint (((syn_ccnv F)).fv) (((syn_csn C)).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv]; exact (show Disjoint ((F).fv) (((syn_csn C)).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show Disjoint (F).fv (C).fv from (by exact dv_C_F.symm))))))⟩))))
  have dv_cache_0002 : Disjoint ((syn_cimage (syn_ccnv F))).fv (N).fv := by
    clear dv_cache_0001
    exact (show Disjoint ((syn_cimage (syn_ccnv F))).fv (N).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage]; exact (show Disjoint (((syn_ccnv F)).fv) ((N).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv]; exact (show Disjoint (F).fv (N).fv from (by exact dv_F_N))))))
  have dv_cache_0003 : Disjoint ((syn_cima (syn_clec) (syn_csn C))).fv (N).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (show Disjoint ((syn_cima (syn_clec) (syn_csn C))).fv (N).fv from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima]; exact (show Disjoint ((((syn_clec)).fv) ∪ (((syn_csn C)).fv)) ((N).fv) from (Finset.disjoint_union_left.mpr ⟨(show Disjoint (((syn_clec)).fv) ((N).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec]; exact (show Disjoint ((∅ : Finset Var)) ((N).fv) from (by simp)))), (show Disjoint (((syn_csn C)).fv) ((N).fv) from (by rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]; exact (show Disjoint (C).fv (N).fv from (by exact dv_C_N))))⟩))))
  have p0000 :=
    @g_wppreachopfn F hyp_wppreachsucndv_1
  have p0001 :=
    @g_fnfun (syn_cvv) (syn_cimage (syn_ccnv F))
  have p0002 :=
    Nominal.mp p0000 p0001
  have p0003 :=
    @g_cnvex F hyp_wppreachsucndv_1
  have p0004 :=
    @g_imageex (syn_ccnv F) p0003
  have p0005 :=
    @g_elfuns (syn_cimage (syn_ccnv F)) p0004
  have p0006 :=
    @g_mpbir (.classMem (syn_cimage (syn_ccnv F)) (syn_cfuns)) (syn_wfun (syn_cimage (syn_ccnv F))) p0002 p0005
  have p0007 :=
    @g_wppreachupperex C
  have p0008 :=
    @g_wppreachopfn F hyp_wppreachsucndv_1
  have p0009 :=
    @g_fndm (syn_cvv) (syn_cimage (syn_ccnv F))
  have p0010 :=
    Nominal.mp p0008 p0009
  have p0011 :=
    @g_eleqtrri (syn_cima (syn_clec) (syn_csn C)) (syn_cvv) (syn_cdm (syn_cimage (syn_ccnv F))) p0007 p0010
  have p0012 :=
    @g_ssv (syn_crn (syn_cimage (syn_ccnv F)))
  have p0013 :=
    @g_wppreachopfn F hyp_wppreachsucndv_1
  have p0014 :=
    @g_fndm (syn_cvv) (syn_cimage (syn_ccnv F))
  have p0015 :=
    Nominal.mp p0013 p0014
  have p0016 :=
    @g_sseqtr4i (syn_crn (syn_cimage (syn_ccnv F))) (syn_cvv) (syn_cdm (syn_cimage (syn_ccnv F))) p0012 p0015
  have p0017 :=
    @g_n_3pm3_2i (.classMem (syn_cimage (syn_ccnv F)) (syn_cfuns)) (.classMem (syn_cima (syn_clec) (syn_csn C)) (syn_cdm (syn_cimage (syn_ccnv F)))) (syn_wss (syn_crn (syn_cimage (syn_ccnv F))) (syn_cdm (syn_cimage (syn_ccnv F)))) p0006 p0011 p0016
  have p0018 :=
    @g_a1i (syn_w3a (.classMem (syn_cimage (syn_ccnv F)) (syn_cfuns)) (.classMem (syn_cima (syn_clec) (syn_csn C)) (syn_cdm (syn_cimage (syn_ccnv F)))) (syn_wss (syn_crn (syn_cimage (syn_ccnv F))) (syn_cdm (syn_cimage (syn_ccnv F))))) (.classMem N (syn_cnnc)) p0017
  have p0019 :=
    @g_id (.classMem N (syn_cnnc))
  have p0020 :=
    @g_jca (.classMem N (syn_cnnc)) (syn_w3a (.classMem (syn_cimage (syn_ccnv F)) (syn_cfuns)) (.classMem (syn_cima (syn_clec) (syn_csn C)) (syn_cdm (syn_cimage (syn_ccnv F)))) (syn_wss (syn_crn (syn_cimage (syn_ccnv F))) (syn_cdm (syn_cimage (syn_ccnv F))))) (.classMem N (syn_cnnc)) p0018 p0019
  have p0021 :=
    @g_wpporbitsuc (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)) N dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0022 :=
    @g_syl (.classMem N (syn_cnnc)) (syn_wa (syn_w3a (.classMem (syn_cimage (syn_ccnv F)) (syn_cfuns)) (.classMem (syn_cima (syn_clec) (syn_csn C)) (syn_cdm (syn_cimage (syn_ccnv F)))) (syn_wss (syn_crn (syn_cimage (syn_ccnv F))) (syn_cdm (syn_cimage (syn_ccnv F))))) (.classMem N (syn_cnnc))) (.classEq (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_cplc N (syn_c1c))) (syn_cfv (syn_cimage (syn_ccnv F)) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) N))) p0020 p0021
  have p0023 :=
    @g_cnvex F hyp_wppreachsucndv_1
  have p0024 :=
    @g_fvex N (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
  have p0025 :=
    @g_fvimagecl (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) N) (syn_ccnv F) p0023 p0024
  have p0026 :=
    @g_a1i (.classEq (syn_cfv (syn_cimage (syn_ccnv F)) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) N)) (syn_cima (syn_ccnv F) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) N))) (.classMem N (syn_cnnc)) p0025
  have p0027 :=
    @g_eqtrd (.classMem N (syn_cnnc)) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_cplc N (syn_c1c))) (syn_cfv (syn_cimage (syn_ccnv F)) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) N)) (syn_cima (syn_ccnv F) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) N)) p0022 p0026
  exact p0027

noncomputable def g_wpppredfamex
    (C : Class) (F : Class) (hyp_wpppredfamex_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cwpppredfam F C) (syn_cvv)) := by
  let proofSupport : Finset Var := C.fv ∪ F.fv
  have p0000 :=
    (by simpa [syn_cwpppredfam] using (Nominal.classEqRefl (syn_cwpppredfam F C)))
  have p0001 :=
    @g_eqid (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
  have p0002 :=
    @g_cnvex F hyp_wpppredfamex_1
  have p0003 :=
    @g_imageex (syn_ccnv F) p0002
  have p0004 :=
    @g_frecex (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)) p0001 p0003
  have p0005 :=
    @g_tcfnex
  have p0006 :=
    @g_coex (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn) p0004 p0005
  have p0007 :=
    @g_cnvex (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)) p0006
  have p0008 :=
    @g_imageex (syn_ccnv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn))) p0007
  have p0009 :=
    @g_ssetex
  have p0010 :=
    @g_imageex (syn_csset) p0009
  have p0011 :=
    @g_coex (syn_cimage (syn_ccnv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)))) (syn_cimage (syn_csset)) p0008 p0010
  have p0012 :=
    @g_eqeltri (syn_cwpppredfam F C) (syn_ccom (syn_cimage (syn_ccnv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)))) (syn_cimage (syn_csset))) (syn_cvv) p0000 p0011
  exact p0012

noncomputable def g_wppimagefun
    (R : Class) :
    Nominal.NPrf (syn_wfun (syn_cimage R)) := by
  let proofSupport : Finset Var := R.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (h)
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (h)
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    Ne.symm fresh_x_ne_z
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have dv_cache_0001 : x ∉ ((syn_cimage R)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cimage R)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_cimage R)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_R, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0005 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0006 : y ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    @g_vex x
  have p0001 :=
    @g_vex y
  have p0002 :=
    @g_brimage (.cv x) (.cv y) R p0000 p0001
  have p0003 :=
    @g_vex x
  have p0004 :=
    @g_vex z
  have p0005 :=
    @g_brimage (.cv x) (.cv z) R p0003 p0004
  have p0006 :=
    @g_anbi12i (syn_wbr (.cv x) (syn_cimage R) (.cv y)) (.classEq (.cv y) (syn_cima R (.cv x))) (syn_wbr (.cv x) (syn_cimage R) (.cv z)) (.classEq (.cv z) (syn_cima R (.cv x))) p0002 p0005
  have p0007 :=
    @g_eqtr3 (.cv y) (.cv z) (syn_cima R (.cv x))
  have p0008 :=
    @g_sylbi (syn_wa (syn_wbr (.cv x) (syn_cimage R) (.cv y)) (syn_wbr (.cv x) (syn_cimage R) (.cv z))) (syn_wa (.classEq (.cv y) (syn_cima R (.cv x))) (.classEq (.cv z) (syn_cima R (.cv x)))) (.classEq (.cv y) (.cv z)) p0006 p0007
  have p0009 :=
    Nominal.gen p0008 z
  have p0010 :=
    Nominal.gen p0009 y
  have p0011 :=
    Nominal.gen p0010 x
  have p0012 :=
    @g_dffun2 x y z (syn_cimage R) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0013_e01_recanon : Nominal.NPrf (syn_wb (syn_wfun (syn_cimage R)) (.all x (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) (syn_cimage R) (.cv y)) (syn_wbr (.cv x) (syn_cimage R) (.cv z))) (.classEq (.cv y) (.cv z))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wfun syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_ccom syn_copab syn_wex syn_ccnv syn_cid syn_cimage
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.same _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0012
  have p0013 :=
    @g_mpbir (syn_wfun (syn_cimage R)) (.all x (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) (syn_cimage R) (.cv y)) (syn_wbr (.cv x) (syn_cimage R) (.cv z))) (.classEq (.cv y) (.cv z)))))) p0011 p0013_e01_recanon
  exact p0013

noncomputable def g_wppimagefv
    (B : Class) (G : Class) (hyp_wppimagefv_1 : Nominal.NPrf (.classMem G (syn_cvv))) (hyp_wppimagefv_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cimage G) B) (syn_cima G B)) := by
  let proofSupport : Finset Var := B.fv ∪ G.fv
  have p0000 :=
    @g_eqid (syn_cima G B)
  have p0001 :=
    @g_imaex G B hyp_wppimagefv_1 hyp_wppimagefv_2
  have p0002 :=
    @g_brimage B (syn_cima G B) G hyp_wppimagefv_2 p0001
  have p0003 :=
    @g_mpbir (syn_wbr B (syn_cimage G) (syn_cima G B)) (.classEq (syn_cima G B) (syn_cima G B)) p0000 p0002
  have p0004 :=
    @g_wppimagefun G
  have p0005 :=
    @g_funbrfv B (syn_cima G B) (syn_cimage G)
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    Nominal.mp p0003 p0006
  exact p0007

noncomputable def g_wppreachorbitfnndv
    (C : Class) (F : Class) (hyp_wppreachorbitfnndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (syn_wfn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_cnnc)) := by
  let proofSupport : Finset Var := C.fv ∪ F.fv
  have p0000 :=
    @g_cnvex F hyp_wppreachorbitfnndv_1
  have p0001 :=
    @g_wppimagefn (syn_ccnv F) p0000
  have p0002 :=
    @g_fnfun (syn_cvv) (syn_cimage (syn_ccnv F))
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    @g_cnvex F hyp_wppreachorbitfnndv_1
  have p0005 :=
    @g_imageex (syn_ccnv F) p0004
  have p0006 :=
    @g_elfuns (syn_cimage (syn_ccnv F)) p0005
  have p0007 :=
    @g_mpbir (.classMem (syn_cimage (syn_ccnv F)) (syn_cfuns)) (syn_wfun (syn_cimage (syn_ccnv F))) p0003 p0006
  have p0008 :=
    @g_lecex
  have p0009 :=
    @g_snex C
  have p0010 :=
    @g_imaex (syn_clec) (syn_csn C) p0008 p0009
  have p0011 :=
    @g_cnvex F hyp_wppreachorbitfnndv_1
  have p0012 :=
    @g_wppimagefn (syn_ccnv F) p0011
  have p0013 :=
    @g_fndm (syn_cvv) (syn_cimage (syn_ccnv F))
  have p0014 :=
    Nominal.mp p0012 p0013
  have p0015 :=
    @g_eleqtrri (syn_cima (syn_clec) (syn_csn C)) (syn_cvv) (syn_cdm (syn_cimage (syn_ccnv F))) p0010 p0014
  have p0016 :=
    @g_ssv (syn_crn (syn_cimage (syn_ccnv F)))
  have p0017 :=
    @g_cnvex F hyp_wppreachorbitfnndv_1
  have p0018 :=
    @g_wppimagefn (syn_ccnv F) p0017
  have p0019 :=
    @g_fndm (syn_cvv) (syn_cimage (syn_ccnv F))
  have p0020 :=
    Nominal.mp p0018 p0019
  have p0021 :=
    @g_sseqtr4i (syn_crn (syn_cimage (syn_ccnv F))) (syn_cvv) (syn_cdm (syn_cimage (syn_ccnv F))) p0016 p0020
  have p0022 :=
    @g_n_3pm3_2i (.classMem (syn_cimage (syn_ccnv F)) (syn_cfuns)) (.classMem (syn_cima (syn_clec) (syn_csn C)) (syn_cdm (syn_cimage (syn_ccnv F)))) (syn_wss (syn_crn (syn_cimage (syn_ccnv F))) (syn_cdm (syn_cimage (syn_ccnv F)))) p0007 p0015 p0021
  have p0023 :=
    @g_wpporbitfnndv (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))
  have p0024 :=
    Nominal.mp p0022 p0023
  exact p0024

noncomputable def g_wpppredfamfv
    (C : Class) (D : Class) (F : Class) (hyp_wpppredfamfv_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn D))) (syn_cima (syn_ccnv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn))) (syn_cima (syn_csset) (syn_csn (syn_csn D))))) := by
  let proofSupport : Finset Var := C.fv ∪ D.fv ∪ F.fv
  have p0000 :=
    (by simpa [syn_cwpppredfam] using (Nominal.classEqRefl (syn_cwpppredfam F C)))
  have p0001 :=
    @g_fveq1i (syn_csn (syn_csn D)) (syn_cwpppredfam F C) (syn_ccom (syn_cimage (syn_ccnv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)))) (syn_cimage (syn_csset))) p0000
  have p0002 :=
    @g_wppimagefun (syn_csset)
  have p0003 :=
    @g_eqid (syn_cima (syn_csset) (syn_csn (syn_csn D)))
  have p0004 :=
    @g_snex (syn_csn D)
  have p0005 :=
    @g_ssetex
  have p0006 :=
    @g_snex (syn_csn D)
  have p0007 :=
    @g_imaex (syn_csset) (syn_csn (syn_csn D)) p0005 p0006
  have p0008 :=
    @g_brimage (syn_csn (syn_csn D)) (syn_cima (syn_csset) (syn_csn (syn_csn D))) (syn_csset) p0004 p0007
  have p0009 :=
    @g_mpbir (syn_wbr (syn_csn (syn_csn D)) (syn_cimage (syn_csset)) (syn_cima (syn_csset) (syn_csn (syn_csn D)))) (.classEq (syn_cima (syn_csset) (syn_csn (syn_csn D))) (syn_cima (syn_csset) (syn_csn (syn_csn D)))) p0003 p0008
  have p0010 :=
    @g_breldm (syn_csn (syn_csn D)) (syn_cima (syn_csset) (syn_csn (syn_csn D))) (syn_cimage (syn_csset))
  have p0011 :=
    Nominal.mp p0009 p0010
  have p0012 :=
    @g_pm3_2i (syn_wfun (syn_cimage (syn_csset))) (.classMem (syn_csn (syn_csn D)) (syn_cdm (syn_cimage (syn_csset)))) p0002 p0011
  have p0013 :=
    @g_fvco (syn_csn (syn_csn D)) (syn_cimage (syn_ccnv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)))) (syn_cimage (syn_csset))
  have p0014 :=
    Nominal.mp p0012 p0013
  have p0015 :=
    @g_eqtri (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn D))) (syn_cfv (syn_ccom (syn_cimage (syn_ccnv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)))) (syn_cimage (syn_csset))) (syn_csn (syn_csn D))) (syn_cfv (syn_cimage (syn_ccnv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)))) (syn_cfv (syn_cimage (syn_csset)) (syn_csn (syn_csn D)))) p0001 p0014
  have p0016 :=
    @g_ssetex
  have p0017 :=
    @g_snex (syn_csn D)
  have p0018 :=
    @g_wppimagefv (syn_csn (syn_csn D)) (syn_csset) p0016 p0017
  have p0019 :=
    @g_fveq2i (syn_cfv (syn_cimage (syn_csset)) (syn_csn (syn_csn D))) (syn_cima (syn_csset) (syn_csn (syn_csn D))) (syn_cimage (syn_ccnv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)))) p0018
  have p0020 :=
    @g_eqtri (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn D))) (syn_cfv (syn_cimage (syn_ccnv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)))) (syn_cfv (syn_cimage (syn_csset)) (syn_csn (syn_csn D)))) (syn_cfv (syn_cimage (syn_ccnv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)))) (syn_cima (syn_csset) (syn_csn (syn_csn D)))) p0015 p0019
  have p0021 :=
    @g_eqid (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
  have p0022 :=
    @g_cnvex F hyp_wpppredfamfv_1
  have p0023 :=
    @g_imageex (syn_ccnv F) p0022
  have p0024 :=
    @g_frecex (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)) p0021 p0023
  have p0025 :=
    @g_tcfnex
  have p0026 :=
    @g_coex (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn) p0024 p0025
  have p0027 :=
    @g_cnvex (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)) p0026
  have p0028 :=
    @g_ssetex
  have p0029 :=
    @g_snex (syn_csn D)
  have p0030 :=
    @g_imaex (syn_csset) (syn_csn (syn_csn D)) p0028 p0029
  have p0031 :=
    @g_wppimagefv (syn_cima (syn_csset) (syn_csn (syn_csn D))) (syn_ccnv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn))) p0027 p0030
  have p0032 :=
    @g_eqtri (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn D))) (syn_cfv (syn_cimage (syn_ccnv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)))) (syn_cima (syn_csset) (syn_csn (syn_csn D)))) (syn_cima (syn_ccnv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn))) (syn_cima (syn_csset) (syn_csn (syn_csn D)))) p0020 p0031
  exact p0032

noncomputable def g_elwpppredfam
    (C : Class) (D : Class) (F : Class) (q : Var) (hyp_elwpppredfam_1 : Nominal.NPrf (.classMem F (syn_cvv))) (hyp_elwpppredfam_2 : Nominal.NPrf (.classMem D (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem (syn_csn (.cv q)) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn D)))) (.classMem D (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv q))))) := by
  let proofSupport : Finset Var := C.fv ∪ D.fv ∪ F.fv ∪ ({q} : Finset Var)
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_q : y ≠ q := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_y : q ≠ y :=
    Ne.symm fresh_y_ne_q
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_ne_q : z ≠ q := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_z : q ≠ z :=
    Ne.symm fresh_z_ne_q
  have fresh_y_ne_z : y ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    Ne.symm fresh_y_ne_z
  have dv_cache_0001 : y ∉ ((Class.cv z)).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Wff.classMem D (.cv z))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_D, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_cima (syn_csset) (syn_csn (syn_csn D)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((Class.cab y (.classMem D (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_D, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_cfv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)) (syn_csn (.cv q)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctcfn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_q, fresh_y_not_F, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((Wff.classMem D (syn_cfv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)) (syn_csn (.cv q))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctcfn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_D, fresh_y_ne_q, fresh_y_not_F, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_wpppredfamfv C D F hyp_elwpppredfam_1
  have p0001 :=
    @g_eleq2i (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn D))) (syn_cima (syn_ccnv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn))) (syn_cima (syn_csset) (syn_csn (syn_csn D)))) (syn_csn (.cv q)) p0000
  have p0002 :=
    @g_elimasn (syn_csset) (syn_csn D) (.cv z)
  have p0003 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (syn_csn D) (syn_csset) (.cv z))))
  have p0004 :=
    @g_bicomi (syn_wbr (syn_csn D) (syn_csset) (.cv z)) (.classMem (syn_cop (syn_csn D) (.cv z)) (syn_csset)) p0003
  have p0005 :=
    @g_bitri (.classMem (.cv z) (syn_cima (syn_csset) (syn_csn (syn_csn D)))) (.classMem (syn_cop (syn_csn D) (.cv z)) (syn_csset)) (syn_wbr (syn_csn D) (syn_csset) (.cv z)) p0002 p0004
  have p0006 :=
    @g_vex z
  have p0007 :=
    @g_brssetsn D (.cv z) hyp_elwpppredfam_2 p0006
  have p0008 :=
    @g_bitri (.classMem (.cv z) (syn_cima (syn_csset) (syn_csn (syn_csn D)))) (syn_wbr (syn_csn D) (syn_csset) (.cv z)) (.classMem D (.cv z)) p0005 p0007
  have p0009 :=
    @g_vex z
  have p0010 :=
    @g_id (.classEq (.cv y) (.cv z))
  have p0011 :=
    @g_eleq2d (.classEq (.cv y) (.cv z)) (.cv y) (.cv z) D p0010
  have p0012 :=
    @g_elab (.classMem D (.cv y)) (.classMem D (.cv z)) y (.cv z) dv_cache_0001 dv_cache_0002 p0009 p0011
  have p0013 :=
    @g_bitr4i (.classMem (.cv z) (syn_cima (syn_csset) (syn_csn (syn_csn D)))) (.classMem D (.cv z)) (.classMem (.cv z) (.cab y (.classMem D (.cv y)))) p0008 p0012
  have p0014 :=
    @g_eqriv z (syn_cima (syn_csset) (syn_csn (syn_csn D))) (.cab y (.classMem D (.cv y))) dv_cache_0003 dv_cache_0004 p0013
  have p0015 :=
    @g_imaeq2i (syn_cima (syn_csset) (syn_csn (syn_csn D))) (.cab y (.classMem D (.cv y))) (syn_ccnv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn))) p0014
  have p0016 :=
    @g_eleq2i (syn_cima (syn_ccnv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn))) (syn_cima (syn_csset) (syn_csn (syn_csn D)))) (syn_cima (syn_ccnv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn))) (.cab y (.classMem D (.cv y)))) (syn_csn (.cv q)) p0015
  have p0017 :=
    @g_bitri (.classMem (syn_csn (.cv q)) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn D)))) (.classMem (syn_csn (.cv q)) (syn_cima (syn_ccnv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn))) (syn_cima (syn_csset) (syn_csn (syn_csn D))))) (.classMem (syn_csn (.cv q)) (syn_cima (syn_ccnv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn))) (.cab y (.classMem D (.cv y))))) p0001 p0016
  have p0018 :=
    @g_wppreachorbitfnndv C F hyp_elwpppredfam_1
  have p0019 :=
    @g_fnfun (syn_cnnc) (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
  have p0020 :=
    Nominal.mp p0018 p0019
  have p0021 :=
    @g_fntcfn
  have p0022 :=
    @g_fnfun (syn_c1c) (syn_ctcfn)
  have p0023 :=
    Nominal.mp p0021 p0022
  have p0024 :=
    @g_pm3_2i (syn_wfun (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))) (syn_wfun (syn_ctcfn)) p0020 p0023
  have p0025 :=
    @g_funco (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)
  have p0026 :=
    Nominal.mp p0024 p0025
  have p0027 :=
    @g_funfn (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn))
  have p0028 :=
    @g_mpbi (syn_wfun (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn))) (syn_wfn (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)) (syn_cdm (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)))) p0026 p0027
  have p0029 :=
    @g_elpreima (syn_cdm (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn))) (syn_csn (.cv q)) (.cab y (.classMem D (.cv y))) (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn))
  have p0030 :=
    Nominal.mp p0028 p0029
  have p0031 :=
    @g_fvex (syn_csn (.cv q)) (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn))
  have p0032 :=
    @g_id (.classEq (.cv y) (syn_cfv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)) (syn_csn (.cv q))))
  have p0033 :=
    @g_eleq2d (.classEq (.cv y) (syn_cfv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)) (syn_csn (.cv q)))) (.cv y) (syn_cfv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)) (syn_csn (.cv q))) D p0032
  have p0034 :=
    @g_elab (.classMem D (.cv y)) (.classMem D (syn_cfv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)) (syn_csn (.cv q)))) y (syn_cfv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)) (syn_csn (.cv q))) dv_cache_0005 dv_cache_0006 p0031 p0033
  have p0035 :=
    @g_elfvdm D (syn_csn (.cv q)) (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn))
  have p0036 :=
    @g_sylbi (.classMem (syn_cfv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)) (syn_csn (.cv q))) (.cab y (.classMem D (.cv y)))) (.classMem D (syn_cfv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)) (syn_csn (.cv q)))) (.classMem (syn_csn (.cv q)) (syn_cdm (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)))) p0034 p0035
  have p0037 :=
    @g_pm4_71ri (.classMem (syn_cfv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)) (syn_csn (.cv q))) (.cab y (.classMem D (.cv y)))) (.classMem (syn_csn (.cv q)) (syn_cdm (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)))) p0036
  have p0038 :=
    @g_bicomi (.classMem (syn_cfv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)) (syn_csn (.cv q))) (.cab y (.classMem D (.cv y)))) (syn_wa (.classMem (syn_csn (.cv q)) (syn_cdm (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)))) (.classMem (syn_cfv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)) (syn_csn (.cv q))) (.cab y (.classMem D (.cv y))))) p0037
  have p0039 :=
    @g_bitri (.classMem (syn_csn (.cv q)) (syn_cima (syn_ccnv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn))) (.cab y (.classMem D (.cv y))))) (syn_wa (.classMem (syn_csn (.cv q)) (syn_cdm (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)))) (.classMem (syn_cfv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)) (syn_csn (.cv q))) (.cab y (.classMem D (.cv y))))) (.classMem (syn_cfv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)) (syn_csn (.cv q))) (.cab y (.classMem D (.cv y)))) p0030 p0038
  have p0040 :=
    @g_fvex (syn_csn (.cv q)) (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn))
  have p0041 :=
    @g_id (.classEq (.cv y) (syn_cfv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)) (syn_csn (.cv q))))
  have p0042 :=
    @g_eleq2d (.classEq (.cv y) (syn_cfv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)) (syn_csn (.cv q)))) (.cv y) (syn_cfv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)) (syn_csn (.cv q))) D p0041
  have p0043 :=
    @g_elab (.classMem D (.cv y)) (.classMem D (syn_cfv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)) (syn_csn (.cv q)))) y (syn_cfv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)) (syn_csn (.cv q))) dv_cache_0005 dv_cache_0006 p0040 p0042
  have p0044 :=
    @g_bitri (.classMem (syn_csn (.cv q)) (syn_cima (syn_ccnv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn))) (.cab y (.classMem D (.cv y))))) (.classMem (syn_cfv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)) (syn_csn (.cv q))) (.cab y (.classMem D (.cv y)))) (.classMem D (syn_cfv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)) (syn_csn (.cv q)))) p0039 p0043
  have p0045 :=
    @g_fntcfn
  have p0046 :=
    @g_vex q
  have p0047 :=
    @g_snel1c (.cv q) p0046
  have p0048 :=
    @g_pm3_2i (syn_wfn (syn_ctcfn) (syn_c1c)) (.classMem (syn_csn (.cv q)) (syn_c1c)) p0045 p0047
  have p0049 :=
    @g_fvco2 (syn_c1c) (syn_csn (.cv q)) (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)
  have p0050 :=
    Nominal.mp p0048 p0049
  have p0051 :=
    @g_vex q
  have p0052 :=
    @g_tcfnfv (.cv q) p0051
  have p0053 :=
    @g_fveq2i (syn_cfv (syn_ctcfn) (syn_csn (.cv q))) (syn_ctc (.cv q)) (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) p0052
  have p0054 :=
    @g_eqtri (syn_cfv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)) (syn_csn (.cv q))) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_cfv (syn_ctcfn) (syn_csn (.cv q)))) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv q))) p0050 p0053
  have p0055 :=
    @g_eleq2i (syn_cfv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)) (syn_csn (.cv q))) (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv q))) D p0054
  have p0056 :=
    @g_bitri (.classMem (syn_csn (.cv q)) (syn_cima (syn_ccnv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn))) (.cab y (.classMem D (.cv y))))) (.classMem D (syn_cfv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn)) (syn_csn (.cv q)))) (.classMem D (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv q)))) p0044 p0055
  have p0057 :=
    @g_bitri (.classMem (syn_csn (.cv q)) (syn_cfv (syn_cwpppredfam F C) (syn_csn (syn_csn D)))) (.classMem (syn_csn (.cv q)) (syn_cima (syn_ccnv (syn_ccom (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctcfn))) (.cab y (.classMem D (.cv y))))) (.classMem D (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) (syn_ctc (.cv q)))) p0017 p0056
  exact p0057

noncomputable def g_wpppostcompex
    (F : Class) (hyp_wpppostcompex_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cwpppostcomp F) (syn_cvv)) := by
  let proofSupport : Finset Var := F.fv
  have p0000 :=
    (by simpa [syn_cwpppostcomp] using (Nominal.classEqRefl (syn_cwpppostcomp F)))
  have p0001 :=
    @g_composeex
  have p0002 :=
    @g_vvex
  have p0003 :=
    @g_snex F
  have p0004 :=
    @g_xpex (syn_cvv) (syn_csn F) p0002 p0003
  have p0005 :=
    @g_idex
  have p0006 :=
    @g_txpex (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid) p0004 p0005
  have p0007 :=
    @g_coex (syn_ccompose) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid)) p0001 p0006
  have p0008 :=
    @g_eqeltri (syn_cwpppostcomp F) (syn_ccom (syn_ccompose) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid))) (syn_cvv) p0000 p0007
  exact p0008

noncomputable def g_wppupperpreopex
    (C : Class) :
    Nominal.NPrf (.classMem (syn_cwppupperpreop C) (syn_cvv)) := by
  let proofSupport : Finset Var := C.fv
  have p0000 :=
    (by simpa [syn_cwppupperpreop] using (Nominal.classEqRefl (syn_cwppupperpreop C)))
  have p0001 :=
    @g_lnimageopex
  have p0002 :=
    @g_swapex
  have p0003 :=
    @g_imageex (syn_cswap) p0002
  have p0004 :=
    @g_vvex
  have p0005 :=
    @g_snex (syn_cima (syn_clec) (syn_csn C))
  have p0006 :=
    @g_xpex (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C))) p0004 p0005
  have p0007 :=
    @g_txpex (syn_cimage (syn_cswap)) (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C)))) p0003 p0006
  have p0008 :=
    @g_coex (syn_clnimageop) (syn_ctxp (syn_cimage (syn_cswap)) (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C))))) p0001 p0007
  have p0009 :=
    @g_eqeltri (syn_cwppupperpreop C) (syn_ccom (syn_clnimageop) (syn_ctxp (syn_cimage (syn_cswap)) (syn_cxp (syn_cvv) (syn_csn (syn_cima (syn_clec) (syn_csn C)))))) (syn_cvv) p0000 p0008
  exact p0009

noncomputable def g_wpppowlayerseqex
    (C : Class) (F : Class) (hyp_wpppowlayerseqex_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cwpppowlayerseq F C) (syn_cvv)) := by
  let proofSupport : Finset Var := C.fv ∪ F.fv
  have p0000 :=
    (by simpa [syn_cwpppowlayerseq] using (Nominal.classEqRefl (syn_cwpppowlayerseq F C)))
  have p0001 :=
    @g_wppupperpreopex C
  have p0002 :=
    @g_eqid (syn_cfrec (syn_cwpppostcomp F) (syn_cid))
  have p0003 :=
    @g_wpppostcompex F hyp_wpppowlayerseqex_1
  have p0004 :=
    @g_frecex (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_cwpppostcomp F) (syn_cid) p0002 p0003
  have p0005 :=
    @g_tcfnex
  have p0006 :=
    @g_coex (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn) p0004 p0005
  have p0007 :=
    @g_coex (syn_cwppupperpreop C) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn)) p0001 p0006
  have p0008 :=
    @g_eqeltri (syn_cwpppowlayerseq F C) (syn_ccom (syn_cwppupperpreop C) (syn_ccom (syn_cfrec (syn_cwpppostcomp F) (syn_cid)) (syn_ctcfn))) (syn_cvv) p0000 p0007
  exact p0008

noncomputable def g_wpphitfamex
    (C : Class) (F : Class) (hyp_wpphitfamex_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cwpphitfam F C) (syn_cvv)) := by
  let proofSupport : Finset Var := C.fv ∪ F.fv
  have p0000 :=
    (by simpa [syn_cwpphitfam] using (Nominal.classEqRefl (syn_cwpphitfam F C)))
  have p0001 :=
    @g_wpppowlayerseqex C F hyp_wpphitfamex_1
  have p0002 :=
    @g_cnvex (syn_cwpppowlayerseq F C) p0001
  have p0003 :=
    @g_imageex (syn_ccnv (syn_cwpppowlayerseq F C)) p0002
  have p0004 :=
    @g_ssetex
  have p0005 :=
    @g_imageex (syn_csset) p0004
  have p0006 :=
    @g_coex (syn_cimage (syn_ccnv (syn_cwpppowlayerseq F C))) (syn_cimage (syn_csset)) p0003 p0005
  have p0007 :=
    @g_eqeltri (syn_cwpphitfam F C) (syn_ccom (syn_cimage (syn_ccnv (syn_cwpppowlayerseq F C))) (syn_cimage (syn_csset))) (syn_cvv) p0000 p0006
  exact p0007

noncomputable def g_wpppostcompfn
    (F : Class) (hyp_wpppostcompfn_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (syn_wfn (syn_cwpppostcomp F) (syn_cvv)) := by
  let proofSupport : Finset Var := F.fv
  have p0000 :=
    @g_composefn
  have p0001 :=
    @g_fnconstg (syn_cvv) F (syn_cvv)
  have p0002 :=
    Nominal.mp hyp_wpppostcompfn_1 p0001
  have p0003 :=
    @g_f1ovi
  have p0004 :=
    @g_f1ofn (syn_cvv) (syn_cvv) (syn_cid)
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_pm3_2i (syn_wfn (syn_cxp (syn_cvv) (syn_csn F)) (syn_cvv)) (syn_wfn (syn_cid) (syn_cvv)) p0002 p0005
  have p0007 :=
    @g_fntxp (syn_cvv) (syn_cvv) (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid)
  have p0008 :=
    Nominal.mp p0006 p0007
  have p0009 :=
    @g_inidm (syn_cvv)
  have p0010 :=
    @g_fneq2i (syn_cin (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid)) p0009
  have p0011 :=
    @g_mpbi (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid)) (syn_cin (syn_cvv) (syn_cvv))) (syn_wfn (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid)) (syn_cvv)) p0008 p0010
  have p0012 :=
    @g_fncovv (syn_ccompose) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid)) p0000 p0011
  have p0013 :=
    (by simpa [syn_cwpppostcomp] using (Nominal.classEqRefl (syn_cwpppostcomp F)))
  have p0014 :=
    @g_fneq1i (syn_cvv) (syn_cwpppostcomp F) (syn_ccom (syn_ccompose) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid))) p0013
  have p0015 :=
    @g_mpbir (syn_wfn (syn_cwpppostcomp F) (syn_cvv)) (syn_wfn (syn_ccom (syn_ccompose) (syn_ctxp (syn_cxp (syn_cvv) (syn_csn F)) (syn_cid))) (syn_cvv)) p0012 p0014
  exact p0015

#print axioms g_wpppostcompfn

end NFChoice.DirectNominalPrf.WPPReplay
