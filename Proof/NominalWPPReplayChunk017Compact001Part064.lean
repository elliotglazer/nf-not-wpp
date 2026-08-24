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
import NominalWPPReplayChunk017Compact001Part063

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

noncomputable def g_wppstopgammaprefixeqndv
    (C : Class) (F : Class) (p : Var) (dv_C_p : p ∉ C.fv) (dv_F_p : p ∉ F.fv) (hyp_wppstopgammaprefixeqndv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppstopgammaprefixeqndv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_chwcards (syn_cvv)))) (hyp_wppstopgammaprefixeqndv_3 : Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv)))) (hyp_wppstopgammaprefixeqndv_4 : Nominal.NPrf (syn_wbr (syn_ctc C) (syn_clec) C)) (hyp_wppstopgammaprefixeqndv_5 : Nominal.NPrf (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm F))))) :
    Nominal.NPrf (.classEq (syn_cwppgamma (syn_cwppstopstep F (syn_ctc C)) (syn_ctc C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))) := by
  let proofSupport : Finset Var := C.fv ∪ F.fv ∪ ({p} : Finset Var)
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_p : y ≠ p := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_y : p ≠ y :=
    Ne.symm fresh_y_ne_p
  have dv_cache_0001 : p ∉ (C).fv := by
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ (F).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : p ≠ y := by
    clear dv_cache_0001 dv_cache_0002
    exact (show p ≠ y from (by exact fresh_p_ne_y))
  have dv_cache_0004 : y ∉ ((syn_cwppstopstep F C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_cwppstopstep F (syn_ctc C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, fresh_y_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_ctc C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_wppstopstepfunsndv C F hyp_wppstopgammaprefixeqndv_1 hyp_wppstopgammaprefixeqndv_2
  have p0001 :=
    @g_wppstopsteprndmndv C F hyp_wppstopgammaprefixeqndv_1 hyp_wppstopgammaprefixeqndv_2
  have p0002 :=
    @g_wppstopstepdmndv C F hyp_wppstopgammaprefixeqndv_1 hyp_wppstopgammaprefixeqndv_2
  have p0003 :=
    @g_wppstopstepfunsndv (syn_ctc C) F hyp_wppstopgammaprefixeqndv_1 hyp_wppstopgammaprefixeqndv_2
  have p0004 :=
    @g_wppstopsteprndmndv (syn_ctc C) F hyp_wppstopgammaprefixeqndv_1 hyp_wppstopgammaprefixeqndv_2
  have p0005 :=
    @g_wppstopstepdmndv (syn_ctc C) F hyp_wppstopgammaprefixeqndv_1 hyp_wppstopgammaprefixeqndv_2
  have p0006 :=
    @g_hwcardstcclndv C
  have p0007 :=
    Nominal.mp hyp_wppstopgammaprefixeqndv_3 p0006
  have p0008 :=
    @g_wppstopstepsamebelowdndv y C F p dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_wppstopgammaprefixeqndv_1 hyp_wppstopgammaprefixeqndv_2 hyp_wppstopgammaprefixeqndv_3 hyp_wppstopgammaprefixeqndv_4 hyp_wppstopgammaprefixeqndv_5
  have p0009 :=
    Nominal.gen p0008 y
  have p0010 :=
    (by simpa [syn_wb, syn_wral] using (Nominal.biimpRefl (syn_wral y (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc C)) (.classEq (syn_cfv (syn_cwppstopstep F C) (.cv y)) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (.cv y)))))))
  have p0011 :=
    @g_mpbir (syn_wral y (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc C)) (.classEq (syn_cfv (syn_cwppstopstep F C) (.cv y)) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (.cv y))))) (.all y (.imp (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc C)) (.classEq (syn_cfv (syn_cwppstopstep F C) (.cv y)) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (.cv y)))))) p0009 p0010
  have p0012 :=
    @g_wppgammaprefixeqhwselfmapndv y (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_ctc C) dv_cache_0004 dv_cache_0005 dv_cache_0006 p0000 p0001 p0002 p0003 p0004 p0005 p0007 p0011
  have p0013 :=
    @g_eqcomi (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppgamma (syn_cwppstopstep F (syn_ctc C)) (syn_ctc C)) p0012
  exact p0013

noncomputable def g_wpphitstartcongrndv
    (C : Class) (F : Class) (I : Class) (J : Class) :
    Nominal.NPrf (.imp (.classEq I J) (.classEq (syn_cwpphit F I C) (syn_cwpphit F J C))) := by
  let proofSupport : Finset Var := C.fv ∪ F.fv ∪ I.fv ∪ J.fv
  have p0000 :=
    @g_id (.classEq I J)
  have p0001 :=
    @g_eqid F
  have p0002 :=
    @g_jctil (.classEq I J) (.classEq I J) (.classEq F F) p0000 p0001
  have p0003 :=
    @g_freceq12 F F I J
  have p0004 :=
    @g_syl (.classEq I J) (syn_wa (.classEq F F) (.classEq I J)) (.classEq (syn_cfrec F I) (syn_cfrec F J)) p0002 p0003
  have p0005 :=
    @g_cnveqd (.classEq I J) (syn_cfrec F I) (syn_cfrec F J) p0004
  have p0006 :=
    @g_imaeq1d (.classEq I J) (syn_ccnv (syn_cfrec F I)) (syn_ccnv (syn_cfrec F J)) (syn_cima (syn_clec) (syn_csn C)) p0005
  have p0007 :=
    (by simpa [syn_cwpphit] using (Nominal.classEqRefl (syn_cwpphit F I C)))
  have p0008 :=
    (by simpa [syn_cwpphit] using (Nominal.classEqRefl (syn_cwpphit F J C)))
  have p0009 :=
    @g_n_3eqtr4g (.classEq I J) (syn_cima (syn_ccnv (syn_cfrec F I)) (syn_cima (syn_clec) (syn_csn C))) (syn_cima (syn_ccnv (syn_cfrec F J)) (syn_cima (syn_clec) (syn_csn C))) (syn_cwpphit F I C) (syn_cwpphit F J C) p0006 p0007 p0008
  exact p0009

noncomputable def g_wppcrossgammaleasthitpairhwndv
    (C : Class) (k : Var) (m : Var) (n : Var) (F : Class) (G : Class) (q : Var) (p : Var) (dv_C_k : k ∉ C.fv) (dv_C_m : m ∉ C.fv) (dv_C_n : n ∉ C.fv) (dv_C_p : p ∉ C.fv) (dv_C_q : q ∉ C.fv) (dv_F_k : k ∉ F.fv) (dv_F_m : m ∉ F.fv) (dv_F_n : n ∉ F.fv) (dv_F_p : p ∉ F.fv) (dv_F_q : q ∉ F.fv) (dv_G_k : k ∉ G.fv) (dv_G_m : m ∉ G.fv) (dv_G_n : n ∉ G.fv) (dv_G_p : p ∉ G.fv) (dv_G_q : q ∉ G.fv) (dv_k_m : k ≠ m) (dv_k_n : k ≠ n) (dv_k_p : k ≠ p) (dv_k_q : k ≠ q) (dv_m_n : m ≠ n) (dv_m_p : m ≠ p) (dv_m_q : m ≠ q) (dv_n_p : n ≠ p) (dv_n_q : n ≠ q) (dv_p_q : p ≠ q) (hyp_wppcrossgammaleasthitpairhwndv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppcrossgammaleasthitpairhwndv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) (hyp_wppcrossgammaleasthitpairhwndv_3 : Nominal.NPrf (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm F))))) (hyp_wppcrossgammaleasthitpairhwndv_4 : Nominal.NPrf (.classMem G (syn_cfuns))) (hyp_wppcrossgammaleasthitpairhwndv_5 : Nominal.NPrf (syn_wss (syn_crn G) (syn_cdm G))) (hyp_wppcrossgammaleasthitpairhwndv_6 : Nominal.NPrf (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) (syn_ctc C)) (.classMem (.cv p) (syn_cdm G))))) (hyp_wppcrossgammaleasthitpairhwndv_7 : Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv)))) (hyp_wppcrossgammaleasthitpairhwndv_8 : Nominal.NPrf (.classEq (syn_ctc (syn_cwppgamma F C)) (syn_cwppgamma G (syn_ctc C)))) :
    Nominal.NPrf (syn_wa (syn_wrex m (syn_cnnc) (syn_wa (.classMem (.cv m) (syn_cwpphit F (syn_cwppgamma F C) C)) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F (syn_cwppgamma F C) C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wrex k (syn_cnnc) (syn_wa (.classMem (.cv k) (syn_cwpphit G (syn_ctc (syn_cwppgamma F C)) (syn_ctc C))) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G (syn_ctc (syn_cwppgamma F C)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q))))))) := by
  let proofSupport : Finset Var := C.fv ∪ ({k} : Finset Var) ∪ ({m} : Finset Var) ∪ ({n} : Finset Var) ∪ F.fv ∪ G.fv ∪ ({q} : Finset Var) ∪ ({p} : Finset Var)
  have dv_cache_0001 : m ∉ (C).fv := by
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : n ∉ (C).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : p ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : m ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : n ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : p ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : m ≠ n := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show m ≠ n from (by exact dv_m_n))
  have dv_cache_0008 : k ∉ ((syn_ctc C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : q ∉ ((syn_ctc C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : p ∉ ((syn_ctc C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : k ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_G_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : q ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_G_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : p ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_G_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : k ≠ q := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show k ≠ q from (by exact dv_k_q))
  have p0000 :=
    @g_wppgammaleasthithwndv C m n F p dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 hyp_wppcrossgammaleasthitpairhwndv_1 hyp_wppcrossgammaleasthitpairhwndv_2 hyp_wppcrossgammaleasthitpairhwndv_3 hyp_wppcrossgammaleasthitpairhwndv_7
  have p0001 :=
    @g_hwcardstcclndv C
  have p0002 :=
    Nominal.mp hyp_wppcrossgammaleasthitpairhwndv_7 p0001
  have p0003 :=
    @g_wppgammaleasthithwndv (syn_ctc C) k q G p dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 hyp_wppcrossgammaleasthitpairhwndv_4 hyp_wppcrossgammaleasthitpairhwndv_5 hyp_wppcrossgammaleasthitpairhwndv_6 p0002
  have p0004 :=
    @g_eqcomi (syn_ctc (syn_cwppgamma F C)) (syn_cwppgamma G (syn_ctc C)) hyp_wppcrossgammaleasthitpairhwndv_8
  have p0005 :=
    @g_wpphitstartcongrndv (syn_ctc C) G (syn_cwppgamma G (syn_ctc C)) (syn_ctc (syn_cwppgamma F C))
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_eleq2i (syn_cwpphit G (syn_cwppgamma G (syn_ctc C)) (syn_ctc C)) (syn_cwpphit G (syn_ctc (syn_cwppgamma F C)) (syn_ctc C)) (.cv k) p0006
  have p0008 :=
    @g_eqcomi (syn_ctc (syn_cwppgamma F C)) (syn_cwppgamma G (syn_ctc C)) hyp_wppcrossgammaleasthitpairhwndv_8
  have p0009 :=
    @g_wpphitstartcongrndv (syn_ctc C) G (syn_cwppgamma G (syn_ctc C)) (syn_ctc (syn_cwppgamma F C))
  have p0010 :=
    Nominal.mp p0008 p0009
  have p0011 :=
    @g_eleq2i (syn_cwpphit G (syn_cwppgamma G (syn_ctc C)) (syn_ctc C)) (syn_cwpphit G (syn_ctc (syn_cwppgamma F C)) (syn_ctc C)) (.cv q) p0010
  have p0012 :=
    @g_imbi1i (.classMem (.cv q) (syn_cwpphit G (syn_cwppgamma G (syn_ctc C)) (syn_ctc C))) (.classMem (.cv q) (syn_cwpphit G (syn_ctc (syn_cwppgamma F C)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)) p0011
  have p0013 :=
    @g_ralbii (.imp (.classMem (.cv q) (syn_cwpphit G (syn_cwppgamma G (syn_ctc C)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q))) (.imp (.classMem (.cv q) (syn_cwpphit G (syn_ctc (syn_cwppgamma F C)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q))) q (syn_cnnc) p0012
  have p0014 :=
    @g_anbi12i (.classMem (.cv k) (syn_cwpphit G (syn_cwppgamma G (syn_ctc C)) (syn_ctc C))) (.classMem (.cv k) (syn_cwpphit G (syn_ctc (syn_cwppgamma F C)) (syn_ctc C))) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G (syn_cwppgamma G (syn_ctc C)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G (syn_ctc (syn_cwppgamma F C)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))) p0007 p0013
  have p0015 :=
    @g_rexbii (syn_wa (.classMem (.cv k) (syn_cwpphit G (syn_cwppgamma G (syn_ctc C)) (syn_ctc C))) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G (syn_cwppgamma G (syn_ctc C)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q))))) (syn_wa (.classMem (.cv k) (syn_cwpphit G (syn_ctc (syn_cwppgamma F C)) (syn_ctc C))) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G (syn_ctc (syn_cwppgamma F C)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q))))) k (syn_cnnc) p0014
  have p0016 :=
    @g_mpbi (syn_wrex k (syn_cnnc) (syn_wa (.classMem (.cv k) (syn_cwpphit G (syn_cwppgamma G (syn_ctc C)) (syn_ctc C))) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G (syn_cwppgamma G (syn_ctc C)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) (syn_wrex k (syn_cnnc) (syn_wa (.classMem (.cv k) (syn_cwpphit G (syn_ctc (syn_cwppgamma F C)) (syn_ctc C))) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G (syn_ctc (syn_cwppgamma F C)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) p0003 p0015
  have p0017 :=
    @g_pm3_2i (syn_wrex m (syn_cnnc) (syn_wa (.classMem (.cv m) (syn_cwpphit F (syn_cwppgamma F C) C)) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F (syn_cwppgamma F C) C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wrex k (syn_cnnc) (syn_wa (.classMem (.cv k) (syn_cwpphit G (syn_ctc (syn_cwppgamma F C)) (syn_ctc C))) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit G (syn_ctc (syn_cwppgamma F C)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))) p0000 p0016
  exact p0017

noncomputable def g_wppstopgammaleasthitpairndv
    (x : Var) (C : Class) (k : Var) (m : Var) (n : Var) (F : Class) (q : Var) (dv_C_k : k ∉ C.fv) (dv_C_m : m ∉ C.fv) (dv_C_n : n ∉ C.fv) (dv_C_q : q ∉ C.fv) (dv_C_x : x ∉ C.fv) (dv_F_k : k ∉ F.fv) (dv_F_m : m ∉ F.fv) (dv_F_n : n ∉ F.fv) (dv_F_q : q ∉ F.fv) (dv_F_x : x ∉ F.fv) (dv_k_m : k ≠ m) (dv_k_n : k ≠ n) (dv_k_q : k ≠ q) (dv_k_x : k ≠ x) (dv_m_n : m ≠ n) (dv_m_q : m ≠ q) (dv_m_x : m ≠ x) (dv_n_q : n ≠ q) (dv_n_x : n ≠ x) (dv_q_x : q ≠ x) (hyp_wppstopgammaleasthitpairndv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppstopgammaleasthitpairndv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_chwcards (syn_cvv)))) (hyp_wppstopgammaleasthitpairndv_3 : Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv)))) (hyp_wppstopgammaleasthitpairndv_4 : Nominal.NPrf (syn_wral x (syn_cdm (syn_cwppstopstep F C)) (.classEq (syn_ctc (syn_cfv (syn_cwppstopstep F C) (.cv x))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (.cv x)))))) :
    Nominal.NPrf (syn_wa (syn_wrex m (syn_cnnc) (syn_wa (.classMem (.cv m) (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wrex k (syn_cnnc) (syn_wa (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C))) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q))))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ C.fv ∪ ({k} : Finset Var) ∪ ({m} : Finset Var) ∪ ({n} : Finset Var) ∪ F.fv ∪ ({q} : Finset Var)
  let p : Var := freshVar proofSupport 0
  let r : Var := freshVar proofSupport 1
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_ne_x : p ≠ x := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_p : x ≠ p :=
    Ne.symm fresh_p_ne_x
  have fresh_p_not_C : p ∉ C.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_p_ne_k : p ≠ k := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_k_ne_p : k ≠ p :=
    Ne.symm fresh_p_ne_k
  have fresh_p_ne_m : p ≠ m := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_m_ne_p : m ≠ p :=
    Ne.symm fresh_p_ne_m
  have fresh_p_ne_n : p ≠ n := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_n_ne_p : n ≠ p :=
    Ne.symm fresh_p_ne_n
  have fresh_p_not_F : p ∉ F.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_ne_q : p ≠ q := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_p : q ≠ p :=
    Ne.symm fresh_p_ne_q
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_r_ne_x : r ≠ x := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_r : x ≠ r :=
    Ne.symm fresh_r_ne_x
  have fresh_r_not_C : r ∉ C.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_r_ne_k : r ≠ k := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_k_ne_r : k ≠ r :=
    Ne.symm fresh_r_ne_k
  have fresh_r_ne_m : r ≠ m := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_m_ne_r : m ≠ r :=
    Ne.symm fresh_r_ne_m
  have fresh_r_ne_n : r ≠ n := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_n_ne_r : n ≠ r :=
    Ne.symm fresh_r_ne_n
  have fresh_r_not_F : r ∉ F.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_ne_q : r ≠ q := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_r : q ≠ r :=
    Ne.symm fresh_r_ne_q
  have fresh_p_ne_r : p ≠ r := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_r_ne_p : r ≠ p :=
    Ne.symm fresh_p_ne_r
  have dv_cache_0001 : r ∉ ((syn_chwcards (syn_cvv))).fv := by
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : p ≠ r := by
    clear dv_cache_0001
    exact (show p ≠ r from (by exact fresh_p_ne_r))
  have dv_cache_0003 : p ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : r ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : p ∉ ((syn_cwppstopstep F C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_C, fresh_p_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : r ∉ ((syn_cwppstopstep F C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_C, fresh_r_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_cwppstopstep F C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_x, dv_F_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : p ∉ ((syn_cwppstopstep F (syn_ctc C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_C, fresh_p_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : r ∉ ((syn_cwppstopstep F (syn_ctc C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_C, fresh_r_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((syn_cwppstopstep F (syn_ctc C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_x, dv_F_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : p ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show p ≠ x from (by exact fresh_p_ne_x))
  have dv_cache_0013 : r ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0014 : k ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : m ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : n ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : q ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : k ∉ ((syn_cwppstopstep F C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_k, dv_F_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : m ∉ ((syn_cwppstopstep F C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_m, dv_F_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : n ∉ ((syn_cwppstopstep F C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_n, dv_F_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : q ∉ ((syn_cwppstopstep F C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_q, dv_F_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : k ∉ ((syn_cwppstopstep F (syn_ctc C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_k, dv_F_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : m ∉ ((syn_cwppstopstep F (syn_ctc C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_m, dv_F_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : n ∉ ((syn_cwppstopstep F (syn_ctc C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_n, dv_F_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : q ∉ ((syn_cwppstopstep F (syn_ctc C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_q, dv_F_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : k ≠ m := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (show k ≠ m from (by exact dv_k_m))
  have dv_cache_0027 : k ≠ n := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (show k ≠ n from (by exact dv_k_n))
  have dv_cache_0028 : k ≠ p := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (show k ≠ p from (by exact fresh_k_ne_p))
  have dv_cache_0029 : k ≠ q := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (show k ≠ q from (by exact dv_k_q))
  have dv_cache_0030 : m ≠ n := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (show m ≠ n from (by exact dv_m_n))
  have dv_cache_0031 : m ≠ p := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (show m ≠ p from (by exact fresh_m_ne_p))
  have dv_cache_0032 : m ≠ q := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (show m ≠ q from (by exact dv_m_q))
  have dv_cache_0033 : n ≠ p := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (show n ≠ p from (by exact fresh_n_ne_p))
  have dv_cache_0034 : n ≠ q := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (show n ≠ q from (by exact dv_n_q))
  have dv_cache_0035 : p ≠ q := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact (show p ≠ q from (by exact fresh_p_ne_q))
  have p0000 :=
    @g_wppstopstepfunsndv C F hyp_wppstopgammaleasthitpairndv_1 hyp_wppstopgammaleasthitpairndv_2
  have p0001 :=
    @g_wppstopsteprndmndv C F hyp_wppstopgammaleasthitpairndv_1 hyp_wppstopgammaleasthitpairndv_2
  have p0002 :=
    @g_wppstopstepdmndv C F hyp_wppstopgammaleasthitpairndv_1 hyp_wppstopgammaleasthitpairndv_2
  have p0003 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F C)) (syn_chwcards (syn_cvv)) (.cv p) p0002
  have p0004 :=
    @g_biimpri (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (.classMem (.cv p) (syn_chwcards (syn_cvv))) p0003
  have p0005 :=
    Nominal.gen p0004 p
  have p0006 :=
    (by simpa [syn_wb, syn_wral] using (Nominal.biimpRefl (syn_wral p (syn_chwcards (syn_cvv)) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))))))
  have p0007 :=
    @g_mpbir (syn_wral p (syn_chwcards (syn_cvv)) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C)))) (.all p (.imp (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))))) p0005 p0006
  have p0008 :=
    Nominal.ax1 (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (syn_wbr (.cv p) (syn_clec) C)
  have p0009 :=
    @g_a1i (.imp (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))))) (.classMem (.cv p) (syn_chwcards (syn_cvv))) p0008
  have p0010 :=
    @g_ralimia (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C)))) p (syn_chwcards (syn_cvv)) p0009
  have p0011 :=
    Nominal.mp p0007 p0010
  have p0012 :=
    @g_wppstopstepfunsndv (syn_ctc C) F hyp_wppstopgammaleasthitpairndv_1 hyp_wppstopgammaleasthitpairndv_2
  have p0013 :=
    @g_wppstopsteprndmndv (syn_ctc C) F hyp_wppstopgammaleasthitpairndv_1 hyp_wppstopgammaleasthitpairndv_2
  have p0014 :=
    @g_wppstopstepdmndv (syn_ctc C) F hyp_wppstopgammaleasthitpairndv_1 hyp_wppstopgammaleasthitpairndv_2
  have p0015 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F (syn_ctc C))) (syn_chwcards (syn_cvv)) (.cv p) p0014
  have p0016 :=
    @g_biimpri (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) (.classMem (.cv p) (syn_chwcards (syn_cvv))) p0015
  have p0017 :=
    Nominal.gen p0016 p
  have p0018 :=
    (by simpa [syn_wb, syn_wral] using (Nominal.biimpRefl (syn_wral p (syn_chwcards (syn_cvv)) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))))))
  have p0019 :=
    @g_mpbir (syn_wral p (syn_chwcards (syn_cvv)) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F (syn_ctc C))))) (.all p (.imp (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))))) p0017 p0018
  have p0020 :=
    Nominal.ax1 (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) (syn_wbr (.cv p) (syn_clec) (syn_ctc C))
  have p0021 :=
    @g_a1i (.imp (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) (.imp (syn_wbr (.cv p) (syn_clec) (syn_ctc C)) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))))) (.classMem (.cv p) (syn_chwcards (syn_cvv))) p0020
  have p0022 :=
    @g_ralimia (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) (.imp (syn_wbr (.cv p) (syn_clec) (syn_ctc C)) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F (syn_ctc C))))) p (syn_chwcards (syn_cvv)) p0021
  have p0023 :=
    Nominal.mp p0019 p0022
  have p0024 :=
    @g_wppstopstepfunsndv C F hyp_wppstopgammaleasthitpairndv_1 hyp_wppstopgammaleasthitpairndv_2
  have p0025 :=
    @g_wppstopsteprndmndv C F hyp_wppstopgammaleasthitpairndv_1 hyp_wppstopgammaleasthitpairndv_2
  have p0026 :=
    @g_wppstopstepfunsndv (syn_ctc C) F hyp_wppstopgammaleasthitpairndv_1 hyp_wppstopgammaleasthitpairndv_2
  have p0027 :=
    @g_wppstopsteprndmndv (syn_ctc C) F hyp_wppstopgammaleasthitpairndv_1 hyp_wppstopgammaleasthitpairndv_2
  have p0028 :=
    @g_wppstopstepdmndv C F hyp_wppstopgammaleasthitpairndv_1 hyp_wppstopgammaleasthitpairndv_2
  have p0029 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F C)) (syn_chwcards (syn_cvv)) (.cv p) p0028
  have p0030 :=
    @g_biimpri (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (.classMem (.cv p) (syn_chwcards (syn_cvv))) p0029
  have p0031 :=
    @g_hwcardstcclndv (.cv p)
  have p0032 :=
    @g_wppstopstepdmndv (syn_ctc C) F hyp_wppstopgammaleasthitpairndv_1 hyp_wppstopgammaleasthitpairndv_2
  have p0033 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F (syn_ctc C))) (syn_chwcards (syn_cvv)) (syn_ctc (.cv p)) p0032
  have p0034 :=
    @g_sylibr (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (syn_ctc (.cv p)) (syn_chwcards (syn_cvv))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) p0031 p0033
  have p0035 :=
    @g_jca (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) p0030 p0034
  have p0036 :=
    Nominal.gen p0035 p
  have p0037 :=
    (by simpa [syn_wb, syn_wral] using (Nominal.biimpRefl (syn_wral p (syn_chwcards (syn_cvv)) (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppstopstep F (syn_ctc C))))))))
  have p0038 :=
    @g_mpbir (syn_wral p (syn_chwcards (syn_cvv)) (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))))) (.all p (.imp (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppstopstep F (syn_ctc C))))))) p0036 p0037
  have p0039 :=
    Nominal.ax1 (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppstopstep F (syn_ctc C))))) (syn_wbr (.cv p) (syn_clec) C)
  have p0040 :=
    @g_a1i (.imp (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppstopstep F (syn_ctc C))))) (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppstopstep F (syn_ctc C))))))) (.classMem (.cv p) (syn_chwcards (syn_cvv))) p0039
  have p0041 :=
    @g_ralimia (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppstopstep F (syn_ctc C))))) (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))))) p (syn_chwcards (syn_cvv)) p0040
  have p0042 :=
    Nominal.mp p0038 p0041
  have p0043 :=
    @g_wppstopstepfunsndv C F hyp_wppstopgammaleasthitpairndv_1 hyp_wppstopgammaleasthitpairndv_2
  have p0044 :=
    @g_a1i (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc))) p0043
  have p0045 :=
    @g_simpl (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc))
  have p0046 :=
    @g_wppstopstepdmndv C F hyp_wppstopgammaleasthitpairndv_1 hyp_wppstopgammaleasthitpairndv_2
  have p0047 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F C)) (syn_chwcards (syn_cvv)) (.cv p) p0046
  have p0048 :=
    @g_biimpri (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (.classMem (.cv p) (syn_chwcards (syn_cvv))) p0047
  have p0049 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc))) (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) p0045 p0048
  have p0050 :=
    @g_wppstopsteprndmndv C F hyp_wppstopgammaleasthitpairndv_1 hyp_wppstopgammaleasthitpairndv_2
  have p0051 :=
    @g_a1i (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))) (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc))) p0050
  have p0052 :=
    @g_n_3jca (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc))) (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))) p0044 p0049 p0051
  have p0053 :=
    @g_simpr (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc))
  have p0054 :=
    @g_jca (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc))) (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (.classMem (.cv r) (syn_cnnc)) p0052 p0053
  have p0055 :=
    @g_frecdomfv (syn_cwppstopstep F C) (.cv p) (.cv r)
  have p0056 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc))) (syn_wa (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (.classMem (.cv r) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cdm (syn_cwppstopstep F C))) p0054 p0055
  have p0057 :=
    @g_wppstopstepdmndv C F hyp_wppstopgammaleasthitpairndv_1 hyp_wppstopgammaleasthitpairndv_2
  have p0058 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F C)) (syn_chwcards (syn_cvv)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) p0057
  have p0059 :=
    @g_sylib (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cdm (syn_cwppstopstep F C))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_chwcards (syn_cvv))) p0056 p0058
  have p0060 :=
    @g_hwcardssnc (syn_cvv)
  have p0061 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) p0060
  have p0062 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_chwcards (syn_cvv))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs)) p0059 p0061
  have p0063 :=
    @g_rgen2 (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs)) p r (syn_chwcards (syn_cvv)) (syn_cnnc) dv_cache_0001 dv_cache_0002 p0062
  have p0064 :=
    Nominal.ax1 (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs))) (syn_wbr (.cv p) (syn_clec) C)
  have p0065 :=
    @g_a1i (.imp (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs))) (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs))))) (.classMem (.cv p) (syn_chwcards (syn_cvv))) p0064
  have p0066 :=
    @g_ralimia (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs))) (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs)))) p (syn_chwcards (syn_cvv)) p0065
  have p0067 :=
    Nominal.mp p0063 p0066
  have p0068 :=
    @g_wppgammatchwboundedeqndv x C (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) r p dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0002 dv_cache_0012 dv_cache_0013 p0024 p0025 p0026 p0027 hyp_wppstopgammaleasthitpairndv_4 p0042 p0067 hyp_wppstopgammaleasthitpairndv_3
  have p0069 :=
    @g_wppcrossgammaleasthitpairhwndv C k m n (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) q p dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0003 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0006 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0009 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 p0000 p0001 p0011 p0012 p0013 p0023 hyp_wppstopgammaleasthitpairndv_3 p0068
  exact p0069

#print axioms g_wppstopgammaleasthitpairndv

end NFChoice.DirectNominalPrf.WPPReplay
