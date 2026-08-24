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
import NominalWPPReplayChunk017Compact001Part066

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

noncomputable def g_wppstopfixedhitcontrgrowfixdndv
    (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var) (C : Class) (k : Var) (m : Var) (n : Var) (F : Class) (I : Class) (p : Var) (dv_C_k : k ∉ C.fv) (dv_C_m : m ∉ C.fv) (dv_C_n : n ∉ C.fv) (dv_C_p : p ∉ C.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_F_k : k ∉ F.fv) (dv_F_m : m ∉ F.fv) (dv_F_n : n ∉ F.fv) (dv_F_p : p ∉ F.fv) (dv_F_x : x ∉ F.fv) (dv_F_y : y ∉ F.fv) (dv_I_k : k ∉ I.fv) (dv_I_m : m ∉ I.fv) (dv_I_n : n ∉ I.fv) (dv_I_p : p ∉ I.fv) (dv_I_x : x ∉ I.fv) (dv_I_y : y ∉ I.fv) (dv_ch_n : n ∉ ch.fv) (dv_ch_p : p ∉ ch.fv) (dv_ch_x : x ∉ ch.fv) (dv_ch_y : y ∉ ch.fv) (dv_k_m : k ≠ m) (dv_k_n : k ≠ n) (dv_k_p : k ≠ p) (dv_k_x : k ≠ x) (dv_k_y : k ≠ y) (dv_m_n : m ≠ n) (dv_m_p : m ≠ p) (dv_m_x : m ≠ x) (dv_m_y : m ≠ y) (dv_n_p : n ≠ p) (dv_n_ph : n ∉ ph.fv) (dv_n_ps : n ∉ ps.fv) (dv_n_x : n ≠ x) (dv_n_y : n ≠ y) (dv_p_ph : p ∉ ph.fv) (dv_p_ps : p ∉ ps.fv) (dv_p_x : p ≠ x) (dv_p_y : p ≠ y) (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv) (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv) (dv_x_y : x ≠ y) (hyp_wppstopfixedhitcontrgrowfixdndv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppstopfixedhitcontrgrowfixdndv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_chwcards (syn_cvv)))) (hyp_wppstopfixedhitcontrgrowfixdndv_3 : Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv)))) (hyp_wppstopfixedhitcontrgrowfixdndv_4 : Nominal.NPrf (syn_wbr (syn_ctc C) (syn_clec) C)) (hyp_wppstopfixedhitcontrgrowfixdndv_5 : Nominal.NPrf (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm F))))) (hyp_wppstopfixedhitcontrgrowfixdndv_6 : Nominal.NPrf (syn_wral x (syn_cdm (syn_cwppstopstep F C)) (.classEq (syn_ctc (syn_cfv (syn_cwppstopstep F C) (.cv x))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (.cv x)))))) (hyp_wppstopfixedhitcontrgrowfixdndv_7 : Nominal.NPrf (.classMem I (syn_chwcards (syn_cvv)))) (hyp_wppstopfixedhitcontrgrowfixdndv_9 : Nominal.NPrf (syn_wral y (syn_chwcards (syn_cvv)) (.imp (syn_wbr C (syn_clec) (.cv y)) (syn_wne (.cv y) (syn_ctc (.cv y)))))) (hyp_wppstopfixedhitcontrgrowfixdndv_10 : Nominal.NPrf (.imp ph (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv m) (syn_cwpphit (syn_cwppstopstep F C) I C)) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) I C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))))))) (hyp_wppstopfixedhitcontrgrowfixdndv_11 : Nominal.NPrf (.imp ps (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc I) (syn_ctc C))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc I) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))))) (hyp_wppstopfixedhitcontrgrowfixdndv_12 : Nominal.NPrf (.imp ch (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))))) :
    Nominal.NPrf (.imp (.classEq I (syn_ctc I)) (.imp (syn_wa ph (syn_wa ps ch)) (.neg (.classEq (syn_c0c) (syn_c0c))))) := by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ C.fv ∪ ({k} : Finset Var) ∪ ({m} : Finset Var) ∪ ({n} : Finset Var) ∪ F.fv ∪ I.fv ∪ ({p} : Finset Var)
  let q : Var := freshVar proofSupport 0
  let r : Var := freshVar proofSupport 1
  let s : Var := freshVar proofSupport 2
  let d : Var := freshVar proofSupport 3
  let a : Var := freshVar proofSupport 4
  let z : Var := freshVar proofSupport 5
  let b : Var := freshVar proofSupport 6
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_ph : q ∉ ph.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))))))))
  have fresh_q_not_ps : q ∉ ps.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))))))))
  have fresh_q_not_ch : q ∉ ch.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))))))
  have fresh_q_ne_x : q ≠ x := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))))
  have fresh_x_ne_q : x ≠ q :=
    Ne.symm fresh_q_ne_x
  have fresh_q_ne_y : q ≠ y := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))))
  have fresh_y_ne_q : y ≠ q :=
    Ne.symm fresh_q_ne_y
  have fresh_q_not_C : q ∉ C.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))))
  have fresh_q_ne_k : q ≠ k := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_k_ne_q : k ≠ q :=
    Ne.symm fresh_q_ne_k
  have fresh_q_ne_m : q ≠ m := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_m_ne_q : m ≠ q :=
    Ne.symm fresh_q_ne_m
  have fresh_q_ne_n : q ≠ n := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_n_ne_q : n ≠ q :=
    Ne.symm fresh_q_ne_n
  have fresh_q_not_F : q ∉ F.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_q_not_I : q ∉ I.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_ne_p : q ≠ p := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_q : p ≠ q :=
    Ne.symm fresh_q_ne_p
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_r_not_ph : r ∉ ph.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))))))))
  have fresh_r_not_ps : r ∉ ps.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))))))))
  have fresh_r_not_ch : r ∉ ch.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))))))
  have fresh_r_ne_x : r ≠ x := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))))
  have fresh_x_ne_r : x ≠ r :=
    Ne.symm fresh_r_ne_x
  have fresh_r_ne_y : r ≠ y := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))))
  have fresh_y_ne_r : y ≠ r :=
    Ne.symm fresh_r_ne_y
  have fresh_r_not_C : r ∉ C.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))))
  have fresh_r_ne_k : r ≠ k := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_k_ne_r : k ≠ r :=
    Ne.symm fresh_r_ne_k
  have fresh_r_ne_m : r ≠ m := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_m_ne_r : m ≠ r :=
    Ne.symm fresh_r_ne_m
  have fresh_r_ne_n : r ≠ n := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_n_ne_r : n ≠ r :=
    Ne.symm fresh_r_ne_n
  have fresh_r_not_F : r ∉ F.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_r_not_I : r ∉ I.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_ne_p : r ≠ p := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_r : p ≠ r :=
    Ne.symm fresh_r_ne_p
  have fresh_s : s ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_s_not_ph : s ∉ ph.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))))))))
  have fresh_s_not_ps : s ∉ ps.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))))))))
  have fresh_s_not_ch : s ∉ ch.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))))))
  have fresh_s_ne_x : s ≠ x := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))))
  have fresh_x_ne_s : x ≠ s :=
    Ne.symm fresh_s_ne_x
  have fresh_s_ne_y : s ≠ y := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))))
  have fresh_y_ne_s : y ≠ s :=
    Ne.symm fresh_s_ne_y
  have fresh_s_not_C : s ∉ C.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))))
  have fresh_s_ne_k : s ≠ k := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_k_ne_s : k ≠ s :=
    Ne.symm fresh_s_ne_k
  have fresh_s_ne_m : s ≠ m := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_m_ne_s : m ≠ s :=
    Ne.symm fresh_s_ne_m
  have fresh_s_ne_n : s ≠ n := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_n_ne_s : n ≠ s :=
    Ne.symm fresh_s_ne_n
  have fresh_s_not_F : s ∉ F.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_s_not_I : s ∉ I.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_s_ne_p : s ≠ p := by
    intro h
    exact fresh_s (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_s : p ≠ s :=
    Ne.symm fresh_s_ne_p
  have fresh_d : d ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_d_not_ph : d ∉ ph.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))))))))
  have fresh_d_not_ps : d ∉ ps.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))))))))
  have fresh_d_not_ch : d ∉ ch.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))))))
  have fresh_d_ne_x : d ≠ x := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))))
  have fresh_x_ne_d : x ≠ d :=
    Ne.symm fresh_d_ne_x
  have fresh_d_ne_y : d ≠ y := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))))
  have fresh_y_ne_d : y ≠ d :=
    Ne.symm fresh_d_ne_y
  have fresh_d_not_C : d ∉ C.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))))
  have fresh_d_ne_k : d ≠ k := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_k_ne_d : k ≠ d :=
    Ne.symm fresh_d_ne_k
  have fresh_d_ne_m : d ≠ m := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_m_ne_d : m ≠ d :=
    Ne.symm fresh_d_ne_m
  have fresh_d_ne_n : d ≠ n := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_n_ne_d : n ≠ d :=
    Ne.symm fresh_d_ne_n
  have fresh_d_not_F : d ∉ F.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_d_not_I : d ∉ I.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_ne_p : d ≠ p := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_d : p ≠ d :=
    Ne.symm fresh_d_ne_p
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_a_not_ph : a ∉ ph.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))))))))
  have fresh_a_not_ps : a ∉ ps.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))))))))
  have fresh_a_not_ch : a ∉ ch.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))))))
  have fresh_a_ne_x : a ≠ x := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))))
  have fresh_x_ne_a : x ≠ a :=
    Ne.symm fresh_a_ne_x
  have fresh_a_ne_y : a ≠ y := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))))
  have fresh_y_ne_a : y ≠ a :=
    Ne.symm fresh_a_ne_y
  have fresh_a_not_C : a ∉ C.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))))
  have fresh_a_ne_k : a ≠ k := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_k_ne_a : k ≠ a :=
    Ne.symm fresh_a_ne_k
  have fresh_a_ne_m : a ≠ m := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_m_ne_a : m ≠ a :=
    Ne.symm fresh_a_ne_m
  have fresh_a_ne_n : a ≠ n := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_n_ne_a : n ≠ a :=
    Ne.symm fresh_a_ne_n
  have fresh_a_not_F : a ∉ F.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a_not_I : a ∉ I.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_ne_p : a ≠ p := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_a : p ≠ a :=
    Ne.symm fresh_a_ne_p
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))))))))
  have fresh_z_not_ps : z ∉ ps.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))))))))
  have fresh_z_not_ch : z ∉ ch.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))))))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))))
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))))
  have fresh_z_ne_k : z ≠ k := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_k_ne_z : k ≠ z :=
    Ne.symm fresh_z_ne_k
  have fresh_z_ne_m : z ≠ m := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_m_ne_z : m ≠ z :=
    Ne.symm fresh_z_ne_m
  have fresh_z_ne_n : z ≠ n := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_n_ne_z : n ≠ z :=
    Ne.symm fresh_z_ne_n
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_I : z ∉ I.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_ne_p : z ≠ p := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_z : p ≠ z :=
    Ne.symm fresh_z_ne_p
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_b_not_ph : b ∉ ph.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))))))))
  have fresh_b_not_ps : b ∉ ps.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))))))))
  have fresh_b_not_ch : b ∉ ch.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))))))
  have fresh_b_ne_x : b ≠ x := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))))
  have fresh_x_ne_b : x ≠ b :=
    Ne.symm fresh_b_ne_x
  have fresh_b_ne_y : b ≠ y := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))))
  have fresh_y_ne_b : y ≠ b :=
    Ne.symm fresh_b_ne_y
  have fresh_b_not_C : b ∉ C.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))))
  have fresh_b_ne_k : b ≠ k := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_k_ne_b : k ≠ b :=
    Ne.symm fresh_b_ne_k
  have fresh_b_ne_m : b ≠ m := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_m_ne_b : m ≠ b :=
    Ne.symm fresh_b_ne_m
  have fresh_b_ne_n : b ≠ n := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_n_ne_b : n ≠ b :=
    Ne.symm fresh_b_ne_n
  have fresh_b_not_F : b ∉ F.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_b_not_I : b ∉ I.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_ne_p : b ≠ p := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_b : p ≠ b :=
    Ne.symm fresh_b_ne_p
  have fresh_q_ne_r : q ≠ r := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_r_ne_q : r ≠ q :=
    Ne.symm fresh_q_ne_r
  have fresh_q_ne_s : q ≠ s := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_s_ne_q : s ≠ q :=
    Ne.symm fresh_q_ne_s
  have fresh_q_ne_d : q ≠ d := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_d_ne_q : d ≠ q :=
    Ne.symm fresh_q_ne_d
  have fresh_q_ne_a : q ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_a_ne_q : a ≠ q :=
    Ne.symm fresh_q_ne_a
  have fresh_q_ne_z : q ≠ z := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_z_ne_q : z ≠ q :=
    Ne.symm fresh_q_ne_z
  have fresh_q_ne_b : q ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_b_ne_q : b ≠ q :=
    Ne.symm fresh_q_ne_b
  have fresh_r_ne_s : r ≠ s := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_s_ne_r : s ≠ r :=
    Ne.symm fresh_r_ne_s
  have fresh_r_ne_d : r ≠ d := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_d_ne_r : d ≠ r :=
    Ne.symm fresh_r_ne_d
  have fresh_r_ne_a : r ≠ a := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_a_ne_r : a ≠ r :=
    Ne.symm fresh_r_ne_a
  have fresh_r_ne_z : r ≠ z := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_z_ne_r : z ≠ r :=
    Ne.symm fresh_r_ne_z
  have fresh_r_ne_b : r ≠ b := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_b_ne_r : b ≠ r :=
    Ne.symm fresh_r_ne_b
  have fresh_s_ne_d : s ≠ d := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_d_ne_s : d ≠ s :=
    Ne.symm fresh_s_ne_d
  have fresh_s_ne_a : s ≠ a := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_a_ne_s : a ≠ s :=
    Ne.symm fresh_s_ne_a
  have fresh_s_ne_z : s ≠ z := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_z_ne_s : z ≠ s :=
    Ne.symm fresh_s_ne_z
  have fresh_s_ne_b : s ≠ b := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_b_ne_s : b ≠ s :=
    Ne.symm fresh_s_ne_b
  have fresh_d_ne_a : d ≠ a := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_a_ne_d : a ≠ d :=
    Ne.symm fresh_d_ne_a
  have fresh_d_ne_z : d ≠ z := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_z_ne_d : z ≠ d :=
    Ne.symm fresh_d_ne_z
  have fresh_d_ne_b : d ≠ b := by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_b_ne_d : b ≠ d :=
    Ne.symm fresh_d_ne_b
  have fresh_a_ne_z : a ≠ z := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_z_ne_a : z ≠ a :=
    Ne.symm fresh_a_ne_z
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have fresh_z_ne_b : z ≠ b := by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_b_ne_z : b ≠ z :=
    Ne.symm fresh_z_ne_b
  have dv_cache_0001 : n ∉ ((syn_wa (.classEq I (syn_ctc I)) ph)).fv := by
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_I_n, dv_n_ph, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : n ∉ ((syn_wa (.classEq I (syn_ctc I)) ps)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_I_n, dv_n_ps, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : d ∉ ((syn_c0)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : s ∉ ((syn_c0)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : d ∉ ((syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : s ∉ ((syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : d ∉ ((syn_wa (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe) (syn_c0)) (.classEq (syn_c0c) (syn_cnc (syn_c0))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : s ∉ ((syn_wa (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe) (syn_c0)) (.classEq (syn_c0c) (syn_cnc (syn_c0))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : d ≠ s := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show d ≠ s from (by exact fresh_d_ne_s))
  have dv_cache_0010 : s ∉ ((Wff.classEq (.cv k) (syn_c0c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : d ∉ ((Wff.classEq (.cv k) (syn_c0c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : d ≠ k := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show d ≠ k from (by exact fresh_d_ne_k))
  have dv_cache_0013 : k ≠ s := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show k ≠ s from (by exact fresh_k_ne_s))
  have dv_cache_0014 : k ∉ ((syn_c0c)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : k ∉ ((syn_wb (.classMem (syn_c0c) (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (syn_c0c) (syn_cnc (.cv d)))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_ne_s, fresh_k_ne_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : x ∉ ((syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfrecprefixeq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_x, dv_F_x, dv_I_x, (Ne.symm dv_k_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : x ∉ ((syn_c0c)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : x ∉ ((Wff.classMem (syn_c0c) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfrecprefixeq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_x, dv_F_x, dv_I_x, (Ne.symm dv_k_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : x ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_x_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : x ∉ ((Wff.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfrecprefixeq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_x_y, dv_C_x, dv_F_x, dv_I_x, (Ne.symm dv_k_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : z ∉ ((Wff.classEq (.cv r) (syn_ckqrel (syn_clefin)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : x ∉ ((Wff.classEq (.cv r) (syn_ckqrel (syn_clefin)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : a ∉ ((Wff.classEq (.cv r) (syn_ckqrel (syn_clefin)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : z ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : z ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : a ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : a ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0028 : x ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0029 : x ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0030 : b ≠ r := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (show b ≠ r from (by exact fresh_b_ne_r))
  have dv_cache_0031 : b ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (show b ≠ x from (by exact fresh_b_ne_x))
  have dv_cache_0032 : b ≠ a := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (show b ≠ a from (by exact fresh_b_ne_a))
  have dv_cache_0033 : b ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (show b ≠ z from (by exact fresh_b_ne_z))
  have dv_cache_0034 : r ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0035 : r ≠ a := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact (show r ≠ a from (by exact fresh_r_ne_a))
  have dv_cache_0036 : r ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact (show r ≠ z from (by exact fresh_r_ne_z))
  have dv_cache_0037 : x ≠ a := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036
    exact (show x ≠ a from (by exact fresh_x_ne_a))
  have dv_cache_0038 : x ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0039 : a ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038
    exact (show a ≠ z from (by exact fresh_a_ne_z))
  have dv_cache_0040 : r ∉ ((syn_ckqrel (syn_clefin))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0041 : b ∉ ((syn_ckqrel (syn_clefin))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0042 : r ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0043 : b ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0044 : r ∉ ((syn_wral x (syn_cnnc) (syn_wral a (syn_cnnc) (syn_wral z (syn_cnnc) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_x, fresh_r_ne_a, fresh_r_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0045 : b ∉ ((syn_wral x (syn_cnnc) (syn_wral a (syn_cnnc) (syn_wral z (syn_cnnc) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_x, fresh_b_ne_a, fresh_b_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0046 : r ≠ b := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045
    exact (show r ≠ b from (by exact fresh_r_ne_b))
  have dv_cache_0047 : a ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0048 : z ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0049 : a ∉ ((syn_cplc (.cv y) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0050 : z ∉ ((syn_cplc (.cv y) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0051 : z ∉ ((Class.cv k)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0052 : x ∉ ((Wff.imp (syn_wa (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_x_y, fresh_x_ne_a, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0053 : z ∉ ((Wff.imp (syn_wa (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0054 : a ∉ ((Wff.imp (syn_wa (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_y, fresh_a_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0055 : x ∉ ((syn_cplc (.cv y) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_x_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0056 : a ∉ ((Class.cv k)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0057 : x ∉ ((Wff.imp (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_x_y, fresh_x_ne_a, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0058 : z ∉ ((Wff.imp (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0059 : a ∉ ((Wff.imp (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_y, fresh_a_ne_k, fresh_a_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0060 : n ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0061 : q ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0062 : q ∉ ((Wff.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_n, fresh_q_not_C, fresh_q_not_F, fresh_q_not_I, fresh_q_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0063 : n ∉ ((Wff.imp (.classMem (.cv q) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_q, dv_C_n, dv_F_n, dv_I_n, (Ne.symm dv_k_n), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0064 : q ∉ ((Class.cv y)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0065 : q ∉ ((Wff.imp (.classMem (.cv y) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_y, fresh_q_not_C, fresh_q_not_F, fresh_q_not_I, fresh_q_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0066 : q ∉ ((syn_cwppstopstep F (syn_ctc C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_C, fresh_q_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0067 : q ∉ ((syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_I, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0068 : q ∉ ((Wff.imp (.neg (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))) (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)) (syn_clec) (syn_ctc C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_C, fresh_q_ne_y, fresh_q_not_F, fresh_q_not_I, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0069 : p ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0070 : p ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0071 : p ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070
    exact (show p ≠ y from (by exact dv_p_y))
  have dv_cache_0072 : y ∉ ((syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_q, dv_C_y, dv_F_y, dv_I_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0073 : y ∉ ((syn_chwcards (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0074 : y ∉ ((Wff.imp (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_clec) (syn_ctc C)) (.classEq (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_q, dv_C_y, dv_F_y, dv_I_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0075 : q ∉ ((Wff.imp (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)) (syn_clec) (syn_ctc C)) (.classEq (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_y, fresh_q_not_C, fresh_q_not_F, fresh_q_not_I, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0076 : x ∉ ((Wff.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfrecprefixeq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_x_y, dv_C_x, dv_F_x, dv_I_x, (Ne.symm dv_k_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0077 : y ∉ ((syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_I_y, dv_ph_y, dv_ps_y, dv_ch_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0078 : y ∉ (syn_wtru).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0079 : y ∉ ((Class.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfrecprefixeq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_y), dv_C_y, dv_F_y, dv_I_y, (Ne.symm dv_k_y), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0080 : x ∉ ((Class.cv n)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_n_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0081 : x ∉ ((Wff.classMem (.cv n) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfrecprefixeq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_n_x), dv_C_x, dv_F_x, dv_I_x, (Ne.symm dv_k_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0082 : n ∉ ((syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_I_n, dv_n_ph, dv_n_ps, dv_ch_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0083 : n ∉ ((Class.cv k)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_k_n), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0084 : n ∉ ((Wff.imp (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_k_n), dv_C_n, dv_F_n, dv_I_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0085 : y ∉ ((Wff.classEq (.cv r) (syn_ckqrel (syn_clefin)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0086 : y ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0087 : y ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0088 : x ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0089 : a ≠ r := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088
    exact (show a ≠ r from (by exact fresh_a_ne_r))
  have dv_cache_0090 : a ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0091 : a ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090
    exact (show a ≠ y from (by exact fresh_a_ne_y))
  have dv_cache_0092 : r ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091
    exact (show r ≠ y from (by exact fresh_r_ne_y))
  have dv_cache_0093 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0094 : a ∉ ((syn_ckqrel (syn_clefin))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0095 : r ∉ ((syn_wral x (syn_cnnc) (syn_wral y (syn_cnnc) (syn_wo (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_x, fresh_r_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0096 : a ∉ ((syn_wral x (syn_cnnc) (syn_wral y (syn_cnnc) (syn_wo (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_x, fresh_a_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0097 : y ∉ ((Class.cv n)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_n_y), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0098 : y ∉ ((Class.cv k)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_k_y), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0099 : x ∉ ((syn_wo (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv n)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_n_x), dv_x_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0100 : y ∉ ((syn_wo (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_n_y), (Ne.symm dv_k_y), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0101 : q ∉ ((Class.cv n)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0102 : q ∉ ((Wff.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_n, fresh_q_not_C, fresh_q_not_F, fresh_q_not_I, fresh_q_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0103 : q ∉ ((Wff.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_n, fresh_q_not_C, fresh_q_not_F, fresh_q_not_I, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0104 : n ∉ ((Wff.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_cncs))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_ne_q, dv_C_n, dv_F_n, dv_I_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0105 : y ∉ ((syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv r))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_r, dv_C_y, dv_F_y, dv_I_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0106 : y ∉ ((syn_cdm (syn_cwppstopstep F C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_y, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0107 : y ∉ ((Wff.imp (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv r))) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv r)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_y, fresh_y_ne_r, dv_F_y, dv_I_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0108 : y ∉ ((Wff.classMem (.cv r) (syn_cnnc))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0109 : r ∉ ((syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_I, fresh_r_not_ph, fresh_r_not_ps, fresh_r_not_ch, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0110 : k ∉ ((syn_cwppstopstep F C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_k, dv_F_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0111 : m ∉ ((syn_cwppstopstep F C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_m, dv_F_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0112 : n ∉ ((syn_cwppstopstep F C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_n, dv_F_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0113 : q ∉ ((syn_cwppstopstep F C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_C, fresh_q_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0114 : r ∉ ((syn_cwppstopstep F C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_C, fresh_r_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0115 : k ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0116 : m ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0117 : n ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0118 : q ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0119 : r ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0120 : k ∉ ((syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_I_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0121 : m ∉ ((syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119 dv_cache_0120
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_I_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0122 : n ∉ ((syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119 dv_cache_0120 dv_cache_0121
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_I_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0123 : r ∉ ((syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119 dv_cache_0120 dv_cache_0121 dv_cache_0122
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_I, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0124 : k ∉ ((syn_ctc C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119 dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0125 : m ∉ ((syn_ctc C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119 dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_m, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0126 : n ∉ ((syn_ctc C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119 dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0127 : q ∉ ((syn_ctc C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119 dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125 dv_cache_0126
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0128 : r ∉ ((syn_ctc C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119 dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125 dv_cache_0126 dv_cache_0127
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0129 : k ≠ m := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119 dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125 dv_cache_0126 dv_cache_0127 dv_cache_0128
    exact (show k ≠ m from (by exact dv_k_m))
  have dv_cache_0130 : k ≠ n := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119 dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125 dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129
    exact (show k ≠ n from (by exact dv_k_n))
  have dv_cache_0131 : m ≠ n := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119 dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125 dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130
    exact (show m ≠ n from (by exact dv_m_n))
  have dv_cache_0132 : n ≠ q := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119 dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125 dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131
    exact (show n ≠ q from (by exact fresh_n_ne_q))
  have dv_cache_0133 : n ≠ r := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119 dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125 dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131 dv_cache_0132
    exact (show n ≠ r from (by exact fresh_n_ne_r))
  have dv_cache_0134 : x ∉ ((syn_cwppstopstep F C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119 dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125 dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131 dv_cache_0132 dv_cache_0133
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_x, dv_F_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0135 : x ∉ ((syn_cwppstopstep F (syn_ctc C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119 dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125 dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131 dv_cache_0132 dv_cache_0133 dv_cache_0134
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_x, dv_F_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0136 : x ∉ ((syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119 dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125 dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131 dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_I_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0137 : n ∉ ((Class.cv m)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119 dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125 dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131 dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_m_n), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0138 : n ∉ ((syn_wb (.classMem (.cv m) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (.classMem (syn_ctc (.cv m)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119 dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125 dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131 dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_m_n), dv_C_n, dv_F_n, dv_I_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0139 : n ∉ ((syn_ctc (.cv m))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119 dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125 dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131 dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137 dv_cache_0138
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_m_n), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0140 : n ∉ ((Wff.imp (.classMem (syn_ctc (.cv m)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (syn_ctc (.cv m))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119 dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125 dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131 dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137 dv_cache_0138 dv_cache_0139
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_m_n), dv_C_n, dv_F_n, dv_I_n, (Ne.symm dv_k_n), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0141 : x ∉ ((Class.cv k)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119 dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125 dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131 dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137 dv_cache_0138 dv_cache_0139 dv_cache_0140
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_k_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0142 : n ∉ ((Class.cv x)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119 dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125 dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131 dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137 dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_n_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0143 : n ∉ ((syn_wb (.classMem (.cv x) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (.classMem (syn_ctc (.cv x)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119 dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125 dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131 dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137 dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_n_x, dv_C_n, dv_F_n, dv_I_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0144 : n ∉ ((Wff.imp (.classMem (.cv x) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119 dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125 dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131 dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137 dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_n_x, dv_C_n, dv_F_n, dv_I_n, (Ne.symm dv_m_n), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0145 : x ∉ ((syn_wbr (syn_ctc (.cv m)) (syn_ckqrel (syn_clefin)) (.cv k))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119 dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125 dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131 dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137 dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143 dv_cache_0144
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_m_x), (Ne.symm dv_k_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0146 : x ∉ ((syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119 dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125 dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131 dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137 dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143 dv_cache_0144 dv_cache_0145
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_I_x, dv_ph_x, dv_ps_x, dv_ch_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0147 : y ∉ ((syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119 dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125 dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131 dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137 dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143 dv_cache_0144 dv_cache_0145 dv_cache_0146
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_y), dv_C_y, dv_F_y, dv_I_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0148 : y ∉ ((Wff.imp (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x))) (syn_wne (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x)) (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119 dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125 dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131 dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137 dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143 dv_cache_0144 dv_cache_0145 dv_cache_0146 dv_cache_0147
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_y, (Ne.symm dv_x_y), dv_F_y, dv_I_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0149 : y ∉ ((Wff.classMem (.cv x) (syn_cnnc))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119 dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125 dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131 dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137 dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143 dv_cache_0144 dv_cache_0145 dv_cache_0146 dv_cache_0147 dv_cache_0148
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_y), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0150 : x ∉ ((Class.cv m)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119 dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125 dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131 dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137 dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143 dv_cache_0144 dv_cache_0145 dv_cache_0146 dv_cache_0147 dv_cache_0148 dv_cache_0149
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_m_x), compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0151 : x ∉ ((Wff.imp (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m))) (syn_wne (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m)) (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077 dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081 dv_cache_0082 dv_cache_0083 dv_cache_0084 dv_cache_0085 dv_cache_0086 dv_cache_0087 dv_cache_0088 dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0092 dv_cache_0093 dv_cache_0094 dv_cache_0095 dv_cache_0096 dv_cache_0097 dv_cache_0098 dv_cache_0099 dv_cache_0100 dv_cache_0101 dv_cache_0102 dv_cache_0103 dv_cache_0104 dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 dv_cache_0109 dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119 dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0123 dv_cache_0124 dv_cache_0125 dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131 dv_cache_0132 dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136 dv_cache_0137 dv_cache_0138 dv_cache_0139 dv_cache_0140 dv_cache_0141 dv_cache_0142 dv_cache_0143 dv_cache_0144 dv_cache_0145 dv_cache_0146 dv_cache_0147 dv_cache_0148 dv_cache_0149 dv_cache_0150
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_x, (Ne.symm dv_m_x), dv_F_x, dv_I_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (.classEq I (syn_ctc I)) (syn_wa ph (syn_wa ps ch))
  have p0001 :=
    @g_simpr (.classEq I (syn_ctc I)) (syn_wa ph (syn_wa ps ch))
  have p0002 :=
    @g_simpl ph (syn_wa ps ch)
  have p0003 :=
    @g_syl (syn_wa (.classEq I (syn_ctc I)) (syn_wa ph (syn_wa ps ch))) (syn_wa ph (syn_wa ps ch)) ph p0001 p0002
  have p0004 :=
    @g_jca (syn_wa (.classEq I (syn_ctc I)) (syn_wa ph (syn_wa ps ch))) (.classEq I (syn_ctc I)) ph p0000 p0003
  have p0005 :=
    @g_simpr ph (syn_wa ps ch)
  have p0006 :=
    @g_syl (syn_wa (.classEq I (syn_ctc I)) (syn_wa ph (syn_wa ps ch))) (syn_wa ph (syn_wa ps ch)) (syn_wa ps ch) p0001 p0005
  have p0007 :=
    @g_simpl ps ch
  have p0008 :=
    @g_syl (syn_wa (.classEq I (syn_ctc I)) (syn_wa ph (syn_wa ps ch))) (syn_wa ps ch) ps p0006 p0007
  have p0009 :=
    @g_jca (syn_wa (.classEq I (syn_ctc I)) (syn_wa ph (syn_wa ps ch))) (.classEq I (syn_ctc I)) ps p0000 p0008
  have p0010 :=
    @g_simpr ps ch
  have p0011 :=
    @g_syl (syn_wa (.classEq I (syn_ctc I)) (syn_wa ph (syn_wa ps ch))) (syn_wa ps ch) ch p0006 p0010
  have p0012 :=
    @g_jca (syn_wa (.classEq I (syn_ctc I)) (syn_wa ph (syn_wa ps ch))) (.classEq I (syn_ctc I)) ch p0000 p0011
  have p0013 :=
    @g_jca (syn_wa (.classEq I (syn_ctc I)) (syn_wa ph (syn_wa ps ch))) (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch) p0009 p0012
  have p0014 :=
    @g_jca (syn_wa (.classEq I (syn_ctc I)) (syn_wa ph (syn_wa ps ch))) (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch)) p0004 p0013
  have p0015 :=
    @g_ex (.classEq I (syn_ctc I)) (syn_wa ph (syn_wa ps ch)) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) p0014
  have p0016 :=
    @g_eqid (.cv m)
  have p0017 :=
    @g_a1i (.classEq (.cv m) (.cv m)) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) p0016
  have p0018 :=
    @g_simpl (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))
  have p0019 :=
    @g_simpr (.classEq I (syn_ctc I)) ph
  have p0020 :=
    @g_syl (syn_wa (.classEq I (syn_ctc I)) ph) ph (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv m) (syn_cwpphit (syn_cwppstopstep F C) I C)) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) I C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))))) p0019 hyp_wppstopfixedhitcontrgrowfixdndv_10
  have p0021 :=
    @g_iftrue (.classEq I (syn_ctc I)) I (syn_c0c)
  have p0022 :=
    @g_eqcomd (.classEq I (syn_ctc I)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) I p0021
  have p0023 :=
    @g_adantr (.classEq I (syn_ctc I)) (.classEq I (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) ph p0022
  have p0024 :=
    @g_wpphitstartcongrndv C (syn_cwppstopstep F C) I (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))
  have p0025 :=
    @g_syl (syn_wa (.classEq I (syn_ctc I)) ph) (.classEq I (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.classEq (syn_cwpphit (syn_cwppstopstep F C) I C) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) p0023 p0024
  have p0026 :=
    @g_eleq2d (syn_wa (.classEq I (syn_ctc I)) ph) (syn_cwpphit (syn_cwppstopstep F C) I C) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C) (.cv m) p0025
  have p0027 :=
    @g_eleq2d (syn_wa (.classEq I (syn_ctc I)) ph) (syn_cwpphit (syn_cwppstopstep F C) I C) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C) (.cv n) p0025
  have p0028 :=
    @g_imbi1d (syn_wa (.classEq I (syn_ctc I)) ph) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) I C)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)) p0027
  have p0029 :=
    @g_ralbidv (syn_wa (.classEq I (syn_ctc I)) ph) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) I C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n))) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n))) n (syn_cnnc) dv_cache_0001 p0028
  have p0030 :=
    @g_anbi12d (syn_wa (.classEq I (syn_ctc I)) ph) (.classMem (.cv m) (syn_cwpphit (syn_cwppstopstep F C) I C)) (.classMem (.cv m) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) I C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) p0026 p0029
  have p0031 :=
    @g_anbi2d (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (.classMem (.cv m) (syn_cwpphit (syn_cwppstopstep F C) I C)) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) I C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (.classMem (.cv m) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n))))) (.classMem (.cv m) (syn_cnnc)) p0030
  have p0032 :=
    @g_mpbid (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv m) (syn_cwpphit (syn_cwppstopstep F C) I C)) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) I C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv m) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))))) p0020 p0031
  have p0033 :=
    @g_syl (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv m) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))))) p0018 p0032
  have p0034 :=
    @g_simpld (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv m) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n))))) p0033
  have p0035 :=
    @g_simpr (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))
  have p0036 :=
    @g_simpl (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch)
  have p0037 :=
    @g_syl (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch)) (syn_wa (.classEq I (syn_ctc I)) ps) p0035 p0036
  have p0038 :=
    @g_simpr (.classEq I (syn_ctc I)) ps
  have p0039 :=
    @g_syl (syn_wa (.classEq I (syn_ctc I)) ps) ps (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc I) (syn_ctc C))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc I) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) p0038 hyp_wppstopfixedhitcontrgrowfixdndv_11
  have p0040 :=
    @g_tceq I (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))
  have p0041 :=
    @g_syl (.classEq I (syn_ctc I)) (.classEq I (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.classEq (syn_ctc I) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))) p0022 p0040
  have p0042 :=
    @g_adantr (.classEq I (syn_ctc I)) (.classEq (syn_ctc I) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))) ps p0041
  have p0043 :=
    @g_wpphitstartcongrndv (syn_ctc C) (syn_cwppstopstep F (syn_ctc C)) (syn_ctc I) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))
  have p0044 :=
    @g_syl (syn_wa (.classEq I (syn_ctc I)) ps) (.classEq (syn_ctc I) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))) (.classEq (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc I) (syn_ctc C)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) p0042 p0043
  have p0045 :=
    @g_eleq2d (syn_wa (.classEq I (syn_ctc I)) ps) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc I) (syn_ctc C)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C)) (.cv k) p0044
  have p0046 :=
    @g_eleq2d (syn_wa (.classEq I (syn_ctc I)) ps) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc I) (syn_ctc C)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C)) (.cv n) p0044
  have p0047 :=
    @g_imbi1d (syn_wa (.classEq I (syn_ctc I)) ps) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc I) (syn_ctc C))) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)) p0046
  have p0048 :=
    @g_ralbidv (syn_wa (.classEq I (syn_ctc I)) ps) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc I) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))) n (syn_cnnc) dv_cache_0002 p0047
  have p0049 :=
    @g_anbi12d (syn_wa (.classEq I (syn_ctc I)) ps) (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc I) (syn_ctc C))) (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc I) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))) p0045 p0048
  have p0050 :=
    @g_anbi2d (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc I) (syn_ctc C))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc I) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (.classMem (.cv k) (syn_cnnc)) p0049
  have p0051 :=
    @g_mpbid (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc I) (syn_ctc C))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc I) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) p0039 p0050
  have p0052 :=
    @g_syl (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) p0037 p0051
  have p0053 :=
    @g_simpld (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) p0052
  have p0054 :=
    @g_jca (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)) p0034 p0053
  have p0055 :=
    @g_simprd (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv m) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n))))) p0033
  have p0056 :=
    @g_simpld (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv m) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) p0055
  have p0057 :=
    @g_simprd (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) p0052
  have p0058 :=
    @g_simpld (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))) p0057
  have p0059 :=
    (by simpa [syn_cwpphit] using (Nominal.classEqRefl (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))))
  have p0060 :=
    @g_eqid (syn_cwppstopstep F (syn_ctc C))
  have p0061 :=
    @g_id (.classEq I (syn_ctc I))
  have p0062 :=
    @g_tceq (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) I
  have p0063 :=
    @g_syl (.classEq I (syn_ctc I)) (.classEq (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) I) (.classEq (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc I)) p0021 p0062
  have p0064 :=
    @g_eqcomd (.classEq I (syn_ctc I)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc I) p0063
  have p0065 :=
    @g_n_3eqtrd (.classEq I (syn_ctc I)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) I (syn_ctc I) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) p0021 p0061 p0064
  have p0066 :=
    @g_iffalse (.classEq I (syn_ctc I)) I (syn_c0c)
  have p0067 :=
    @g_tc0c
  have p0068 :=
    @g_eqcomi (syn_ctc (syn_c0c)) (syn_c0c) p0067
  have p0069 :=
    @g_a1i (.classEq (syn_c0c) (syn_ctc (syn_c0c))) (.neg (.classEq I (syn_ctc I))) p0068
  have p0070 :=
    @g_tceq (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_c0c)
  have p0071 :=
    @g_syl (.neg (.classEq I (syn_ctc I))) (.classEq (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_c0c)) (.classEq (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc (syn_c0c))) p0066 p0070
  have p0072 :=
    @g_eqcomd (.neg (.classEq I (syn_ctc I))) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc (syn_c0c)) p0071
  have p0073 :=
    @g_n_3eqtrd (.neg (.classEq I (syn_ctc I))) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_c0c) (syn_ctc (syn_c0c)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) p0066 p0069 p0072
  have p0074 :=
    @g_pm2_61i (.classEq I (syn_ctc I)) (.classEq (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))) p0065 p0073
  have p0075 :=
    @g_pm3_2i (.classEq (syn_cwppstopstep F (syn_ctc C)) (syn_cwppstopstep F (syn_ctc C))) (.classEq (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))) p0060 p0074
  have p0076 :=
    @g_freceq12 (syn_cwppstopstep F (syn_ctc C)) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))
  have p0077 :=
    Nominal.mp p0075 p0076
  have p0078 :=
    @g_cnveqi (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))) p0077
  have p0079 :=
    @g_imaeq1i (syn_ccnv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))) (syn_ccnv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))))) (syn_cima (syn_clec) (syn_csn (syn_ctc C))) p0078
  have p0080 :=
    @g_eqtri (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)) (syn_cima (syn_ccnv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))) (syn_cima (syn_clec) (syn_csn (syn_ctc C)))) (syn_cima (syn_ccnv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))))) (syn_cima (syn_clec) (syn_csn (syn_ctc C)))) p0059 p0079
  have p0081 :=
    (by simpa [syn_cwpphit] using (Nominal.classEqRefl (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))))
  have p0082 :=
    @g_eqtr4i (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)) (syn_cima (syn_ccnv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))))) (syn_cima (syn_clec) (syn_csn (syn_ctc C)))) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C)) p0080 p0081
  have p0083 :=
    @g_syl6eleqr (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)) p0058 p0082
  have p0084 :=
    @g_wppstopstepfunsndv (syn_ctc C) F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0085 :=
    @g_wecomparisondefaultemptywe
  have p0086 :=
    @g_df0c2
  have p0087 :=
    @g_pm3_2i (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe) (syn_c0)) (.classEq (syn_c0c) (syn_cnc (syn_c0))) p0085 p0086
  have p0088 :=
    @g_n_0ex
  have p0089 :=
    @g_brex (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0) (syn_cwe)
  have p0090 :=
    Nominal.mp p0085 p0089
  have p0091 :=
    @g_simpli (.classMem (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cvv)) (.classMem (syn_c0) (syn_cvv)) p0090
  have p0092 :=
    @g_simpr (.classEq (.cv d) (syn_c0)) (.classEq (.cv s) (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))
  have p0093 :=
    @g_simpl (.classEq (.cv d) (syn_c0)) (.classEq (.cv s) (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))
  have p0094 :=
    @g_breq12d (syn_wa (.classEq (.cv d) (syn_c0)) (.classEq (.cv s) (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) (.cv s) (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (.cv d) (syn_c0) (syn_cwe) p0092 p0093
  have p0095 :=
    @g_nceqd (syn_wa (.classEq (.cv d) (syn_c0)) (.classEq (.cv s) (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) (.cv d) (syn_c0) p0093
  have p0096 :=
    @g_eqeq2d (syn_wa (.classEq (.cv d) (syn_c0)) (.classEq (.cv s) (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) (syn_cnc (.cv d)) (syn_cnc (syn_c0)) (syn_c0c) p0095
  have p0097 :=
    @g_anbi12d (syn_wa (.classEq (.cv d) (syn_c0)) (.classEq (.cv s) (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))))) (syn_wbr (.cv s) (syn_cwe) (.cv d)) (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe) (syn_c0)) (.classEq (syn_c0c) (syn_cnc (.cv d))) (.classEq (syn_c0c) (syn_cnc (syn_c0))) p0094 p0096
  have p0098 :=
    @g_spc2ev (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (syn_c0c) (syn_cnc (.cv d)))) (syn_wa (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe) (syn_c0)) (.classEq (syn_c0c) (syn_cnc (syn_c0)))) d s (syn_c0) (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 p0088 p0091 p0097
  have p0099 :=
    Nominal.mp p0087 p0098
  have p0100 :=
    @g_n_0cex
  have p0101 :=
    @g_id (.classEq (.cv k) (syn_c0c))
  have p0102 :=
    @g_eleq1d (.classEq (.cv k) (syn_c0c)) (.cv k) (syn_c0c) (syn_chwcards (syn_cvv)) p0101
  have p0103 :=
    @g_id (.classEq (.cv k) (syn_c0c))
  have p0104 :=
    @g_eqeq1d (.classEq (.cv k) (syn_c0c)) (.cv k) (syn_c0c) (syn_cnc (.cv d)) p0103
  have p0105 :=
    @g_anbi2d (.classEq (.cv k) (syn_c0c)) (.classEq (.cv k) (syn_cnc (.cv d))) (.classEq (syn_c0c) (syn_cnc (.cv d))) (syn_wbr (.cv s) (syn_cwe) (.cv d)) p0104
  have p0106 :=
    @g_exbidv (.classEq (.cv k) (syn_c0c)) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d)))) (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (syn_c0c) (syn_cnc (.cv d)))) s dv_cache_0010 p0105
  have p0107 :=
    @g_exbidv (.classEq (.cv k) (syn_c0c)) (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d))))) (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (syn_c0c) (syn_cnc (.cv d))))) d dv_cache_0011 p0106
  have p0108 :=
    @g_bibi12d (.classEq (.cv k) (syn_c0c)) (.classMem (.cv k) (syn_chwcards (syn_cvv))) (.classMem (syn_c0c) (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d)))))) (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (syn_c0c) (syn_cnc (.cv d)))))) p0102 p0107
  have p0109 :=
    @g_elhwcardswev k s d dv_cache_0012 dv_cache_0009 dv_cache_0013
  have p0110 :=
    @g_vtoclg (syn_wb (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d))))))) (syn_wb (.classMem (syn_c0c) (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (syn_c0c) (syn_cnc (.cv d))))))) k (syn_c0c) (syn_cvv) dv_cache_0014 dv_cache_0015 p0108 p0109
  have p0111 :=
    Nominal.mp p0100 p0110
  have p0112 :=
    @g_mpbir (.classMem (syn_c0c) (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (syn_c0c) (syn_cnc (.cv d)))))) p0099 p0111
  have p0113 :=
    @g_pm3_2i (.classMem I (syn_chwcards (syn_cvv))) (.classMem (syn_c0c) (syn_chwcards (syn_cvv))) hyp_wppstopfixedhitcontrgrowfixdndv_7 p0112
  have p0114 :=
    @g_ifcl (.classEq I (syn_ctc I)) I (syn_c0c) (syn_chwcards (syn_cvv))
  have p0115 :=
    Nominal.mp p0113 p0114
  have p0116 :=
    @g_wppstopstepdmndv (syn_ctc C) F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0117 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F (syn_ctc C))) (syn_chwcards (syn_cvv)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) p0116
  have p0118 :=
    @g_biimpri (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_chwcards (syn_cvv))) p0117
  have p0119 :=
    Nominal.mp p0115 p0118
  have p0120 :=
    @g_wppstopsteprndmndv (syn_ctc C) F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0121 :=
    @g_n_3pm3_2i (.classMem (syn_cwppstopstep F (syn_ctc C)) (syn_cfuns)) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) (syn_wss (syn_crn (syn_cwppstopstep F (syn_ctc C))) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) p0084 p0119 p0120
  have p0122 :=
    @g_elwpphitvndv (syn_ctc C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (.cv k)
  have p0123 :=
    Nominal.mp p0121 p0122
  have p0124 :=
    @g_sylib (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k)))) p0083 p0123
  have p0125 :=
    @g_simprd (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv k) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k))) p0124
  have p0126 :=
    @g_finlewe
  have p0127 :=
    @g_wppweref (syn_cnnc) (syn_ckqrel (syn_clefin))
  have p0128 :=
    Nominal.mp p0126 p0127
  have p0129 :=
    @g_a1i (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cref) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)) p0128
  have p0130 :=
    @g_id (.classMem (.cv k) (syn_cnnc))
  have p0131 :=
    @g_refd (.classMem (.cv k) (syn_cnnc)) (syn_cnnc) (syn_ckqrel (syn_clefin)) (.cv k) p0129 p0130
  have p0132 :=
    @g_syl (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv k) (syn_cnnc)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv k)) p0053 p0131
  have p0133 :=
    @g_tru
  have p0134 :=
    @g_wppstopstepfunsndv C F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0135 :=
    @g_wppfrecprefixeqexndv k (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) p0134 p0084
  have p0136 :=
    @g_abid2 x (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k) dv_cache_0016
  have p0137 :=
    @g_eleq1i (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k) (syn_cvv) p0136
  have p0138 :=
    @g_mpbir (.classMem (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))) (syn_cvv)) (.classMem (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k) (syn_cvv)) p0135 p0137
  have p0139 :=
    @g_a1i (.classMem (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))) (syn_cvv)) syn_wtru p0138
  have p0140 :=
    @g_wppstopstepdmndv C F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0141 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F C)) (syn_chwcards (syn_cvv)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) p0140
  have p0142 :=
    @g_biimpri (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F C))) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_chwcards (syn_cvv))) p0141
  have p0143 :=
    Nominal.mp p0115 p0142
  have p0144 :=
    @g_wppstopsteprndmndv C F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0145 :=
    @g_n_3pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))) p0134 p0143 p0144
  have p0146 :=
    @g_wpporbit0ndv (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))
  have p0147 :=
    Nominal.mp p0145 p0146
  have p0148 :=
    @g_n_3pm3_2i (.classMem (syn_cwppstopstep F (syn_ctc C)) (syn_cfuns)) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) (syn_wss (syn_crn (syn_cwppstopstep F (syn_ctc C))) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) p0084 p0119 p0120
  have p0149 :=
    @g_wpporbit0ndv (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))
  have p0150 :=
    Nominal.mp p0148 p0149
  have p0151 :=
    @g_eqcomi (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_c0c)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) p0150
  have p0152 :=
    @g_eqtri (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_c0c)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_c0c)) p0147 p0151
  have p0153 :=
    @g_a1i (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_c0c)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_c0c))) (syn_wbr (syn_c0c) (syn_ckqrel (syn_clefin)) (.cv k)) p0152
  have p0154 :=
    @g_peano1
  have p0155 :=
    @g_wppfrecprefixeqvalndv (syn_c0c) k (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) p0134 p0143 p0144 p0084 p0119 p0120
  have p0156 :=
    Nominal.mp p0154 p0155
  have p0157 :=
    @g_mpbir (.classMem (syn_c0c) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (.imp (syn_wbr (syn_c0c) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_c0c)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_c0c)))) p0153 p0156
  have p0158 :=
    @g_a1i (.classMem (syn_c0c) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) syn_wtru p0157
  have p0159 :=
    @g_n_0cex
  have p0160 :=
    @g_id (.classEq (.cv x) (syn_c0c))
  have p0161 :=
    @g_eleq1d (.classEq (.cv x) (syn_c0c)) (.cv x) (syn_c0c) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k) p0160
  have p0162 :=
    @g_elab (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (.classMem (syn_c0c) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) x (syn_c0c) dv_cache_0017 dv_cache_0018 p0159 p0161
  have p0163 :=
    @g_sylibr syn_wtru (.classMem (syn_c0c) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (.classMem (syn_c0c) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)))) p0158 p0162
  have p0164 :=
    @g_jca syn_wtru (.classMem (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))) (syn_cvv)) (.classMem (syn_c0c) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)))) p0139 p0163
  have p0165 :=
    @g_vex y
  have p0166 :=
    @g_id (.classEq (.cv x) (.cv y))
  have p0167 :=
    @g_eleq1d (.classEq (.cv x) (.cv y)) (.cv x) (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k) p0166
  have p0168 :=
    @g_elab (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) x (.cv y) dv_cache_0019 dv_cache_0020 p0165 p0167
  have p0169 :=
    @g_n_3pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))) p0134 p0143 p0144
  have p0170 :=
    @g_a1i (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) p0169
  have p0171 :=
    @g_simp1 (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0172 :=
    @g_jca (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (.classMem (.cv y) (syn_cnnc)) p0170 p0171
  have p0173 :=
    @g_wpporbitsucndv (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (.cv y)
  have p0174 :=
    @g_syl (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (.classMem (.cv y) (syn_cnnc))) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))) p0172 p0173
  have p0175 :=
    @g_simp1 (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0176 :=
    @g_simp2 (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0177 :=
    @g_jca (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) p0175 p0176
  have p0178 :=
    @g_simp1 (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0179 :=
    @g_simp3 (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0180 :=
    @g_jca (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) p0178 p0179
  have p0181 :=
    @g_simpr (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0182 :=
    @g_simpl (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0183 :=
    @g_finlewe
  have p0184 :=
    @g_wppweref (syn_cnnc) (syn_ckqrel (syn_clefin))
  have p0185 :=
    Nominal.mp p0183 p0184
  have p0186 :=
    @g_a1i (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cref) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) p0185
  have p0187 :=
    @g_id (.classMem (.cv y) (syn_cnnc))
  have p0188 :=
    @g_refd (.classMem (.cv y) (syn_cnnc)) (syn_cnnc) (syn_ckqrel (syn_clefin)) (.cv y) p0186 p0187
  have p0189 :=
    @g_orc (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv y)) (.classEq (.cv y) (syn_cplc (.cv y) (syn_c1c)))
  have p0190 :=
    @g_syl (.classMem (.cv y) (syn_cnnc)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wo (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv y)) (.classEq (.cv y) (syn_cplc (.cv y) (syn_c1c)))) p0188 p0189
  have p0191 :=
    @g_id (.classMem (.cv y) (syn_cnnc))
  have p0192 :=
    @g_id (.classMem (.cv y) (syn_cnnc))
  have p0193 :=
    @g_jca (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) p0191 p0192
  have p0194 :=
    @g_kqfinsucsplit (.cv y) (.cv y)
  have p0195 :=
    @g_syl (.classMem (.cv y) (syn_cnnc)) (syn_wa (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (syn_wb (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) (syn_wo (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv y)) (.classEq (.cv y) (syn_cplc (.cv y) (syn_c1c))))) p0193 p0194
  have p0196 :=
    @g_mpbird (.classMem (.cv y) (syn_cnnc)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) (syn_wo (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv y)) (.classEq (.cv y) (syn_cplc (.cv y) (syn_c1c)))) p0190 p0195
  have p0197 :=
    @g_syl (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classMem (.cv y) (syn_cnnc)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) p0182 p0196
  have p0198 :=
    @g_a1d (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) p0197
  have p0199 :=
    @g_ancom (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c)))
  have p0200 :=
    @g_finlewe
  have p0201 :=
    @g_wppwepo (syn_cnnc) (syn_ckqrel (syn_clefin))
  have p0202 :=
    Nominal.mp p0200 p0201
  have p0203 :=
    @g_porta (syn_cnnc) (syn_ckqrel (syn_clefin))
  have p0204 :=
    @g_mpbi (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cpartial) (syn_cnnc)) (syn_w3a (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cref) (syn_cnnc)) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc)) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cantisym) (syn_cnnc))) p0202 p0203
  have p0205 :=
    @g_simp2 (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cref) (syn_cnnc)) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc)) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cantisym) (syn_cnnc))
  have p0206 :=
    Nominal.mp p0204 p0205
  have p0207 :=
    @g_a1i (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc)) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) p0206
  have p0208 :=
    @g_brex (syn_ckqrel (syn_clefin)) (syn_cnnc) (syn_ctrans)
  have p0209 :=
    @g_breq (.cv x) (.cv a) (.cv r) (syn_ckqrel (syn_clefin))
  have p0210 :=
    @g_breq (.cv a) (.cv z) (.cv r) (syn_ckqrel (syn_clefin))
  have p0211 :=
    @g_anbi12d (.classEq (.cv r) (syn_ckqrel (syn_clefin))) (syn_wbr (.cv x) (.cv r) (.cv a)) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (.cv r) (.cv z)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z)) p0209 p0210
  have p0212 :=
    @g_breq (.cv x) (.cv z) (.cv r) (syn_ckqrel (syn_clefin))
  have p0213 :=
    @g_imbi12d (.classEq (.cv r) (syn_ckqrel (syn_clefin))) (syn_wa (syn_wbr (.cv x) (.cv r) (.cv a)) (syn_wbr (.cv a) (.cv r) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z)) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)) p0211 p0212
  have p0214 :=
    @g_ralbidv (.classEq (.cv r) (syn_ckqrel (syn_clefin))) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv a)) (syn_wbr (.cv a) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z))) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z))) z (.cv b) dv_cache_0021 p0213
  have p0215 :=
    @g_n_2ralbidv (.classEq (.cv r) (syn_ckqrel (syn_clefin))) (syn_wral z (.cv b) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv a)) (syn_wbr (.cv a) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z)))) (syn_wral z (.cv b) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))) x a (.cv b) (.cv b) dv_cache_0022 dv_cache_0023 p0214
  have p0216 :=
    @g_raleq (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z))) z (.cv b) (syn_cnnc) dv_cache_0024 dv_cache_0025
  have p0217 :=
    @g_raleqbi1dv (syn_wral z (.cv b) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))) (syn_wral z (syn_cnnc) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))) a (.cv b) (syn_cnnc) dv_cache_0026 dv_cache_0027 p0216
  have p0218 :=
    @g_raleqbi1dv (syn_wral a (.cv b) (syn_wral z (.cv b) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z))))) (syn_wral a (syn_cnnc) (syn_wral z (syn_cnnc) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z))))) x (.cv b) (syn_cnnc) dv_cache_0028 dv_cache_0029 p0217
  have p0219 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_trans x a z r b dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
  have p0220 :=
    @g_brabg (syn_wral x (.cv b) (syn_wral a (.cv b) (syn_wral z (.cv b) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv a)) (syn_wbr (.cv a) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z)))))) (syn_wral x (.cv b) (syn_wral a (.cv b) (syn_wral z (.cv b) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))))) (syn_wral x (syn_cnnc) (syn_wral a (syn_cnnc) (syn_wral z (syn_cnnc) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))))) r b (syn_ckqrel (syn_clefin)) (syn_cnnc) (syn_cvv) (syn_cvv) (syn_ctrans) dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 p0215 p0218 p0219
  have p0221 :=
    @g_syl (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc)) (syn_wa (.classMem (syn_ckqrel (syn_clefin)) (syn_cvv)) (.classMem (syn_cnnc) (syn_cvv))) (syn_wb (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc)) (syn_wral x (syn_cnnc) (syn_wral a (syn_cnnc) (syn_wral z (syn_cnnc) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z))))))) p0208 p0220
  have p0222 :=
    @g_ibi (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc)) (syn_wral x (syn_cnnc) (syn_wral a (syn_cnnc) (syn_wral z (syn_cnnc) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))))) p0221
  have p0223 :=
    @g_syl (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc)) (syn_wral x (syn_cnnc) (syn_wral a (syn_cnnc) (syn_wral z (syn_cnnc) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))))) p0207 p0222
  have p0224 :=
    @g_simpl (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0225 :=
    @g_simpl (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0226 :=
    @g_peano2 (.cv y)
  have p0227 :=
    @g_syl (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classMem (.cv y) (syn_cnnc)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) p0225 p0226
  have p0228 :=
    @g_jca (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classMem (.cv y) (syn_cnnc)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) p0224 p0227
  have p0229 :=
    @g_a1d (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) p0053
  have p0230 :=
    @g_pm3_2 (syn_wa (.classMem (.cv y) (syn_cnnc)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc))) (.classMem (.cv k) (syn_cnnc))
  have p0231 :=
    @g_syl9 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv y) (syn_cnnc)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc))) (.classMem (.cv k) (syn_cnnc))) p0229 p0230
  have p0232 :=
    @g_syl5 (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc))) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.imp (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc))) (.classMem (.cv k) (syn_cnnc)))) p0228 p0231
  have p0233 :=
    @g_pm2_43d (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc))) (.classMem (.cv k) (syn_cnnc))) p0232
  have p0234 :=
    (by simpa [syn_wb, syn_w3a] using (Nominal.biimpRefl (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))))
  have p0235 :=
    @g_syl6ibr (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc))) (.classMem (.cv k) (syn_cnnc))) (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) p0233 p0234
  have p0236 :=
    @g_breq1 (.cv x) (.cv y) (.cv a) (syn_ckqrel (syn_clefin))
  have p0237 :=
    @g_anbi1d (.classEq (.cv x) (.cv y)) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z)) p0236
  have p0238 :=
    @g_breq1 (.cv x) (.cv y) (.cv z) (syn_ckqrel (syn_clefin))
  have p0239 :=
    @g_imbi12d (.classEq (.cv x) (.cv y)) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wa (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)) p0237 p0238
  have p0240 :=
    @g_breq2 (.cv a) (syn_cplc (.cv y) (syn_c1c)) (.cv y) (syn_ckqrel (syn_clefin))
  have p0241 :=
    @g_breq1 (.cv a) (syn_cplc (.cv y) (syn_c1c)) (.cv z) (syn_ckqrel (syn_clefin))
  have p0242 :=
    @g_anbi12d (.classEq (.cv a) (syn_cplc (.cv y) (syn_c1c))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z)) p0240 p0241
  have p0243 :=
    @g_imbi1d (.classEq (.cv a) (syn_cplc (.cv y) (syn_c1c))) (syn_wa (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wa (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)) p0242
  have p0244 :=
    @g_breq2 (.cv z) (.cv k) (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin))
  have p0245 :=
    @g_anbi2d (.classEq (.cv z) (.cv k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) p0244
  have p0246 :=
    @g_breq2 (.cv z) (.cv k) (.cv y) (syn_ckqrel (syn_clefin))
  have p0247 :=
    @g_imbi12d (.classEq (.cv z) (.cv k)) (syn_wa (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wa (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)) p0245 p0246
  have p0248 :=
    @g_rspc3v (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z))) (.imp (syn_wa (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k))) (.imp (syn_wa (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))) (.imp (syn_wa (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))) x a z (.cv y) (syn_cplc (.cv y) (syn_c1c)) (.cv k) (syn_cnnc) (syn_cnnc) (syn_cnnc) dv_cache_0019 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0029 dv_cache_0029 dv_cache_0027 dv_cache_0029 dv_cache_0027 dv_cache_0025 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0037 dv_cache_0038 dv_cache_0039 p0239 p0243 p0247
  have p0249 :=
    @g_syl6 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (.imp (syn_wral x (syn_cnnc) (syn_wral a (syn_cnnc) (syn_wral z (syn_cnnc) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))))) (.imp (syn_wa (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)))) p0235 p0248
  have p0250 :=
    @g_mpdi (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wral x (syn_cnnc) (syn_wral a (syn_cnnc) (syn_wral z (syn_cnnc) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))))) (.imp (syn_wa (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k))) p0223 p0249
  have p0251 :=
    @g_syl7bi (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c)))) (syn_wa (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)) p0199 p0250
  have p0252 :=
    @g_exp4a (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)) p0251
  have p0253 :=
    Nominal.ax2 (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0254 :=
    @g_syl6 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.imp (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (.imp (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)))) (.imp (.imp (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c)))) (.imp (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)))) p0252 p0253
  have p0255 :=
    @g_mpdi (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.imp (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv y) (syn_c1c)))) (.imp (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k))) p0198 p0254
  have p0256 :=
    @g_mpdi (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)) p0181 p0255
  have p0257 :=
    @g_syl5 (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)) p0180 p0256
  have p0258 :=
    @g_pm3_2 (syn_wa (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0259 :=
    @g_syl9 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wa (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k))) p0257 p0258
  have p0260 :=
    @g_syl5 (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.imp (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)))) p0177 p0259
  have p0261 :=
    @g_pm2_43d (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k))) p0260
  have p0262 :=
    (by simpa [syn_wb, syn_w3a] using (Nominal.biimpRefl (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)))))
  have p0263 :=
    @g_syl6ibr (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k))) p0261 p0262
  have p0264 :=
    @g_wppfrecprefixeqvalndv (.cv y) k (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) p0134 p0143 p0144 p0084 p0119 p0120
  have p0265 :=
    @g_biimpd (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (.imp (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))) p0264
  have p0266 :=
    @g_n_3imp (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))) p0265
  have p0267 :=
    @g_syl6 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv k))) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))) p0263 p0266
  have p0268 :=
    @g_fveq2 (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)) (syn_cwppstopstep F C)
  have p0269 :=
    @g_syl6 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))) (.classEq (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))) p0267 p0268
  have p0270 :=
    @g_eqeq2 (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c)))
  have p0271 :=
    @g_syl6 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classEq (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))) (syn_wb (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))))) p0269 p0270
  have p0272 :=
    @g_bi1 (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))))
  have p0273 :=
    @g_syl6 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wb (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))))) (.imp (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))))) p0271 p0272
  have p0274 :=
    @g_mpdi (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))) p0174 p0273
  have p0275 :=
    @g_simp1 (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0276 :=
    @g_simp3 (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0277 :=
    @g_jca (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) p0275 p0276
  have p0278 :=
    @g_simpl (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0279 :=
    @g_kqfinsucnle (.cv y)
  have p0280 :=
    @g_syl (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classMem (.cv y) (syn_cnnc)) (.neg (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y))) p0278 p0279
  have p0281 :=
    @g_notnot2 (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))
  have p0282 :=
    @g_simpr (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))
  have p0283 :=
    @g_simpl (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))
  have p0284 :=
    @g_simpr (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0285 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) p0283 p0284
  have p0286 :=
    @g_a1d (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) p0285
  have p0287 :=
    @g_ancom (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0288 :=
    @g_finlewe
  have p0289 :=
    @g_wppwepo (syn_cnnc) (syn_ckqrel (syn_clefin))
  have p0290 :=
    Nominal.mp p0288 p0289
  have p0291 :=
    @g_porta (syn_cnnc) (syn_ckqrel (syn_clefin))
  have p0292 :=
    @g_mpbi (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cpartial) (syn_cnnc)) (syn_w3a (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cref) (syn_cnnc)) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc)) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cantisym) (syn_cnnc))) p0290 p0291
  have p0293 :=
    @g_simp2 (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cref) (syn_cnnc)) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc)) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cantisym) (syn_cnnc))
  have p0294 :=
    Nominal.mp p0292 p0293
  have p0295 :=
    @g_a1i (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc)) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) p0294
  have p0296 :=
    @g_brex (syn_ckqrel (syn_clefin)) (syn_cnnc) (syn_ctrans)
  have p0297 :=
    @g_breq (.cv x) (.cv a) (.cv r) (syn_ckqrel (syn_clefin))
  have p0298 :=
    @g_breq (.cv a) (.cv z) (.cv r) (syn_ckqrel (syn_clefin))
  have p0299 :=
    @g_anbi12d (.classEq (.cv r) (syn_ckqrel (syn_clefin))) (syn_wbr (.cv x) (.cv r) (.cv a)) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (.cv r) (.cv z)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z)) p0297 p0298
  have p0300 :=
    @g_breq (.cv x) (.cv z) (.cv r) (syn_ckqrel (syn_clefin))
  have p0301 :=
    @g_imbi12d (.classEq (.cv r) (syn_ckqrel (syn_clefin))) (syn_wa (syn_wbr (.cv x) (.cv r) (.cv a)) (syn_wbr (.cv a) (.cv r) (.cv z))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z)) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)) p0299 p0300
  have p0302 :=
    @g_ralbidv (.classEq (.cv r) (syn_ckqrel (syn_clefin))) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv a)) (syn_wbr (.cv a) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z))) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z))) z (.cv b) dv_cache_0021 p0301
  have p0303 :=
    @g_n_2ralbidv (.classEq (.cv r) (syn_ckqrel (syn_clefin))) (syn_wral z (.cv b) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv a)) (syn_wbr (.cv a) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z)))) (syn_wral z (.cv b) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))) x a (.cv b) (.cv b) dv_cache_0022 dv_cache_0023 p0302
  have p0304 :=
    @g_raleq (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z))) z (.cv b) (syn_cnnc) dv_cache_0024 dv_cache_0025
  have p0305 :=
    @g_raleqbi1dv (syn_wral z (.cv b) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))) (syn_wral z (syn_cnnc) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))) a (.cv b) (syn_cnnc) dv_cache_0026 dv_cache_0027 p0304
  have p0306 :=
    @g_raleqbi1dv (syn_wral a (.cv b) (syn_wral z (.cv b) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z))))) (syn_wral a (syn_cnnc) (syn_wral z (syn_cnnc) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z))))) x (.cv b) (syn_cnnc) dv_cache_0028 dv_cache_0029 p0305
  have p0307 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_trans x a z r b dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
  have p0308 :=
    @g_brabg (syn_wral x (.cv b) (syn_wral a (.cv b) (syn_wral z (.cv b) (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv a)) (syn_wbr (.cv a) (.cv r) (.cv z))) (syn_wbr (.cv x) (.cv r) (.cv z)))))) (syn_wral x (.cv b) (syn_wral a (.cv b) (syn_wral z (.cv b) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))))) (syn_wral x (syn_cnnc) (syn_wral a (syn_cnnc) (syn_wral z (syn_cnnc) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))))) r b (syn_ckqrel (syn_clefin)) (syn_cnnc) (syn_cvv) (syn_cvv) (syn_ctrans) dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 p0303 p0306 p0307
  have p0309 :=
    @g_syl (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc)) (syn_wa (.classMem (syn_ckqrel (syn_clefin)) (syn_cvv)) (.classMem (syn_cnnc) (syn_cvv))) (syn_wb (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc)) (syn_wral x (syn_cnnc) (syn_wral a (syn_cnnc) (syn_wral z (syn_cnnc) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z))))))) p0296 p0308
  have p0310 :=
    @g_ibi (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc)) (syn_wral x (syn_cnnc) (syn_wral a (syn_cnnc) (syn_wral z (syn_cnnc) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))))) p0309
  have p0311 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc)) (syn_wral x (syn_cnnc) (syn_wral a (syn_cnnc) (syn_wral z (syn_cnnc) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))))) p0295 p0310
  have p0312 :=
    @g_simpl (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))
  have p0313 :=
    @g_simpl (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0314 :=
    @g_peano2 (.cv y)
  have p0315 :=
    @g_syl (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classMem (.cv y) (syn_cnnc)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) p0313 p0314
  have p0316 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) p0312 p0315
  have p0317 :=
    @g_simpl (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))
  have p0318 :=
    @g_syl5 (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv k) (syn_cnnc)) p0317 p0229
  have p0319 :=
    @g_pm3_2 (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))
  have p0320 :=
    @g_syl9 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (.classMem (.cv k) (syn_cnnc)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (syn_wa (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) p0318 p0319
  have p0321 :=
    @g_syl5 (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.imp (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wa (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))) p0316 p0320
  have p0322 :=
    @g_pm2_43d (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wa (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) p0321
  have p0323 :=
    @g_simpl (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))
  have p0324 :=
    @g_simpl (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0325 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classMem (.cv y) (syn_cnnc)) p0323 p0324
  have p0326 :=
    @g_pm3_2 (syn_wa (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (.classMem (.cv y) (syn_cnnc))
  have p0327 :=
    @g_syl5 (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (.classMem (.cv y) (syn_cnnc)) (syn_wa (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (syn_wa (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (.classMem (.cv y) (syn_cnnc))) p0325 p0326
  have p0328 :=
    @g_syl6 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wa (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (.imp (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wa (syn_wa (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (.classMem (.cv y) (syn_cnnc)))) p0322 p0327
  have p0329 :=
    @g_pm2_43d (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wa (syn_wa (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (.classMem (.cv y) (syn_cnnc))) p0328
  have p0330 :=
    (by simpa [syn_wb, syn_w3a] using (Nominal.biimpRefl (syn_w3a (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))))
  have p0331 :=
    @g_syl6ibr (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wa (syn_wa (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (.classMem (.cv y) (syn_cnnc))) (syn_w3a (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) p0329 p0330
  have p0332 :=
    @g_breq1 (.cv x) (syn_cplc (.cv y) (syn_c1c)) (.cv a) (syn_ckqrel (syn_clefin))
  have p0333 :=
    @g_anbi1d (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z)) p0332
  have p0334 :=
    @g_breq1 (.cv x) (syn_cplc (.cv y) (syn_c1c)) (.cv z) (syn_ckqrel (syn_clefin))
  have p0335 :=
    @g_imbi12d (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z)) p0333 p0334
  have p0336 :=
    @g_breq2 (.cv a) (.cv k) (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin))
  have p0337 :=
    @g_breq1 (.cv a) (.cv k) (.cv z) (syn_ckqrel (syn_clefin))
  have p0338 :=
    @g_anbi12d (.classEq (.cv a) (.cv k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)) p0336 p0337
  have p0339 :=
    @g_imbi1d (.classEq (.cv a) (.cv k)) (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z)) p0338
  have p0340 :=
    @g_breq2 (.cv z) (.cv y) (.cv k) (syn_ckqrel (syn_clefin))
  have p0341 :=
    @g_anbi2d (.classEq (.cv z) (.cv y)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) p0340
  have p0342 :=
    @g_breq2 (.cv z) (.cv y) (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin))
  have p0343 :=
    @g_imbi12d (.classEq (.cv z) (.cv y)) (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)) p0341 p0342
  have p0344 :=
    @g_rspc3v (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z))) (.imp (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y))) (.imp (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z))) (.imp (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv z))) x a z (syn_cplc (.cv y) (syn_c1c)) (.cv k) (.cv y) (syn_cnnc) (syn_cnnc) (syn_cnnc) dv_cache_0055 dv_cache_0049 dv_cache_0050 dv_cache_0056 dv_cache_0051 dv_cache_0048 dv_cache_0029 dv_cache_0029 dv_cache_0027 dv_cache_0029 dv_cache_0027 dv_cache_0025 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0037 dv_cache_0038 dv_cache_0039 p0335 p0339 p0343
  have p0345 :=
    @g_syl6 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_w3a (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))) (.imp (syn_wral x (syn_cnnc) (syn_wral a (syn_cnnc) (syn_wral z (syn_cnnc) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))))) (.imp (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)))) p0331 p0344
  have p0346 :=
    @g_mpdi (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wral x (syn_cnnc) (syn_wral a (syn_cnnc) (syn_wral z (syn_cnnc) (.imp (syn_wa (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv a)) (syn_wbr (.cv a) (syn_ckqrel (syn_clefin)) (.cv z))) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv z)))))) (.imp (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y))) p0311 p0345
  have p0347 :=
    @g_syl7bi (syn_wa (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)) p0287 p0346
  have p0348 :=
    @g_exp4a (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)) p0347
  have p0349 :=
    Nominal.ax2 (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y))
  have p0350 :=
    @g_syl6 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (.imp (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) (.imp (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)))) (.imp (.imp (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.imp (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)))) p0348 p0349
  have p0351 :=
    @g_mpdi (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (.imp (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.imp (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y))) p0286 p0350
  have p0352 :=
    @g_mpdi (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)) p0282 p0351
  have p0353 :=
    @g_exp3a (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)) p0352
  have p0354 :=
    @g_syl7 (.neg (.neg (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)) p0281 p0353
  have p0355 :=
    @g_notnot1 (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y))
  have p0356 :=
    @g_syl8 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.neg (.neg (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)))) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)) (.neg (.neg (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)))) p0354 p0355
  have p0357 :=
    Nominal.ax3 (.neg (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (.neg (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)))
  have p0358 :=
    @g_syl6 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.imp (.neg (.neg (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)))) (.neg (.neg (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y))))) (.imp (.neg (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y))) (.neg (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)))) p0356 p0357
  have p0359 :=
    @g_mpdi (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.neg (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y))) (.neg (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) p0280 p0358
  have p0360 :=
    @g_notnot2 (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))
  have p0361 :=
    @g_simpl (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0362 :=
    @g_pm3_2 (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))
  have p0363 :=
    @g_n_3pm3_2i (.classMem (syn_cwppstopstep F (syn_ctc C)) (syn_cfuns)) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) (syn_wss (syn_crn (syn_cwppstopstep F (syn_ctc C))) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) p0084 p0119 p0120
  have p0364 :=
    @g_elwpphitvndv (syn_ctc C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (.cv y)
  have p0365 :=
    Nominal.mp p0363 p0364
  have p0366 :=
    @g_biimpri (.classMem (.cv y) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))) p0365
  have p0367 :=
    @g_syl6 (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))) (.classMem (.cv y) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) p0362 p0366
  have p0368 :=
    @g_simprd (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))) p0057
  have p0369 :=
    @g_id (.classEq (.cv n) (.cv q))
  have p0370 :=
    @g_eleq1d (.classEq (.cv n) (.cv q)) (.cv n) (.cv q) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C)) p0369
  have p0371 :=
    @g_id (.classEq (.cv n) (.cv q))
  have p0372 :=
    @g_breq2d (.classEq (.cv n) (.cv q)) (.cv n) (.cv q) (.cv k) (syn_ckqrel (syn_clefin)) p0371
  have p0373 :=
    @g_imbi12d (.classEq (.cv n) (.cv q)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (.classMem (.cv q) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)) p0370 p0372
  have p0374_e00_recanon : Nominal.NPrf (.imp (.objEq n q) (syn_wb (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))) (.imp (.classMem (.cv q) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cwpphit syn_cima syn_wrex syn_wex syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_ccnv syn_copab syn_cfrec syn_cclos1 syn_cint syn_csn syn_cpprod syn_ctxp syn_cin syn_ccom syn_cmpt syn_cvv syn_cplc syn_c1c syn_cwppstopstep syn_ctc syn_cio syn_cuni
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0373
  have p0374 :=
    @g_cbvralv (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))) (.imp (.classMem (.cv q) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q))) n q (syn_cnnc) dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 p0374_e00_recanon
  have p0375 :=
    @g_sylib (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))) p0368 p0374
  have p0376 :=
    (by simpa [syn_cwpphit] using (Nominal.classEqRefl (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))))
  have p0377 :=
    @g_eqid (syn_cwppstopstep F (syn_ctc C))
  have p0378 :=
    @g_pm3_2i (.classEq (syn_cwppstopstep F (syn_ctc C)) (syn_cwppstopstep F (syn_ctc C))) (.classEq (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))) p0377 p0074
  have p0379 :=
    @g_freceq12 (syn_cwppstopstep F (syn_ctc C)) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))
  have p0380 :=
    Nominal.mp p0378 p0379
  have p0381 :=
    @g_cnveqi (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))) p0380
  have p0382 :=
    @g_imaeq1i (syn_ccnv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))) (syn_ccnv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))))) (syn_cima (syn_clec) (syn_csn (syn_ctc C))) p0381
  have p0383 :=
    @g_eqtri (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)) (syn_cima (syn_ccnv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))) (syn_cima (syn_clec) (syn_csn (syn_ctc C)))) (syn_cima (syn_ccnv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))))) (syn_cima (syn_clec) (syn_csn (syn_ctc C)))) p0376 p0382
  have p0384 :=
    (by simpa [syn_cwpphit] using (Nominal.classEqRefl (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))))
  have p0385 :=
    @g_eqtr4i (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)) (syn_cima (syn_ccnv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))))) (syn_cima (syn_clec) (syn_csn (syn_ctc C)))) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C)) p0383 p0384
  have p0386 :=
    @g_eleq2i (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C)) (.cv q) p0385
  have p0387 :=
    @g_imbi1i (.classMem (.cv q) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (.classMem (.cv q) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)) p0386
  have p0388 :=
    @g_ralbii (.imp (.classMem (.cv q) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q))) (.imp (.classMem (.cv q) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q))) q (syn_cnnc) p0387
  have p0389 :=
    @g_sylibr (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))) p0375 p0388
  have p0390 :=
    @g_id (.classEq (.cv q) (.cv y))
  have p0391 :=
    @g_eleq1d (.classEq (.cv q) (.cv y)) (.cv q) (.cv y) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)) p0390
  have p0392 :=
    @g_id (.classEq (.cv q) (.cv y))
  have p0393 :=
    @g_breq2d (.classEq (.cv q) (.cv y)) (.cv q) (.cv y) (.cv k) (syn_ckqrel (syn_clefin)) p0392
  have p0394 :=
    @g_imbi12d (.classEq (.cv q) (.cv y)) (.classMem (.cv q) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (.classMem (.cv y) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) p0391 p0393
  have p0395 :=
    @g_rspcv (.imp (.classMem (.cv q) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q))) (.imp (.classMem (.cv y) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) q (.cv y) (syn_cnnc) dv_cache_0064 dv_cache_0061 dv_cache_0065 p0394
  have p0396 :=
    @g_syl5com (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))) (.classMem (.cv y) (syn_cnnc)) (.imp (.classMem (.cv y) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) p0389 p0395
  have p0397 :=
    @g_a1dd (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv y) (syn_cnnc)) (.imp (.classMem (.cv y) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))) p0396
  have p0398 :=
    Nominal.ax2 (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))) (.classMem (.cv y) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))
  have p0399 :=
    @g_syl6 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv y) (syn_cnnc)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))) (.imp (.classMem (.cv y) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)))) (.imp (.imp (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))) (.classMem (.cv y) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (.imp (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)))) p0397 p0398
  have p0400 :=
    @g_mpdi (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv y) (syn_cnnc)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))) (.classMem (.cv y) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (.imp (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) p0367 p0399
  have p0401 :=
    @g_syl5 (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classMem (.cv y) (syn_cnnc)) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.imp (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) p0361 p0400
  have p0402 :=
    @g_syl7 (.neg (.neg (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) p0360 p0401
  have p0403 :=
    @g_notnot1 (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))
  have p0404 :=
    @g_syl8 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.neg (.neg (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)) (.neg (.neg (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)))) p0402 p0403
  have p0405 :=
    Nominal.ax3 (.neg (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))) (.neg (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y)))
  have p0406 :=
    @g_syl6 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.imp (.neg (.neg (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))))) (.neg (.neg (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))))) (.imp (.neg (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (.neg (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))))) p0404 p0405
  have p0407 :=
    @g_mpdd (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.neg (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv y))) (.neg (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))) p0359 p0406
  have p0408 :=
    @g_simpl (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0409 :=
    @g_wppstopstepfunsndv (syn_ctc C) F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0410 :=
    @g_wppstopstepdmndv (syn_ctc C) F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0411 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F (syn_ctc C))) (syn_chwcards (syn_cvv)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) p0410
  have p0412 :=
    @g_biimpri (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_chwcards (syn_cvv))) p0411
  have p0413 :=
    Nominal.mp p0115 p0412
  have p0414 :=
    @g_wppstopsteprndmndv (syn_ctc C) F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0415 :=
    @g_wppstopstepdmndv (syn_ctc C) F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0416 :=
    @g_wpporbithwcldmndv (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) q dv_cache_0066 dv_cache_0067 p0409 p0413 p0414 p0415
  have p0417 :=
    @g_hwcardstcclndv C
  have p0418 :=
    Nominal.mp hyp_wppstopfixedhitcontrgrowfixdndv_3 p0417
  have p0419 :=
    @g_a1i (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wa (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_chwcards (syn_cvv)))) p0418
  have p0420 :=
    @g_simpr (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_chwcards (syn_cvv)))
  have p0421 :=
    @g_jca (syn_wa (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_chwcards (syn_cvv)))) (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_chwcards (syn_cvv))) p0419 p0420
  have p0422 :=
    @g_hwcardslecconnexndv (syn_ctc C) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q))
  have p0423 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_chwcards (syn_cvv)))) (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_chwcards (syn_cvv)))) (syn_wo (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q))) (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_clec) (syn_ctc C))) p0421 p0422
  have p0424 :=
    @g_notnot (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)))
  have p0425 :=
    @g_biimpi (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q))) (.neg (.neg (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q))))) p0424
  have p0426 :=
    @g_pm2_21 (.neg (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_clec) (syn_ctc C))
  have p0427 :=
    @g_syl (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q))) (.neg (.neg (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q))))) (.imp (.neg (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_clec) (syn_ctc C))) p0425 p0426
  have p0428 :=
    @g_id (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_clec) (syn_ctc C))
  have p0429 :=
    @g_a1d (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_clec) (syn_ctc C)) (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_clec) (syn_ctc C)) (.neg (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)))) p0428
  have p0430 :=
    @g_jaoi (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q))) (.imp (.neg (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_clec) (syn_ctc C))) (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_clec) (syn_ctc C)) p0427 p0429
  have p0431 :=
    @g_syl (syn_wa (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_chwcards (syn_cvv)))) (syn_wo (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q))) (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_clec) (syn_ctc C))) (.imp (.neg (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_clec) (syn_ctc C))) p0423 p0430
  have p0432 :=
    @g_ralimiaa (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_chwcards (syn_cvv))) (.imp (.neg (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_clec) (syn_ctc C))) q (syn_cnnc) p0431
  have p0433 :=
    Nominal.mp p0416 p0432
  have p0434 :=
    @g_id (.classEq (.cv q) (.cv y))
  have p0435 :=
    @g_fveq2d (.classEq (.cv q) (.cv y)) (.cv q) (.cv y) (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) p0434
  have p0436 :=
    @g_breq2d (.classEq (.cv q) (.cv y)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)) (syn_ctc C) (syn_clec) p0435
  have p0437 :=
    @g_notbid (.classEq (.cv q) (.cv y)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))) p0436
  have p0438 :=
    @g_id (.classEq (.cv q) (.cv y))
  have p0439 :=
    @g_fveq2d (.classEq (.cv q) (.cv y)) (.cv q) (.cv y) (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) p0438
  have p0440 :=
    @g_breq1d (.classEq (.cv q) (.cv y)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)) (syn_ctc C) (syn_clec) p0439
  have p0441 :=
    @g_imbi12d (.classEq (.cv q) (.cv y)) (.neg (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)))) (.neg (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))) (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_clec) (syn_ctc C)) (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)) (syn_clec) (syn_ctc C)) p0437 p0440
  have p0442 :=
    @g_rspcv (.imp (.neg (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_clec) (syn_ctc C))) (.imp (.neg (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))) (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)) (syn_clec) (syn_ctc C))) q (.cv y) (syn_cnnc) dv_cache_0064 dv_cache_0061 dv_cache_0068 p0441
  have p0443 :=
    @g_mpi (.classMem (.cv y) (syn_cnnc)) (syn_wral q (syn_cnnc) (.imp (.neg (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)))) (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_clec) (syn_ctc C)))) (.imp (.neg (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))) (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)) (syn_clec) (syn_ctc C))) p0433 p0442
  have p0444 :=
    @g_syl (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classMem (.cv y) (syn_cnnc)) (.imp (.neg (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))) (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)) (syn_clec) (syn_ctc C))) p0408 p0443
  have p0445 :=
    @g_sylcom (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.neg (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))) (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)) (syn_clec) (syn_ctc C)) p0407 p0444
  have p0446 :=
    @g_simpl (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0447 :=
    @g_wppstopstepfunsndv (syn_ctc C) F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0448 :=
    @g_wppstopstepdmndv (syn_ctc C) F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0449 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F (syn_ctc C))) (syn_chwcards (syn_cvv)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) p0448
  have p0450 :=
    @g_biimpri (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_chwcards (syn_cvv))) p0449
  have p0451 :=
    Nominal.mp p0115 p0450
  have p0452 :=
    @g_wppstopsteprndmndv (syn_ctc C) F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0453 :=
    @g_n_3pm3_2i (.classMem (syn_cwppstopstep F (syn_ctc C)) (syn_cfuns)) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) (syn_wss (syn_crn (syn_cwppstopstep F (syn_ctc C))) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) p0447 p0451 p0452
  have p0454 :=
    @g_a1i (syn_w3a (.classMem (syn_cwppstopstep F (syn_ctc C)) (syn_cfuns)) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) (syn_wss (syn_crn (syn_cwppstopstep F (syn_ctc C))) (syn_cdm (syn_cwppstopstep F (syn_ctc C))))) (.classMem (.cv q) (syn_cnnc)) p0453
  have p0455 :=
    @g_id (.classMem (.cv q) (syn_cnnc))
  have p0456 :=
    @g_jca (.classMem (.cv q) (syn_cnnc)) (syn_w3a (.classMem (syn_cwppstopstep F (syn_ctc C)) (syn_cfuns)) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) (syn_wss (syn_crn (syn_cwppstopstep F (syn_ctc C))) (syn_cdm (syn_cwppstopstep F (syn_ctc C))))) (.classMem (.cv q) (syn_cnnc)) p0454 p0455
  have p0457 :=
    @g_frecdomfv (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (.cv q)
  have p0458 :=
    @g_syl (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_w3a (.classMem (syn_cwppstopstep F (syn_ctc C)) (syn_cfuns)) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) (syn_wss (syn_crn (syn_cwppstopstep F (syn_ctc C))) (syn_cdm (syn_cwppstopstep F (syn_ctc C))))) (.classMem (.cv q) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) p0456 p0457
  have p0459 :=
    @g_wppstopstepdmndv (syn_ctc C) F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0460 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F (syn_ctc C))) (syn_chwcards (syn_cvv)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) p0459
  have p0461 :=
    @g_biimpi (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_chwcards (syn_cvv))) p0460
  have p0462 :=
    @g_syl (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_chwcards (syn_cvv))) p0458 p0461
  have p0463 :=
    @g_wppstopstepsamebelowdndv y C F p dv_cache_0069 dv_cache_0070 dv_cache_0071 hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2 hyp_wppstopfixedhitcontrgrowfixdndv_3 hyp_wppstopfixedhitcontrgrowfixdndv_4 hyp_wppstopfixedhitcontrgrowfixdndv_5
  have p0464 :=
    @g_rgen (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc C)) (.classEq (syn_cfv (syn_cwppstopstep F C) (.cv y)) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (.cv y)))) y (syn_chwcards (syn_cvv)) p0463
  have p0465 :=
    @g_id (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)))
  have p0466 :=
    @g_breq1d (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q))) (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_ctc C) (syn_clec) p0465
  have p0467 :=
    @g_id (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)))
  have p0468 :=
    @g_fveq2d (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q))) (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_cwppstopstep F C) p0467
  have p0469 :=
    @g_id (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)))
  have p0470 :=
    @g_fveq2d (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q))) (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_cwppstopstep F (syn_ctc C)) p0469
  have p0471 :=
    @g_eqeq12d (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q))) (syn_cfv (syn_cwppstopstep F C) (.cv y)) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (.cv y)) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q))) p0468 p0470
  have p0472 :=
    @g_imbi12d (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q))) (syn_wbr (.cv y) (syn_clec) (syn_ctc C)) (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_clec) (syn_ctc C)) (.classEq (syn_cfv (syn_cwppstopstep F C) (.cv y)) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (.cv y))) (.classEq (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)))) p0466 p0471
  have p0473 :=
    @g_rspcv (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc C)) (.classEq (syn_cfv (syn_cwppstopstep F C) (.cv y)) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (.cv y)))) (.imp (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_clec) (syn_ctc C)) (.classEq (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q))))) y (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_chwcards (syn_cvv)) dv_cache_0072 dv_cache_0073 dv_cache_0074 p0472
  have p0474 :=
    @g_mpi (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_chwcards (syn_cvv))) (syn_wral y (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc C)) (.classEq (syn_cfv (syn_cwppstopstep F C) (.cv y)) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (.cv y))))) (.imp (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_clec) (syn_ctc C)) (.classEq (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q))))) p0464 p0473
  have p0475 :=
    @g_syl (.classMem (.cv q) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_clec) (syn_ctc C)) (.classEq (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q))))) p0462 p0474
  have p0476 :=
    @g_rgen (.imp (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_clec) (syn_ctc C)) (.classEq (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q))))) q (syn_cnnc) p0475
  have p0477 :=
    @g_id (.classEq (.cv q) (.cv y))
  have p0478 :=
    @g_fveq2d (.classEq (.cv q) (.cv y)) (.cv q) (.cv y) (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) p0477
  have p0479 :=
    @g_breq1d (.classEq (.cv q) (.cv y)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)) (syn_ctc C) (syn_clec) p0478
  have p0480 :=
    @g_id (.classEq (.cv q) (.cv y))
  have p0481 :=
    @g_fveq2d (.classEq (.cv q) (.cv y)) (.cv q) (.cv y) (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) p0480
  have p0482 :=
    @g_fveq2d (.classEq (.cv q) (.cv y)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)) (syn_cwppstopstep F C) p0481
  have p0483 :=
    @g_id (.classEq (.cv q) (.cv y))
  have p0484 :=
    @g_fveq2d (.classEq (.cv q) (.cv y)) (.cv q) (.cv y) (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) p0483
  have p0485 :=
    @g_fveq2d (.classEq (.cv q) (.cv y)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)) (syn_cwppstopstep F (syn_ctc C)) p0484
  have p0486 :=
    @g_eqeq12d (.classEq (.cv q) (.cv y)) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q))) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))) p0482 p0485
  have p0487 :=
    @g_imbi12d (.classEq (.cv q) (.cv y)) (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_clec) (syn_ctc C)) (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)) (syn_clec) (syn_ctc C)) (.classEq (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)))) (.classEq (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))) p0479 p0486
  have p0488 :=
    @g_rspcv (.imp (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_clec) (syn_ctc C)) (.classEq (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q))))) (.imp (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)) (syn_clec) (syn_ctc C)) (.classEq (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))))) q (.cv y) (syn_cnnc) dv_cache_0064 dv_cache_0061 dv_cache_0075 p0487
  have p0489 :=
    @g_mpi (.classMem (.cv y) (syn_cnnc)) (syn_wral q (syn_cnnc) (.imp (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_clec) (syn_ctc C)) (.classEq (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)))))) (.imp (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)) (syn_clec) (syn_ctc C)) (.classEq (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))))) p0476 p0488
  have p0490 :=
    @g_syl (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classMem (.cv y) (syn_cnnc)) (.imp (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)) (syn_clec) (syn_ctc C)) (.classEq (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))))) p0446 p0489
  have p0491 :=
    @g_sylcom (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)) (syn_clec) (syn_ctc C)) (.classEq (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))) p0445 p0490
  have p0492 :=
    @g_syl5 (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classEq (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))) p0277 p0491
  have p0493 :=
    @g_eqeq2 (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c)))
  have p0494 :=
    @g_syl6 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classEq (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))) (syn_wb (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))))) p0492 p0493
  have p0495 :=
    @g_bi1 (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))))
  have p0496 :=
    @g_syl6 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wb (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))))) (.imp (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))))) p0494 p0495
  have p0497 :=
    @g_mpdd (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))) p0274 p0496
  have p0498 :=
    @g_n_3pm3_2i (.classMem (syn_cwppstopstep F (syn_ctc C)) (syn_cfuns)) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) (syn_wss (syn_crn (syn_cwppstopstep F (syn_ctc C))) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) p0084 p0119 p0120
  have p0499 :=
    @g_a1i (syn_w3a (.classMem (syn_cwppstopstep F (syn_ctc C)) (syn_cfuns)) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) (syn_wss (syn_crn (syn_cwppstopstep F (syn_ctc C))) (syn_cdm (syn_cwppstopstep F (syn_ctc C))))) (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) p0498
  have p0500 :=
    @g_simp1 (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0501 :=
    @g_jca (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_w3a (.classMem (syn_cwppstopstep F (syn_ctc C)) (syn_cfuns)) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) (syn_wss (syn_crn (syn_cwppstopstep F (syn_ctc C))) (syn_cdm (syn_cwppstopstep F (syn_ctc C))))) (.classMem (.cv y) (syn_cnnc)) p0499 p0500
  have p0502 :=
    @g_wpporbitsucndv (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (.cv y)
  have p0503 :=
    @g_syl (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (syn_w3a (.classMem (syn_cwppstopstep F (syn_ctc C)) (syn_cfuns)) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) (syn_wss (syn_crn (syn_cwppstopstep F (syn_ctc C))) (syn_cdm (syn_cwppstopstep F (syn_ctc C))))) (.classMem (.cv y) (syn_cnnc))) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))) p0501 p0502
  have p0504 :=
    @g_eqcomd (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))) p0503
  have p0505 :=
    @g_eqeq2d (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y))) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c))) p0504
  have p0506 :=
    @g_mpbidi (syn_w3a (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv y)))) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c)))) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) p0497 p0505
  have p0507 :=
    @g_n_3expd (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c)))) p0506
  have p0508 :=
    @g_peano2 (.cv y)
  have p0509 :=
    @g_wppfrecprefixeqvalndv (syn_cplc (.cv y) (syn_c1c)) k (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) p0134 p0143 p0144 p0084 p0119 p0120
  have p0510 :=
    @g_syl (.classMem (.cv y) (syn_cnnc)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc)) (syn_wb (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (.imp (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c)))))) p0508 p0509
  have p0511 :=
    @g_biimprd (.classMem (.cv y) (syn_cnnc)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (.imp (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c))))) p0510
  have p0512 :=
    @g_a1d (.classMem (.cv y) (syn_cnnc)) (.imp (.imp (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c))))) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) p0511
  have p0513 :=
    @g_a2d (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (.imp (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c))))) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) p0512
  have p0514 :=
    @g_sylcom (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv y) (syn_cnnc)) (.imp (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (.imp (syn_wbr (syn_cplc (.cv y) (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c))) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cplc (.cv y) (syn_c1c)))))) (.imp (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))) p0507 p0513
  have p0515 :=
    @g_adantrd (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv y) (syn_cnnc)) (.imp (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))) syn_wtru p0514
  have p0516 :=
    @g_syl7bi (.classMem (.cv y) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)))) (.classMem (.cv y) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv y) (syn_cnnc)) syn_wtru) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) p0168 p0515
  have p0517 :=
    @g_n_1cex
  have p0518 :=
    @g_addcex (.cv y) (syn_c1c) p0165 p0517
  have p0519 :=
    @g_id (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c)))
  have p0520 :=
    @g_eleq1d (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.cv x) (syn_cplc (.cv y) (syn_c1c)) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k) p0519
  have p0521 :=
    @g_elab (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) x (syn_cplc (.cv y) (syn_c1c)) dv_cache_0055 dv_cache_0076 p0518 p0520
  have p0522 :=
    @g_biimpri (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)))) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) p0521
  have p0523 :=
    @g_syl8 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv y) (syn_cnnc)) syn_wtru) (.classMem (.cv y) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)))) (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)))) p0516 p0522
  have p0524 :=
    @g_ancomsd (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv y) (syn_cnnc)) syn_wtru (.imp (.classMem (.cv y) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)))) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))))) p0523
  have p0525 :=
    @g_exp3a (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) syn_wtru (.classMem (.cv y) (syn_cnnc)) (.imp (.classMem (.cv y) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)))) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))))) p0524
  have p0526 :=
    @g_ralrimdv (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) syn_wtru (.imp (.classMem (.cv y) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)))) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))))) y (syn_cnnc) dv_cache_0077 dv_cache_0078 p0525
  have p0527 :=
    @g_pm3_2 (syn_wa (.classMem (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))) (syn_cvv)) (.classMem (syn_c0c) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))))) (syn_wral y (syn_cnnc) (.imp (.classMem (.cv y) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)))) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))))))
  have p0528 :=
    @g_syl9 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) syn_wtru (syn_wral y (syn_cnnc) (.imp (.classMem (.cv y) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)))) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)))))) (syn_wa (.classMem (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))) (syn_cvv)) (.classMem (syn_c0c) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))))) (syn_wa (syn_wa (.classMem (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))) (syn_cvv)) (.classMem (syn_c0c) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))))) (syn_wral y (syn_cnnc) (.imp (.classMem (.cv y) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)))) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))))))) p0526 p0527
  have p0529 :=
    @g_syl5 syn_wtru (syn_wa (.classMem (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))) (syn_cvv)) (.classMem (syn_c0c) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))))) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.imp syn_wtru (syn_wa (syn_wa (.classMem (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))) (syn_cvv)) (.classMem (syn_c0c) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))))) (syn_wral y (syn_cnnc) (.imp (.classMem (.cv y) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)))) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)))))))) p0164 p0528
  have p0530 :=
    @g_pm2_43d (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) syn_wtru (syn_wa (syn_wa (.classMem (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))) (syn_cvv)) (.classMem (syn_c0c) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))))) (syn_wral y (syn_cnnc) (.imp (.classMem (.cv y) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)))) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))))))) p0529
  have p0531 :=
    (by simpa [syn_wb, syn_w3a] using (Nominal.biimpRefl (syn_w3a (.classMem (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))) (syn_cvv)) (.classMem (syn_c0c) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)))) (syn_wral y (syn_cnnc) (.imp (.classMem (.cv y) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)))) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)))))))))
  have p0532 :=
    @g_syl6ibr (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) syn_wtru (syn_wa (syn_wa (.classMem (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))) (syn_cvv)) (.classMem (syn_c0c) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))))) (syn_wral y (syn_cnnc) (.imp (.classMem (.cv y) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)))) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))))))) (syn_w3a (.classMem (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))) (syn_cvv)) (.classMem (syn_c0c) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)))) (syn_wral y (syn_cnnc) (.imp (.classMem (.cv y) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)))) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))))))) p0530 p0531
  have p0533 :=
    @g_peano5 y (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))) (syn_cvv) dv_cache_0079
  have p0534 :=
    @g_syl6 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) syn_wtru (syn_w3a (.classMem (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))) (syn_cvv)) (.classMem (syn_c0c) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)))) (syn_wral y (syn_cnnc) (.imp (.classMem (.cv y) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)))) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))))))) (syn_wss (syn_cnnc) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)))) p0532 p0533
  have p0535 :=
    @g_ssel (syn_cnnc) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))) (.cv n)
  have p0536 :=
    @g_syl6 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) syn_wtru (syn_wss (syn_cnnc) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)))) (.imp (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))))) p0534 p0535
  have p0537 :=
    @g_com23 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) syn_wtru (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)))) p0536
  have p0538 :=
    @g_imp3a (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv n) (syn_cnnc)) syn_wtru (.classMem (.cv n) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)))) p0537
  have p0539 :=
    @g_id (.classEq (.cv x) (.cv n))
  have p0540 :=
    @g_eleq1d (.classEq (.cv x) (.cv n)) (.cv x) (.cv n) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k) p0539
  have p0541 :=
    @g_elabg (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (.classMem (.cv n) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) x (.cv n) (syn_cnnc) dv_cache_0080 dv_cache_0081 p0540
  have p0542 :=
    @g_adantr (.classMem (.cv n) (syn_cnnc)) (syn_wb (.classMem (.cv n) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)))) (.classMem (.cv n) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k))) syn_wtru p0541
  have p0543 :=
    @g_mpbidi (syn_wa (.classMem (.cv n) (syn_cnnc)) syn_wtru) (.classMem (.cv n) (.cab x (.classMem (.cv x) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)))) (.classMem (.cv n) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) p0538 p0542
  have p0544 :=
    @g_mpan2i (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv n) (syn_cnnc)) syn_wtru (.classMem (.cv n) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) p0133 p0543
  have p0545 :=
    @g_wppfrecprefixeqvalndv (.cv n) k (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) p0134 p0143 p0144 p0084 p0119 p0120
  have p0546 :=
    @g_mpbidi (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwppfrecprefixeq (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) k)) (.imp (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)))) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) p0544 p0545
  have p0547 :=
    @g_ralrimiv (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.imp (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)))) n (syn_cnnc) dv_cache_0082 p0546
  have p0548 :=
    @g_id (.classEq (.cv n) (.cv k))
  have p0549 :=
    @g_breq1d (.classEq (.cv n) (.cv k)) (.cv n) (.cv k) (.cv k) (syn_ckqrel (syn_clefin)) p0548
  have p0550 :=
    @g_id (.classEq (.cv n) (.cv k))
  have p0551 :=
    @g_fveq2d (.classEq (.cv n) (.cv k)) (.cv n) (.cv k) (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) p0550
  have p0552 :=
    @g_id (.classEq (.cv n) (.cv k))
  have p0553 :=
    @g_fveq2d (.classEq (.cv n) (.cv k)) (.cv n) (.cv k) (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) p0552
  have p0554 :=
    @g_eqeq12d (.classEq (.cv n) (.cv k)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k)) p0551 p0553
  have p0555 :=
    @g_imbi12d (.classEq (.cv n) (.cv k)) (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n))) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k))) p0549 p0554
  have p0556 :=
    @g_rspcv (.imp (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)))) (.imp (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k)))) n (.cv k) (syn_cnnc) dv_cache_0083 dv_cache_0060 dv_cache_0084 p0555
  have p0557 :=
    @g_syl5com (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wral n (syn_cnnc) (.imp (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n))))) (.classMem (.cv k) (syn_cnnc)) (.imp (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k)))) p0547 p0556
  have p0558 :=
    @g_mpd (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv k) (syn_cnnc)) (.imp (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k)))) p0053 p0557
  have p0559 :=
    @g_mpd (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k))) p0132 p0558
  have p0560 :=
    @g_eqcomd (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k)) p0559
  have p0561 :=
    @g_breq2d (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k)) (syn_ctc C) (syn_clec) p0560
  have p0562 :=
    @g_mpbid (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k))) p0125 p0561
  have p0563 :=
    @g_jca (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv k) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k))) p0053 p0562
  have p0564 :=
    @g_n_3pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))) p0134 p0143 p0144
  have p0565 :=
    @g_elwpphitvndv (syn_ctc C) (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (.cv k)
  have p0566 :=
    Nominal.mp p0564 p0565
  have p0567 :=
    @g_sylibr (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k)))) (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) p0563 p0566
  have p0568 :=
    @g_jca (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k))) p0567 p0560
  have p0569 :=
    @g_simpl (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k)))
  have p0570 :=
    @g_syl (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k)))) (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) p0568 p0569
  have p0571 :=
    @g_finlewe
  have p0572 :=
    @g_wppweconnex (syn_cnnc) (syn_ckqrel (syn_clefin))
  have p0573 :=
    Nominal.mp p0571 p0572
  have p0574 :=
    @g_a1i (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cconnex) (syn_cnnc)) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) p0573
  have p0575 :=
    @g_brex (syn_ckqrel (syn_clefin)) (syn_cnnc) (syn_cconnex)
  have p0576 :=
    @g_breq (.cv x) (.cv y) (.cv r) (syn_ckqrel (syn_clefin))
  have p0577 :=
    @g_breq (.cv y) (.cv x) (.cv r) (syn_ckqrel (syn_clefin))
  have p0578 :=
    @g_orbi12d (.classEq (.cv r) (syn_ckqrel (syn_clefin))) (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)) p0576 p0577
  have p0579 :=
    @g_n_2ralbidv (.classEq (.cv r) (syn_ckqrel (syn_clefin))) (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) (syn_wo (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))) x y (.cv a) (.cv a) dv_cache_0022 dv_cache_0085 p0578
  have p0580 :=
    @g_raleq (syn_wo (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))) y (.cv a) (syn_cnnc) dv_cache_0086 dv_cache_0087
  have p0581 :=
    @g_raleqbi1dv (syn_wral y (.cv a) (syn_wo (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))) (syn_wral y (syn_cnnc) (syn_wo (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))) x (.cv a) (syn_cnnc) dv_cache_0088 dv_cache_0029 p0580
  have p0582 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_connex x y r a dv_cache_0089 dv_cache_0090 dv_cache_0091 dv_cache_0034 dv_cache_0092 dv_cache_0093
  have p0583 :=
    @g_brabg (syn_wral x (.cv a) (syn_wral y (.cv a) (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))))) (syn_wral x (.cv a) (syn_wral y (.cv a) (syn_wo (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))))) (syn_wral x (syn_cnnc) (syn_wral y (syn_cnnc) (syn_wo (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))))) r a (syn_ckqrel (syn_clefin)) (syn_cnnc) (syn_cvv) (syn_cvv) (syn_cconnex) dv_cache_0040 dv_cache_0094 dv_cache_0042 dv_cache_0027 dv_cache_0095 dv_cache_0096 dv_cache_0035 p0579 p0581 p0582
  have p0584 :=
    @g_syl (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cconnex) (syn_cnnc)) (syn_wa (.classMem (syn_ckqrel (syn_clefin)) (syn_cvv)) (.classMem (syn_cnnc) (syn_cvv))) (syn_wb (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cconnex) (syn_cnnc)) (syn_wral x (syn_cnnc) (syn_wral y (syn_cnnc) (syn_wo (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)))))) p0575 p0583
  have p0585 :=
    @g_ibi (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cconnex) (syn_cnnc)) (syn_wral x (syn_cnnc) (syn_wral y (syn_cnnc) (syn_wo (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))))) p0584
  have p0586 :=
    @g_simpl (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))
  have p0587 :=
    @g_a1d (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) p0053
  have p0588 :=
    @g_breq1 (.cv x) (.cv n) (.cv y) (syn_ckqrel (syn_clefin))
  have p0589 :=
    @g_breq2 (.cv x) (.cv n) (.cv y) (syn_ckqrel (syn_clefin))
  have p0590 :=
    @g_orbi12d (.classEq (.cv x) (.cv n)) (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv n)) p0588 p0589
  have p0591 :=
    @g_breq2 (.cv y) (.cv k) (.cv n) (syn_ckqrel (syn_clefin))
  have p0592 :=
    @g_breq1 (.cv y) (.cv k) (.cv n) (syn_ckqrel (syn_clefin))
  have p0593 :=
    @g_orbi12d (.classEq (.cv y) (.cv k)) (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv n)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)) p0591 p0592
  have p0594 :=
    @g_rspc2v (syn_wo (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))) (syn_wo (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))) (syn_wo (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv n))) x y (.cv n) (.cv k) (syn_cnnc) (syn_cnnc) dv_cache_0080 dv_cache_0097 dv_cache_0098 dv_cache_0029 dv_cache_0029 dv_cache_0087 dv_cache_0099 dv_cache_0100 dv_cache_0093 p0590 p0593
  have p0595 :=
    @g_ex (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)) (.imp (syn_wral x (syn_cnnc) (syn_wral y (syn_cnnc) (syn_wo (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))))) (syn_wo (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))) p0594
  have p0596 :=
    @g_syl9 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (.imp (syn_wral x (syn_cnnc) (syn_wral y (syn_cnnc) (syn_wo (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))))) (syn_wo (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))) p0587 p0595
  have p0597 :=
    @g_syl5 (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (.classMem (.cv n) (syn_cnnc)) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.imp (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (.imp (syn_wral x (syn_cnnc) (syn_wral y (syn_cnnc) (syn_wo (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))))) (syn_wo (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) p0586 p0596
  have p0598 :=
    @g_pm2_43d (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (.imp (syn_wral x (syn_cnnc) (syn_wral y (syn_cnnc) (syn_wo (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))))) (syn_wo (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))) p0597
  have p0599 :=
    @g_syl7 (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cconnex) (syn_cnnc)) (syn_wral x (syn_cnnc) (syn_wral y (syn_cnnc) (syn_wo (syn_wbr (.cv x) (syn_ckqrel (syn_clefin)) (.cv y)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv x))))) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wo (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))) p0585 p0598
  have p0600 :=
    @g_mpdi (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cconnex) (syn_cnnc)) (syn_wo (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))) p0574 p0599
  have p0601 :=
    @g_pm2_53 (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))
  have p0602 :=
    @g_id (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))
  have p0603 :=
    @g_a1i (.imp (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) p0602
  have p0604 :=
    @g_com12 (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)) p0603
  have p0605 :=
    @g_syl6 (syn_wo (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))) (.neg (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)) (.imp (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))) p0601 p0604
  have p0606 :=
    @g_con1d (syn_wo (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))) (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (.imp (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))) p0605
  have p0607 :=
    @g_simpl (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0608 :=
    @g_simpl (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))
  have p0609 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (.classMem (.cv n) (syn_cnnc)) p0607 p0608
  have p0610 :=
    @g_simpl (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0611 :=
    @g_simpr (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))
  have p0612 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) p0610 p0611
  have p0613 :=
    @g_wppstopstepfunsndv C F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0614 :=
    @g_wppstopstepdmndv C F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0615 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F C)) (syn_chwcards (syn_cvv)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) p0614
  have p0616 :=
    @g_biimpri (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F C))) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_chwcards (syn_cvv))) p0615
  have p0617 :=
    Nominal.mp p0115 p0616
  have p0618 :=
    @g_wppstopsteprndmndv C F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0619 :=
    @g_n_3pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))) p0613 p0617 p0618
  have p0620 :=
    @g_elwpphitvndv (syn_ctc C) (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (.cv n)
  have p0621 :=
    Nominal.mp p0619 p0620
  have p0622 :=
    @g_biimpi (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)))) p0621
  have p0623 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)))) p0612 p0622
  have p0624 :=
    @g_simpr (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)))
  have p0625 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n))) p0623 p0624
  have p0626 :=
    @g_simpr (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0627 :=
    @g_simpl (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0628 :=
    @g_simpl (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))
  have p0629 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (.classMem (.cv n) (syn_cnnc)) p0627 p0628
  have p0630 :=
    @g_syl5 (syn_wa (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))) (.classMem (.cv n) (syn_cnnc)) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.imp (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)))) p0629 p0546
  have p0631 :=
    @g_mpdi (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n))) p0626 p0630
  have p0632 :=
    @g_breq2 (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_ctc C) (syn_clec)
  have p0633 :=
    @g_syl6 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n))) (syn_wb (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)))) p0631 p0632
  have p0634 :=
    @g_bi1 (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)))
  have p0635 :=
    @g_syl6 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wb (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)))) (.imp (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)))) p0633 p0634
  have p0636 :=
    @g_mpdi (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n))) p0625 p0635
  have p0637 :=
    @g_pm3_2 (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)))
  have p0638 :=
    @g_syl9 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n))) (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)))) p0636 p0637
  have p0639 :=
    @g_syl5 (syn_wa (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))) (.classMem (.cv n) (syn_cnnc)) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.imp (syn_wa (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n))))) p0609 p0638
  have p0640 :=
    @g_pm2_43d (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)))) p0639
  have p0641 :=
    @g_wppstopstepfunsndv (syn_ctc C) F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0642 :=
    @g_wppstopstepdmndv (syn_ctc C) F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0643 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F (syn_ctc C))) (syn_chwcards (syn_cvv)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) p0642
  have p0644 :=
    @g_biimpri (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_chwcards (syn_cvv))) p0643
  have p0645 :=
    Nominal.mp p0115 p0644
  have p0646 :=
    @g_wppstopsteprndmndv (syn_ctc C) F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0647 :=
    @g_n_3pm3_2i (.classMem (syn_cwppstopstep F (syn_ctc C)) (syn_cfuns)) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) (syn_wss (syn_crn (syn_cwppstopstep F (syn_ctc C))) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) p0641 p0645 p0646
  have p0648 :=
    @g_elwpphitvndv (syn_ctc C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (.cv n)
  have p0649 :=
    Nominal.mp p0647 p0648
  have p0650 :=
    @g_biimpri (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)))) p0649
  have p0651 :=
    @g_syl6 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)))) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) p0640 p0650
  have p0652 :=
    @g_simpl (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0653 :=
    @g_simpl (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))
  have p0654 :=
    @g_syl (syn_wa (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (.classMem (.cv n) (syn_cnnc)) p0652 p0653
  have p0655 :=
    @g_id (.classEq (.cv q) (.cv n))
  have p0656 :=
    @g_eleq1d (.classEq (.cv q) (.cv n)) (.cv q) (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)) p0655
  have p0657 :=
    @g_id (.classEq (.cv q) (.cv n))
  have p0658 :=
    @g_breq2d (.classEq (.cv q) (.cv n)) (.cv q) (.cv n) (.cv k) (syn_ckqrel (syn_clefin)) p0657
  have p0659 :=
    @g_imbi12d (.classEq (.cv q) (.cv n)) (.classMem (.cv q) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)) p0656 p0658
  have p0660 :=
    @g_rspcv (.imp (.classMem (.cv q) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q))) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))) q (.cv n) (syn_cnnc) dv_cache_0101 dv_cache_0061 dv_cache_0102 p0659
  have p0661 :=
    @g_syl5com (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))) (.classMem (.cv n) (syn_cnnc)) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))) p0389 p0660
  have p0662 :=
    @g_syl5 (syn_wa (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))) (.classMem (.cv n) (syn_cnnc)) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))) p0654 p0661
  have p0663 :=
    @g_mpdd (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)) p0651 p0662
  have p0664 :=
    @g_exp3a (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)) p0663
  have p0665 :=
    @g_com23 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)) p0664
  have p0666 :=
    @g_a1d (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.imp (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (.imp (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wo (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))) p0665
  have p0667 :=
    @g_a1dd (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wo (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))) (.imp (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (.imp (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))) (.neg (.imp (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))) p0666
  have p0668 :=
    Nominal.ax2 (.neg (.imp (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (.imp (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))
  have p0669 :=
    @g_syl6 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wo (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))) (.imp (.neg (.imp (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))) (.imp (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (.imp (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (.imp (.imp (.neg (.imp (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))) (.imp (.neg (.imp (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))) (.imp (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) p0667 p0668
  have p0670 :=
    @g_mpdi (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wo (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))) (.imp (.neg (.imp (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k))) (.imp (.neg (.imp (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))) (.imp (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))) p0606 p0669
  have p0671 :=
    @g_pm2_18 (.imp (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))
  have p0672 :=
    @g_syl6 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wo (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))) (.imp (.neg (.imp (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))) (.imp (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))) (.imp (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))) p0670 p0671
  have p0673 :=
    @g_com23 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wo (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)) p0672
  have p0674 :=
    @g_mpdd (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) (syn_wo (syn_wbr (.cv n) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)) p0600 p0673
  have p0675 :=
    @g_exp3a (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)) p0674
  have p0676 :=
    @g_ralrimiv (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))) n (syn_cnnc) dv_cache_0082 p0675
  have p0677 :=
    @g_eqid (syn_cwppstopstep F (syn_ctc C))
  have p0678 :=
    @g_pm3_2i (.classEq (syn_cwppstopstep F (syn_ctc C)) (syn_cwppstopstep F (syn_ctc C))) (.classEq (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))) p0677 p0074
  have p0679 :=
    @g_freceq12 (syn_cwppstopstep F (syn_ctc C)) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))
  have p0680 :=
    Nominal.mp p0678 p0679
  have p0681 :=
    @g_fveq1i (.cv k) (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))) p0680
  have p0682 :=
    @g_eqcomi (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))) (.cv k)) p0681
  have p0683 :=
    @g_syl5eq (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))) (.cv k)) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k)) p0682 p0560
  have p0684 :=
    @g_n_3jca (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))) (.cv k)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k))) p0570 p0676 p0683
  have p0685 :=
    @g_simp1d (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))) (.cv k)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k))) p0684
  have p0686 :=
    @g_jca (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv m) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) p0056 p0685
  have p0687 :=
    @g_jca (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C)))) p0054 p0686
  have p0688 :=
    @g_simprd (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv m) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) p0055
  have p0689 :=
    @g_jca (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))) p0688 p0676
  have p0690 :=
    @g_jca (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) p0687 p0689
  have p0691 :=
    @g_wppstopstepfunsndv C F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0692 :=
    @g_wppstopstepdmndv C F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0693 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F C)) (syn_chwcards (syn_cvv)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) p0692
  have p0694 :=
    @g_biimpri (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F C))) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_chwcards (syn_cvv))) p0693
  have p0695 :=
    Nominal.mp p0115 p0694
  have p0696 :=
    @g_wppstopsteprndmndv C F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0697 :=
    @g_n_3pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))) p0691 p0695 p0696
  have p0698 :=
    @g_hwcardssnc (syn_cvv)
  have p0699 :=
    @g_sselii (syn_chwcards (syn_cvv)) (syn_cncs) C p0698 hyp_wppstopfixedhitcontrgrowfixdndv_3
  have p0700 :=
    @g_tccl C
  have p0701 :=
    Nominal.mp p0699 p0700
  have p0702 :=
    @g_n_3pm3_2i (.classMem (syn_ctc C) (syn_cncs)) (.classMem C (syn_cncs)) (syn_wbr (syn_ctc C) (syn_clec) C) p0701 p0699 hyp_wppstopfixedhitcontrgrowfixdndv_4
  have p0703 :=
    @g_pm3_2i (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (syn_w3a (.classMem (syn_ctc C) (syn_cncs)) (.classMem C (syn_cncs)) (syn_wbr (syn_ctc C) (syn_clec) C)) p0697 p0702
  have p0704 :=
    @g_wppstopstepfunsndv C F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0705 :=
    @g_wppstopstepdmndv C F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0706 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F C)) (syn_chwcards (syn_cvv)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) p0705
  have p0707 :=
    @g_biimpri (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F C))) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_chwcards (syn_cvv))) p0706
  have p0708 :=
    Nominal.mp p0115 p0707
  have p0709 :=
    @g_wppstopsteprndmndv C F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0710 :=
    @g_n_3pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))) p0704 p0708 p0709
  have p0711 :=
    @g_frecdomfv (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (.cv n)
  have p0712 :=
    @g_mpan (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cdm (syn_cwppstopstep F C))) p0710 p0711
  have p0713 :=
    @g_wppstopstepdmndv C F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0714 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F C)) (syn_chwcards (syn_cvv)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) p0713
  have p0715 :=
    @g_biimpi (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cdm (syn_cwppstopstep F C))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_chwcards (syn_cvv))) p0714
  have p0716 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cdm (syn_cwppstopstep F C))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_chwcards (syn_cvv))) p0712 p0715
  have p0717 :=
    @g_hwcardssnc (syn_cvv)
  have p0718 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) p0717
  have p0719 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_chwcards (syn_cvv))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs)) p0716 p0718
  have p0720 :=
    @g_rgen (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs)) n (syn_cnnc) p0719
  have p0721 :=
    @g_id (.classEq (.cv n) (.cv q))
  have p0722 :=
    @g_fveq2d (.classEq (.cv n) (.cv q)) (.cv n) (.cv q) (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) p0721
  have p0723 :=
    @g_eleq1d (.classEq (.cv n) (.cv q)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_cncs) p0722
  have p0724_e00_recanon : Nominal.NPrf (.imp (.objEq n q) (syn_wb (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_cncs)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cfv syn_cio syn_cuni syn_wex syn_wa syn_csn syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex syn_cphi syn_cfrec syn_cclos1 syn_cint syn_cpprod syn_ctxp syn_cin syn_ccom syn_copab syn_ccnv syn_c1st syn_cmpt syn_cvv syn_cplc syn_c1c syn_cwppstopstep syn_cif syn_wo syn_ctc syn_c0c syn_cncs syn_cqs syn_cen
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0723
  have p0724 :=
    @g_cbvralv (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_cncs)) n q (syn_cnnc) dv_cache_0060 dv_cache_0061 dv_cache_0103 dv_cache_0104 p0724_e00_recanon
  have p0725 :=
    @g_mpbi (syn_wral n (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs))) (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_cncs))) p0720 p0724
  have p0726 :=
    @g_pm3_2i (syn_wa (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (syn_w3a (.classMem (syn_ctc C) (syn_cncs)) (.classMem C (syn_cncs)) (syn_wbr (syn_ctc C) (syn_clec) C))) (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_cncs))) p0703 p0725
  have p0727 :=
    @g_jctir (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (syn_w3a (.classMem (syn_ctc C) (syn_cncs)) (.classMem C (syn_cncs)) (syn_wbr (syn_ctc C) (syn_clec) C))) (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_cncs)))) p0690 p0726
  have p0728 :=
    @g_simpr (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))
  have p0729 :=
    @g_simpr (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch)
  have p0730 :=
    @g_syl (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch)) (syn_wa (.classEq I (syn_ctc I)) ch) p0728 p0729
  have p0731 :=
    @g_simpr (.classEq I (syn_ctc I)) ch
  have p0732 :=
    @g_syl (syn_wa (.classEq I (syn_ctc I)) ch) ch (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) p0731 hyp_wppstopfixedhitcontrgrowfixdndv_12
  have p0733 :=
    @g_syl (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classEq I (syn_ctc I)) ch) (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) p0730 p0732
  have p0734 :=
    @g_wppstopstepfunsndv C F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0735 :=
    @g_wppstopstepdmndv C F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0736 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F C)) (syn_chwcards (syn_cvv)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) p0735
  have p0737 :=
    @g_biimpri (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F C))) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_chwcards (syn_cvv))) p0736
  have p0738 :=
    Nominal.mp p0115 p0737
  have p0739 :=
    @g_wppstopsteprndmndv C F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0740 :=
    @g_n_3pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))) p0734 p0738 p0739
  have p0741 :=
    @g_frecdomfv (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (.cv r)
  have p0742 :=
    @g_mpan (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (.classMem (.cv r) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv r)) (syn_cdm (syn_cwppstopstep F C))) p0740 p0741
  have p0743 :=
    @g_simpr (.classMem (.cv r) (syn_cnnc)) (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv r)))
  have p0744 :=
    @g_breq2d (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv r)))) (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv r)) (syn_ctc C) (syn_clec) p0743
  have p0745 :=
    @g_simpr (.classMem (.cv r) (syn_cnnc)) (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv r)))
  have p0746 :=
    @g_fveq2d (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv r)))) (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv r)) (syn_cwppstopstep F C) p0745
  have p0747 :=
    @g_breq2d (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv r)))) (syn_cfv (syn_cwppstopstep F C) (.cv y)) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv r))) C (syn_clec) p0746
  have p0748 :=
    @g_imbi12d (syn_wa (.classMem (.cv r) (syn_cnnc)) (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv r)))) (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv r))) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv r)))) p0744 p0747
  have p0749 :=
    @g_rspcdv (.classMem (.cv r) (syn_cnnc)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))) (.imp (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv r))) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv r))))) y (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv r)) (syn_cdm (syn_cwppstopstep F C)) dv_cache_0105 dv_cache_0106 dv_cache_0107 dv_cache_0108 p0742 p0748
  have p0750 :=
    @g_syl5com (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (.classMem (.cv r) (syn_cnnc)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv r))) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv r))))) p0733 p0749
  have p0751 :=
    @g_ralrimiv (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.imp (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv r))) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv r))))) r (syn_cnnc) dv_cache_0109 p0750
  have p0752 :=
    (by simpa [syn_wb, syn_w3a] using (Nominal.biimpRefl (syn_w3a (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (syn_w3a (.classMem (syn_ctc C) (syn_cncs)) (.classMem C (syn_cncs)) (syn_wbr (syn_ctc C) (syn_clec) C))) (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc) (.imp (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv r))) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv r)))))))))
  have p0753 :=
    @g_sylanbrc (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (syn_w3a (.classMem (syn_ctc C) (syn_cncs)) (.classMem C (syn_cncs)) (syn_wbr (syn_ctc C) (syn_clec) C))) (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_cncs))))) (syn_wral r (syn_cnnc) (.imp (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv r))) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv r)))))) (syn_w3a (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (syn_w3a (.classMem (syn_ctc C) (syn_cncs)) (.classMem C (syn_cncs)) (syn_wbr (syn_ctc C) (syn_clec) C))) (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc) (.imp (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv r))) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv r))))))) p0727 p0751 p0752
  have p0754 :=
    @g_wpphitminadjndv k m n (syn_cwppstopstep F C) C (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C) r q dv_cache_0110 dv_cache_0111 dv_cache_0112 dv_cache_0113 dv_cache_0114 dv_cache_0115 dv_cache_0116 dv_cache_0117 dv_cache_0118 dv_cache_0119 dv_cache_0120 dv_cache_0121 dv_cache_0122 dv_cache_0067 dv_cache_0123 dv_cache_0124 dv_cache_0125 dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130 dv_cache_0131 dv_cache_0132 dv_cache_0133
  have p0755 :=
    @g_syl (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_w3a (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))) (syn_wa (.classMem (.cv m) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))))) (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wa (syn_wa (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (syn_w3a (.classMem (syn_ctc C) (syn_cncs)) (.classMem C (syn_cncs)) (syn_wbr (syn_ctc C) (syn_clec) C))) (syn_wral q (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv q)) (syn_cncs)))) (syn_wral r (syn_cnnc) (.imp (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv r))) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv r))))))) (syn_wo (.classEq (.cv m) (.cv k)) (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c)))) p0753 p0754
  have p0756 :=
    @g_a1i (.classMem C (syn_cncs)) (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs))) p0699
  have p0757 :=
    @g_simpl (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs))
  have p0758 :=
    @g_jca (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs))) (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc)) p0756 p0757
  have p0759 :=
    @g_simpr (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs))
  have p0760 :=
    @g_jca (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs))) (syn_wa (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs)) p0758 p0759
  have p0761 :=
    @g_n_3pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))) p0691 p0695 p0696
  have p0762 :=
    @g_elwpphitvndv C (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (.cv n)
  have p0763 :=
    Nominal.mp p0761 p0762
  have p0764 :=
    @g_a1i (syn_wb (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n))))) (syn_wa (syn_wa (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs))) p0763
  have p0765 :=
    @g_simpl (syn_wa (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs))
  have p0766 :=
    @g_simpr (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))
  have p0767 :=
    @g_syl (syn_wa (syn_wa (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs))) (syn_wa (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cnnc)) p0765 p0766
  have p0768 :=
    @g_simpl (syn_wa (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs))
  have p0769 :=
    @g_simpr (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))
  have p0770 :=
    @g_syl (syn_wa (syn_wa (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs))) (syn_wa (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cnnc)) p0768 p0769
  have p0771 :=
    @g_nntccl (.cv n)
  have p0772 :=
    @g_syl (syn_wa (syn_wa (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs))) (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_ctc (.cv n)) (syn_cnnc)) p0770 p0771
  have p0773 :=
    @g_n_2thd (syn_wa (syn_wa (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs))) (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_ctc (.cv n)) (syn_cnnc)) p0767 p0772
  have p0774 :=
    @g_simpl (syn_wa (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs))
  have p0775 :=
    @g_simpl (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))
  have p0776 :=
    @g_syl (syn_wa (syn_wa (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs))) (syn_wa (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))) (.classMem C (syn_cncs)) p0774 p0775
  have p0777 :=
    @g_simpr (syn_wa (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs))
  have p0778 :=
    @g_jca (syn_wa (syn_wa (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs))) (.classMem C (syn_cncs)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs)) p0776 p0777
  have p0779 :=
    @g_tlecg C (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n))
  have p0780 :=
    @g_syl (syn_wa (syn_wa (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs))) (syn_wa (.classMem C (syn_cncs)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs))) (syn_wb (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n))) (syn_wbr (syn_ctc C) (syn_clec) (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n))))) p0778 p0779
  have p0781 :=
    @g_simpl (syn_wa (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs))
  have p0782 :=
    @g_simpr (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))
  have p0783 :=
    @g_syl (syn_wa (syn_wa (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs))) (syn_wa (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))) (.classMem (.cv n) (syn_cnnc)) p0781 p0782
  have p0784 :=
    @g_wppstopstepfunsndv (syn_ctc C) F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0785 :=
    @g_eqeltrri (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_chwcards (syn_cvv)) p0074 p0115
  have p0786 :=
    @g_wppstopstepdmndv (syn_ctc C) F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0787 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F (syn_ctc C))) (syn_chwcards (syn_cvv)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) p0786
  have p0788 :=
    @g_biimpri (.classMem (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) (.classMem (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_chwcards (syn_cvv))) p0787
  have p0789 :=
    Nominal.mp p0785 p0788
  have p0790 :=
    @g_wppstopsteprndmndv (syn_ctc C) F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0791 :=
    @g_frectchom0 x (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (.cv n) dv_cache_0134 dv_cache_0135 dv_cache_0136 p0691 p0695 p0696 p0784 p0789 p0790 hyp_wppstopfixedhitcontrgrowfixdndv_6
  have p0792 :=
    @g_syl (syn_wa (syn_wa (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs))) (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n))) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))) (syn_ctc (.cv n)))) p0783 p0791
  have p0793 :=
    @g_breq2d (syn_wa (syn_wa (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs))) (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n))) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))) (syn_ctc (.cv n))) (syn_ctc C) (syn_clec) p0792
  have p0794 :=
    @g_bitrd (syn_wa (syn_wa (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n))) (syn_wbr (syn_ctc C) (syn_clec) (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))) (syn_ctc (.cv n)))) p0780 p0793
  have p0795 :=
    @g_anbi12d (syn_wa (syn_wa (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs))) (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_ctc (.cv n)) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))) (syn_ctc (.cv n)))) p0773 p0794
  have p0796 :=
    @g_bitrd (syn_wa (syn_wa (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs))) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)))) (syn_wa (.classMem (syn_ctc (.cv n)) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))) (syn_ctc (.cv n))))) p0764 p0795
  have p0797 :=
    @g_n_3pm3_2i (.classMem (syn_cwppstopstep F (syn_ctc C)) (syn_cfuns)) (.classMem (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) (syn_wss (syn_crn (syn_cwppstopstep F (syn_ctc C))) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) p0784 p0789 p0790
  have p0798 :=
    @g_elwpphitvndv (syn_ctc C) (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc (.cv n))
  have p0799 :=
    Nominal.mp p0797 p0798
  have p0800 :=
    @g_a1i (syn_wb (.classMem (syn_ctc (.cv n)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wa (.classMem (syn_ctc (.cv n)) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))) (syn_ctc (.cv n)))))) (syn_wa (syn_wa (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs))) p0799
  have p0801 :=
    @g_bicomd (syn_wa (syn_wa (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs))) (.classMem (syn_ctc (.cv n)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wa (.classMem (syn_ctc (.cv n)) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))) (syn_ctc (.cv n))))) p0800
  have p0802 :=
    @g_bitrd (syn_wa (syn_wa (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs))) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wa (.classMem (syn_ctc (.cv n)) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))) (syn_ctc (.cv n))))) (.classMem (syn_ctc (.cv n)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) p0796 p0801
  have p0803 :=
    @g_syl (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs))) (syn_wa (syn_wa (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs))) (syn_wb (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (.classMem (syn_ctc (.cv n)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C)))) p0760 p0802
  have p0804 :=
    @g_ralimiaa (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv n)) (syn_cncs)) (syn_wb (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (.classMem (syn_ctc (.cv n)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C)))) n (syn_cnnc) p0803
  have p0805 :=
    Nominal.mp p0720 p0804
  have p0806 :=
    @g_jctir (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv m) (syn_cnnc)) (syn_wral n (syn_cnnc) (syn_wb (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (.classMem (syn_ctc (.cv n)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))))) p0034 p0805
  have p0807 :=
    @g_id (.classEq (.cv n) (.cv m))
  have p0808 :=
    @g_eleq1d (.classEq (.cv n) (.cv m)) (.cv n) (.cv m) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C) p0807
  have p0809 :=
    @g_tceq (.cv n) (.cv m)
  have p0810 :=
    @g_eleq1d (.classEq (.cv n) (.cv m)) (syn_ctc (.cv n)) (syn_ctc (.cv m)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C)) p0809
  have p0811 :=
    @g_bibi12d (.classEq (.cv n) (.cv m)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (.classMem (.cv m) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (.classMem (syn_ctc (.cv n)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (.classMem (syn_ctc (.cv m)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) p0808 p0810
  have p0812 :=
    @g_rspcva (syn_wb (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (.classMem (syn_ctc (.cv n)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C)))) (syn_wb (.classMem (.cv m) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (.classMem (syn_ctc (.cv m)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C)))) n (.cv m) (syn_cnnc) dv_cache_0137 dv_cache_0060 dv_cache_0138 p0811
  have p0813 :=
    @g_syl (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wral n (syn_cnnc) (syn_wb (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (.classMem (syn_ctc (.cv n)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C)))))) (syn_wb (.classMem (.cv m) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (.classMem (syn_ctc (.cv m)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C)))) p0806 p0812
  have p0814 :=
    @g_mpbid (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv m) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (.classMem (syn_ctc (.cv m)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) p0056 p0813
  have p0815 :=
    @g_nntccl (.cv m)
  have p0816 :=
    @g_syl (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv m) (syn_cnnc)) (.classMem (syn_ctc (.cv m)) (syn_cnnc)) p0034 p0815
  have p0817 :=
    @g_jca (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (syn_ctc (.cv m)) (syn_cnnc)) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))) p0816 p0368
  have p0818 :=
    @g_id (.classEq (.cv n) (syn_ctc (.cv m)))
  have p0819 :=
    @g_eleq1d (.classEq (.cv n) (syn_ctc (.cv m))) (.cv n) (syn_ctc (.cv m)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C)) p0818
  have p0820 :=
    @g_id (.classEq (.cv n) (syn_ctc (.cv m)))
  have p0821 :=
    @g_breq2d (.classEq (.cv n) (syn_ctc (.cv m))) (.cv n) (syn_ctc (.cv m)) (.cv k) (syn_ckqrel (syn_clefin)) p0820
  have p0822 :=
    @g_imbi12d (.classEq (.cv n) (syn_ctc (.cv m))) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (.classMem (syn_ctc (.cv m)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (syn_ctc (.cv m))) p0819 p0821
  have p0823 :=
    @g_rspcva (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))) (.imp (.classMem (syn_ctc (.cv m)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (syn_ctc (.cv m)))) n (syn_ctc (.cv m)) (syn_cnnc) dv_cache_0139 dv_cache_0060 dv_cache_0140 p0822
  have p0824 :=
    @g_syl (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (syn_ctc (.cv m)) (syn_cnnc)) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (.imp (.classMem (syn_ctc (.cv m)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (syn_ctc (.cv m)))) p0817 p0823
  have p0825 :=
    @g_mpd (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (syn_ctc (.cv m)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (syn_ctc (.cv m))) p0814 p0824
  have p0826 :=
    @g_nntcpreim x (.cv k) dv_cache_0141
  have p0827 :=
    @g_syl (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv k) (syn_cnnc)) (syn_wrex x (syn_cnnc) (.classEq (syn_ctc (.cv x)) (.cv k))) p0053 p0826
  have p0828 :=
    @g_a1d (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))) p0058
  have p0829 :=
    @g_simpr (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))
  have p0830 :=
    @g_eleq1d (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))) (syn_ctc (.cv x)) (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C)) p0829
  have p0831 :=
    @g_biimprd (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))) (.classMem (syn_ctc (.cv x)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) p0830
  have p0832 :=
    @g_sylcom (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))) (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (.classMem (syn_ctc (.cv x)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) p0828 p0831
  have p0833 :=
    @g_simpl (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))
  have p0834 :=
    @g_a1i (syn_wral n (syn_cnnc) (syn_wb (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (.classMem (syn_ctc (.cv n)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))))) (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))) p0805
  have p0835 :=
    @g_jca (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))) (.classMem (.cv x) (syn_cnnc)) (syn_wral n (syn_cnnc) (syn_wb (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (.classMem (syn_ctc (.cv n)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))))) p0833 p0834
  have p0836 :=
    @g_id (.classEq (.cv n) (.cv x))
  have p0837 :=
    @g_eleq1d (.classEq (.cv n) (.cv x)) (.cv n) (.cv x) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C) p0836
  have p0838 :=
    @g_tceq (.cv n) (.cv x)
  have p0839 :=
    @g_eleq1d (.classEq (.cv n) (.cv x)) (syn_ctc (.cv n)) (syn_ctc (.cv x)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C)) p0838
  have p0840 :=
    @g_bibi12d (.classEq (.cv n) (.cv x)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (.classMem (.cv x) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (.classMem (syn_ctc (.cv n)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (.classMem (syn_ctc (.cv x)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) p0837 p0839
  have p0841 :=
    @g_rspcva (syn_wb (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (.classMem (syn_ctc (.cv n)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C)))) (syn_wb (.classMem (.cv x) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (.classMem (syn_ctc (.cv x)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C)))) n (.cv x) (syn_cnnc) dv_cache_0142 dv_cache_0060 dv_cache_0143 p0840
  have p0842 :=
    @g_syl (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))) (syn_wa (.classMem (.cv x) (syn_cnnc)) (syn_wral n (syn_cnnc) (syn_wb (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (.classMem (syn_ctc (.cv n)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C)))))) (syn_wb (.classMem (.cv x) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (.classMem (syn_ctc (.cv x)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C)))) p0835 p0841
  have p0843 :=
    @g_biimprd (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))) (.classMem (.cv x) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (.classMem (syn_ctc (.cv x)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) p0842
  have p0844 :=
    @g_sylcom (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))) (.classMem (syn_ctc (.cv x)) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (syn_ctc C))) (.classMem (.cv x) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) p0832 p0843
  have p0845 :=
    @g_simpl (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))
  have p0846 :=
    @g_a1d (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))) p0688
  have p0847 :=
    @g_pm3_2 (.classMem (.cv x) (syn_cnnc)) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n))))
  have p0848 :=
    @g_syl9 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (.classMem (.cv x) (syn_cnnc)) (syn_wa (.classMem (.cv x) (syn_cnnc)) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n))))) p0846 p0847
  have p0849 :=
    @g_syl5 (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))) (.classMem (.cv x) (syn_cnnc)) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.imp (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))) (syn_wa (.classMem (.cv x) (syn_cnnc)) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))))) p0845 p0848
  have p0850 :=
    @g_pm2_43d (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))) (syn_wa (.classMem (.cv x) (syn_cnnc)) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n))))) p0849
  have p0851 :=
    @g_id (.classEq (.cv n) (.cv x))
  have p0852 :=
    @g_eleq1d (.classEq (.cv n) (.cv x)) (.cv n) (.cv x) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C) p0851
  have p0853 :=
    @g_id (.classEq (.cv n) (.cv x))
  have p0854 :=
    @g_breq2d (.classEq (.cv n) (.cv x)) (.cv n) (.cv x) (.cv m) (syn_ckqrel (syn_clefin)) p0853
  have p0855 :=
    @g_imbi12d (.classEq (.cv n) (.cv x)) (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (.classMem (.cv x) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv x)) p0852 p0854
  have p0856 :=
    @g_rspcva (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n))) (.imp (.classMem (.cv x) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv x))) n (.cv x) (syn_cnnc) dv_cache_0142 dv_cache_0060 dv_cache_0144 p0855
  have p0857 :=
    @g_syl6 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))) (syn_wa (.classMem (.cv x) (syn_cnnc)) (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n))))) (.imp (.classMem (.cv x) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv x))) p0850 p0856
  have p0858 :=
    @g_mpdd (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))) (.classMem (.cv x) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv x)) p0844 p0857
  have p0859 :=
    @g_a1d (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))) p0034
  have p0860 :=
    @g_simpl (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))
  have p0861 :=
    @g_pm3_2 (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv x) (syn_cnnc))
  have p0862 :=
    @g_syl5 (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))) (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv m) (syn_cnnc)) (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv x) (syn_cnnc))) p0860 p0861
  have p0863 :=
    @g_syl6 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))) (.classMem (.cv m) (syn_cnnc)) (.imp (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))) (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv x) (syn_cnnc)))) p0859 p0862
  have p0864 :=
    @g_pm2_43d (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))) (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv x) (syn_cnnc))) p0863
  have p0865 :=
    @g_kqlefintcb (.cv m) (.cv x)
  have p0866 :=
    @g_syl6 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))) (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv x) (syn_cnnc))) (syn_wb (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv x)) (syn_wbr (syn_ctc (.cv m)) (syn_ckqrel (syn_clefin)) (syn_ctc (.cv x)))) p0864 p0865
  have p0867 :=
    @g_bi1 (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv x)) (syn_wbr (syn_ctc (.cv m)) (syn_ckqrel (syn_clefin)) (syn_ctc (.cv x)))
  have p0868 :=
    @g_syl6 (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))) (syn_wb (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv x)) (syn_wbr (syn_ctc (.cv m)) (syn_ckqrel (syn_clefin)) (syn_ctc (.cv x)))) (.imp (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv x)) (syn_wbr (syn_ctc (.cv m)) (syn_ckqrel (syn_clefin)) (syn_ctc (.cv x)))) p0866 p0867
  have p0869 :=
    @g_mpdd (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv x)) (syn_wbr (syn_ctc (.cv m)) (syn_ckqrel (syn_clefin)) (syn_ctc (.cv x))) p0858 p0868
  have p0870 :=
    @g_simpr (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))
  have p0871 :=
    @g_breq2d (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))) (syn_ctc (.cv x)) (.cv k) (syn_ctc (.cv m)) (syn_ckqrel (syn_clefin)) p0870
  have p0872 :=
    @g_mpbidi (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k))) (syn_wbr (syn_ctc (.cv m)) (syn_ckqrel (syn_clefin)) (syn_ctc (.cv x))) (syn_wbr (syn_ctc (.cv m)) (syn_ckqrel (syn_clefin)) (.cv k)) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) p0869 p0871
  have p0873 :=
    @g_exp3a (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv x) (syn_cnnc)) (.classEq (syn_ctc (.cv x)) (.cv k)) (syn_wbr (syn_ctc (.cv m)) (syn_ckqrel (syn_clefin)) (.cv k)) p0872
  have p0874 :=
    @g_rexlimdv (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classEq (syn_ctc (.cv x)) (.cv k)) (syn_wbr (syn_ctc (.cv m)) (syn_ckqrel (syn_clefin)) (.cv k)) x (syn_cnnc) dv_cache_0145 dv_cache_0146 p0873
  have p0875 :=
    @g_mpd (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wrex x (syn_cnnc) (.classEq (syn_ctc (.cv x)) (.cv k))) (syn_wbr (syn_ctc (.cv m)) (syn_ckqrel (syn_clefin)) (.cv k)) p0827 p0874
  have p0876 :=
    @g_jca (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (syn_ctc (.cv m))) (syn_wbr (syn_ctc (.cv m)) (syn_ckqrel (syn_clefin)) (.cv k)) p0825 p0875
  have p0877 :=
    @g_jca (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv k) (syn_cnnc)) (.classMem (syn_ctc (.cv m)) (syn_cnnc)) p0053 p0816
  have p0878 :=
    @g_kqfinantinn (.cv k) (syn_ctc (.cv m))
  have p0879 :=
    @g_syl (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv k) (syn_cnnc)) (.classMem (syn_ctc (.cv m)) (syn_cnnc))) (.imp (syn_wa (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (syn_ctc (.cv m))) (syn_wbr (syn_ctc (.cv m)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classEq (.cv k) (syn_ctc (.cv m)))) p0877 p0878
  have p0880 :=
    @g_mpd (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (syn_ctc (.cv m))) (syn_wbr (syn_ctc (.cv m)) (syn_ckqrel (syn_clefin)) (.cv k))) (.classEq (.cv k) (syn_ctc (.cv m))) p0876 p0879
  have p0881 :=
    @g_eqeq2d (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.cv k) (syn_ctc (.cv m)) (.cv m) p0880
  have p0882 :=
    @g_addceq1d (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.cv k) (syn_ctc (.cv m)) (syn_c1c) p0880
  have p0883 :=
    @g_eqeq2d (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_cplc (.cv k) (syn_c1c)) (syn_cplc (syn_ctc (.cv m)) (syn_c1c)) (.cv m) p0882
  have p0884 :=
    @g_orbi12d (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classEq (.cv m) (.cv k)) (.classEq (.cv m) (syn_ctc (.cv m))) (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))) (.classEq (.cv m) (syn_cplc (syn_ctc (.cv m)) (syn_c1c))) p0881 p0883
  have p0885 :=
    @g_mpbid (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wo (.classEq (.cv m) (.cv k)) (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c)))) (syn_wo (.classEq (.cv m) (syn_ctc (.cv m))) (.classEq (.cv m) (syn_cplc (syn_ctc (.cv m)) (syn_c1c)))) p0755 p0884
  have p0886 :=
    @g_n_3pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))) p0691 p0695 p0696
  have p0887 :=
    @g_elwpphitvndv C (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (.cv m)
  have p0888 :=
    Nominal.mp p0886 p0887
  have p0889 :=
    @g_sylib (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv m) (syn_cwpphit (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) C)) (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m)))) p0056 p0888
  have p0890 :=
    @g_simpr (.classMem (.cv m) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m)))
  have p0891 :=
    @g_syl (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m)))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m))) p0889 p0890
  have p0892 :=
    @g_wppstopstepfunsndv C F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0893 :=
    @g_wppstopstepdmndv C F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0894 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F C)) (syn_chwcards (syn_cvv)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) p0893
  have p0895 :=
    @g_biimpri (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F C))) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_chwcards (syn_cvv))) p0894
  have p0896 :=
    Nominal.mp p0115 p0895
  have p0897 :=
    @g_wppstopsteprndmndv C F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0898 :=
    @g_n_3pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))) p0892 p0896 p0897
  have p0899 :=
    @g_frecdomfv (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (.cv x)
  have p0900 :=
    @g_mpan (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (.classMem (.cv x) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x)) (syn_cdm (syn_cwppstopstep F C))) p0898 p0899
  have p0901 :=
    @g_wppstopstepdmndv C F hyp_wppstopfixedhitcontrgrowfixdndv_1 hyp_wppstopfixedhitcontrgrowfixdndv_2
  have p0902 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F C)) (syn_chwcards (syn_cvv)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x)) p0901
  have p0903 :=
    @g_biimpi (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x)) (syn_cdm (syn_cwppstopstep F C))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x)) (syn_chwcards (syn_cvv))) p0902
  have p0904 :=
    @g_syl (.classMem (.cv x) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x)) (syn_cdm (syn_cwppstopstep F C))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x)) (syn_chwcards (syn_cvv))) p0900 p0903
  have p0905 :=
    @g_simpr (.classMem (.cv x) (syn_cnnc)) (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x)))
  have p0906 :=
    @g_breq2d (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x)))) (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x)) C (syn_clec) p0905
  have p0907 :=
    @g_simpr (.classMem (.cv x) (syn_cnnc)) (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x)))
  have p0908 :=
    @g_simpr (.classMem (.cv x) (syn_cnnc)) (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x)))
  have p0909 :=
    @g_tceq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x))
  have p0910 :=
    @g_syl (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x)))) (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x))) (.classEq (syn_ctc (.cv y)) (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x)))) p0908 p0909
  have p0911 :=
    @g_neeq12d (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x)))) (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x)) (syn_ctc (.cv y)) (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x))) p0907 p0910
  have p0912 :=
    @g_imbi12d (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x)))) (syn_wbr C (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x))) (syn_wne (.cv y) (syn_ctc (.cv y))) (syn_wne (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x)) (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x)))) p0906 p0911
  have p0913 :=
    @g_rspcdv (.classMem (.cv x) (syn_cnnc)) (.imp (syn_wbr C (syn_clec) (.cv y)) (syn_wne (.cv y) (syn_ctc (.cv y)))) (.imp (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x))) (syn_wne (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x)) (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x))))) y (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x)) (syn_chwcards (syn_cvv)) dv_cache_0147 dv_cache_0073 dv_cache_0148 dv_cache_0149 p0904 p0912
  have p0914 :=
    @g_mpi (.classMem (.cv x) (syn_cnnc)) (syn_wral y (syn_chwcards (syn_cvv)) (.imp (syn_wbr C (syn_clec) (.cv y)) (syn_wne (.cv y) (syn_ctc (.cv y))))) (.imp (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x))) (syn_wne (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x)) (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x))))) hyp_wppstopfixedhitcontrgrowfixdndv_9 p0913
  have p0915 :=
    @g_rgen (.imp (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x))) (syn_wne (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x)) (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x))))) x (syn_cnnc) p0914
  have p0916 :=
    @g_id (.classEq (.cv x) (.cv m))
  have p0917 :=
    @g_fveq2d (.classEq (.cv x) (.cv m)) (.cv x) (.cv m) (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) p0916
  have p0918 :=
    @g_breq2d (.classEq (.cv x) (.cv m)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m)) C (syn_clec) p0917
  have p0919 :=
    @g_id (.classEq (.cv x) (.cv m))
  have p0920 :=
    @g_fveq2d (.classEq (.cv x) (.cv m)) (.cv x) (.cv m) (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) p0919
  have p0921 :=
    @g_id (.classEq (.cv x) (.cv m))
  have p0922 :=
    @g_fveq2d (.classEq (.cv x) (.cv m)) (.cv x) (.cv m) (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) p0921
  have p0923 :=
    @g_tceq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m))
  have p0924 :=
    @g_syl (.classEq (.cv x) (.cv m)) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m))) (.classEq (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x))) (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m)))) p0922 p0923
  have p0925 :=
    @g_neeq12d (.classEq (.cv x) (.cv m)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m)) (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x))) (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m))) p0920 p0924
  have p0926 :=
    @g_imbi12d (.classEq (.cv x) (.cv m)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m))) (syn_wne (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x)) (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x)))) (syn_wne (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m)) (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m)))) p0918 p0925
  have p0927 :=
    @g_rspcv (.imp (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x))) (syn_wne (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x)) (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x))))) (.imp (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m))) (syn_wne (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m)) (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m))))) x (.cv m) (syn_cnnc) dv_cache_0150 dv_cache_0029 dv_cache_0151 p0926
  have p0928 :=
    @g_mpi (.classMem (.cv m) (syn_cnnc)) (syn_wral x (syn_cnnc) (.imp (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x))) (syn_wne (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x)) (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv x)))))) (.imp (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m))) (syn_wne (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m)) (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m))))) p0915 p0927
  have p0929 :=
    @g_syl (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv m) (syn_cnnc)) (.imp (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m))) (syn_wne (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m)) (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m))))) p0034 p0928
  have p0930 :=
    @g_mpd (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m))) (syn_wne (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m)) (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m)))) p0891 p0929
  have p0931 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m)) (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m))))))
  have p0932 :=
    @g_sylib (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wne (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m)) (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m)))) (.neg (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m)) (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m))))) p0930 p0931
  have p0933 :=
    @g_frectchom0 x (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)) (.cv m) dv_cache_0134 dv_cache_0135 dv_cache_0136 p0691 p0695 p0696 p0784 p0789 p0790 hyp_wppstopfixedhitcontrgrowfixdndv_6
  have p0934 :=
    @g_syl (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv m) (syn_cnnc)) (.classEq (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m))) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))) (syn_ctc (.cv m)))) p0034 p0933
  have p0935 :=
    @g_eqcomd (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.cv k) (syn_ctc (.cv m)) p0880
  have p0936 :=
    @g_fveq2d (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_ctc (.cv m)) (.cv k) (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))) p0935
  have p0937 :=
    @g_eqtrd (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m))) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))) (syn_ctc (.cv m))) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))) (.cv k)) p0934 p0936
  have p0938 :=
    @g_eqtrd (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m))) (syn_cfv (syn_cfrec (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c)))) (.cv k)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k)) p0937 p0683
  have p0939 :=
    @g_a1d (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classEq (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m))) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k))) (.classEq (.cv m) (.cv k)) p0938
  have p0940 :=
    @g_id (.classEq (.cv m) (.cv k))
  have p0941 :=
    @g_eqcomd (.classEq (.cv m) (.cv k)) (.cv m) (.cv k) p0940
  have p0942 :=
    @g_fveq2d (.classEq (.cv m) (.cv k)) (.cv k) (.cv m) (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) p0941
  have p0943 :=
    @g_eqeq2d (.classEq (.cv m) (.cv k)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m)) (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m))) p0942
  have p0944 :=
    @g_mpbidi (.classEq (.cv m) (.cv k)) (.classEq (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m))) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv k))) (.classEq (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m))) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m))) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) p0939 p0943
  have p0945 :=
    @g_eqcom (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m))) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m))
  have p0946 :=
    @g_syl6ib (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classEq (.cv m) (.cv k)) (.classEq (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m))) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m))) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m)) (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m)))) p0944 p0945
  have p0947 :=
    @g_necon3bd (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m)) (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m)))) (.cv m) (.cv k) p0946
  have p0948 :=
    @g_mpd (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.neg (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m)) (syn_ctc (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (.classEq I (syn_ctc I)) I (syn_c0c))) (.cv m))))) (syn_wne (.cv m) (.cv k)) p0932 p0947
  have p0949 :=
    @g_neeq2d (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.cv k) (syn_ctc (.cv m)) (.cv m) p0880
  have p0950 :=
    @g_mpbid (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wne (.cv m) (.cv k)) (syn_wne (.cv m) (syn_ctc (.cv m))) p0948 p0949
  have p0951 :=
    (by simpa [syn_wb, syn_wne] using (Nominal.biimpRefl (syn_wne (.cv m) (syn_ctc (.cv m)))))
  have p0952 :=
    @g_sylib (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wne (.cv m) (syn_ctc (.cv m))) (.neg (.classEq (.cv m) (syn_ctc (.cv m)))) p0950 p0951
  have p0953 :=
    @g_nchoicelem1 (.cv m)
  have p0954 :=
    @g_syl (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classMem (.cv m) (syn_cnnc)) (.neg (.classEq (.cv m) (syn_cplc (syn_ctc (.cv m)) (syn_c1c)))) p0034 p0953
  have p0955 :=
    @g_jca (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.neg (.classEq (.cv m) (syn_ctc (.cv m)))) (.neg (.classEq (.cv m) (syn_cplc (syn_ctc (.cv m)) (syn_c1c)))) p0952 p0954
  have p0956 :=
    @g_pm4_56 (.classEq (.cv m) (syn_ctc (.cv m))) (.classEq (.cv m) (syn_cplc (syn_ctc (.cv m)) (syn_c1c)))
  have p0957 :=
    @g_sylib (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wa (.neg (.classEq (.cv m) (syn_ctc (.cv m)))) (.neg (.classEq (.cv m) (syn_cplc (syn_ctc (.cv m)) (syn_c1c))))) (.neg (syn_wo (.classEq (.cv m) (syn_ctc (.cv m))) (.classEq (.cv m) (syn_cplc (syn_ctc (.cv m)) (syn_c1c))))) p0955 p0956
  have p0958 :=
    @g_pm2_21dd (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (syn_wo (.classEq (.cv m) (syn_ctc (.cv m))) (.classEq (.cv m) (syn_cplc (syn_ctc (.cv m)) (syn_c1c)))) (.neg (.classEq (.cv m) (.cv m))) p0885 p0957
  have p0959 :=
    @g_a1d (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.neg (.classEq (.cv m) (.cv m))) (.classEq (syn_c0c) (syn_c0c)) p0958
  have p0960 :=
    @g_mt2d (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.classEq (syn_c0c) (syn_c0c)) (.classEq (.cv m) (.cv m)) p0017 p0959
  have p0961 :=
    @g_syl6 (.classEq I (syn_ctc I)) (syn_wa ph (syn_wa ps ch)) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ph) (syn_wa (syn_wa (.classEq I (syn_ctc I)) ps) (syn_wa (.classEq I (syn_ctc I)) ch))) (.neg (.classEq (syn_c0c) (syn_c0c))) p0015 p0960
  exact p0961

#print axioms g_wppstopfixedhitcontrgrowfixdndv

end NFChoice.DirectNominalPrf.WPPReplay
