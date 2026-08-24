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
import NominalWPPReplayChunk017Compact001Part064

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

noncomputable def g_wppstopgammafixedhwdndv
    (x : Var) (y : Var) (C : Class) (F : Class) (p : Var) (dv_C_p : p ∉ C.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_F_p : p ∉ F.fv) (dv_F_x : x ∉ F.fv) (dv_F_y : y ∉ F.fv) (dv_p_x : p ≠ x) (dv_p_y : p ≠ y) (dv_x_y : x ≠ y) (hyp_wppstopgammafixedhwdndv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppstopgammafixedhwdndv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_chwcards (syn_cvv)))) (hyp_wppstopgammafixedhwdndv_3 : Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv)))) (hyp_wppstopgammafixedhwdndv_4 : Nominal.NPrf (syn_wbr (syn_ctc C) (syn_clec) C)) (hyp_wppstopgammafixedhwdndv_5 : Nominal.NPrf (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm F))))) (hyp_wppstopgammafixedhwdndv_6 : Nominal.NPrf (syn_wral x (syn_cdm (syn_cwppstopstep F C)) (.classEq (syn_ctc (syn_cfv (syn_cwppstopstep F C) (.cv x))) (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (.cv x)))))) :
    Nominal.NPrf (.imp (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (.classEq (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_cwppgamma (syn_cwppstopstep F C) C)))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ C.fv ∪ F.fv ∪ ({p} : Finset Var)
  let r : Var := freshVar proofSupport 0
  let k : Var := freshVar proofSupport 1
  let n : Var := freshVar proofSupport 2
  let m : Var := freshVar proofSupport 3
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_ne_x : r ≠ x := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_r : x ≠ r :=
    Ne.symm fresh_r_ne_x
  have fresh_r_ne_y : r ≠ y := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_r : y ≠ r :=
    Ne.symm fresh_r_ne_y
  have fresh_r_not_C : r ∉ C.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_r_not_F : r ∉ F.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_ne_p : r ≠ p := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_r : p ≠ r :=
    Ne.symm fresh_r_ne_p
  have fresh_k : k ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_k_ne_x : k ≠ x := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_k : x ≠ k :=
    Ne.symm fresh_k_ne_x
  have fresh_k_ne_y : k ≠ y := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_k : y ≠ k :=
    Ne.symm fresh_k_ne_y
  have fresh_k_not_C : k ∉ C.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_k_not_F : k ∉ F.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_k_ne_p : k ≠ p := by
    intro h
    exact fresh_k (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_k : p ≠ k :=
    Ne.symm fresh_k_ne_p
  have fresh_n : n ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_n_ne_x : n ≠ x := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_n : x ≠ n :=
    Ne.symm fresh_n_ne_x
  have fresh_n_ne_y : n ≠ y := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_n : y ≠ n :=
    Ne.symm fresh_n_ne_y
  have fresh_n_not_C : n ∉ C.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_n_not_F : n ∉ F.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_ne_p : n ≠ p := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_n : p ≠ n :=
    Ne.symm fresh_n_ne_p
  have fresh_m : m ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_m_ne_x : m ≠ x := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_m : x ≠ m :=
    Ne.symm fresh_m_ne_x
  have fresh_m_ne_y : m ≠ y := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_m : y ≠ m :=
    Ne.symm fresh_m_ne_y
  have fresh_m_not_C : m ∉ C.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_m_not_F : m ∉ F.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_m_ne_p : m ≠ p := by
    intro h
    exact fresh_m (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_m : p ≠ m :=
    Ne.symm fresh_m_ne_p
  have fresh_r_ne_k : r ≠ k := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_k_ne_r : k ≠ r :=
    Ne.symm fresh_r_ne_k
  have fresh_r_ne_n : r ≠ n := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_n_ne_r : n ≠ r :=
    Ne.symm fresh_r_ne_n
  have fresh_r_ne_m : r ≠ m := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_m_ne_r : m ≠ r :=
    Ne.symm fresh_r_ne_m
  have fresh_k_ne_n : k ≠ n := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_n_ne_k : n ≠ k :=
    Ne.symm fresh_k_ne_n
  have fresh_k_ne_m : k ≠ m := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_m_ne_k : m ≠ k :=
    Ne.symm fresh_k_ne_m
  have fresh_n_ne_m : n ≠ m := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_m_ne_n : m ≠ n :=
    Ne.symm fresh_n_ne_m
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
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
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
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_p, dv_F_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
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
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_p, dv_F_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
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
    exact (show p ≠ x from (by exact dv_p_x))
  have dv_cache_0013 : r ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0014 : p ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : k ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : k ∉ ((syn_cwppstopstep F C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_C, fresh_k_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : k ∉ ((syn_ctc C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : p ∉ ((syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_p, dv_F_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : p ∉ ((syn_chwcards (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : p ∉ ((Wff.imp (syn_wbr (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_clec) C) (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_cdm (syn_cwppstopstep F C))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_p, dv_F_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : n ∉ ((syn_ctc C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : n ∉ ((syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_C, fresh_n_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : n ∉ ((syn_cwppstopstep F C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_C, fresh_n_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : y ∉ ((syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_n, dv_C_y, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : y ∉ ((syn_cdm (syn_cwppstopstep F C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_y, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : y ∉ ((Wff.imp (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n))) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_y, fresh_y_ne_n, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : m ∉ ((syn_cplc (.cv n) (syn_c1c))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0028 : m ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0029 : m ∉ ((syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (syn_cplc (.cv n) (syn_c1c))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_not_C, fresh_m_ne_n, fresh_m_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0030 : n ∉ ((syn_wrex m (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv m))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_C, fresh_n_ne_m, fresh_n_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0031 : n ∉ ((syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_C, fresh_n_not_F, fresh_n_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0032 : n ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0033 : n ∉ ((syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv m)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_C, fresh_n_ne_m, fresh_n_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0034 : m ∉ ((syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_not_C, fresh_m_ne_n, fresh_m_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0035 : r ∉ ((Wff.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_p, fresh_r_not_C, fresh_r_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0036 : p ∉ ((Wff.imp (syn_wbr (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_clec) C) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv r)) (syn_cncs))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_p, dv_F_p, fresh_p_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0037 : r ∉ ((Class.cv n)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_n, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0038 : r ∉ ((syn_cnnc)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0039 : r ∉ ((Wff.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)) (syn_cncs))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_n, fresh_r_not_C, fresh_r_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0040 : n ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0041 : k ∉ ((syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_C, fresh_k_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0042 : k ∉ ((syn_cwppcand (syn_cwppstopstep F C) C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_C, fresh_k_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0043 : k ∉ ((syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_C, fresh_k_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0044 : p ∉ ((syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0045 : p ∉ ((Wff.imp (syn_wbr (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_clec) C) (.classMem (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_cdm (syn_cwppstopstep F C))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_p, dv_F_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0046 : n ∉ ((syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0047 : y ∉ ((syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_n, dv_C_y, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0048 : y ∉ ((Wff.imp (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n))) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_y, fresh_y_ne_n, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0049 : m ∉ ((syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (syn_cplc (.cv n) (syn_c1c))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_not_C, fresh_m_ne_n, fresh_m_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0050 : n ∉ ((syn_wrex m (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv m))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_C, fresh_n_ne_m, fresh_n_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0051 : n ∉ ((syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv m)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_C, fresh_n_ne_m, fresh_n_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0052 : m ∉ ((syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_not_C, fresh_m_ne_n, fresh_m_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0053 : r ∉ ((Wff.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_p, fresh_r_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0054 : p ∉ ((Wff.imp (syn_wbr (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_clec) C) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv r)) (syn_cncs))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_p, fresh_p_ne_r, dv_F_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0055 : r ∉ ((Wff.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)) (syn_cncs))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_n, fresh_r_not_C, fresh_r_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0056 : k ∉ ((syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (syn_ctc C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_C, fresh_k_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0057 : p ∉ ((syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_p, dv_F_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0058 : p ∉ ((Wff.imp (syn_wbr (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_clec) C) (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_cdm (syn_cwppstopstep F C))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_p, dv_F_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0059 : n ∉ ((syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_C, fresh_n_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0060 : y ∉ ((syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_n, dv_C_y, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0061 : y ∉ ((Wff.imp (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n))) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_y, fresh_y_ne_n, dv_F_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0062 : m ∉ ((syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (syn_cplc (.cv n) (syn_c1c))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_not_C, fresh_m_ne_n, fresh_m_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0063 : n ∉ ((syn_wrex m (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv m))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_C, fresh_n_ne_m, fresh_n_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0064 : n ∉ ((syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv m)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063
    exact (by
      have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_n_not_C, fresh_n_ne_m, fresh_n_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0065 : m ∉ ((syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064
    exact (by
      have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_m_not_C, fresh_m_ne_n, fresh_m_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0066 : r ∉ ((Wff.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_p, fresh_r_not_C, fresh_r_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0067 : p ∉ ((Wff.imp (syn_wbr (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_clec) C) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv r)) (syn_cncs))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_p, dv_F_p, fresh_p_ne_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0068 : r ∉ ((Wff.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)) (syn_cncs))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_n, fresh_r_not_C, fresh_r_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0069 : k ∉ ((syn_cwppgamma (syn_cwppstopstep F C) C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_C, fresh_k_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0070 : k ∉ ((syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_C, fresh_k_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0071 : k ∉ ((syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (syn_cwppgamma (syn_cwppstopstep F C) C))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070
    exact (by
      have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_k_not_C, fresh_k_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_wppstopstepfunsndv C F hyp_wppstopgammafixedhwdndv_1 hyp_wppstopgammafixedhwdndv_2
  have p0001 :=
    @g_wppstopsteprndmndv C F hyp_wppstopgammafixedhwdndv_1 hyp_wppstopgammafixedhwdndv_2
  have p0002 :=
    @g_wppstopstepfunsndv (syn_ctc C) F hyp_wppstopgammafixedhwdndv_1 hyp_wppstopgammafixedhwdndv_2
  have p0003 :=
    @g_wppstopsteprndmndv (syn_ctc C) F hyp_wppstopgammafixedhwdndv_1 hyp_wppstopgammafixedhwdndv_2
  have p0004 :=
    @g_wppstopstepdmndv C F hyp_wppstopgammafixedhwdndv_1 hyp_wppstopgammafixedhwdndv_2
  have p0005 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F C)) (syn_chwcards (syn_cvv)) (.cv p) p0004
  have p0006 :=
    @g_biimpri (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (.classMem (.cv p) (syn_chwcards (syn_cvv))) p0005
  have p0007 :=
    @g_hwcardstcclndv (.cv p)
  have p0008 :=
    @g_wppstopstepdmndv (syn_ctc C) F hyp_wppstopgammafixedhwdndv_1 hyp_wppstopgammafixedhwdndv_2
  have p0009 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F (syn_ctc C))) (syn_chwcards (syn_cvv)) (syn_ctc (.cv p)) p0008
  have p0010 :=
    @g_sylibr (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (syn_ctc (.cv p)) (syn_chwcards (syn_cvv))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) p0007 p0009
  have p0011 :=
    @g_jca (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) p0006 p0010
  have p0012 :=
    Nominal.gen p0011 p
  have p0013 :=
    (by simpa [syn_wb, syn_wral] using (Nominal.biimpRefl (syn_wral p (syn_chwcards (syn_cvv)) (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppstopstep F (syn_ctc C))))))))
  have p0014 :=
    @g_mpbir (syn_wral p (syn_chwcards (syn_cvv)) (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))))) (.all p (.imp (.classMem (.cv p) (syn_chwcards (syn_cvv))) (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppstopstep F (syn_ctc C))))))) p0012 p0013
  have p0015 :=
    Nominal.ax1 (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppstopstep F (syn_ctc C))))) (syn_wbr (.cv p) (syn_clec) C)
  have p0016 :=
    @g_a1i (.imp (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppstopstep F (syn_ctc C))))) (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppstopstep F (syn_ctc C))))))) (.classMem (.cv p) (syn_chwcards (syn_cvv))) p0015
  have p0017 :=
    @g_ralimia (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppstopstep F (syn_ctc C))))) (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))))) p (syn_chwcards (syn_cvv)) p0016
  have p0018 :=
    Nominal.mp p0014 p0017
  have p0019 :=
    @g_wppstopstepfunsndv C F hyp_wppstopgammafixedhwdndv_1 hyp_wppstopgammafixedhwdndv_2
  have p0020 :=
    @g_a1i (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc))) p0019
  have p0021 :=
    @g_simpl (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc))
  have p0022 :=
    @g_wppstopstepdmndv C F hyp_wppstopgammafixedhwdndv_1 hyp_wppstopgammafixedhwdndv_2
  have p0023 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F C)) (syn_chwcards (syn_cvv)) (.cv p) p0022
  have p0024 :=
    @g_biimpri (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (.classMem (.cv p) (syn_chwcards (syn_cvv))) p0023
  have p0025 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc))) (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) p0021 p0024
  have p0026 :=
    @g_wppstopsteprndmndv C F hyp_wppstopgammafixedhwdndv_1 hyp_wppstopgammafixedhwdndv_2
  have p0027 :=
    @g_a1i (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))) (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc))) p0026
  have p0028 :=
    @g_n_3jca (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc))) (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))) p0020 p0025 p0027
  have p0029 :=
    @g_simpr (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc))
  have p0030 :=
    @g_jca (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc))) (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (.classMem (.cv r) (syn_cnnc)) p0028 p0029
  have p0031 :=
    @g_frecdomfv (syn_cwppstopstep F C) (.cv p) (.cv r)
  have p0032 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc))) (syn_wa (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (.classMem (.cv r) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cdm (syn_cwppstopstep F C))) p0030 p0031
  have p0033 :=
    @g_wppstopstepdmndv C F hyp_wppstopgammafixedhwdndv_1 hyp_wppstopgammafixedhwdndv_2
  have p0034 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F C)) (syn_chwcards (syn_cvv)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) p0033
  have p0035 :=
    @g_sylib (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cdm (syn_cwppstopstep F C))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_chwcards (syn_cvv))) p0032 p0034
  have p0036 :=
    @g_hwcardssnc (syn_cvv)
  have p0037 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) p0036
  have p0038 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_chwcards (syn_cvv))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs)) p0035 p0037
  have p0039 :=
    @g_rgen2 (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs)) p r (syn_chwcards (syn_cvv)) (syn_cnnc) dv_cache_0001 dv_cache_0002 p0038
  have p0040 :=
    Nominal.ax1 (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs))) (syn_wbr (.cv p) (syn_clec) C)
  have p0041 :=
    @g_a1i (.imp (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs))) (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs))))) (.classMem (.cv p) (syn_chwcards (syn_cvv))) p0040
  have p0042 :=
    @g_ralimia (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs))) (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs)))) p (syn_chwcards (syn_cvv)) p0041
  have p0043 :=
    Nominal.mp p0039 p0042
  have p0044 :=
    @g_wppgammatchwboundedeqndv x C (syn_cwppstopstep F C) (syn_cwppstopstep F (syn_ctc C)) r p dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0002 dv_cache_0012 dv_cache_0013 p0000 p0001 p0002 p0003 hyp_wppstopgammafixedhwdndv_6 p0018 p0043 hyp_wppstopgammafixedhwdndv_3
  have p0045 :=
    @g_wppstopgammaprefixeqndv C F p dv_cache_0003 dv_cache_0014 hyp_wppstopgammafixedhwdndv_1 hyp_wppstopgammafixedhwdndv_2 hyp_wppstopgammafixedhwdndv_3 hyp_wppstopgammafixedhwdndv_4 hyp_wppstopgammafixedhwdndv_5
  have p0046 :=
    @g_eqtri (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_cwppgamma (syn_cwppstopstep F (syn_ctc C)) (syn_ctc C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) p0044 p0045
  have p0047 :=
    @g_wppstopstepfunsndv C F hyp_wppstopgammafixedhwdndv_1 hyp_wppstopgammafixedhwdndv_2
  have p0048 :=
    @g_elex (syn_cwppstopstep F C) (syn_cfuns)
  have p0049 :=
    Nominal.mp p0047 p0048
  have p0050 :=
    @g_pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cvv)) (.classMem C (syn_chwcards (syn_cvv))) p0049 hyp_wppstopgammafixedhwdndv_3
  have p0051 :=
    @g_wppgammaminhwndv C k (syn_cwppstopstep F C) dv_cache_0015 dv_cache_0016
  have p0052 :=
    Nominal.mp p0050 p0051
  have p0053 :=
    @g_simpr (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppcand (syn_cwppstopstep F C) C)) (syn_wral k (syn_cwppcand (syn_cwppstopstep F C) C) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (.cv k)))
  have p0054 :=
    Nominal.mp p0052 p0053
  have p0055 :=
    @g_elex (syn_cwppstopstep F C) (syn_cfuns)
  have p0056 :=
    Nominal.mp p0047 p0055
  have p0057 :=
    @g_hwcardstcclndv C
  have p0058 :=
    Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0057
  have p0059 :=
    @g_pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cvv)) (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) p0056 p0058
  have p0060 :=
    @g_wppgammaminhwndv (syn_ctc C) k (syn_cwppstopstep F C) dv_cache_0017 dv_cache_0016
  have p0061 :=
    Nominal.mp p0059 p0060
  have p0062 :=
    @g_simpl (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C))) (syn_wral k (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C)) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (.cv k)))
  have p0063 :=
    Nominal.mp p0061 p0062
  have p0064 :=
    @g_elwppcand (syn_ctc C) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppstopstep F C)
  have p0065 :=
    @g_mpbi (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C))) (syn_wa (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (syn_ctc C))) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C)))) p0063 p0064
  have p0066 :=
    @g_simpr (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (syn_ctc C))) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C)))
  have p0067 :=
    Nominal.mp p0065 p0066
  have p0068 :=
    @g_elex (syn_cwppstopstep F C) (syn_cfuns)
  have p0069 :=
    Nominal.mp p0047 p0068
  have p0070 :=
    @g_hwcardstcclndv C
  have p0071 :=
    Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0070
  have p0072 :=
    @g_pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cvv)) (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) p0069 p0071
  have p0073 :=
    @g_wppgammaminhwndv (syn_ctc C) k (syn_cwppstopstep F C) dv_cache_0017 dv_cache_0016
  have p0074 :=
    Nominal.mp p0072 p0073
  have p0075 :=
    @g_simpl (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C))) (syn_wral k (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C)) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (.cv k)))
  have p0076 :=
    Nominal.mp p0074 p0075
  have p0077 :=
    @g_elwppcand (syn_ctc C) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppstopstep F C)
  have p0078 :=
    @g_mpbi (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C))) (syn_wa (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (syn_ctc C))) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C)))) p0076 p0077
  have p0079 :=
    @g_simpl (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (syn_ctc C))) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C)))
  have p0080 :=
    Nominal.mp p0078 p0079
  have p0081 :=
    @g_simpl (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (syn_ctc C))
  have p0082 :=
    Nominal.mp p0080 p0081
  have p0083 :=
    @g_elex (syn_cwppstopstep F C) (syn_cfuns)
  have p0084 :=
    Nominal.mp p0047 p0083
  have p0085 :=
    @g_hwcardstcclndv C
  have p0086 :=
    Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0085
  have p0087 :=
    @g_pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cvv)) (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) p0084 p0086
  have p0088 :=
    @g_wppgammaminhwndv (syn_ctc C) k (syn_cwppstopstep F C) dv_cache_0017 dv_cache_0016
  have p0089 :=
    Nominal.mp p0087 p0088
  have p0090 :=
    @g_simpl (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C))) (syn_wral k (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C)) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (.cv k)))
  have p0091 :=
    Nominal.mp p0089 p0090
  have p0092 :=
    @g_elwppcand (syn_ctc C) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppstopstep F C)
  have p0093 :=
    @g_mpbi (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C))) (syn_wa (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (syn_ctc C))) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C)))) p0091 p0092
  have p0094 :=
    @g_simpl (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (syn_ctc C))) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C)))
  have p0095 :=
    Nominal.mp p0093 p0094
  have p0096 :=
    @g_simpr (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (syn_ctc C))
  have p0097 :=
    Nominal.mp p0095 p0096
  have p0098 :=
    @g_pm3_2i (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (syn_ctc C)) (syn_wbr (syn_ctc C) (syn_clec) C) p0097 hyp_wppstopgammafixedhwdndv_4
  have p0099 :=
    @g_elex (syn_cwppstopstep F C) (syn_cfuns)
  have p0100 :=
    Nominal.mp p0047 p0099
  have p0101 :=
    @g_hwcardstcclndv C
  have p0102 :=
    Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0101
  have p0103 :=
    @g_pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cvv)) (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) p0100 p0102
  have p0104 :=
    @g_wppgammaminhwndv (syn_ctc C) k (syn_cwppstopstep F C) dv_cache_0017 dv_cache_0016
  have p0105 :=
    Nominal.mp p0103 p0104
  have p0106 :=
    @g_simpl (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C))) (syn_wral k (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C)) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (.cv k)))
  have p0107 :=
    Nominal.mp p0105 p0106
  have p0108 :=
    @g_elwppcand (syn_ctc C) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppstopstep F C)
  have p0109 :=
    @g_mpbi (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C))) (syn_wa (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (syn_ctc C))) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C)))) p0107 p0108
  have p0110 :=
    @g_simpl (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (syn_ctc C))) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C)))
  have p0111 :=
    Nominal.mp p0109 p0110
  have p0112 :=
    @g_simpl (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (syn_ctc C))
  have p0113 :=
    Nominal.mp p0111 p0112
  have p0114 :=
    @g_hwcardssnc (syn_cvv)
  have p0115 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) p0114
  have p0116 :=
    Nominal.mp p0113 p0115
  have p0117 :=
    @g_hwcardstcclndv C
  have p0118 :=
    Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0117
  have p0119 :=
    @g_hwcardssnc (syn_cvv)
  have p0120 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (syn_ctc C) p0119
  have p0121 :=
    Nominal.mp p0118 p0120
  have p0122 :=
    @g_hwcardssnc (syn_cvv)
  have p0123 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) C p0122
  have p0124 :=
    Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0123
  have p0125 :=
    @g_n_3pm3_2i (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cncs)) (.classMem (syn_ctc C) (syn_cncs)) (.classMem C (syn_cncs)) p0116 p0121 p0124
  have p0126 :=
    @g_lectr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_ctc C) C
  have p0127 :=
    Nominal.mp p0125 p0126
  have p0128 :=
    Nominal.mp p0098 p0127
  have p0129 :=
    @g_pm3_2i (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C) p0082 p0128
  have p0130 :=
    @g_simpr (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)
  have p0131 :=
    @g_iftrue (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C
  have p0132 :=
    @g_breq1d (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C (syn_clec) p0131
  have p0133 :=
    @g_mpbird (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_wbr (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_clec) C) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C) p0130 p0132
  have p0134 :=
    @g_hwcardssnc (syn_cvv)
  have p0135 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) C p0134
  have p0136 :=
    Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0135
  have p0137 :=
    @g_nclecid C
  have p0138 :=
    Nominal.mp p0136 p0137
  have p0139 :=
    @g_a1i (syn_wbr C (syn_clec) C) (.neg (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C))) p0138
  have p0140 :=
    @g_iffalse (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C
  have p0141 :=
    @g_breq1d (.neg (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C))) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) C C (syn_clec) p0140
  have p0142 :=
    @g_mpbird (.neg (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C))) (syn_wbr (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_clec) C) (syn_wbr C (syn_clec) C) p0139 p0141
  have p0143 :=
    @g_pm2_61i (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_wbr (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_clec) C) p0133 p0142
  have p0144 :=
    @g_tru
  have p0145 :=
    @g_simpr syn_wtru (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C))
  have p0146 :=
    @g_simpl (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)
  have p0147 :=
    @g_syl (syn_wa syn_wtru (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C))) (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) p0145 p0146
  have p0148 :=
    @g_a1i (.classMem C (syn_chwcards (syn_cvv))) (syn_wa syn_wtru (.neg (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)))) hyp_wppstopgammafixedhwdndv_3
  have p0149 :=
    @g_ifclda syn_wtru (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C (syn_chwcards (syn_cvv)) p0147 p0148
  have p0150 :=
    Nominal.mp p0144 p0149
  have p0151 :=
    @g_wppstopstepdmndv C F hyp_wppstopgammafixedhwdndv_1 hyp_wppstopgammafixedhwdndv_2
  have p0152 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F C)) (syn_chwcards (syn_cvv)) (.cv p) p0151
  have p0153 :=
    @g_biimpri (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (.classMem (.cv p) (syn_chwcards (syn_cvv))) p0152
  have p0154 :=
    Nominal.gen p0153 p
  have p0155 :=
    (by simpa [syn_wb, syn_wral] using (Nominal.biimpRefl (syn_wral p (syn_chwcards (syn_cvv)) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))))))
  have p0156 :=
    @g_mpbir (syn_wral p (syn_chwcards (syn_cvv)) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C)))) (.all p (.imp (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))))) p0154 p0155
  have p0157 :=
    Nominal.ax1 (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (syn_wbr (.cv p) (syn_clec) C)
  have p0158 :=
    @g_a1i (.imp (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))))) (.classMem (.cv p) (syn_chwcards (syn_cvv))) p0157
  have p0159 :=
    @g_ralimia (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C)))) p (syn_chwcards (syn_cvv)) p0158
  have p0160 :=
    Nominal.mp p0156 p0159
  have p0161 :=
    @g_pm3_2i (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_chwcards (syn_cvv))) (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))))) p0150 p0160
  have p0162 :=
    @g_id (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C))
  have p0163 :=
    @g_breq1d (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) C (syn_clec) p0162
  have p0164 :=
    @g_id (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C))
  have p0165 :=
    @g_eleq1d (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_cdm (syn_cwppstopstep F C)) p0164
  have p0166 :=
    @g_imbi12d (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (syn_wbr (.cv p) (syn_clec) C) (syn_wbr (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_clec) C) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_cdm (syn_cwppstopstep F C))) p0163 p0165
  have p0167 :=
    @g_rspcva (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C)))) (.imp (syn_wbr (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_clec) C) (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_cdm (syn_cwppstopstep F C)))) p (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_chwcards (syn_cvv)) dv_cache_0018 dv_cache_0019 dv_cache_0020 p0166
  have p0168 :=
    Nominal.mp p0161 p0167
  have p0169 :=
    Nominal.mp p0143 p0168
  have p0170 :=
    @g_wppstopsteprndmndv C F hyp_wppstopgammafixedhwdndv_1 hyp_wppstopgammafixedhwdndv_2
  have p0171 :=
    @g_hwcardstcclndv C
  have p0172 :=
    Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0171
  have p0173 :=
    @g_elex (syn_ctc C) (syn_chwcards (syn_cvv))
  have p0174 :=
    Nominal.mp p0172 p0173
  have p0175 :=
    @g_wppreachfwdrexvndv (syn_ctc C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) n (syn_cwppstopstep F C) dv_cache_0021 dv_cache_0022 dv_cache_0023 p0047 p0169 p0170 p0174
  have p0176 :=
    @g_simpl (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))
  have p0177 :=
    @g_peano2 (.cv n)
  have p0178 :=
    @g_syl (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) p0176 p0177
  have p0179 :=
    @g_simpr (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))
  have p0180 :=
    @g_n_3pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))) p0047 p0169 p0170
  have p0181 :=
    @g_a1i (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) p0180
  have p0182 :=
    @g_simpl (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))
  have p0183 :=
    @g_jca (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (.classMem (.cv n) (syn_cnnc)) p0181 p0182
  have p0184 :=
    @g_frecdomfv (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (.cv n)
  have p0185 :=
    @g_syl (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) (syn_wa (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (.classMem (.cv n) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)) (syn_cdm (syn_cwppstopstep F C))) p0183 p0184
  have p0186 :=
    @g_id (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))))
  have p0187 :=
    @g_a1d (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) p0186
  have p0188 :=
    @g_pm3_2 (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)) (syn_cdm (syn_cwppstopstep F C))) (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))))
  have p0189 :=
    @g_syl9 (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)) (syn_cdm (syn_cwppstopstep F C))) (syn_wa (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)) (syn_cdm (syn_cwppstopstep F C))) (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))))) p0187 p0188
  have p0190 :=
    @g_syl5 (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)) (syn_cdm (syn_cwppstopstep F C))) (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (.imp (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) (syn_wa (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)) (syn_cdm (syn_cwppstopstep F C))) (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))))) p0185 p0189
  have p0191 :=
    @g_pm2_43d (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) (syn_wa (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)) (syn_cdm (syn_cwppstopstep F C))) (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))))) p0190
  have p0192 :=
    @g_id (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))
  have p0193 :=
    @g_breq2d (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n))) (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)) (syn_ctc C) (syn_clec) p0192
  have p0194 :=
    @g_id (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))
  have p0195 :=
    @g_fveq2d (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n))) (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)) (syn_cwppstopstep F C) p0194
  have p0196 :=
    @g_breq2d (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n))) (syn_cfv (syn_cwppstopstep F C) (.cv y)) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n))) C (syn_clec) p0195
  have p0197 :=
    @g_imbi12d (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n))) (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n))) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) p0193 p0196
  have p0198 :=
    @g_rspcva (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))) (.imp (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n))) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n))))) y (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)) (syn_cdm (syn_cwppstopstep F C)) dv_cache_0024 dv_cache_0025 dv_cache_0026 p0197
  have p0199 :=
    @g_syl6 (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) (syn_wa (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)) (syn_cdm (syn_cwppstopstep F C))) (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))))) (.imp (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n))) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n))))) p0191 p0198
  have p0200 :=
    @g_mpdi (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n))) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) p0179 p0199
  have p0201 :=
    @g_n_3pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))) p0047 p0169 p0170
  have p0202 :=
    @g_a1i (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) p0201
  have p0203 :=
    @g_simpl (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))
  have p0204 :=
    @g_jca (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (.classMem (.cv n) (syn_cnnc)) p0202 p0203
  have p0205 :=
    @g_wpporbitsucndv (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (.cv n)
  have p0206 :=
    @g_syl (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) (syn_wa (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (.classMem (.cv n) (syn_cnnc))) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (syn_cplc (.cv n) (syn_c1c))) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) p0204 p0205
  have p0207 :=
    @g_breq2d (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (syn_cplc (.cv n) (syn_c1c))) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n))) C (syn_clec) p0206
  have p0208 :=
    @g_biimprd (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (syn_cplc (.cv n) (syn_c1c)))) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) p0207
  have p0209 :=
    @g_sylcom (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (syn_cplc (.cv n) (syn_c1c)))) p0200 p0208
  have p0210 :=
    @g_pm3_2 (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (syn_cplc (.cv n) (syn_c1c))))
  have p0211 :=
    @g_syl9 (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (syn_cplc (.cv n) (syn_c1c)))) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) (syn_wa (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (syn_cplc (.cv n) (syn_c1c))))) p0209 p0210
  have p0212 :=
    @g_syl5 (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (.imp (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) (syn_wa (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (syn_cplc (.cv n) (syn_c1c)))))) p0178 p0211
  have p0213 :=
    @g_pm2_43d (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) (syn_wa (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (syn_cplc (.cv n) (syn_c1c))))) p0212
  have p0214 :=
    @g_id (.classEq (.cv m) (syn_cplc (.cv n) (syn_c1c)))
  have p0215 :=
    @g_fveq2d (.classEq (.cv m) (syn_cplc (.cv n) (syn_c1c))) (.cv m) (syn_cplc (.cv n) (syn_c1c)) (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) p0214
  have p0216 :=
    @g_breq2d (.classEq (.cv m) (syn_cplc (.cv n) (syn_c1c))) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv m)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (syn_cplc (.cv n) (syn_c1c))) C (syn_clec) p0215
  have p0217 :=
    @g_rspcev (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv m))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (syn_cplc (.cv n) (syn_c1c)))) m (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc) dv_cache_0027 dv_cache_0028 dv_cache_0029 p0216
  have p0218 :=
    @g_syl6 (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) (syn_wa (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (syn_cplc (.cv n) (syn_c1c))))) (syn_wrex m (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv m)))) p0213 p0217
  have p0219 :=
    @g_exp3a (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n))) (syn_wrex m (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv m)))) p0218
  have p0220 :=
    @g_rexlimdv (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n))) (syn_wrex m (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv m)))) n (syn_cnnc) dv_cache_0030 dv_cache_0031 p0219
  have p0221 :=
    @g_id (.classEq (.cv m) (.cv n))
  have p0222 :=
    @g_fveq2d (.classEq (.cv m) (.cv n)) (.cv m) (.cv n) (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) p0221
  have p0223 :=
    @g_breq2d (.classEq (.cv m) (.cv n)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv m)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)) C (syn_clec) p0222
  have p0224_e00_recanon : Nominal.NPrf (.imp (.objEq m n) (syn_wb (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv m))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_clec syn_copab syn_cfv syn_cio syn_cuni syn_csn syn_cfrec syn_cclos1 syn_cint syn_cpprod syn_ctxp syn_cin syn_ccom syn_ccnv syn_c1st syn_cmpt syn_cvv syn_cplc syn_c1c syn_cwppstopstep syn_cif syn_wo syn_cwppgamma syn_ctc
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0223
  have p0224 :=
    @g_cbvrexv (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv m))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n))) m n (syn_cnnc) dv_cache_0028 dv_cache_0032 dv_cache_0033 dv_cache_0034 p0224_e00_recanon
  have p0225 :=
    @g_biimpi (syn_wrex m (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv m)))) (syn_wrex n (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) p0224
  have p0226 :=
    @g_syl6 (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wrex n (syn_cnnc) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) (syn_wrex m (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv m)))) (syn_wrex n (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) p0220 p0225
  have p0227 :=
    @g_a1i (syn_wbr (syn_ctc C) (syn_clec) C) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) hyp_wppstopgammafixedhwdndv_4
  have p0228 :=
    @g_simpr (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))
  have p0229 :=
    @g_jca (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) (syn_wbr (syn_ctc C) (syn_clec) C) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n))) p0227 p0228
  have p0230 :=
    @g_hwcardstcclndv C
  have p0231 :=
    Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0230
  have p0232 :=
    @g_hwcardssnc (syn_cvv)
  have p0233 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (syn_ctc C) p0232
  have p0234 :=
    Nominal.mp p0231 p0233
  have p0235 :=
    @g_a1i (.classMem (syn_ctc C) (syn_cncs)) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) p0234
  have p0236 :=
    @g_hwcardssnc (syn_cvv)
  have p0237 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) C p0236
  have p0238 :=
    Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0237
  have p0239 :=
    @g_a1i (.classMem C (syn_cncs)) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) p0238
  have p0240 :=
    @g_simpl (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))
  have p0241 :=
    @g_id (.classMem (.cv n) (syn_cnnc))
  have p0242 :=
    @g_simpr (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)
  have p0243 :=
    @g_iftrue (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C
  have p0244 :=
    @g_breq1d (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C (syn_clec) p0243
  have p0245 :=
    @g_mpbird (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_wbr (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_clec) C) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C) p0242 p0244
  have p0246 :=
    @g_hwcardssnc (syn_cvv)
  have p0247 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) C p0246
  have p0248 :=
    Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0247
  have p0249 :=
    @g_nclecid C
  have p0250 :=
    Nominal.mp p0248 p0249
  have p0251 :=
    @g_a1i (syn_wbr C (syn_clec) C) (.neg (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C))) p0250
  have p0252 :=
    @g_iffalse (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C
  have p0253 :=
    @g_breq1d (.neg (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C))) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) C C (syn_clec) p0252
  have p0254 :=
    @g_mpbird (.neg (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C))) (syn_wbr (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_clec) C) (syn_wbr C (syn_clec) C) p0251 p0253
  have p0255 :=
    @g_pm2_61i (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_wbr (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_clec) C) p0245 p0254
  have p0256 :=
    @g_tru
  have p0257 :=
    @g_simpr syn_wtru (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C))
  have p0258 :=
    @g_simpl (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)
  have p0259 :=
    @g_syl (syn_wa syn_wtru (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C))) (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) p0257 p0258
  have p0260 :=
    @g_a1i (.classMem C (syn_chwcards (syn_cvv))) (syn_wa syn_wtru (.neg (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)))) hyp_wppstopgammafixedhwdndv_3
  have p0261 :=
    @g_ifclda syn_wtru (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C (syn_chwcards (syn_cvv)) p0259 p0260
  have p0262 :=
    Nominal.mp p0256 p0261
  have p0263 :=
    @g_wppstopstepfunsndv C F hyp_wppstopgammafixedhwdndv_1 hyp_wppstopgammafixedhwdndv_2
  have p0264 :=
    @g_a1i (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc))) p0263
  have p0265 :=
    @g_simpl (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc))
  have p0266 :=
    @g_wppstopstepdmndv C F hyp_wppstopgammafixedhwdndv_1 hyp_wppstopgammafixedhwdndv_2
  have p0267 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F C)) (syn_chwcards (syn_cvv)) (.cv p) p0266
  have p0268 :=
    @g_biimpri (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (.classMem (.cv p) (syn_chwcards (syn_cvv))) p0267
  have p0269 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc))) (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) p0265 p0268
  have p0270 :=
    @g_wppstopsteprndmndv C F hyp_wppstopgammafixedhwdndv_1 hyp_wppstopgammafixedhwdndv_2
  have p0271 :=
    @g_a1i (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))) (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc))) p0270
  have p0272 :=
    @g_n_3jca (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc))) (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))) p0264 p0269 p0271
  have p0273 :=
    @g_simpr (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc))
  have p0274 :=
    @g_jca (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc))) (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (.classMem (.cv r) (syn_cnnc)) p0272 p0273
  have p0275 :=
    @g_frecdomfv (syn_cwppstopstep F C) (.cv p) (.cv r)
  have p0276 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc))) (syn_wa (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (.classMem (.cv r) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cdm (syn_cwppstopstep F C))) p0274 p0275
  have p0277 :=
    @g_wppstopstepdmndv C F hyp_wppstopgammafixedhwdndv_1 hyp_wppstopgammafixedhwdndv_2
  have p0278 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F C)) (syn_chwcards (syn_cvv)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) p0277
  have p0279 :=
    @g_sylib (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cdm (syn_cwppstopstep F C))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_chwcards (syn_cvv))) p0276 p0278
  have p0280 :=
    @g_hwcardssnc (syn_cvv)
  have p0281 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) p0280
  have p0282 :=
    @g_syl (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_chwcards (syn_cvv))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs)) p0279 p0281
  have p0283 :=
    @g_rgen2 (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs)) p r (syn_chwcards (syn_cvv)) (syn_cnnc) dv_cache_0001 dv_cache_0002 p0282
  have p0284 :=
    Nominal.ax1 (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs))) (syn_wbr (.cv p) (syn_clec) C)
  have p0285 :=
    @g_a1i (.imp (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs))) (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs))))) (.classMem (.cv p) (syn_chwcards (syn_cvv))) p0284
  have p0286 :=
    @g_ralimia (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs))) (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs)))) p (syn_chwcards (syn_cvv)) p0285
  have p0287 :=
    Nominal.mp p0283 p0286
  have p0288 :=
    @g_pm3_2i (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_chwcards (syn_cvv))) (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs))))) p0262 p0287
  have p0289 :=
    @g_id (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C))
  have p0290 :=
    @g_breq1d (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) C (syn_clec) p0289
  have p0291 :=
    @g_eqidd (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (syn_cwppstopstep F C)
  have p0292 :=
    @g_id (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C))
  have p0293 :=
    @g_jca (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.classEq (syn_cwppstopstep F C) (syn_cwppstopstep F C)) (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) p0291 p0292
  have p0294 :=
    @g_freceq12 (syn_cwppstopstep F C) (syn_cwppstopstep F C) (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)
  have p0295 :=
    @g_syl (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (syn_wa (.classEq (syn_cwppstopstep F C) (syn_cwppstopstep F C)) (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C))) (.classEq (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C))) p0293 p0294
  have p0296 :=
    @g_fveq1d (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv r) (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) p0295
  have p0297 :=
    @g_eleq1d (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv r)) (syn_cncs) p0296
  have p0298 :=
    @g_ralbidv (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv r)) (syn_cncs)) r (syn_cnnc) dv_cache_0035 p0297
  have p0299 :=
    @g_imbi12d (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (syn_wbr (.cv p) (syn_clec) C) (syn_wbr (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_clec) C) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs))) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv r)) (syn_cncs))) p0290 p0298
  have p0300 :=
    @g_rspcva (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs)))) (.imp (syn_wbr (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_clec) C) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv r)) (syn_cncs)))) p (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_chwcards (syn_cvv)) dv_cache_0018 dv_cache_0019 dv_cache_0036 p0299
  have p0301 :=
    Nominal.mp p0288 p0300
  have p0302 :=
    Nominal.mp p0255 p0301
  have p0303 :=
    @g_a1i (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv r)) (syn_cncs))) (.classMem (.cv n) (syn_cnnc)) p0302
  have p0304 :=
    @g_jca (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv r)) (syn_cncs))) p0241 p0303
  have p0305 :=
    @g_id (.classEq (.cv r) (.cv n))
  have p0306 :=
    @g_fveq2d (.classEq (.cv r) (.cv n)) (.cv r) (.cv n) (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) p0305
  have p0307 :=
    @g_eleq1d (.classEq (.cv r) (.cv n)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv r)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)) (syn_cncs) p0306
  have p0308 :=
    @g_rspcva (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv r)) (syn_cncs)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)) (syn_cncs)) r (.cv n) (syn_cnnc) dv_cache_0037 dv_cache_0038 dv_cache_0039 p0307
  have p0309 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv r)) (syn_cncs)))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)) (syn_cncs)) p0304 p0308
  have p0310 :=
    @g_syl (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)) (syn_cncs)) p0240 p0309
  have p0311 :=
    @g_n_3jca (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) (.classMem (syn_ctc C) (syn_cncs)) (.classMem C (syn_cncs)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)) (syn_cncs)) p0235 p0239 p0310
  have p0312 :=
    @g_lectr (syn_ctc C) C (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n))
  have p0313 :=
    @g_syl (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) (syn_w3a (.classMem (syn_ctc C) (syn_cncs)) (.classMem C (syn_cncs)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)) (syn_cncs))) (.imp (syn_wa (syn_wbr (syn_ctc C) (syn_clec) C) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) p0311 p0312
  have p0314 :=
    @g_mpd (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) (syn_wa (syn_wbr (syn_ctc C) (syn_clec) C) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n))) p0229 p0313
  have p0315 :=
    @g_ex (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n))) p0314
  have p0316 :=
    @g_reximia (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n))) n (syn_cnnc) p0315
  have p0317 :=
    @g_impbid1 (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wrex n (syn_cnnc) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) (syn_wrex n (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) p0226 p0316
  have p0318 :=
    @g_syl5bb (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C))) (syn_wrex n (syn_cnnc) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wrex n (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) p0175 p0317
  have p0319 :=
    @g_elex C (syn_chwcards (syn_cvv))
  have p0320 :=
    Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0319
  have p0321 :=
    @g_wppreachfwdrexvndv C (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) n (syn_cwppstopstep F C) dv_cache_0040 dv_cache_0022 dv_cache_0023 p0047 p0169 p0170 p0320
  have p0322 :=
    @g_bicomi (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_cwppreach (syn_cwppstopstep F C) C)) (syn_wrex n (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) p0321
  have p0323 :=
    @g_syl6bb (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C))) (syn_wrex n (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.cv n)))) (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_cwppreach (syn_cwppstopstep F C) C)) p0318 p0322
  have p0324 :=
    @g_iftrue (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C
  have p0325 :=
    @g_eqcomd (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) p0324
  have p0326 :=
    @g_id (.classEq (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C))
  have p0327 :=
    @g_eleq1d (.classEq (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C)) p0326
  have p0328 :=
    @g_id (.classEq (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C))
  have p0329 :=
    @g_eleq1d (.classEq (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_cwppreach (syn_cwppstopstep F C) C) p0328
  have p0330 :=
    @g_bibi12d (.classEq (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C))) (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C))) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppreach (syn_cwppstopstep F C) C)) (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_cwppreach (syn_cwppstopstep F C) C)) p0327 p0329
  have p0331 :=
    @g_syl (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (.classEq (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C)) (syn_wb (syn_wb (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C))) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppreach (syn_cwppstopstep F C) C))) (syn_wb (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C))) (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_cwppreach (syn_cwppstopstep F C) C)))) p0325 p0330
  have p0332 :=
    @g_syl5ibrcom (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wb (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C))) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppreach (syn_cwppstopstep F C) C))) (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_wb (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C))) (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) C) (syn_cwppreach (syn_cwppstopstep F C) C))) p0323 p0331
  have p0333 :=
    @g_mpi (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (syn_wb (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C))) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppreach (syn_cwppstopstep F C) C))) p0129 p0332
  have p0334 :=
    @g_mpbii (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C))) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppreach (syn_cwppstopstep F C) C)) p0067 p0333
  have p0335 :=
    @g_elex (syn_cwppstopstep F C) (syn_cfuns)
  have p0336 :=
    Nominal.mp p0047 p0335
  have p0337 :=
    @g_hwcardstcclndv C
  have p0338 :=
    Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0337
  have p0339 :=
    @g_pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cvv)) (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) p0336 p0338
  have p0340 :=
    @g_wppgammaminhwndv (syn_ctc C) k (syn_cwppstopstep F C) dv_cache_0017 dv_cache_0016
  have p0341 :=
    Nominal.mp p0339 p0340
  have p0342 :=
    @g_simpl (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C))) (syn_wral k (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C)) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (.cv k)))
  have p0343 :=
    Nominal.mp p0341 p0342
  have p0344 :=
    @g_elwppcand (syn_ctc C) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppstopstep F C)
  have p0345 :=
    @g_mpbi (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C))) (syn_wa (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (syn_ctc C))) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C)))) p0343 p0344
  have p0346 :=
    @g_simpl (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (syn_ctc C))) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C)))
  have p0347 :=
    Nominal.mp p0345 p0346
  have p0348 :=
    @g_simpl (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (syn_ctc C))
  have p0349 :=
    Nominal.mp p0347 p0348
  have p0350 :=
    @g_elex (syn_cwppstopstep F C) (syn_cfuns)
  have p0351 :=
    Nominal.mp p0047 p0350
  have p0352 :=
    @g_hwcardstcclndv C
  have p0353 :=
    Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0352
  have p0354 :=
    @g_pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cvv)) (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) p0351 p0353
  have p0355 :=
    @g_wppgammaminhwndv (syn_ctc C) k (syn_cwppstopstep F C) dv_cache_0017 dv_cache_0016
  have p0356 :=
    Nominal.mp p0354 p0355
  have p0357 :=
    @g_simpl (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C))) (syn_wral k (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C)) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (.cv k)))
  have p0358 :=
    Nominal.mp p0356 p0357
  have p0359 :=
    @g_elwppcand (syn_ctc C) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppstopstep F C)
  have p0360 :=
    @g_mpbi (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C))) (syn_wa (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (syn_ctc C))) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C)))) p0358 p0359
  have p0361 :=
    @g_simpl (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (syn_ctc C))) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C)))
  have p0362 :=
    Nominal.mp p0360 p0361
  have p0363 :=
    @g_simpr (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (syn_ctc C))
  have p0364 :=
    Nominal.mp p0362 p0363
  have p0365 :=
    @g_pm3_2i (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (syn_ctc C)) (syn_wbr (syn_ctc C) (syn_clec) C) p0364 hyp_wppstopgammafixedhwdndv_4
  have p0366 :=
    @g_elex (syn_cwppstopstep F C) (syn_cfuns)
  have p0367 :=
    Nominal.mp p0047 p0366
  have p0368 :=
    @g_hwcardstcclndv C
  have p0369 :=
    Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0368
  have p0370 :=
    @g_pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cvv)) (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) p0367 p0369
  have p0371 :=
    @g_wppgammaminhwndv (syn_ctc C) k (syn_cwppstopstep F C) dv_cache_0017 dv_cache_0016
  have p0372 :=
    Nominal.mp p0370 p0371
  have p0373 :=
    @g_simpl (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C))) (syn_wral k (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C)) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (.cv k)))
  have p0374 :=
    Nominal.mp p0372 p0373
  have p0375 :=
    @g_elwppcand (syn_ctc C) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppstopstep F C)
  have p0376 :=
    @g_mpbi (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C))) (syn_wa (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (syn_ctc C))) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C)))) p0374 p0375
  have p0377 :=
    @g_simpl (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (syn_ctc C))) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C)))
  have p0378 :=
    Nominal.mp p0376 p0377
  have p0379 :=
    @g_simpl (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (syn_ctc C))
  have p0380 :=
    Nominal.mp p0378 p0379
  have p0381 :=
    @g_hwcardssnc (syn_cvv)
  have p0382 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) p0381
  have p0383 :=
    Nominal.mp p0380 p0382
  have p0384 :=
    @g_hwcardstcclndv C
  have p0385 :=
    Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0384
  have p0386 :=
    @g_hwcardssnc (syn_cvv)
  have p0387 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (syn_ctc C) p0386
  have p0388 :=
    Nominal.mp p0385 p0387
  have p0389 :=
    @g_hwcardssnc (syn_cvv)
  have p0390 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) C p0389
  have p0391 :=
    Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0390
  have p0392 :=
    @g_n_3pm3_2i (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cncs)) (.classMem (syn_ctc C) (syn_cncs)) (.classMem C (syn_cncs)) p0383 p0388 p0391
  have p0393 :=
    @g_lectr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_ctc C) C
  have p0394 :=
    Nominal.mp p0392 p0393
  have p0395 :=
    Nominal.mp p0365 p0394
  have p0396 :=
    @g_pm3_2i (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C) p0349 p0395
  have p0397 :=
    @g_jctil (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppreach (syn_cwppstopstep F C) C)) (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) p0334 p0396
  have p0398 :=
    @g_elwppcand C (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppstopstep F C)
  have p0399 :=
    @g_sylibr (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) C)) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppreach (syn_cwppstopstep F C) C))) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppcand (syn_cwppstopstep F C) C)) p0397 p0398
  have p0400 :=
    @g_id (.classEq (.cv k) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)))
  have p0401 :=
    @g_breq2d (.classEq (.cv k) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))) (.cv k) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) p0400
  have p0402 :=
    @g_rspcv (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (.cv k)) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))) k (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppcand (syn_cwppstopstep F C) C) dv_cache_0041 dv_cache_0042 dv_cache_0043 p0401
  have p0403 :=
    @g_syl (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppcand (syn_cwppstopstep F C) C)) (.imp (syn_wral k (syn_cwppcand (syn_cwppstopstep F C) C) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (.cv k))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)))) p0399 p0402
  have p0404 :=
    @g_mpi (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wral k (syn_cwppcand (syn_cwppstopstep F C) C) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (.cv k))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))) p0054 p0403
  have p0405 :=
    @g_elex (syn_cwppstopstep F C) (syn_cfuns)
  have p0406 :=
    Nominal.mp p0047 p0405
  have p0407 :=
    @g_hwcardstcclndv C
  have p0408 :=
    Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0407
  have p0409 :=
    @g_pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cvv)) (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) p0406 p0408
  have p0410 :=
    @g_wppgammaminhwndv (syn_ctc C) k (syn_cwppstopstep F C) dv_cache_0017 dv_cache_0016
  have p0411 :=
    Nominal.mp p0409 p0410
  have p0412 :=
    @g_simpr (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C))) (syn_wral k (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C)) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (.cv k)))
  have p0413 :=
    Nominal.mp p0411 p0412
  have p0414 :=
    @g_elex (syn_cwppstopstep F C) (syn_cfuns)
  have p0415 :=
    Nominal.mp p0047 p0414
  have p0416 :=
    @g_pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cvv)) (.classMem C (syn_chwcards (syn_cvv))) p0415 hyp_wppstopgammafixedhwdndv_3
  have p0417 :=
    @g_wppgammaminhwndv C k (syn_cwppstopstep F C) dv_cache_0015 dv_cache_0016
  have p0418 :=
    Nominal.mp p0416 p0417
  have p0419 :=
    @g_simpr (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppcand (syn_cwppstopstep F C) C)) (syn_wral k (syn_cwppcand (syn_cwppstopstep F C) C) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (.cv k)))
  have p0420 :=
    Nominal.mp p0418 p0419
  have p0421 :=
    @g_hwcardstcclndv C
  have p0422 :=
    Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0421
  have p0423 :=
    @g_elex (syn_cwppstopstep F C) (syn_cfuns)
  have p0424 :=
    Nominal.mp p0047 p0423
  have p0425 :=
    @g_wppcandselfndv (syn_ctc C) (syn_cwppstopstep F C) p0424
  have p0426 :=
    Nominal.mp p0422 p0425
  have p0427 :=
    @g_elwppcand (syn_ctc C) (syn_ctc C) (syn_cwppstopstep F C)
  have p0428 :=
    @g_mpbi (.classMem (syn_ctc C) (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C))) (syn_wa (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) (syn_ctc C))) (.classMem (syn_ctc C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C)))) p0426 p0427
  have p0429 :=
    @g_simpr (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) (syn_ctc C))) (.classMem (syn_ctc C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C)))
  have p0430 :=
    Nominal.mp p0428 p0429
  have p0431 :=
    @g_hwcardstcclndv C
  have p0432 :=
    Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0431
  have p0433 :=
    @g_pm3_2i (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C) p0432 hyp_wppstopgammafixedhwdndv_4
  have p0434 :=
    @g_simpr (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)
  have p0435 :=
    @g_iftrue (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C
  have p0436 :=
    @g_breq1d (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_ctc C) C (syn_clec) p0435
  have p0437 :=
    @g_mpbird (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_wbr (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_clec) C) (syn_wbr (syn_ctc C) (syn_clec) C) p0434 p0436
  have p0438 :=
    @g_hwcardssnc (syn_cvv)
  have p0439 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) C p0438
  have p0440 :=
    Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0439
  have p0441 :=
    @g_nclecid C
  have p0442 :=
    Nominal.mp p0440 p0441
  have p0443 :=
    @g_a1i (syn_wbr C (syn_clec) C) (.neg (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C))) p0442
  have p0444 :=
    @g_iffalse (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C
  have p0445 :=
    @g_breq1d (.neg (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C))) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) C C (syn_clec) p0444
  have p0446 :=
    @g_mpbird (.neg (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C))) (syn_wbr (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_clec) C) (syn_wbr C (syn_clec) C) p0443 p0445
  have p0447 :=
    @g_pm2_61i (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_wbr (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_clec) C) p0437 p0446
  have p0448 :=
    @g_tru
  have p0449 :=
    @g_simpr syn_wtru (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C))
  have p0450 :=
    @g_simpl (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)
  have p0451 :=
    @g_syl (syn_wa syn_wtru (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C))) (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) p0449 p0450
  have p0452 :=
    @g_a1i (.classMem C (syn_chwcards (syn_cvv))) (syn_wa syn_wtru (.neg (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)))) hyp_wppstopgammafixedhwdndv_3
  have p0453 :=
    @g_ifclda syn_wtru (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C (syn_chwcards (syn_cvv)) p0451 p0452
  have p0454 :=
    Nominal.mp p0448 p0453
  have p0455 :=
    @g_pm3_2i (.classMem (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_chwcards (syn_cvv))) (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))))) p0454 p0160
  have p0456 :=
    @g_id (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C))
  have p0457 :=
    @g_breq1d (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv p) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) C (syn_clec) p0456
  have p0458 :=
    @g_id (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C))
  have p0459 :=
    @g_eleq1d (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv p) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_cdm (syn_cwppstopstep F C)) p0458
  have p0460 :=
    @g_imbi12d (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (syn_wbr (.cv p) (syn_clec) C) (syn_wbr (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_clec) C) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (.classMem (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_cdm (syn_cwppstopstep F C))) p0457 p0459
  have p0461 :=
    @g_rspcva (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C)))) (.imp (syn_wbr (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_clec) C) (.classMem (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_cdm (syn_cwppstopstep F C)))) p (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_chwcards (syn_cvv)) dv_cache_0044 dv_cache_0019 dv_cache_0045 p0460
  have p0462 :=
    Nominal.mp p0455 p0461
  have p0463 :=
    Nominal.mp p0447 p0462
  have p0464 :=
    @g_hwcardstcclndv C
  have p0465 :=
    Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0464
  have p0466 :=
    @g_elex (syn_ctc C) (syn_chwcards (syn_cvv))
  have p0467 :=
    Nominal.mp p0465 p0466
  have p0468 :=
    @g_wppreachfwdrexvndv (syn_ctc C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) n (syn_cwppstopstep F C) dv_cache_0021 dv_cache_0046 dv_cache_0023 p0047 p0463 p0170 p0467
  have p0469 :=
    @g_simpl (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))
  have p0470 :=
    @g_peano2 (.cv n)
  have p0471 :=
    @g_syl (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) p0469 p0470
  have p0472 :=
    @g_simpr (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))
  have p0473 :=
    @g_n_3pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))) p0047 p0463 p0170
  have p0474 :=
    @g_a1i (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) p0473
  have p0475 :=
    @g_simpl (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))
  have p0476 :=
    @g_jca (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (.classMem (.cv n) (syn_cnnc)) p0474 p0475
  have p0477 :=
    @g_frecdomfv (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (.cv n)
  have p0478 :=
    @g_syl (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) (syn_wa (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (.classMem (.cv n) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)) (syn_cdm (syn_cwppstopstep F C))) p0476 p0477
  have p0479 :=
    @g_a1d (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) p0186
  have p0480 :=
    @g_pm3_2 (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)) (syn_cdm (syn_cwppstopstep F C))) (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))))
  have p0481 :=
    @g_syl9 (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)) (syn_cdm (syn_cwppstopstep F C))) (syn_wa (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)) (syn_cdm (syn_cwppstopstep F C))) (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))))) p0479 p0480
  have p0482 :=
    @g_syl5 (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)) (syn_cdm (syn_cwppstopstep F C))) (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (.imp (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) (syn_wa (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)) (syn_cdm (syn_cwppstopstep F C))) (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))))) p0478 p0481
  have p0483 :=
    @g_pm2_43d (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) (syn_wa (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)) (syn_cdm (syn_cwppstopstep F C))) (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))))) p0482
  have p0484 :=
    @g_id (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))
  have p0485 :=
    @g_breq2d (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n))) (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)) (syn_ctc C) (syn_clec) p0484
  have p0486 :=
    @g_id (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))
  have p0487 :=
    @g_fveq2d (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n))) (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)) (syn_cwppstopstep F C) p0486
  have p0488 :=
    @g_breq2d (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n))) (syn_cfv (syn_cwppstopstep F C) (.cv y)) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n))) C (syn_clec) p0487
  have p0489 :=
    @g_imbi12d (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n))) (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n))) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) p0485 p0488
  have p0490 :=
    @g_rspcva (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))) (.imp (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n))) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n))))) y (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)) (syn_cdm (syn_cwppstopstep F C)) dv_cache_0047 dv_cache_0025 dv_cache_0048 p0489
  have p0491 :=
    @g_syl6 (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) (syn_wa (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)) (syn_cdm (syn_cwppstopstep F C))) (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))))) (.imp (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n))) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n))))) p0483 p0490
  have p0492 :=
    @g_mpdi (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n))) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) p0472 p0491
  have p0493 :=
    @g_n_3pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))) p0047 p0463 p0170
  have p0494 :=
    @g_a1i (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) p0493
  have p0495 :=
    @g_simpl (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))
  have p0496 :=
    @g_jca (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (.classMem (.cv n) (syn_cnnc)) p0494 p0495
  have p0497 :=
    @g_wpporbitsucndv (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (.cv n)
  have p0498 :=
    @g_syl (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) (syn_wa (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (.classMem (.cv n) (syn_cnnc))) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (syn_cplc (.cv n) (syn_c1c))) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) p0496 p0497
  have p0499 :=
    @g_breq2d (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (syn_cplc (.cv n) (syn_c1c))) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n))) C (syn_clec) p0498
  have p0500 :=
    @g_biimprd (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (syn_cplc (.cv n) (syn_c1c)))) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) p0499
  have p0501 :=
    @g_sylcom (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (syn_cplc (.cv n) (syn_c1c)))) p0492 p0500
  have p0502 :=
    @g_pm3_2 (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (syn_cplc (.cv n) (syn_c1c))))
  have p0503 :=
    @g_syl9 (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (syn_cplc (.cv n) (syn_c1c)))) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) (syn_wa (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (syn_cplc (.cv n) (syn_c1c))))) p0501 p0502
  have p0504 :=
    @g_syl5 (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (.imp (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) (syn_wa (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (syn_cplc (.cv n) (syn_c1c)))))) p0471 p0503
  have p0505 :=
    @g_pm2_43d (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) (syn_wa (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (syn_cplc (.cv n) (syn_c1c))))) p0504
  have p0506 :=
    @g_id (.classEq (.cv m) (syn_cplc (.cv n) (syn_c1c)))
  have p0507 :=
    @g_fveq2d (.classEq (.cv m) (syn_cplc (.cv n) (syn_c1c))) (.cv m) (syn_cplc (.cv n) (syn_c1c)) (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) p0506
  have p0508 :=
    @g_breq2d (.classEq (.cv m) (syn_cplc (.cv n) (syn_c1c))) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv m)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (syn_cplc (.cv n) (syn_c1c))) C (syn_clec) p0507
  have p0509 :=
    @g_rspcev (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv m))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (syn_cplc (.cv n) (syn_c1c)))) m (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc) dv_cache_0027 dv_cache_0028 dv_cache_0049 p0508
  have p0510 :=
    @g_syl6 (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) (syn_wa (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (syn_cplc (.cv n) (syn_c1c))))) (syn_wrex m (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv m)))) p0505 p0509
  have p0511 :=
    @g_exp3a (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n))) (syn_wrex m (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv m)))) p0510
  have p0512 :=
    @g_rexlimdv (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n))) (syn_wrex m (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv m)))) n (syn_cnnc) dv_cache_0050 dv_cache_0031 p0511
  have p0513 :=
    @g_id (.classEq (.cv m) (.cv n))
  have p0514 :=
    @g_fveq2d (.classEq (.cv m) (.cv n)) (.cv m) (.cv n) (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) p0513
  have p0515 :=
    @g_breq2d (.classEq (.cv m) (.cv n)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv m)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)) C (syn_clec) p0514
  have p0516_e00_recanon : Nominal.NPrf (.imp (.objEq m n) (syn_wb (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv m))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_clec syn_copab syn_cfv syn_cio syn_cuni syn_csn syn_cfrec syn_cclos1 syn_cint syn_cpprod syn_ctxp syn_cin syn_ccom syn_ccnv syn_c1st syn_cmpt syn_cvv syn_cplc syn_c1c syn_cwppstopstep syn_cif syn_wo syn_ctc
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0515
  have p0516 :=
    @g_cbvrexv (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv m))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n))) m n (syn_cnnc) dv_cache_0028 dv_cache_0032 dv_cache_0051 dv_cache_0052 p0516_e00_recanon
  have p0517 :=
    @g_biimpi (syn_wrex m (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv m)))) (syn_wrex n (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) p0516
  have p0518 :=
    @g_syl6 (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wrex n (syn_cnnc) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) (syn_wrex m (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv m)))) (syn_wrex n (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) p0512 p0517
  have p0519 :=
    @g_a1i (syn_wbr (syn_ctc C) (syn_clec) C) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) hyp_wppstopgammafixedhwdndv_4
  have p0520 :=
    @g_simpr (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))
  have p0521 :=
    @g_jca (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) (syn_wbr (syn_ctc C) (syn_clec) C) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n))) p0519 p0520
  have p0522 :=
    @g_hwcardstcclndv C
  have p0523 :=
    Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0522
  have p0524 :=
    @g_hwcardssnc (syn_cvv)
  have p0525 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (syn_ctc C) p0524
  have p0526 :=
    Nominal.mp p0523 p0525
  have p0527 :=
    @g_a1i (.classMem (syn_ctc C) (syn_cncs)) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) p0526
  have p0528 :=
    @g_hwcardssnc (syn_cvv)
  have p0529 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) C p0528
  have p0530 :=
    Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0529
  have p0531 :=
    @g_a1i (.classMem C (syn_cncs)) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) p0530
  have p0532 :=
    @g_simpl (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))
  have p0533 :=
    @g_id (.classMem (.cv n) (syn_cnnc))
  have p0534 :=
    @g_simpr (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)
  have p0535 :=
    @g_iftrue (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C
  have p0536 :=
    @g_breq1d (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_ctc C) C (syn_clec) p0535
  have p0537 :=
    @g_mpbird (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_wbr (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_clec) C) (syn_wbr (syn_ctc C) (syn_clec) C) p0534 p0536
  have p0538 :=
    @g_hwcardssnc (syn_cvv)
  have p0539 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) C p0538
  have p0540 :=
    Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0539
  have p0541 :=
    @g_nclecid C
  have p0542 :=
    Nominal.mp p0540 p0541
  have p0543 :=
    @g_a1i (syn_wbr C (syn_clec) C) (.neg (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C))) p0542
  have p0544 :=
    @g_iffalse (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C
  have p0545 :=
    @g_breq1d (.neg (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C))) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) C C (syn_clec) p0544
  have p0546 :=
    @g_mpbird (.neg (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C))) (syn_wbr (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_clec) C) (syn_wbr C (syn_clec) C) p0543 p0545
  have p0547 :=
    @g_pm2_61i (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_wbr (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_clec) C) p0537 p0546
  have p0548 :=
    @g_tru
  have p0549 :=
    @g_simpr syn_wtru (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C))
  have p0550 :=
    @g_simpl (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)
  have p0551 :=
    @g_syl (syn_wa syn_wtru (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C))) (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) p0549 p0550
  have p0552 :=
    @g_a1i (.classMem C (syn_chwcards (syn_cvv))) (syn_wa syn_wtru (.neg (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)))) hyp_wppstopgammafixedhwdndv_3
  have p0553 :=
    @g_ifclda syn_wtru (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C (syn_chwcards (syn_cvv)) p0551 p0552
  have p0554 :=
    Nominal.mp p0548 p0553
  have p0555 :=
    @g_pm3_2i (.classMem (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_chwcards (syn_cvv))) (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs))))) p0554 p0287
  have p0556 :=
    @g_id (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C))
  have p0557 :=
    @g_breq1d (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv p) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) C (syn_clec) p0556
  have p0558 :=
    @g_eqidd (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (syn_cwppstopstep F C)
  have p0559 :=
    @g_id (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C))
  have p0560 :=
    @g_jca (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.classEq (syn_cwppstopstep F C) (syn_cwppstopstep F C)) (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) p0558 p0559
  have p0561 :=
    @g_freceq12 (syn_cwppstopstep F C) (syn_cwppstopstep F C) (.cv p) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)
  have p0562 :=
    @g_syl (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (syn_wa (.classEq (syn_cwppstopstep F C) (syn_cwppstopstep F C)) (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C))) (.classEq (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C))) p0560 p0561
  have p0563 :=
    @g_fveq1d (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv r) (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) p0562
  have p0564 :=
    @g_eleq1d (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv r)) (syn_cncs) p0563
  have p0565 :=
    @g_ralbidv (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv r)) (syn_cncs)) r (syn_cnnc) dv_cache_0053 p0564
  have p0566 :=
    @g_imbi12d (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (syn_wbr (.cv p) (syn_clec) C) (syn_wbr (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_clec) C) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs))) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv r)) (syn_cncs))) p0557 p0565
  have p0567 :=
    @g_rspcva (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs)))) (.imp (syn_wbr (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_clec) C) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv r)) (syn_cncs)))) p (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_chwcards (syn_cvv)) dv_cache_0044 dv_cache_0019 dv_cache_0054 p0566
  have p0568 :=
    Nominal.mp p0555 p0567
  have p0569 :=
    Nominal.mp p0547 p0568
  have p0570 :=
    @g_a1i (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv r)) (syn_cncs))) (.classMem (.cv n) (syn_cnnc)) p0569
  have p0571 :=
    @g_jca (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv r)) (syn_cncs))) p0533 p0570
  have p0572 :=
    @g_id (.classEq (.cv r) (.cv n))
  have p0573 :=
    @g_fveq2d (.classEq (.cv r) (.cv n)) (.cv r) (.cv n) (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) p0572
  have p0574 :=
    @g_eleq1d (.classEq (.cv r) (.cv n)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv r)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)) (syn_cncs) p0573
  have p0575 :=
    @g_rspcva (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv r)) (syn_cncs)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)) (syn_cncs)) r (.cv n) (syn_cnnc) dv_cache_0037 dv_cache_0038 dv_cache_0055 p0574
  have p0576 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv r)) (syn_cncs)))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)) (syn_cncs)) p0571 p0575
  have p0577 :=
    @g_syl (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)) (syn_cncs)) p0532 p0576
  have p0578 :=
    @g_n_3jca (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) (.classMem (syn_ctc C) (syn_cncs)) (.classMem C (syn_cncs)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)) (syn_cncs)) p0527 p0531 p0577
  have p0579 :=
    @g_lectr (syn_ctc C) C (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n))
  have p0580 :=
    @g_syl (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) (syn_w3a (.classMem (syn_ctc C) (syn_cncs)) (.classMem C (syn_cncs)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)) (syn_cncs))) (.imp (syn_wa (syn_wbr (syn_ctc C) (syn_clec) C) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) p0578 p0579
  have p0581 :=
    @g_mpd (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) (syn_wa (syn_wbr (syn_ctc C) (syn_clec) C) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n))) p0521 p0580
  have p0582 :=
    @g_ex (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n))) p0581
  have p0583 :=
    @g_reximia (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n))) n (syn_cnnc) p0582
  have p0584 :=
    @g_impbid1 (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wrex n (syn_cnnc) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) (syn_wrex n (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) p0518 p0583
  have p0585 :=
    @g_syl5bb (.classMem (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C))) (syn_wrex n (syn_cnnc) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wrex n (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) p0468 p0584
  have p0586 :=
    @g_elex C (syn_chwcards (syn_cvv))
  have p0587 :=
    Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0586
  have p0588 :=
    @g_wppreachfwdrexvndv C (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) n (syn_cwppstopstep F C) dv_cache_0040 dv_cache_0046 dv_cache_0023 p0047 p0463 p0170 p0587
  have p0589 :=
    @g_bicomi (.classMem (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_cwppreach (syn_cwppstopstep F C) C)) (syn_wrex n (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) p0588
  have p0590 :=
    @g_syl6bb (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (.classMem (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C))) (syn_wrex n (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.cv n)))) (.classMem (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_cwppreach (syn_cwppstopstep F C) C)) p0585 p0589
  have p0591 :=
    @g_iftrue (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C
  have p0592 :=
    @g_eqcomd (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_ctc C) p0591
  have p0593 :=
    @g_id (.classEq (syn_ctc C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C))
  have p0594 :=
    @g_eleq1d (.classEq (syn_ctc C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (syn_ctc C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C)) p0593
  have p0595 :=
    @g_id (.classEq (syn_ctc C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C))
  have p0596 :=
    @g_eleq1d (.classEq (syn_ctc C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (syn_ctc C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_cwppreach (syn_cwppstopstep F C) C) p0595
  have p0597 :=
    @g_bibi12d (.classEq (syn_ctc C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (.classMem (syn_ctc C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C))) (.classMem (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C))) (.classMem (syn_ctc C) (syn_cwppreach (syn_cwppstopstep F C) C)) (.classMem (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_cwppreach (syn_cwppstopstep F C) C)) p0594 p0596
  have p0598 :=
    @g_syl (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (.classEq (syn_ctc C) (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C)) (syn_wb (syn_wb (.classMem (syn_ctc C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C))) (.classMem (syn_ctc C) (syn_cwppreach (syn_cwppstopstep F C) C))) (syn_wb (.classMem (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C))) (.classMem (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_cwppreach (syn_cwppstopstep F C) C)))) p0592 p0597
  have p0599 :=
    @g_syl5ibrcom (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wb (.classMem (syn_ctc C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C))) (.classMem (syn_ctc C) (syn_cwppreach (syn_cwppstopstep F C) C))) (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_wb (.classMem (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C))) (.classMem (syn_cif (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_ctc C) C) (syn_cwppreach (syn_cwppstopstep F C) C))) p0590 p0598
  have p0600 :=
    @g_mpi (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (syn_wb (.classMem (syn_ctc C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C))) (.classMem (syn_ctc C) (syn_cwppreach (syn_cwppstopstep F C) C))) p0433 p0599
  have p0601 :=
    @g_mpbii (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (.classMem (syn_ctc C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C))) (.classMem (syn_ctc C) (syn_cwppreach (syn_cwppstopstep F C) C)) p0430 p0600
  have p0602 :=
    @g_hwcardstcclndv C
  have p0603 :=
    Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0602
  have p0604 :=
    @g_pm3_2i (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C) p0603 hyp_wppstopgammafixedhwdndv_4
  have p0605 :=
    @g_jctil (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (.classMem (syn_ctc C) (syn_cwppreach (syn_cwppstopstep F C) C)) (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) p0601 p0604
  have p0606 :=
    @g_elwppcand C (syn_ctc C) (syn_cwppstopstep F C)
  have p0607 :=
    @g_sylibr (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa (syn_wa (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc C) (syn_clec) C)) (.classMem (syn_ctc C) (syn_cwppreach (syn_cwppstopstep F C) C))) (.classMem (syn_ctc C) (syn_cwppcand (syn_cwppstopstep F C) C)) p0605 p0606
  have p0608 :=
    @g_id (.classEq (.cv k) (syn_ctc C))
  have p0609 :=
    @g_breq2d (.classEq (.cv k) (syn_ctc C)) (.cv k) (syn_ctc C) (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) p0608
  have p0610 :=
    @g_rspcv (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (.cv k)) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (syn_ctc C)) k (syn_ctc C) (syn_cwppcand (syn_cwppstopstep F C) C) dv_cache_0017 dv_cache_0042 dv_cache_0056 p0609
  have p0611 :=
    @g_syl (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (.classMem (syn_ctc C) (syn_cwppcand (syn_cwppstopstep F C) C)) (.imp (syn_wral k (syn_cwppcand (syn_cwppstopstep F C) C) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (.cv k))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (syn_ctc C))) p0607 p0610
  have p0612 :=
    @g_mpi (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wral k (syn_cwppcand (syn_cwppstopstep F C) C) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (.cv k))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (syn_ctc C)) p0420 p0611
  have p0613 :=
    @g_elex (syn_cwppstopstep F C) (syn_cfuns)
  have p0614 :=
    Nominal.mp p0047 p0613
  have p0615 :=
    @g_pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cvv)) (.classMem C (syn_chwcards (syn_cvv))) p0614 hyp_wppstopgammafixedhwdndv_3
  have p0616 :=
    @g_wppgammaminhwndv C k (syn_cwppstopstep F C) dv_cache_0015 dv_cache_0016
  have p0617 :=
    Nominal.mp p0615 p0616
  have p0618 :=
    @g_simpl (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppcand (syn_cwppstopstep F C) C)) (syn_wral k (syn_cwppcand (syn_cwppstopstep F C) C) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (.cv k)))
  have p0619 :=
    Nominal.mp p0617 p0618
  have p0620 :=
    @g_elwppcand C (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppstopstep F C)
  have p0621 :=
    @g_mpbi (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppcand (syn_cwppstopstep F C) C)) (syn_wa (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppreach (syn_cwppstopstep F C) C))) p0619 p0620
  have p0622 :=
    @g_simpl (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppreach (syn_cwppstopstep F C) C))
  have p0623 :=
    Nominal.mp p0621 p0622
  have p0624 :=
    @g_simpl (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)
  have p0625 :=
    Nominal.mp p0623 p0624
  have p0626 :=
    @g_jctil (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (syn_ctc C)) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) p0612 p0625
  have p0627 :=
    @g_elex (syn_cwppstopstep F C) (syn_cfuns)
  have p0628 :=
    Nominal.mp p0047 p0627
  have p0629 :=
    @g_pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cvv)) (.classMem C (syn_chwcards (syn_cvv))) p0628 hyp_wppstopgammafixedhwdndv_3
  have p0630 :=
    @g_wppgammaminhwndv C k (syn_cwppstopstep F C) dv_cache_0015 dv_cache_0016
  have p0631 :=
    Nominal.mp p0629 p0630
  have p0632 :=
    @g_simpl (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppcand (syn_cwppstopstep F C) C)) (syn_wral k (syn_cwppcand (syn_cwppstopstep F C) C) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (.cv k)))
  have p0633 :=
    Nominal.mp p0631 p0632
  have p0634 :=
    @g_elwppcand C (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppstopstep F C)
  have p0635 :=
    @g_mpbi (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppcand (syn_cwppstopstep F C) C)) (syn_wa (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppreach (syn_cwppstopstep F C) C))) p0633 p0634
  have p0636 :=
    @g_simpr (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppreach (syn_cwppstopstep F C) C))
  have p0637 :=
    Nominal.mp p0635 p0636
  have p0638 :=
    @g_elex (syn_cwppstopstep F C) (syn_cfuns)
  have p0639 :=
    Nominal.mp p0047 p0638
  have p0640 :=
    @g_pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cvv)) (.classMem C (syn_chwcards (syn_cvv))) p0639 hyp_wppstopgammafixedhwdndv_3
  have p0641 :=
    @g_wppgammaminhwndv C k (syn_cwppstopstep F C) dv_cache_0015 dv_cache_0016
  have p0642 :=
    Nominal.mp p0640 p0641
  have p0643 :=
    @g_simpl (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppcand (syn_cwppstopstep F C) C)) (syn_wral k (syn_cwppcand (syn_cwppstopstep F C) C) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (.cv k)))
  have p0644 :=
    Nominal.mp p0642 p0643
  have p0645 :=
    @g_elwppcand C (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppstopstep F C)
  have p0646 :=
    @g_mpbi (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppcand (syn_cwppstopstep F C) C)) (syn_wa (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppreach (syn_cwppstopstep F C) C))) p0644 p0645
  have p0647 :=
    @g_simpl (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppreach (syn_cwppstopstep F C) C))
  have p0648 :=
    Nominal.mp p0646 p0647
  have p0649 :=
    @g_simpl (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)
  have p0650 :=
    Nominal.mp p0648 p0649
  have p0651 :=
    @g_elex (syn_cwppstopstep F C) (syn_cfuns)
  have p0652 :=
    Nominal.mp p0047 p0651
  have p0653 :=
    @g_pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cvv)) (.classMem C (syn_chwcards (syn_cvv))) p0652 hyp_wppstopgammafixedhwdndv_3
  have p0654 :=
    @g_wppgammaminhwndv C k (syn_cwppstopstep F C) dv_cache_0015 dv_cache_0016
  have p0655 :=
    Nominal.mp p0653 p0654
  have p0656 :=
    @g_simpl (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppcand (syn_cwppstopstep F C) C)) (syn_wral k (syn_cwppcand (syn_cwppstopstep F C) C) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (.cv k)))
  have p0657 :=
    Nominal.mp p0655 p0656
  have p0658 :=
    @g_elwppcand C (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppstopstep F C)
  have p0659 :=
    @g_mpbi (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppcand (syn_cwppstopstep F C) C)) (syn_wa (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppreach (syn_cwppstopstep F C) C))) p0657 p0658
  have p0660 :=
    @g_simpl (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppreach (syn_cwppstopstep F C) C))
  have p0661 :=
    Nominal.mp p0659 p0660
  have p0662 :=
    @g_simpr (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)
  have p0663 :=
    Nominal.mp p0661 p0662
  have p0664 :=
    @g_pm3_2i (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C) p0650 p0663
  have p0665 :=
    @g_simpr (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)
  have p0666 :=
    @g_iftrue (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C
  have p0667 :=
    @g_breq1d (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_cwppgamma (syn_cwppstopstep F C) C) C (syn_clec) p0666
  have p0668 :=
    @g_mpbird (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_wbr (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_clec) C) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C) p0665 p0667
  have p0669 :=
    @g_hwcardssnc (syn_cvv)
  have p0670 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) C p0669
  have p0671 :=
    Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0670
  have p0672 :=
    @g_nclecid C
  have p0673 :=
    Nominal.mp p0671 p0672
  have p0674 :=
    @g_a1i (syn_wbr C (syn_clec) C) (.neg (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C))) p0673
  have p0675 :=
    @g_iffalse (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C
  have p0676 :=
    @g_breq1d (.neg (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C))) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) C C (syn_clec) p0675
  have p0677 :=
    @g_mpbird (.neg (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C))) (syn_wbr (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_clec) C) (syn_wbr C (syn_clec) C) p0674 p0676
  have p0678 :=
    @g_pm2_61i (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_wbr (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_clec) C) p0668 p0677
  have p0679 :=
    @g_tru
  have p0680 :=
    @g_simpr syn_wtru (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C))
  have p0681 :=
    @g_simpl (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)
  have p0682 :=
    @g_syl (syn_wa syn_wtru (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C))) (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) p0680 p0681
  have p0683 :=
    @g_a1i (.classMem C (syn_chwcards (syn_cvv))) (syn_wa syn_wtru (.neg (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)))) hyp_wppstopgammafixedhwdndv_3
  have p0684 :=
    @g_ifclda syn_wtru (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C (syn_chwcards (syn_cvv)) p0682 p0683
  have p0685 :=
    Nominal.mp p0679 p0684
  have p0686 :=
    @g_pm3_2i (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_chwcards (syn_cvv))) (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))))) p0685 p0160
  have p0687 :=
    @g_id (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
  have p0688 :=
    @g_breq1d (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) C (syn_clec) p0687
  have p0689 :=
    @g_id (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
  have p0690 :=
    @g_eleq1d (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_cdm (syn_cwppstopstep F C)) p0689
  have p0691 :=
    @g_imbi12d (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (syn_wbr (.cv p) (syn_clec) C) (syn_wbr (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_clec) C) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_cdm (syn_cwppstopstep F C))) p0688 p0690
  have p0692 :=
    @g_rspcva (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C)))) (.imp (syn_wbr (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_clec) C) (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_cdm (syn_cwppstopstep F C)))) p (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_chwcards (syn_cvv)) dv_cache_0057 dv_cache_0019 dv_cache_0058 p0691
  have p0693 :=
    Nominal.mp p0686 p0692
  have p0694 :=
    Nominal.mp p0678 p0693
  have p0695 :=
    @g_hwcardstcclndv C
  have p0696 :=
    Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0695
  have p0697 :=
    @g_elex (syn_ctc C) (syn_chwcards (syn_cvv))
  have p0698 :=
    Nominal.mp p0696 p0697
  have p0699 :=
    @g_wppreachfwdrexvndv (syn_ctc C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) n (syn_cwppstopstep F C) dv_cache_0021 dv_cache_0059 dv_cache_0023 p0047 p0694 p0170 p0698
  have p0700 :=
    @g_simpl (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))
  have p0701 :=
    @g_peano2 (.cv n)
  have p0702 :=
    @g_syl (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) p0700 p0701
  have p0703 :=
    @g_simpr (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))
  have p0704 :=
    @g_n_3pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))) p0047 p0694 p0170
  have p0705 :=
    @g_a1i (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) p0704
  have p0706 :=
    @g_simpl (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))
  have p0707 :=
    @g_jca (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (.classMem (.cv n) (syn_cnnc)) p0705 p0706
  have p0708 :=
    @g_frecdomfv (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (.cv n)
  have p0709 :=
    @g_syl (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) (syn_wa (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (.classMem (.cv n) (syn_cnnc))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)) (syn_cdm (syn_cwppstopstep F C))) p0707 p0708
  have p0710 :=
    @g_a1d (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) p0186
  have p0711 :=
    @g_pm3_2 (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)) (syn_cdm (syn_cwppstopstep F C))) (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))))
  have p0712 :=
    @g_syl9 (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)) (syn_cdm (syn_cwppstopstep F C))) (syn_wa (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)) (syn_cdm (syn_cwppstopstep F C))) (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))))) p0710 p0711
  have p0713 :=
    @g_syl5 (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)) (syn_cdm (syn_cwppstopstep F C))) (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (.imp (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) (syn_wa (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)) (syn_cdm (syn_cwppstopstep F C))) (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))))) p0709 p0712
  have p0714 :=
    @g_pm2_43d (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) (syn_wa (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)) (syn_cdm (syn_cwppstopstep F C))) (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))))) p0713
  have p0715 :=
    @g_id (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))
  have p0716 :=
    @g_breq2d (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n))) (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)) (syn_ctc C) (syn_clec) p0715
  have p0717 :=
    @g_id (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))
  have p0718 :=
    @g_fveq2d (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n))) (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)) (syn_cwppstopstep F C) p0717
  have p0719 :=
    @g_breq2d (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n))) (syn_cfv (syn_cwppstopstep F C) (.cv y)) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n))) C (syn_clec) p0718
  have p0720 :=
    @g_imbi12d (.classEq (.cv y) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n))) (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n))) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) p0716 p0719
  have p0721 :=
    @g_rspcva (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))) (.imp (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n))) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n))))) y (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)) (syn_cdm (syn_cwppstopstep F C)) dv_cache_0060 dv_cache_0025 dv_cache_0061 p0720
  have p0722 :=
    @g_syl6 (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) (syn_wa (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)) (syn_cdm (syn_cwppstopstep F C))) (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y)))))) (.imp (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n))) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n))))) p0714 p0721
  have p0723 :=
    @g_mpdi (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n))) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) p0703 p0722
  have p0724 :=
    @g_n_3pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))) p0047 p0694 p0170
  have p0725 :=
    @g_a1i (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) p0724
  have p0726 :=
    @g_simpl (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))
  have p0727 :=
    @g_jca (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (.classMem (.cv n) (syn_cnnc)) p0725 p0726
  have p0728 :=
    @g_wpporbitsucndv (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (.cv n)
  have p0729 :=
    @g_syl (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) (syn_wa (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns)) (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_cdm (syn_cwppstopstep F C))) (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))) (.classMem (.cv n) (syn_cnnc))) (.classEq (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (syn_cplc (.cv n) (syn_c1c))) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) p0727 p0728
  have p0730 :=
    @g_breq2d (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (syn_cplc (.cv n) (syn_c1c))) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n))) C (syn_clec) p0729
  have p0731 :=
    @g_biimprd (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (syn_cplc (.cv n) (syn_c1c)))) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) p0730
  have p0732 :=
    @g_sylcom (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (syn_cplc (.cv n) (syn_c1c)))) p0723 p0731
  have p0733 :=
    @g_pm3_2 (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (syn_cplc (.cv n) (syn_c1c))))
  have p0734 :=
    @g_syl9 (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (syn_cplc (.cv n) (syn_c1c)))) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) (syn_wa (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (syn_cplc (.cv n) (syn_c1c))))) p0732 p0733
  have p0735 :=
    @g_syl5 (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (.imp (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) (syn_wa (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (syn_cplc (.cv n) (syn_c1c)))))) p0702 p0734
  have p0736 :=
    @g_pm2_43d (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) (syn_wa (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (syn_cplc (.cv n) (syn_c1c))))) p0735
  have p0737 :=
    @g_id (.classEq (.cv m) (syn_cplc (.cv n) (syn_c1c)))
  have p0738 :=
    @g_fveq2d (.classEq (.cv m) (syn_cplc (.cv n) (syn_c1c))) (.cv m) (syn_cplc (.cv n) (syn_c1c)) (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) p0737
  have p0739 :=
    @g_breq2d (.classEq (.cv m) (syn_cplc (.cv n) (syn_c1c))) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv m)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (syn_cplc (.cv n) (syn_c1c))) C (syn_clec) p0738
  have p0740 :=
    @g_rspcev (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv m))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (syn_cplc (.cv n) (syn_c1c)))) m (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc) dv_cache_0027 dv_cache_0028 dv_cache_0062 p0739
  have p0741 :=
    @g_syl6 (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) (syn_wa (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (syn_cplc (.cv n) (syn_c1c))))) (syn_wrex m (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv m)))) p0736 p0740
  have p0742 :=
    @g_exp3a (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (.classMem (.cv n) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n))) (syn_wrex m (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv m)))) p0741
  have p0743 :=
    @g_rexlimdv (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n))) (syn_wrex m (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv m)))) n (syn_cnnc) dv_cache_0063 dv_cache_0031 p0742
  have p0744 :=
    @g_id (.classEq (.cv m) (.cv n))
  have p0745 :=
    @g_fveq2d (.classEq (.cv m) (.cv n)) (.cv m) (.cv n) (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) p0744
  have p0746 :=
    @g_breq2d (.classEq (.cv m) (.cv n)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv m)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)) C (syn_clec) p0745
  have p0747_e00_recanon : Nominal.NPrf (.imp (.objEq m n) (syn_wb (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv m))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi syn_clec syn_copab syn_cfv syn_cio syn_cuni syn_csn syn_cfrec syn_cclos1 syn_cint syn_cpprod syn_ctxp syn_cin syn_ccom syn_ccnv syn_c1st syn_cmpt syn_cvv syn_cplc syn_c1c syn_cwppstopstep syn_cif syn_wo syn_cwppgamma
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0746
  have p0747 :=
    @g_cbvrexv (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv m))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n))) m n (syn_cnnc) dv_cache_0028 dv_cache_0032 dv_cache_0064 dv_cache_0065 p0747_e00_recanon
  have p0748 :=
    @g_biimpi (syn_wrex m (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv m)))) (syn_wrex n (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) p0747
  have p0749 :=
    @g_syl6 (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wrex n (syn_cnnc) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) (syn_wrex m (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv m)))) (syn_wrex n (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) p0743 p0748
  have p0750 :=
    @g_a1i (syn_wbr (syn_ctc C) (syn_clec) C) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) hyp_wppstopgammafixedhwdndv_4
  have p0751 :=
    @g_simpr (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))
  have p0752 :=
    @g_jca (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) (syn_wbr (syn_ctc C) (syn_clec) C) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n))) p0750 p0751
  have p0753 :=
    @g_hwcardstcclndv C
  have p0754 :=
    Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0753
  have p0755 :=
    @g_hwcardssnc (syn_cvv)
  have p0756 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (syn_ctc C) p0755
  have p0757 :=
    Nominal.mp p0754 p0756
  have p0758 :=
    @g_a1i (.classMem (syn_ctc C) (syn_cncs)) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) p0757
  have p0759 :=
    @g_hwcardssnc (syn_cvv)
  have p0760 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) C p0759
  have p0761 :=
    Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0760
  have p0762 :=
    @g_a1i (.classMem C (syn_cncs)) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) p0761
  have p0763 :=
    @g_simpl (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))
  have p0764 :=
    @g_id (.classMem (.cv n) (syn_cnnc))
  have p0765 :=
    @g_simpr (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)
  have p0766 :=
    @g_iftrue (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C
  have p0767 :=
    @g_breq1d (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_cwppgamma (syn_cwppstopstep F C) C) C (syn_clec) p0766
  have p0768 :=
    @g_mpbird (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_wbr (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_clec) C) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C) p0765 p0767
  have p0769 :=
    @g_hwcardssnc (syn_cvv)
  have p0770 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) C p0769
  have p0771 :=
    Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0770
  have p0772 :=
    @g_nclecid C
  have p0773 :=
    Nominal.mp p0771 p0772
  have p0774 :=
    @g_a1i (syn_wbr C (syn_clec) C) (.neg (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C))) p0773
  have p0775 :=
    @g_iffalse (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C
  have p0776 :=
    @g_breq1d (.neg (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C))) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) C C (syn_clec) p0775
  have p0777 :=
    @g_mpbird (.neg (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C))) (syn_wbr (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_clec) C) (syn_wbr C (syn_clec) C) p0774 p0776
  have p0778 :=
    @g_pm2_61i (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_wbr (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_clec) C) p0768 p0777
  have p0779 :=
    @g_tru
  have p0780 :=
    @g_simpr syn_wtru (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C))
  have p0781 :=
    @g_simpl (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)
  have p0782 :=
    @g_syl (syn_wa syn_wtru (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C))) (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) p0780 p0781
  have p0783 :=
    @g_a1i (.classMem C (syn_chwcards (syn_cvv))) (syn_wa syn_wtru (.neg (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)))) hyp_wppstopgammafixedhwdndv_3
  have p0784 :=
    @g_ifclda syn_wtru (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C (syn_chwcards (syn_cvv)) p0782 p0783
  have p0785 :=
    Nominal.mp p0779 p0784
  have p0786 :=
    @g_pm3_2i (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_chwcards (syn_cvv))) (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs))))) p0785 p0287
  have p0787 :=
    @g_id (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
  have p0788 :=
    @g_breq1d (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) C (syn_clec) p0787
  have p0789 :=
    @g_eqidd (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (syn_cwppstopstep F C)
  have p0790 :=
    @g_id (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
  have p0791 :=
    @g_jca (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.classEq (syn_cwppstopstep F C) (syn_cwppstopstep F C)) (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) p0789 p0790
  have p0792 :=
    @g_freceq12 (syn_cwppstopstep F C) (syn_cwppstopstep F C) (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)
  have p0793 :=
    @g_syl (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (syn_wa (.classEq (syn_cwppstopstep F C) (syn_cwppstopstep F C)) (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C))) (.classEq (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C))) p0791 p0792
  have p0794 :=
    @g_fveq1d (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv r) (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) p0793
  have p0795 :=
    @g_eleq1d (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv r)) (syn_cncs) p0794
  have p0796 :=
    @g_ralbidv (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv r)) (syn_cncs)) r (syn_cnnc) dv_cache_0066 p0795
  have p0797 :=
    @g_imbi12d (.classEq (.cv p) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (syn_wbr (.cv p) (syn_clec) C) (syn_wbr (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_clec) C) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs))) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv r)) (syn_cncs))) p0788 p0796
  have p0798 :=
    @g_rspcva (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs)))) (.imp (syn_wbr (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_clec) C) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv r)) (syn_cncs)))) p (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_chwcards (syn_cvv)) dv_cache_0057 dv_cache_0019 dv_cache_0067 p0797
  have p0799 :=
    Nominal.mp p0786 p0798
  have p0800 :=
    Nominal.mp p0778 p0799
  have p0801 :=
    @g_a1i (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv r)) (syn_cncs))) (.classMem (.cv n) (syn_cnnc)) p0800
  have p0802 :=
    @g_jca (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv r)) (syn_cncs))) p0764 p0801
  have p0803 :=
    @g_id (.classEq (.cv r) (.cv n))
  have p0804 :=
    @g_fveq2d (.classEq (.cv r) (.cv n)) (.cv r) (.cv n) (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) p0803
  have p0805 :=
    @g_eleq1d (.classEq (.cv r) (.cv n)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv r)) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)) (syn_cncs) p0804
  have p0806 :=
    @g_rspcva (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv r)) (syn_cncs)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)) (syn_cncs)) r (.cv n) (syn_cnnc) dv_cache_0037 dv_cache_0038 dv_cache_0068 p0805
  have p0807 :=
    @g_syl (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv r)) (syn_cncs)))) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)) (syn_cncs)) p0802 p0806
  have p0808 :=
    @g_syl (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)) (syn_cncs)) p0763 p0807
  have p0809 :=
    @g_n_3jca (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) (.classMem (syn_ctc C) (syn_cncs)) (.classMem C (syn_cncs)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)) (syn_cncs)) p0758 p0762 p0808
  have p0810 :=
    @g_lectr (syn_ctc C) C (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n))
  have p0811 :=
    @g_syl (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) (syn_w3a (.classMem (syn_ctc C) (syn_cncs)) (.classMem C (syn_cncs)) (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)) (syn_cncs))) (.imp (syn_wa (syn_wbr (syn_ctc C) (syn_clec) C) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) p0809 p0810
  have p0812 :=
    @g_mpd (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) (syn_wa (syn_wbr (syn_ctc C) (syn_clec) C) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n))) p0752 p0811
  have p0813 :=
    @g_ex (.classMem (.cv n) (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n))) p0812
  have p0814 :=
    @g_reximia (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n))) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n))) n (syn_cnnc) p0813
  have p0815 :=
    @g_impbid1 (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wrex n (syn_cnnc) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) (syn_wrex n (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) p0749 p0814
  have p0816 :=
    @g_syl5bb (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C))) (syn_wrex n (syn_cnnc) (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wrex n (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) p0699 p0815
  have p0817 :=
    @g_elex C (syn_chwcards (syn_cvv))
  have p0818 :=
    Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0817
  have p0819 :=
    @g_wppreachfwdrexvndv C (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) n (syn_cwppstopstep F C) dv_cache_0040 dv_cache_0059 dv_cache_0023 p0047 p0694 p0170 p0818
  have p0820 :=
    @g_bicomi (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_cwppreach (syn_cwppstopstep F C) C)) (syn_wrex n (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) p0819
  have p0821 :=
    @g_syl6bb (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C))) (syn_wrex n (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.cv n)))) (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_cwppreach (syn_cwppstopstep F C) C)) p0816 p0820
  have p0822 :=
    @g_iftrue (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C
  have p0823 :=
    @g_eqcomd (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_cwppgamma (syn_cwppstopstep F C) C) p0822
  have p0824 :=
    @g_id (.classEq (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
  have p0825 :=
    @g_eleq1d (.classEq (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C)) p0824
  have p0826 :=
    @g_id (.classEq (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
  have p0827 :=
    @g_eleq1d (.classEq (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_cwppreach (syn_cwppstopstep F C) C) p0826
  have p0828 :=
    @g_bibi12d (.classEq (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C))) (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C))) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppreach (syn_cwppstopstep F C) C)) (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_cwppreach (syn_cwppstopstep F C) C)) p0825 p0827
  have p0829 :=
    @g_syl (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (.classEq (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C)) (syn_wb (syn_wb (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C))) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppreach (syn_cwppstopstep F C) C))) (syn_wb (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C))) (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_cwppreach (syn_cwppstopstep F C) C)))) p0823 p0828
  have p0830 :=
    @g_syl5ibrcom (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wb (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C))) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppreach (syn_cwppstopstep F C) C))) (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_wb (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C))) (.classMem (syn_cif (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_cwppgamma (syn_cwppstopstep F C) C) C) (syn_cwppreach (syn_cwppstopstep F C) C))) p0821 p0829
  have p0831 :=
    @g_mpi (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (syn_wb (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C))) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppreach (syn_cwppstopstep F C) C))) p0664 p0830
  have p0832 :=
    @g_mpbiri (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C))) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppreach (syn_cwppstopstep F C) C)) p0637 p0831
  have p0833 :=
    @g_jca (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (syn_ctc C))) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C))) p0626 p0832
  have p0834 :=
    @g_elwppcand (syn_ctc C) (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppstopstep F C)
  have p0835 :=
    @g_sylibr (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (syn_ctc C))) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C)))) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C))) p0833 p0834
  have p0836 :=
    @g_id (.classEq (.cv k) (syn_cwppgamma (syn_cwppstopstep F C) C))
  have p0837 :=
    @g_breq2d (.classEq (.cv k) (syn_cwppgamma (syn_cwppstopstep F C) C)) (.cv k) (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) p0836
  have p0838 :=
    @g_rspcv (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (.cv k)) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (syn_cwppgamma (syn_cwppstopstep F C) C)) k (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C)) dv_cache_0069 dv_cache_0070 dv_cache_0071 p0837
  have p0839 :=
    @g_syl (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C))) (.imp (syn_wral k (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C)) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (.cv k))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (syn_cwppgamma (syn_cwppstopstep F C) C))) p0835 p0838
  have p0840 :=
    @g_mpi (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wral k (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C)) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (.cv k))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (syn_cwppgamma (syn_cwppstopstep F C) C)) p0413 p0839
  have p0841 :=
    @g_jca (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (syn_cwppgamma (syn_cwppstopstep F C) C)) p0404 p0840
  have p0842 :=
    @g_elex (syn_cwppstopstep F C) (syn_cfuns)
  have p0843 :=
    Nominal.mp p0047 p0842
  have p0844 :=
    @g_pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cvv)) (.classMem C (syn_chwcards (syn_cvv))) p0843 hyp_wppstopgammafixedhwdndv_3
  have p0845 :=
    @g_wppgammaminhwndv C k (syn_cwppstopstep F C) dv_cache_0015 dv_cache_0016
  have p0846 :=
    Nominal.mp p0844 p0845
  have p0847 :=
    @g_simpl (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppcand (syn_cwppstopstep F C) C)) (syn_wral k (syn_cwppcand (syn_cwppstopstep F C) C) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (.cv k)))
  have p0848 :=
    Nominal.mp p0846 p0847
  have p0849 :=
    @g_elwppcand C (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppstopstep F C)
  have p0850 :=
    @g_mpbi (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppcand (syn_cwppstopstep F C) C)) (syn_wa (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppreach (syn_cwppstopstep F C) C))) p0848 p0849
  have p0851 :=
    @g_simpl (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppreach (syn_cwppstopstep F C) C))
  have p0852 :=
    Nominal.mp p0850 p0851
  have p0853 :=
    @g_simpl (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)
  have p0854 :=
    Nominal.mp p0852 p0853
  have p0855 :=
    @g_hwcardssnc (syn_cvv)
  have p0856 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (syn_cwppgamma (syn_cwppstopstep F C) C) p0855
  have p0857 :=
    Nominal.mp p0854 p0856
  have p0858 :=
    @g_elex (syn_cwppstopstep F C) (syn_cfuns)
  have p0859 :=
    Nominal.mp p0047 p0858
  have p0860 :=
    @g_hwcardstcclndv C
  have p0861 :=
    Nominal.mp hyp_wppstopgammafixedhwdndv_3 p0860
  have p0862 :=
    @g_pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cvv)) (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))) p0859 p0861
  have p0863 :=
    @g_wppgammaminhwndv (syn_ctc C) k (syn_cwppstopstep F C) dv_cache_0017 dv_cache_0016
  have p0864 :=
    Nominal.mp p0862 p0863
  have p0865 :=
    @g_simpl (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C))) (syn_wral k (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C)) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (.cv k)))
  have p0866 :=
    Nominal.mp p0864 p0865
  have p0867 :=
    @g_elwppcand (syn_ctc C) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppstopstep F C)
  have p0868 :=
    @g_mpbi (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppcand (syn_cwppstopstep F C) (syn_ctc C))) (syn_wa (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (syn_ctc C))) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C)))) p0866 p0867
  have p0869 :=
    @g_simpl (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (syn_ctc C))) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppreach (syn_cwppstopstep F C) (syn_ctc C)))
  have p0870 :=
    Nominal.mp p0868 p0869
  have p0871 :=
    @g_simpl (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (syn_ctc C))
  have p0872 :=
    Nominal.mp p0870 p0871
  have p0873 :=
    @g_hwcardssnc (syn_cvv)
  have p0874 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) p0873
  have p0875 :=
    Nominal.mp p0872 p0874
  have p0876 :=
    @g_pm3_2i (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cncs)) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cncs)) p0857 p0875
  have p0877 :=
    @g_sbth (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))
  have p0878 :=
    Nominal.mp p0876 p0877
  have p0879 :=
    @g_syl (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_wa (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_clec) (syn_cwppgamma (syn_cwppstopstep F C) C))) (.classEq (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))) p0841 p0878
  have p0880 :=
    @g_eqcomd (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) p0879
  have p0881 :=
    @g_syl5eq (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C)) (syn_cwppgamma (syn_cwppstopstep F C) C) p0046 p0880
  have p0882 :=
    @g_wppstopstepfunsndv C F hyp_wppstopgammafixedhwdndv_1 hyp_wppstopgammafixedhwdndv_2
  have p0883 :=
    @g_elex (syn_cwppstopstep F C) (syn_cfuns)
  have p0884 :=
    Nominal.mp p0882 p0883
  have p0885 :=
    @g_pm3_2i (.classMem (syn_cwppstopstep F C) (syn_cvv)) (.classMem C (syn_chwcards (syn_cvv))) p0884 hyp_wppstopgammafixedhwdndv_3
  have p0886 :=
    @g_wppgammaminhwndv C k (syn_cwppstopstep F C) dv_cache_0015 dv_cache_0016
  have p0887 :=
    Nominal.mp p0885 p0886
  have p0888 :=
    @g_simpl (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppcand (syn_cwppstopstep F C) C)) (syn_wral k (syn_cwppcand (syn_cwppstopstep F C) C) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) (.cv k)))
  have p0889 :=
    Nominal.mp p0887 p0888
  have p0890 :=
    @g_elwppcand C (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppstopstep F C)
  have p0891 :=
    @g_mpbi (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppcand (syn_cwppstopstep F C) C)) (syn_wa (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppreach (syn_cwppstopstep F C) C))) p0889 p0890
  have p0892 :=
    @g_simpl (syn_wa (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_cwppreach (syn_cwppstopstep F C) C))
  have p0893 :=
    Nominal.mp p0891 p0892
  have p0894 :=
    @g_simpl (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) (syn_wbr (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_clec) C)
  have p0895 :=
    Nominal.mp p0893 p0894
  have p0896 :=
    @g_jctil (syn_wral y (syn_cdm (syn_cwppstopstep F C)) (.imp (syn_wbr (syn_ctc C) (syn_clec) (.cv y)) (syn_wbr C (syn_clec) (syn_cfv (syn_cwppstopstep F C) (.cv y))))) (.classEq (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_cwppgamma (syn_cwppstopstep F C) C)) (.classMem (syn_cwppgamma (syn_cwppstopstep F C) C) (syn_chwcards (syn_cvv))) p0881 p0895
  exact p0896

#print axioms g_wppstopgammafixedhwdndv

end NFChoice.DirectNominalPrf.WPPReplay
