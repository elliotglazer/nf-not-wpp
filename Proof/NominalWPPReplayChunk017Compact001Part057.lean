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
import NominalWPPReplayChunk017Compact001Part056

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

noncomputable def g_wppcandtchwboundedimagebindv
    (x : Var) (C : Class) (k : Var) (F : Class) (G : Class) (r : Var) (p : Var) (d : Var) (dv_C_d : d ∉ C.fv) (dv_C_p : p ∉ C.fv) (dv_C_r : r ∉ C.fv) (dv_C_x : x ∉ C.fv) (dv_F_d : d ∉ F.fv) (dv_F_p : p ∉ F.fv) (dv_F_r : r ∉ F.fv) (dv_F_x : x ∉ F.fv) (dv_G_d : d ∉ G.fv) (dv_G_p : p ∉ G.fv) (dv_G_r : r ∉ G.fv) (dv_G_x : x ∉ G.fv) (dv_d_k : d ≠ k) (dv_d_p : d ≠ p) (dv_d_r : d ≠ r) (dv_d_x : d ≠ x) (dv_k_p : k ≠ p) (dv_k_r : k ≠ r) (dv_k_x : k ≠ x) (dv_p_r : p ≠ r) (dv_p_x : p ≠ x) (dv_r_x : r ≠ x) (hyp_wppcandtchwboundedimagebindv_1 : Nominal.NPrf (.classMem F (syn_cfuns))) (hyp_wppcandtchwboundedimagebindv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F))) (hyp_wppcandtchwboundedimagebindv_3 : Nominal.NPrf (.classMem G (syn_cfuns))) (hyp_wppcandtchwboundedimagebindv_4 : Nominal.NPrf (syn_wss (syn_crn G) (syn_cdm G))) (hyp_wppcandtchwboundedimagebindv_5 : Nominal.NPrf (syn_wral x (syn_cdm F) (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv G (syn_ctc (.cv x)))))) (hyp_wppcandtchwboundedimagebindv_6 : Nominal.NPrf (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wa (.classMem (.cv p) (syn_cdm F)) (.classMem (syn_ctc (.cv p)) (syn_cdm G)))))) (hyp_wppcandtchwboundedimagebindv_7 : Nominal.NPrf (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F (.cv p)) (.cv r)) (syn_cncs)))))) (hyp_wppcandtchwboundedimagebindv_8 : Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf (syn_wb (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wex d (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ C.fv ∪ ({k} : Finset Var) ∪ F.fv ∪ G.fv ∪ ({r} : Finset Var) ∪ ({p} : Finset Var) ∪ ({d} : Finset Var)
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_ne_x : q ≠ x := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))))
  have fresh_x_ne_q : x ≠ q :=
    Ne.symm fresh_q_ne_x
  have fresh_q_not_C : q ∉ C.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))))
  have fresh_q_ne_k : q ≠ k := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_k_ne_q : k ≠ q :=
    Ne.symm fresh_q_ne_k
  have fresh_q_not_F : q ∉ F.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_q_not_G : q ∉ G.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_q_ne_r : q ≠ r := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_r_ne_q : r ≠ q :=
    Ne.symm fresh_q_ne_r
  have fresh_q_ne_p : q ≠ p := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_p_ne_q : p ≠ q :=
    Ne.symm fresh_q_ne_p
  have fresh_q_ne_d : q ≠ d := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_d_ne_q : d ≠ q :=
    Ne.symm fresh_q_ne_d
  have dv_cache_0001 : q ∉ ((Class.cv k)).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ (C).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : r ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_C_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : p ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : r ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ (F).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_F_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : p ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_G_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : r ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_G_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_G_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : q ≠ p := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show q ≠ p from (by exact fresh_q_ne_p))
  have dv_cache_0012 : q ≠ r := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show q ≠ r from (by exact fresh_q_ne_r))
  have dv_cache_0013 : q ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show q ≠ x from (by exact fresh_q_ne_x))
  have dv_cache_0014 : p ≠ r := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show p ≠ r from (by exact dv_p_r))
  have dv_cache_0015 : p ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show p ≠ x from (by exact dv_p_x))
  have dv_cache_0016 : r ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show r ≠ x from (by exact dv_r_x))
  have dv_cache_0017 : d ∉ ((Class.cv q)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : d ∉ ((syn_wa (.classMem (.cv q) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv q))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_q, dv_C_d, dv_F_d, dv_d_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : q ∉ ((syn_wex d (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_d, fresh_q_not_C, fresh_q_not_F, fresh_q_ne_k, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : q ∉ ((Wff.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_k, fresh_q_not_C, fresh_q_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : d ≠ p := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show d ≠ p from (by exact dv_d_p))
  have dv_cache_0022 : d ≠ r := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show d ≠ r from (by exact dv_d_r))
  have dv_cache_0023 : d ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show d ≠ x from (by exact dv_d_x))
  have dv_cache_0024 : d ∉ ((Wff.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_d_k, dv_C_d, dv_G_d, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elwppcand (syn_ctc C) (.cv k) G
  have p0001 :=
    @g_biimpi (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))) (.classMem (.cv k) (syn_cwppreach G (syn_ctc C)))) p0000
  have p0002 :=
    @g_simpl (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))) (.classMem (.cv k) (syn_cwppreach G (syn_ctc C)))
  have p0003 :=
    @g_syl (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))) (.classMem (.cv k) (syn_cwppreach G (syn_ctc C)))) (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))) p0001 p0002
  have p0004 :=
    @g_simpl (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))
  have p0005 :=
    @g_syl (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))) (.classMem (.cv k) (syn_chwcards (syn_cvv))) p0003 p0004
  have p0006 :=
    @g_hwcardssnc (syn_cvv)
  have p0007 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (.cv k) p0006
  have p0008 :=
    @g_syl (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (.classMem (.cv k) (syn_chwcards (syn_cvv))) (.classMem (.cv k) (syn_cncs)) p0005 p0007
  have p0009 :=
    @g_hwcardssnc (syn_cvv)
  have p0010 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) C p0009
  have p0011 :=
    Nominal.mp hyp_wppcandtchwboundedimagebindv_8 p0010
  have p0012 :=
    @g_a1i (.classMem C (syn_cncs)) (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) p0011
  have p0013 :=
    @g_elwppcand (syn_ctc C) (.cv k) G
  have p0014 :=
    @g_biimpi (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))) (.classMem (.cv k) (syn_cwppreach G (syn_ctc C)))) p0013
  have p0015 :=
    @g_simpl (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))) (.classMem (.cv k) (syn_cwppreach G (syn_ctc C)))
  have p0016 :=
    @g_syl (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))) (.classMem (.cv k) (syn_cwppreach G (syn_ctc C)))) (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))) p0014 p0015
  have p0017 :=
    @g_simpr (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))
  have p0018 :=
    @g_syl (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C)) p0016 p0017
  have p0019 :=
    @g_n_3jca (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (.classMem (.cv k) (syn_cncs)) (.classMem C (syn_cncs)) (syn_wbr (.cv k) (syn_clec) (syn_ctc C)) p0008 p0012 p0018
  have p0020 :=
    @g_letc (.cv k) C q dv_cache_0001
  have p0021 :=
    @g_syl (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_w3a (.classMem (.cv k) (syn_cncs)) (.classMem C (syn_cncs)) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))) (syn_wrex q (syn_cncs) (.classEq (.cv k) (syn_ctc (.cv q)))) p0019 p0020
  have p0022 :=
    @g_simpr (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))
  have p0023 :=
    @g_simpl (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))
  have p0024 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))) (.classMem (.cv q) (syn_cncs)) p0022 p0023
  have p0025 :=
    @g_a1i (.classMem C (syn_chwcards (syn_cvv))) (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) hyp_wppcandtchwboundedimagebindv_8
  have p0026 :=
    @g_jca (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (.classMem (.cv q) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))) p0024 p0025
  have p0027 :=
    @g_simpl (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))
  have p0028 :=
    @g_elwppcand (syn_ctc C) (.cv k) G
  have p0029 :=
    @g_biimpi (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))) (.classMem (.cv k) (syn_cwppreach G (syn_ctc C)))) p0028
  have p0030 :=
    @g_simpl (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))) (.classMem (.cv k) (syn_cwppreach G (syn_ctc C)))
  have p0031 :=
    @g_syl (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))) (.classMem (.cv k) (syn_cwppreach G (syn_ctc C)))) (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))) p0029 p0030
  have p0032 :=
    @g_simpr (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))
  have p0033 :=
    @g_syl (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C)) p0031 p0032
  have p0034 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C)) p0027 p0033
  have p0035 :=
    @g_simpr (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))
  have p0036 :=
    @g_simpr (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))
  have p0037 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))) (.classEq (.cv k) (syn_ctc (.cv q))) p0035 p0036
  have p0038 :=
    @g_id (.classEq (.cv k) (syn_ctc (.cv q)))
  have p0039 :=
    @g_breq1d (.classEq (.cv k) (syn_ctc (.cv q))) (.cv k) (syn_ctc (.cv q)) (syn_ctc C) (syn_clec) p0038
  have p0040 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (.classEq (.cv k) (syn_ctc (.cv q))) (syn_wb (syn_wbr (.cv k) (syn_clec) (syn_ctc C)) (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc C))) p0037 p0039
  have p0041 :=
    @g_mpbid (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C)) (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc C)) p0034 p0040
  have p0042 :=
    @g_simpr (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))
  have p0043 :=
    @g_simpl (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))
  have p0044 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))) (.classMem (.cv q) (syn_cncs)) p0042 p0043
  have p0045 :=
    @g_hwcardssnc (syn_cvv)
  have p0046 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) C p0045
  have p0047 :=
    Nominal.mp hyp_wppcandtchwboundedimagebindv_8 p0046
  have p0048 :=
    @g_a1i (.classMem C (syn_cncs)) (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) p0047
  have p0049 :=
    @g_jca (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (.classMem (.cv q) (syn_cncs)) (.classMem C (syn_cncs)) p0044 p0048
  have p0050 :=
    @g_tlecg (.cv q) C
  have p0051 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classMem C (syn_cncs))) (syn_wb (syn_wbr (.cv q) (syn_clec) C) (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc C))) p0049 p0050
  have p0052 :=
    @g_mpbird (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (syn_wbr (.cv q) (syn_clec) C) (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc C)) p0041 p0051
  have p0053 :=
    @g_jca (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv q) (syn_clec) C) p0026 p0052
  have p0054 :=
    @g_hwcardsdownltcndv C q
  have p0055 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (syn_wa (syn_wa (.classMem (.cv q) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv q) (syn_clec) C)) (.classMem (.cv q) (syn_chwcards (syn_cvv))) p0053 p0054
  have p0056 :=
    @g_simpl (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))
  have p0057 :=
    @g_elwppcand (syn_ctc C) (.cv k) G
  have p0058 :=
    @g_biimpi (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))) (.classMem (.cv k) (syn_cwppreach G (syn_ctc C)))) p0057
  have p0059 :=
    @g_simpl (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))) (.classMem (.cv k) (syn_cwppreach G (syn_ctc C)))
  have p0060 :=
    @g_syl (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))) (.classMem (.cv k) (syn_cwppreach G (syn_ctc C)))) (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))) p0058 p0059
  have p0061 :=
    @g_simpr (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))
  have p0062 :=
    @g_syl (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C)) p0060 p0061
  have p0063 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C)) p0056 p0062
  have p0064 :=
    @g_simpr (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))
  have p0065 :=
    @g_simpr (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))
  have p0066 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))) (.classEq (.cv k) (syn_ctc (.cv q))) p0064 p0065
  have p0067 :=
    @g_id (.classEq (.cv k) (syn_ctc (.cv q)))
  have p0068 :=
    @g_breq1d (.classEq (.cv k) (syn_ctc (.cv q))) (.cv k) (syn_ctc (.cv q)) (syn_ctc C) (syn_clec) p0067
  have p0069 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (.classEq (.cv k) (syn_ctc (.cv q))) (syn_wb (syn_wbr (.cv k) (syn_clec) (syn_ctc C)) (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc C))) p0066 p0068
  have p0070 :=
    @g_mpbid (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C)) (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc C)) p0063 p0069
  have p0071 :=
    @g_simpr (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))
  have p0072 :=
    @g_simpl (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))
  have p0073 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))) (.classMem (.cv q) (syn_cncs)) p0071 p0072
  have p0074 :=
    @g_hwcardssnc (syn_cvv)
  have p0075 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) C p0074
  have p0076 :=
    Nominal.mp hyp_wppcandtchwboundedimagebindv_8 p0075
  have p0077 :=
    @g_a1i (.classMem C (syn_cncs)) (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) p0076
  have p0078 :=
    @g_jca (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (.classMem (.cv q) (syn_cncs)) (.classMem C (syn_cncs)) p0073 p0077
  have p0079 :=
    @g_tlecg (.cv q) C
  have p0080 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classMem C (syn_cncs))) (syn_wb (syn_wbr (.cv q) (syn_clec) C) (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc C))) p0078 p0079
  have p0081 :=
    @g_mpbird (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (syn_wbr (.cv q) (syn_clec) C) (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc C)) p0070 p0080
  have p0082 :=
    @g_jca (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (.classMem (.cv q) (syn_chwcards (syn_cvv))) (syn_wbr (.cv q) (syn_clec) C) p0055 p0081
  have p0083 :=
    @g_simpl (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))
  have p0084 :=
    @g_elwppcand (syn_ctc C) (.cv k) G
  have p0085 :=
    @g_biimpi (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))) (.classMem (.cv k) (syn_cwppreach G (syn_ctc C)))) p0084
  have p0086 :=
    @g_simpr (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))) (.classMem (.cv k) (syn_cwppreach G (syn_ctc C)))
  have p0087 :=
    @g_syl (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))) (.classMem (.cv k) (syn_cwppreach G (syn_ctc C)))) (.classMem (.cv k) (syn_cwppreach G (syn_ctc C))) p0085 p0086
  have p0088 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (.classMem (.cv k) (syn_cwppreach G (syn_ctc C))) p0083 p0087
  have p0089 :=
    @g_simpr (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))
  have p0090 :=
    @g_simpr (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))
  have p0091 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))) (.classEq (.cv k) (syn_ctc (.cv q))) p0089 p0090
  have p0092 :=
    @g_id (.classEq (.cv k) (syn_ctc (.cv q)))
  have p0093 :=
    @g_eleq1d (.classEq (.cv k) (syn_ctc (.cv q))) (.cv k) (syn_ctc (.cv q)) (syn_cwppreach G (syn_ctc C)) p0092
  have p0094 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (.classEq (.cv k) (syn_ctc (.cv q))) (syn_wb (.classMem (.cv k) (syn_cwppreach G (syn_ctc C))) (.classMem (syn_ctc (.cv q)) (syn_cwppreach G (syn_ctc C)))) p0091 p0093
  have p0095 :=
    @g_mpbid (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (.classMem (.cv k) (syn_cwppreach G (syn_ctc C))) (.classMem (syn_ctc (.cv q)) (syn_cwppreach G (syn_ctc C))) p0088 p0094
  have p0096 :=
    @g_simpr (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))
  have p0097 :=
    @g_simpl (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))
  have p0098 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))) (.classMem (.cv q) (syn_cncs)) p0096 p0097
  have p0099 :=
    @g_a1i (.classMem C (syn_chwcards (syn_cvv))) (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) hyp_wppcandtchwboundedimagebindv_8
  have p0100 :=
    @g_jca (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (.classMem (.cv q) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))) p0098 p0099
  have p0101 :=
    @g_simpl (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))
  have p0102 :=
    @g_elwppcand (syn_ctc C) (.cv k) G
  have p0103 :=
    @g_biimpi (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))) (.classMem (.cv k) (syn_cwppreach G (syn_ctc C)))) p0102
  have p0104 :=
    @g_simpl (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))) (.classMem (.cv k) (syn_cwppreach G (syn_ctc C)))
  have p0105 :=
    @g_syl (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))) (.classMem (.cv k) (syn_cwppreach G (syn_ctc C)))) (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))) p0103 p0104
  have p0106 :=
    @g_simpr (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))
  have p0107 :=
    @g_syl (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C)) p0105 p0106
  have p0108 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C)) p0101 p0107
  have p0109 :=
    @g_simpr (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))
  have p0110 :=
    @g_simpr (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))
  have p0111 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))) (.classEq (.cv k) (syn_ctc (.cv q))) p0109 p0110
  have p0112 :=
    @g_id (.classEq (.cv k) (syn_ctc (.cv q)))
  have p0113 :=
    @g_breq1d (.classEq (.cv k) (syn_ctc (.cv q))) (.cv k) (syn_ctc (.cv q)) (syn_ctc C) (syn_clec) p0112
  have p0114 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (.classEq (.cv k) (syn_ctc (.cv q))) (syn_wb (syn_wbr (.cv k) (syn_clec) (syn_ctc C)) (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc C))) p0111 p0113
  have p0115 :=
    @g_mpbid (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C)) (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc C)) p0108 p0114
  have p0116 :=
    @g_simpr (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))
  have p0117 :=
    @g_simpl (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))
  have p0118 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))) (.classMem (.cv q) (syn_cncs)) p0116 p0117
  have p0119 :=
    @g_hwcardssnc (syn_cvv)
  have p0120 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) C p0119
  have p0121 :=
    Nominal.mp hyp_wppcandtchwboundedimagebindv_8 p0120
  have p0122 :=
    @g_a1i (.classMem C (syn_cncs)) (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) p0121
  have p0123 :=
    @g_jca (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (.classMem (.cv q) (syn_cncs)) (.classMem C (syn_cncs)) p0118 p0122
  have p0124 :=
    @g_tlecg (.cv q) C
  have p0125 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classMem C (syn_cncs))) (syn_wb (syn_wbr (.cv q) (syn_clec) C) (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc C))) p0123 p0124
  have p0126 :=
    @g_mpbird (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (syn_wbr (.cv q) (syn_clec) C) (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc C)) p0115 p0125
  have p0127 :=
    @g_jca (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv q) (syn_clec) C) p0100 p0126
  have p0128 :=
    @g_hwcardsdownltcndv C q
  have p0129 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (syn_wa (syn_wa (.classMem (.cv q) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))) (syn_wbr (.cv q) (syn_clec) C)) (.classMem (.cv q) (syn_chwcards (syn_cvv))) p0127 p0128
  have p0130 :=
    @g_simpl (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))
  have p0131 :=
    @g_elwppcand (syn_ctc C) (.cv k) G
  have p0132 :=
    @g_biimpi (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))) (.classMem (.cv k) (syn_cwppreach G (syn_ctc C)))) p0131
  have p0133 :=
    @g_simpl (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))) (.classMem (.cv k) (syn_cwppreach G (syn_ctc C)))
  have p0134 :=
    @g_syl (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))) (.classMem (.cv k) (syn_cwppreach G (syn_ctc C)))) (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))) p0132 p0133
  have p0135 :=
    @g_simpr (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))
  have p0136 :=
    @g_syl (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C)) p0134 p0135
  have p0137 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C)) p0130 p0136
  have p0138 :=
    @g_simpr (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))
  have p0139 :=
    @g_simpr (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))
  have p0140 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))) (.classEq (.cv k) (syn_ctc (.cv q))) p0138 p0139
  have p0141 :=
    @g_id (.classEq (.cv k) (syn_ctc (.cv q)))
  have p0142 :=
    @g_breq1d (.classEq (.cv k) (syn_ctc (.cv q))) (.cv k) (syn_ctc (.cv q)) (syn_ctc C) (syn_clec) p0141
  have p0143 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (.classEq (.cv k) (syn_ctc (.cv q))) (syn_wb (syn_wbr (.cv k) (syn_clec) (syn_ctc C)) (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc C))) p0140 p0142
  have p0144 :=
    @g_mpbid (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (syn_wbr (.cv k) (syn_clec) (syn_ctc C)) (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc C)) p0137 p0143
  have p0145 :=
    @g_simpr (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))
  have p0146 :=
    @g_simpl (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))
  have p0147 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))) (.classMem (.cv q) (syn_cncs)) p0145 p0146
  have p0148 :=
    @g_hwcardssnc (syn_cvv)
  have p0149 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) C p0148
  have p0150 :=
    Nominal.mp hyp_wppcandtchwboundedimagebindv_8 p0149
  have p0151 :=
    @g_a1i (.classMem C (syn_cncs)) (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) p0150
  have p0152 :=
    @g_jca (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (.classMem (.cv q) (syn_cncs)) (.classMem C (syn_cncs)) p0147 p0151
  have p0153 :=
    @g_tlecg (.cv q) C
  have p0154 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classMem C (syn_cncs))) (syn_wb (syn_wbr (.cv q) (syn_clec) C) (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc C))) p0152 p0153
  have p0155 :=
    @g_mpbird (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (syn_wbr (.cv q) (syn_clec) C) (syn_wbr (syn_ctc (.cv q)) (syn_clec) (syn_ctc C)) p0144 p0154
  have p0156 :=
    @g_jca (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (.classMem (.cv q) (syn_chwcards (syn_cvv))) (syn_wbr (.cv q) (syn_clec) C) p0129 p0155
  have p0157 :=
    @g_wppreachtchwboundedndv x C F G r p q dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 hyp_wppcandtchwboundedimagebindv_1 hyp_wppcandtchwboundedimagebindv_2 hyp_wppcandtchwboundedimagebindv_3 hyp_wppcandtchwboundedimagebindv_4 hyp_wppcandtchwboundedimagebindv_5 hyp_wppcandtchwboundedimagebindv_6 hyp_wppcandtchwboundedimagebindv_7 hyp_wppcandtchwboundedimagebindv_8
  have p0158 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (syn_wa (.classMem (.cv q) (syn_chwcards (syn_cvv))) (syn_wbr (.cv q) (syn_clec) C)) (syn_wb (.classMem (.cv q) (syn_cwppreach F C)) (.classMem (syn_ctc (.cv q)) (syn_cwppreach G (syn_ctc C)))) p0156 p0157
  have p0159 :=
    @g_mpbird (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (.classMem (.cv q) (syn_cwppreach F C)) (.classMem (syn_ctc (.cv q)) (syn_cwppreach G (syn_ctc C))) p0095 p0158
  have p0160 :=
    @g_jca (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (syn_wa (.classMem (.cv q) (syn_chwcards (syn_cvv))) (syn_wbr (.cv q) (syn_clec) C)) (.classMem (.cv q) (syn_cwppreach F C)) p0082 p0159
  have p0161 :=
    @g_elwppcand C (.cv q) F
  have p0162 :=
    @g_biimpri (.classMem (.cv q) (syn_cwppcand F C)) (syn_wa (syn_wa (.classMem (.cv q) (syn_chwcards (syn_cvv))) (syn_wbr (.cv q) (syn_clec) C)) (.classMem (.cv q) (syn_cwppreach F C))) p0161
  have p0163 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (syn_wa (syn_wa (.classMem (.cv q) (syn_chwcards (syn_cvv))) (syn_wbr (.cv q) (syn_clec) C)) (.classMem (.cv q) (syn_cwppreach F C))) (.classMem (.cv q) (syn_cwppcand F C)) p0160 p0162
  have p0164 :=
    @g_simpr (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))
  have p0165 :=
    @g_simpr (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))
  have p0166 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q)))) (.classEq (.cv k) (syn_ctc (.cv q))) p0164 p0165
  have p0167 :=
    @g_jca (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (.classMem (.cv q) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv q))) p0163 p0166
  have p0168 :=
    @g_vex q
  have p0169 :=
    @g_id (.classEq (.cv d) (.cv q))
  have p0170 :=
    @g_eleq1d (.classEq (.cv d) (.cv q)) (.cv d) (.cv q) (syn_cwppcand F C) p0169
  have p0171 :=
    @g_tceq (.cv d) (.cv q)
  have p0172 :=
    @g_eqeq2d (.classEq (.cv d) (.cv q)) (syn_ctc (.cv d)) (syn_ctc (.cv q)) (.cv k) p0171
  have p0173 :=
    @g_anbi12d (.classEq (.cv d) (.cv q)) (.classMem (.cv d) (syn_cwppcand F C)) (.classMem (.cv q) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))) (.classEq (.cv k) (syn_ctc (.cv q))) p0170 p0172
  have p0174 :=
    @g_spcev (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (syn_wa (.classMem (.cv q) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv q)))) d (.cv q) dv_cache_0017 dv_cache_0018 p0168 p0173
  have p0175 :=
    @g_syl (syn_wa (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wa (.classMem (.cv q) (syn_cncs)) (.classEq (.cv k) (syn_ctc (.cv q))))) (syn_wa (.classMem (.cv q) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv q)))) (syn_wex d (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))))) p0167 p0174
  have p0176 :=
    @g_rexlimddv (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (.classEq (.cv k) (syn_ctc (.cv q))) (syn_wex d (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))))) q (syn_cncs) dv_cache_0019 dv_cache_0020 p0021 p0175
  have p0177 :=
    @g_simpl (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))
  have p0178 :=
    @g_elwppcand C (.cv d) F
  have p0179 :=
    @g_biimpi (.classMem (.cv d) (syn_cwppcand F C)) (syn_wa (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cwppreach F C))) p0178
  have p0180 :=
    @g_syl (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (.classMem (.cv d) (syn_cwppcand F C)) (syn_wa (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cwppreach F C))) p0177 p0179
  have p0181 :=
    @g_simpl (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cwppreach F C))
  have p0182 :=
    @g_syl (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (syn_wa (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cwppreach F C))) (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) p0180 p0181
  have p0183 :=
    @g_simpl (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)
  have p0184 :=
    @g_syl (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_chwcards (syn_cvv))) p0182 p0183
  have p0185 :=
    @g_hwcardstcclndv (.cv d)
  have p0186 :=
    @g_syl (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (.classMem (.cv d) (syn_chwcards (syn_cvv))) (.classMem (syn_ctc (.cv d)) (syn_chwcards (syn_cvv))) p0184 p0185
  have p0187 :=
    @g_simpl (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))
  have p0188 :=
    @g_elwppcand C (.cv d) F
  have p0189 :=
    @g_biimpi (.classMem (.cv d) (syn_cwppcand F C)) (syn_wa (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cwppreach F C))) p0188
  have p0190 :=
    @g_syl (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (.classMem (.cv d) (syn_cwppcand F C)) (syn_wa (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cwppreach F C))) p0187 p0189
  have p0191 :=
    @g_simpl (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cwppreach F C))
  have p0192 :=
    @g_syl (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (syn_wa (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cwppreach F C))) (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) p0190 p0191
  have p0193 :=
    @g_simpr (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)
  have p0194 :=
    @g_syl (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wbr (.cv d) (syn_clec) C) p0192 p0193
  have p0195 :=
    @g_simpl (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))
  have p0196 :=
    @g_elwppcand C (.cv d) F
  have p0197 :=
    @g_biimpi (.classMem (.cv d) (syn_cwppcand F C)) (syn_wa (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cwppreach F C))) p0196
  have p0198 :=
    @g_syl (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (.classMem (.cv d) (syn_cwppcand F C)) (syn_wa (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cwppreach F C))) p0195 p0197
  have p0199 :=
    @g_simpl (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cwppreach F C))
  have p0200 :=
    @g_syl (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (syn_wa (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cwppreach F C))) (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) p0198 p0199
  have p0201 :=
    @g_simpl (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)
  have p0202 :=
    @g_syl (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_chwcards (syn_cvv))) p0200 p0201
  have p0203 :=
    @g_hwcardssnc (syn_cvv)
  have p0204 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (.cv d) p0203
  have p0205 :=
    @g_syl (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (.classMem (.cv d) (syn_chwcards (syn_cvv))) (.classMem (.cv d) (syn_cncs)) p0202 p0204
  have p0206 :=
    @g_hwcardssnc (syn_cvv)
  have p0207 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) C p0206
  have p0208 :=
    Nominal.mp hyp_wppcandtchwboundedimagebindv_8 p0207
  have p0209 :=
    @g_a1i (.classMem C (syn_cncs)) (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) p0208
  have p0210 :=
    @g_jca (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_cncs)) p0205 p0209
  have p0211 :=
    @g_tlecg (.cv d) C
  have p0212 :=
    @g_syl (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_cncs))) (syn_wb (syn_wbr (.cv d) (syn_clec) C) (syn_wbr (syn_ctc (.cv d)) (syn_clec) (syn_ctc C))) p0210 p0211
  have p0213 :=
    @g_mpbid (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (syn_wbr (.cv d) (syn_clec) C) (syn_wbr (syn_ctc (.cv d)) (syn_clec) (syn_ctc C)) p0194 p0212
  have p0214 :=
    @g_jca (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (.classMem (syn_ctc (.cv d)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (.cv d)) (syn_clec) (syn_ctc C)) p0186 p0213
  have p0215 :=
    @g_simpl (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))
  have p0216 :=
    @g_elwppcand C (.cv d) F
  have p0217 :=
    @g_biimpi (.classMem (.cv d) (syn_cwppcand F C)) (syn_wa (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cwppreach F C))) p0216
  have p0218 :=
    @g_syl (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (.classMem (.cv d) (syn_cwppcand F C)) (syn_wa (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cwppreach F C))) p0215 p0217
  have p0219 :=
    @g_simpr (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cwppreach F C))
  have p0220 :=
    @g_syl (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (syn_wa (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cwppreach F C))) (.classMem (.cv d) (syn_cwppreach F C)) p0218 p0219
  have p0221 :=
    @g_simpl (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))
  have p0222 :=
    @g_elwppcand C (.cv d) F
  have p0223 :=
    @g_biimpi (.classMem (.cv d) (syn_cwppcand F C)) (syn_wa (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cwppreach F C))) p0222
  have p0224 :=
    @g_syl (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (.classMem (.cv d) (syn_cwppcand F C)) (syn_wa (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cwppreach F C))) p0221 p0223
  have p0225 :=
    @g_simpl (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cwppreach F C))
  have p0226 :=
    @g_syl (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (syn_wa (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cwppreach F C))) (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) p0224 p0225
  have p0227 :=
    @g_simpl (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)
  have p0228 :=
    @g_syl (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_chwcards (syn_cvv))) p0226 p0227
  have p0229 :=
    @g_simpl (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))
  have p0230 :=
    @g_elwppcand C (.cv d) F
  have p0231 :=
    @g_biimpi (.classMem (.cv d) (syn_cwppcand F C)) (syn_wa (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cwppreach F C))) p0230
  have p0232 :=
    @g_syl (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (.classMem (.cv d) (syn_cwppcand F C)) (syn_wa (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cwppreach F C))) p0229 p0231
  have p0233 :=
    @g_simpl (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cwppreach F C))
  have p0234 :=
    @g_syl (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (syn_wa (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cwppreach F C))) (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) p0232 p0233
  have p0235 :=
    @g_simpr (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)
  have p0236 :=
    @g_syl (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wbr (.cv d) (syn_clec) C) p0234 p0235
  have p0237 :=
    @g_jca (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C) p0228 p0236
  have p0238 :=
    @g_wppreachtchwboundedndv x C F G r p d dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0014 dv_cache_0015 dv_cache_0016 hyp_wppcandtchwboundedimagebindv_1 hyp_wppcandtchwboundedimagebindv_2 hyp_wppcandtchwboundedimagebindv_3 hyp_wppcandtchwboundedimagebindv_4 hyp_wppcandtchwboundedimagebindv_5 hyp_wppcandtchwboundedimagebindv_6 hyp_wppcandtchwboundedimagebindv_7 hyp_wppcandtchwboundedimagebindv_8
  have p0239 :=
    @g_syl (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)) (syn_wb (.classMem (.cv d) (syn_cwppreach F C)) (.classMem (syn_ctc (.cv d)) (syn_cwppreach G (syn_ctc C)))) p0237 p0238
  have p0240 :=
    @g_mpbid (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (.classMem (.cv d) (syn_cwppreach F C)) (.classMem (syn_ctc (.cv d)) (syn_cwppreach G (syn_ctc C))) p0220 p0239
  have p0241 :=
    @g_jca (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (syn_wa (.classMem (syn_ctc (.cv d)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (.cv d)) (syn_clec) (syn_ctc C))) (.classMem (syn_ctc (.cv d)) (syn_cwppreach G (syn_ctc C))) p0214 p0240
  have p0242 :=
    @g_elwppcand (syn_ctc C) (syn_ctc (.cv d)) G
  have p0243 :=
    @g_biimpri (.classMem (syn_ctc (.cv d)) (syn_cwppcand G (syn_ctc C))) (syn_wa (syn_wa (.classMem (syn_ctc (.cv d)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (.cv d)) (syn_clec) (syn_ctc C))) (.classMem (syn_ctc (.cv d)) (syn_cwppreach G (syn_ctc C)))) p0242
  have p0244 :=
    @g_syl (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (syn_wa (syn_wa (.classMem (syn_ctc (.cv d)) (syn_chwcards (syn_cvv))) (syn_wbr (syn_ctc (.cv d)) (syn_clec) (syn_ctc C))) (.classMem (syn_ctc (.cv d)) (syn_cwppreach G (syn_ctc C)))) (.classMem (syn_ctc (.cv d)) (syn_cwppcand G (syn_ctc C))) p0241 p0243
  have p0245 :=
    @g_simpr (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))
  have p0246 :=
    @g_id (.classEq (.cv k) (syn_ctc (.cv d)))
  have p0247 :=
    @g_eleq1d (.classEq (.cv k) (syn_ctc (.cv d))) (.cv k) (syn_ctc (.cv d)) (syn_cwppcand G (syn_ctc C)) p0246
  have p0248 :=
    @g_syl (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (.classEq (.cv k) (syn_ctc (.cv d))) (syn_wb (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (.classMem (syn_ctc (.cv d)) (syn_cwppcand G (syn_ctc C)))) p0245 p0247
  have p0249 :=
    @g_mpbird (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (.classMem (syn_ctc (.cv d)) (syn_cwppcand G (syn_ctc C))) p0244 p0248
  have p0250 :=
    @g_exlimiv (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))) (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) d dv_cache_0024 p0249
  have p0251 :=
    @g_impbii (.classMem (.cv k) (syn_cwppcand G (syn_ctc C))) (syn_wex d (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))))) p0176 p0250
  exact p0251

#print axioms g_wppcandtchwboundedimagebindv

end NFChoice.DirectNominalPrf.WPPReplay
