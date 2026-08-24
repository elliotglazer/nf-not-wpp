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
import NominalWPPReplayChunk013Compact001Part040

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

noncomputable def g_enprmaplem6
    (x : Var) (y : Var) (A : Class) (B : Class) (W : Class) (r : Var) (dv_A_r : r ∉ A.fv) (dv_B_r : r ∉ B.fv) (dv_r_x : r ≠ x) (dv_r_y : r ≠ y) (hyp_enprmaplem6_1 : Nominal.NPrf (.classEq W (syn_cmpt r (syn_co A (syn_cmap) B) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x)))))) (hyp_enprmaplem6_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (.classEq (syn_crn W) (syn_cpw B))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ W.fv ∪ ({r} : Finset Var)
  let p : Var := freshVar proofSupport 0
  let s : Var := freshVar proofSupport 1
  let u : Var := freshVar proofSupport 2
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_ne_x : p ≠ x := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_p : x ≠ p :=
    Ne.symm fresh_p_ne_x
  have fresh_p_ne_y : p ≠ y := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_y_ne_p : y ≠ p :=
    Ne.symm fresh_p_ne_y
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_p_not_B : p ∉ B.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_p_not_W : p ∉ W.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_ne_r : p ≠ r := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_p : r ≠ p :=
    Ne.symm fresh_p_ne_r
  have fresh_s : s ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_s_ne_x : s ≠ x := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_s : x ≠ s :=
    Ne.symm fresh_s_ne_x
  have fresh_s_ne_y : s ≠ y := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_y_ne_s : y ≠ s :=
    Ne.symm fresh_s_ne_y
  have fresh_s_not_A : s ∉ A.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_s_not_B : s ∉ B.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_s_not_W : s ∉ W.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_s_ne_r : s ≠ r := by
    intro h
    exact fresh_s (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_s : r ≠ s :=
    Ne.symm fresh_s_ne_r
  have fresh_u : u ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_u_ne_x : u ≠ x := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_u : x ≠ u :=
    Ne.symm fresh_u_ne_x
  have fresh_u_ne_y : u ≠ y := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_y_ne_u : y ≠ u :=
    Ne.symm fresh_u_ne_y
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_not_W : u ∉ W.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_ne_r : u ≠ r := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_u : r ≠ u :=
    Ne.symm fresh_u_ne_r
  have fresh_p_ne_s : p ≠ s := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_s_ne_p : s ≠ p :=
    Ne.symm fresh_p_ne_s
  have fresh_p_ne_u : p ≠ u := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_u_ne_p : u ≠ p :=
    Ne.symm fresh_p_ne_u
  have fresh_s_ne_u : s ≠ u := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_u_ne_s : u ≠ s :=
    Ne.symm fresh_s_ne_u
  have dv_cache_0001 : r ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : r ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : r ∉ ((Class.cv s)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_s, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : r ∉ ((syn_cima (syn_ccnv (.cv s)) (syn_csn (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_s, dv_r_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : r ∉ ((syn_co A (syn_cmap) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_r, dv_B_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : s ∉ ((syn_wss (.cv p) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_ne_p, fresh_s_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : s ∉ ((syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_ne_x, fresh_s_ne_y, fresh_s_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : s ∉ ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : s ∉ (W).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_s_not_W, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : p ∉ ((syn_crn W)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_W, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : p ∉ ((syn_cpw B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : p ∉ ((syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_x, fresh_p_ne_y, fresh_p_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : p ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : u ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : p ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : u ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_u_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : r ∉ ((syn_cmpt u B (syn_cif (.objMem u p) (.cv x) (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_r, dv_r_x, dv_r_y, fresh_r_ne_u, fresh_r_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : p ∉ (W).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_W, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : p ≠ u := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (show p ≠ u from (by exact fresh_p_ne_u))
  have dv_cache_0020 : p ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (show p ≠ x from (by exact fresh_p_ne_x))
  have dv_cache_0021 : p ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show p ≠ y from (by exact fresh_p_ne_y))
  have dv_cache_0022 : r ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show r ≠ x from (by exact dv_r_x))
  have dv_cache_0023 : u ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0024 : u ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show u ≠ y from (by exact fresh_u_ne_y))
  have p0000 :=
    @g_breldm (.cv s) (.cv p) W
  have p0001 :=
    @g_enprmaplem2 x A B W r dv_cache_0001 dv_cache_0002 hyp_enprmaplem6_1
  have p0002 :=
    @g_fndm (syn_co A (syn_cmap) B) W
  have p0003 :=
    Nominal.mp p0001 p0002
  have p0004 :=
    @g_syl6eleq (syn_wbr (.cv s) W (.cv p)) (.cv s) (syn_cdm W) (syn_co A (syn_cmap) B) p0000 p0003
  have p0005 :=
    @g_fnbrfvb (syn_co A (syn_cmap) B) (.cv s) (.cv p) W
  have p0006 :=
    @g_sylancr (syn_wbr (.cv s) W (.cv p)) (syn_wfn W (syn_co A (syn_cmap) B)) (.classMem (.cv s) (syn_co A (syn_cmap) B)) (syn_wb (.classEq (syn_cfv W (.cv s)) (.cv p)) (syn_wbr (.cv s) W (.cv p))) p0001 p0004 p0005
  have p0007 :=
    @g_ibir (syn_wbr (.cv s) W (.cv p)) (.classEq (syn_cfv W (.cv s)) (.cv p)) p0006
  have p0008 :=
    @g_jca (syn_wbr (.cv s) W (.cv p)) (.classMem (.cv s) (syn_co A (syn_cmap) B)) (.classEq (syn_cfv W (.cv s)) (.cv p)) p0004 p0007
  have p0009 :=
    @g_cnveq (.cv r) (.cv s)
  have p0010_e00_recanon : Nominal.NPrf (.imp (.objEq r s) (.classEq (syn_ccnv (.cv r)) (syn_ccnv (.cv s)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_ccnv syn_copab syn_wex syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0009
  have p0010 :=
    @g_imaeq1d (.objEq r s) (syn_ccnv (.cv r)) (syn_ccnv (.cv s)) (syn_csn (.cv x)) p0010_e00_recanon
  have p0011 :=
    @g_vex s
  have p0012 :=
    @g_cnvex (.cv s) p0011
  have p0013 :=
    @g_snex (.cv x)
  have p0014 :=
    @g_imaex (syn_ccnv (.cv s)) (syn_csn (.cv x)) p0012 p0013
  have p0015_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv r) (.cv s)) (.classEq (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv s)) (syn_csn (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cima syn_wrex syn_wex syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_ccnv syn_copab syn_csn
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0010
  have p0015 :=
    @g_fvmpt r (.cv s) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv s)) (syn_csn (.cv x))) (syn_co A (syn_cmap) B) W dv_cache_0003 dv_cache_0004 dv_cache_0005 p0015_e00_recanon hyp_enprmaplem6_1 p0014
  have p0016 :=
    @g_eqeq1d (.classMem (.cv s) (syn_co A (syn_cmap) B)) (syn_cfv W (.cv s)) (syn_cima (syn_ccnv (.cv s)) (syn_csn (.cv x))) (.cv p) p0015
  have p0017 :=
    @g_n_3ad2ant3 (.classMem (.cv s) (syn_co A (syn_cmap) B)) (syn_wne (.cv x) (.cv y)) (syn_wb (.classEq (syn_cfv W (.cv s)) (.cv p)) (.classEq (syn_cima (syn_ccnv (.cv s)) (syn_csn (.cv x))) (.cv p))) (.classEq A (syn_cpr (.cv x) (.cv y))) p0016
  have p0018 :=
    @g_imassrn (syn_ccnv (.cv s)) (syn_csn (.cv x))
  have p0019 :=
    (by simpa [syn_cdm] using (Nominal.classEqRefl (syn_cdm (.cv s))))
  have p0020 :=
    @g_elmapi (.cv s) A B
  have p0021 :=
    @g_fdm B A (.cv s)
  have p0022 :=
    @g_eqimss (syn_cdm (.cv s)) B
  have p0023 :=
    @g_n_3syl (.classMem (.cv s) (syn_co A (syn_cmap) B)) (syn_wf (.cv s) B A) (.classEq (syn_cdm (.cv s)) B) (syn_wss (syn_cdm (.cv s)) B) p0020 p0021 p0022
  have p0024 :=
    @g_syl5eqssr (.classMem (.cv s) (syn_co A (syn_cmap) B)) (syn_crn (syn_ccnv (.cv s))) (syn_cdm (.cv s)) B p0019 p0023
  have p0025 :=
    @g_syl5ss (.classMem (.cv s) (syn_co A (syn_cmap) B)) (syn_cima (syn_ccnv (.cv s)) (syn_csn (.cv x))) (syn_crn (syn_ccnv (.cv s))) B p0018 p0024
  have p0026 :=
    @g_n_3ad2ant3 (.classMem (.cv s) (syn_co A (syn_cmap) B)) (syn_wne (.cv x) (.cv y)) (syn_wss (syn_cima (syn_ccnv (.cv s)) (syn_csn (.cv x))) B) (.classEq A (syn_cpr (.cv x) (.cv y))) p0025
  have p0027 :=
    @g_sseq1 (syn_cima (syn_ccnv (.cv s)) (syn_csn (.cv x))) (.cv p) B
  have p0028 :=
    @g_syl5ibcom (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))) (.classMem (.cv s) (syn_co A (syn_cmap) B))) (syn_wss (syn_cima (syn_ccnv (.cv s)) (syn_csn (.cv x))) B) (.classEq (syn_cima (syn_ccnv (.cv s)) (syn_csn (.cv x))) (.cv p)) (syn_wss (.cv p) B) p0026 p0027
  have p0029 :=
    @g_sylbid (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))) (.classMem (.cv s) (syn_co A (syn_cmap) B))) (.classEq (syn_cfv W (.cv s)) (.cv p)) (.classEq (syn_cima (syn_ccnv (.cv s)) (syn_csn (.cv x))) (.cv p)) (syn_wss (.cv p) B) p0017 p0028
  have p0030 :=
    @g_n_3expia (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))) (.classMem (.cv s) (syn_co A (syn_cmap) B)) (.imp (.classEq (syn_cfv W (.cv s)) (.cv p)) (syn_wss (.cv p) B)) p0029
  have p0031 :=
    @g_imp3a (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (.classMem (.cv s) (syn_co A (syn_cmap) B)) (.classEq (syn_cfv W (.cv s)) (.cv p)) (syn_wss (.cv p) B) p0030
  have p0032 :=
    @g_syl5 (syn_wbr (.cv s) W (.cv p)) (syn_wa (.classMem (.cv s) (syn_co A (syn_cmap) B)) (.classEq (syn_cfv W (.cv s)) (.cv p))) (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wss (.cv p) B) p0008 p0031
  have p0033 :=
    @g_exlimdv (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wbr (.cv s) W (.cv p)) (syn_wss (.cv p) B) s dv_cache_0006 dv_cache_0007 p0032
  have p0034 :=
    @g_elrn s (.cv p) W dv_cache_0008 dv_cache_0009
  have p0035 :=
    @g_vex p
  have p0036 :=
    @g_elpw (.cv p) B p0035
  have p0037 :=
    @g_n_3imtr4g (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wex s (syn_wbr (.cv s) W (.cv p))) (syn_wss (.cv p) B) (.classMem (.cv p) (syn_crn W)) (.classMem (.cv p) (syn_cpw B)) p0033 p0034 p0036
  have p0038 :=
    @g_ssrdv (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) p (syn_crn W) (syn_cpw B) dv_cache_0010 dv_cache_0011 dv_cache_0012 p0037
  have p0039 :=
    @g_eqid (syn_cmpt u B (syn_cif (.objMem u p) (.cv x) (.cv y)))
  have p0040 :=
    @g_enprmaplem5 x y u A B (syn_cmpt u B (syn_cif (.objMem u p) (.cv x) (.cv y))) W r p dv_cache_0013 dv_cache_0001 dv_cache_0014 dv_cache_0015 dv_cache_0002 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 hyp_enprmaplem6_1 p0039 hyp_enprmaplem6_2
  have p0041 :=
    @g_eqssd (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_crn W) (syn_cpw B) p0038 p0040
  exact p0041

noncomputable def g_enprmap
    (x : Var) (y : Var) (A : Class) (B : Class) (hyp_enprmap_1 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wbr (syn_co A (syn_cmap) B) (syn_cen) (syn_cpw B))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv
  let r : Var := freshVar proofSupport 0
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_ne_x : r ≠ x := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_r : x ≠ r :=
    Ne.symm fresh_r_ne_x
  have fresh_r_ne_y : r ≠ y := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_r : y ≠ r :=
    Ne.symm fresh_r_ne_y
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_not_B : r ∉ B.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have dv_cache_0001 : r ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : r ∉ (B).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : r ≠ x := by
    clear dv_cache_0001 dv_cache_0002
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0004 : r ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show r ≠ y from (by exact fresh_r_ne_y))
  have p0000 :=
    @g_eqid (syn_cmpt r (syn_co A (syn_cmap) B) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x))))
  have p0001 :=
    @g_enprmaplem2 x A B (syn_cmpt r (syn_co A (syn_cmap) B) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x)))) r dv_cache_0001 dv_cache_0002 p0000
  have p0002 :=
    @g_a1i (syn_wfn (syn_cmpt r (syn_co A (syn_cmap) B) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x)))) (syn_co A (syn_cmap) B)) (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) p0001
  have p0003 :=
    @g_enprmaplem3 x y A B (syn_cmpt r (syn_co A (syn_cmap) B) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x)))) r dv_cache_0001 dv_cache_0002 dv_cache_0003 p0000
  have p0004 :=
    @g_enprmaplem6 x y A B (syn_cmpt r (syn_co A (syn_cmap) B) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x)))) r dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 p0000 hyp_enprmap_1
  have p0005 :=
    @g_dff1o2 (syn_co A (syn_cmap) B) (syn_cpw B) (syn_cmpt r (syn_co A (syn_cmap) B) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x))))
  have p0006 :=
    @g_syl3anbrc (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wfn (syn_cmpt r (syn_co A (syn_cmap) B) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x)))) (syn_co A (syn_cmap) B)) (syn_wfun (syn_ccnv (syn_cmpt r (syn_co A (syn_cmap) B) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x)))))) (.classEq (syn_crn (syn_cmpt r (syn_co A (syn_cmap) B) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x))))) (syn_cpw B)) (syn_wf1o (syn_cmpt r (syn_co A (syn_cmap) B) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x)))) (syn_co A (syn_cmap) B) (syn_cpw B)) p0002 p0003 p0004 p0005
  have p0007 :=
    @g_enprmaplem1 x A B (syn_cmpt r (syn_co A (syn_cmap) B) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x)))) r dv_cache_0001 dv_cache_0002 dv_cache_0003 p0000
  have p0008 :=
    @g_f1oen (syn_co A (syn_cmap) B) (syn_cpw B) (syn_cmpt r (syn_co A (syn_cmap) B) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x)))) p0007
  have p0009 :=
    @g_syl (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wf1o (syn_cmpt r (syn_co A (syn_cmap) B) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x)))) (syn_co A (syn_cmap) B) (syn_cpw B)) (syn_wbr (syn_co A (syn_cmap) B) (syn_cen) (syn_cpw B)) p0006 p0008
  exact p0009

noncomputable def g_enprmapc
    (A : Class) (B : Class) (C : Class) (P : Class) (hyp_enprmapc_1 : Nominal.NPrf (.classMem A (syn_cvv))) (hyp_enprmapc_2 : Nominal.NPrf (.classMem B (syn_cvv))) (hyp_enprmapc_3 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wa (syn_wne A B) (.classEq P (syn_cpr A B))) (syn_wbr (syn_co P (syn_cmap) C) (syn_cen) (syn_cpw C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ P.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_P : x ∉ P.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_P : y ∉ P.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : y ∉ (B).fv := by
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Wff.imp (syn_wa (syn_wne (.cv x) B) (.classEq P (syn_cpr (.cv x) B))) (syn_wbr (syn_co P (syn_cmap) C) (syn_cen) (syn_cpw C)))).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_B, fresh_y_not_P, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.imp (syn_wa (syn_wne A B) (.classEq P (syn_cpr A B))) (syn_wbr (syn_co P (syn_cmap) C) (syn_cen) (syn_cpw C)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmap, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, fresh_x_not_P, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_neeq1 (.cv x) A B
  have p0001 :=
    @g_preq1 (.cv x) A B
  have p0002 :=
    @g_eqeq2d (.classEq (.cv x) A) (syn_cpr (.cv x) B) (syn_cpr A B) P p0001
  have p0003 :=
    @g_anbi12d (.classEq (.cv x) A) (syn_wne (.cv x) B) (syn_wne A B) (.classEq P (syn_cpr (.cv x) B)) (.classEq P (syn_cpr A B)) p0000 p0002
  have p0004 :=
    @g_imbi1d (.classEq (.cv x) A) (syn_wa (syn_wne (.cv x) B) (.classEq P (syn_cpr (.cv x) B))) (syn_wa (syn_wne A B) (.classEq P (syn_cpr A B))) (syn_wbr (syn_co P (syn_cmap) C) (syn_cen) (syn_cpw C)) p0003
  have p0005 :=
    @g_neeq2 (.cv y) B (.cv x)
  have p0006 :=
    @g_preq2 (.cv y) B (.cv x)
  have p0007 :=
    @g_eqeq2d (.classEq (.cv y) B) (syn_cpr (.cv x) (.cv y)) (syn_cpr (.cv x) B) P p0006
  have p0008 :=
    @g_anbi12d (.classEq (.cv y) B) (syn_wne (.cv x) (.cv y)) (syn_wne (.cv x) B) (.classEq P (syn_cpr (.cv x) (.cv y))) (.classEq P (syn_cpr (.cv x) B)) p0005 p0007
  have p0009 :=
    @g_imbi1d (.classEq (.cv y) B) (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq P (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wne (.cv x) B) (.classEq P (syn_cpr (.cv x) B))) (syn_wbr (syn_co P (syn_cmap) C) (syn_cen) (syn_cpw C)) p0008
  have p0010 :=
    @g_enprmap x y P C hyp_enprmapc_3
  have p0011 :=
    @g_vtocl (.imp (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq P (syn_cpr (.cv x) (.cv y)))) (syn_wbr (syn_co P (syn_cmap) C) (syn_cen) (syn_cpw C))) (.imp (syn_wa (syn_wne (.cv x) B) (.classEq P (syn_cpr (.cv x) B))) (syn_wbr (syn_co P (syn_cmap) C) (syn_cen) (syn_cpw C))) y B dv_cache_0001 dv_cache_0002 hyp_enprmapc_2 p0009 p0010
  have p0012 :=
    @g_vtocl (.imp (syn_wa (syn_wne (.cv x) B) (.classEq P (syn_cpr (.cv x) B))) (syn_wbr (syn_co P (syn_cmap) C) (syn_cen) (syn_cpw C))) (.imp (syn_wa (syn_wne A B) (.classEq P (syn_cpr A B))) (syn_wbr (syn_co P (syn_cmap) C) (syn_cen) (syn_cpw C))) x A dv_cache_0003 dv_cache_0004 hyp_enprmapc_1 p0004 p0011
  exact p0012

noncomputable def g_enpw
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wbr A (syn_cen) B) (syn_wbr (syn_cpw A) (syn_cen) (syn_cpw B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (h))
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (h))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have dv_cache_0001 : a ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : b ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : b ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : b ∉ ((Wff.imp (syn_wbr A (syn_cen) B) (syn_wbr (syn_cpw A) (syn_cen) (syn_cpw B)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_A, fresh_b_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : a ∉ ((Wff.imp (syn_wbr A (syn_cen) (.cv b)) (syn_wbr (syn_cpw A) (syn_cen) (syn_cpw (.cv b))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, fresh_a_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_brex A B (syn_cen)
  have p0001 :=
    @g_breq1 (.cv a) A (.cv b) (syn_cen)
  have p0002 :=
    @g_pweq (.cv a) A
  have p0003 :=
    @g_breq1d (.classEq (.cv a) A) (syn_cpw (.cv a)) (syn_cpw A) (syn_cpw (.cv b)) (syn_cen) p0002
  have p0004 :=
    @g_imbi12d (.classEq (.cv a) A) (syn_wbr (.cv a) (syn_cen) (.cv b)) (syn_wbr A (syn_cen) (.cv b)) (syn_wbr (syn_cpw (.cv a)) (syn_cen) (syn_cpw (.cv b))) (syn_wbr (syn_cpw A) (syn_cen) (syn_cpw (.cv b))) p0001 p0003
  have p0005 :=
    @g_breq2 (.cv b) B A (syn_cen)
  have p0006 :=
    @g_pweq (.cv b) B
  have p0007 :=
    @g_breq2d (.classEq (.cv b) B) (syn_cpw (.cv b)) (syn_cpw B) (syn_cpw A) (syn_cen) p0006
  have p0008 :=
    @g_imbi12d (.classEq (.cv b) B) (syn_wbr A (syn_cen) (.cv b)) (syn_wbr A (syn_cen) B) (syn_wbr (syn_cpw A) (syn_cen) (syn_cpw (.cv b))) (syn_wbr (syn_cpw A) (syn_cen) (syn_cpw B)) p0005 p0007
  have p0009 :=
    @g_enmap2 (.cv a) (.cv b) (syn_cpr (syn_cvv) (syn_c0))
  have p0010 :=
    @g_vn0
  have p0011 :=
    @g_eqid (syn_cpr (syn_cvv) (syn_c0))
  have p0012 :=
    @g_vvex
  have p0013 :=
    @g_n_0ex
  have p0014 :=
    @g_vex a
  have p0015 :=
    @g_enprmapc (syn_cvv) (syn_c0) (.cv a) (syn_cpr (syn_cvv) (syn_c0)) p0012 p0013 p0014
  have p0016 :=
    @g_mp2an (syn_wne (syn_cvv) (syn_c0)) (.classEq (syn_cpr (syn_cvv) (syn_c0)) (syn_cpr (syn_cvv) (syn_c0))) (syn_wbr (syn_co (syn_cpr (syn_cvv) (syn_c0)) (syn_cmap) (.cv a)) (syn_cen) (syn_cpw (.cv a))) p0010 p0011 p0015
  have p0017 :=
    @g_ensym (syn_cpw (.cv a)) (syn_co (syn_cpr (syn_cvv) (syn_c0)) (syn_cmap) (.cv a))
  have p0018 :=
    @g_mpbir (syn_wbr (syn_cpw (.cv a)) (syn_cen) (syn_co (syn_cpr (syn_cvv) (syn_c0)) (syn_cmap) (.cv a))) (syn_wbr (syn_co (syn_cpr (syn_cvv) (syn_c0)) (syn_cmap) (.cv a)) (syn_cen) (syn_cpw (.cv a))) p0016 p0017
  have p0019 :=
    @g_vn0
  have p0020 :=
    @g_vvex
  have p0021 :=
    @g_n_0ex
  have p0022 :=
    @g_vex b
  have p0023 :=
    @g_enprmapc (syn_cvv) (syn_c0) (.cv b) (syn_cpr (syn_cvv) (syn_c0)) p0020 p0021 p0022
  have p0024 :=
    @g_mp2an (syn_wne (syn_cvv) (syn_c0)) (.classEq (syn_cpr (syn_cvv) (syn_c0)) (syn_cpr (syn_cvv) (syn_c0))) (syn_wbr (syn_co (syn_cpr (syn_cvv) (syn_c0)) (syn_cmap) (.cv b)) (syn_cen) (syn_cpw (.cv b))) p0019 p0011 p0023
  have p0025 :=
    @g_entr (syn_co (syn_cpr (syn_cvv) (syn_c0)) (syn_cmap) (.cv a)) (syn_co (syn_cpr (syn_cvv) (syn_c0)) (syn_cmap) (.cv b)) (syn_cpw (.cv b))
  have p0026 :=
    @g_mpan2 (syn_wbr (syn_co (syn_cpr (syn_cvv) (syn_c0)) (syn_cmap) (.cv a)) (syn_cen) (syn_co (syn_cpr (syn_cvv) (syn_c0)) (syn_cmap) (.cv b))) (syn_wbr (syn_co (syn_cpr (syn_cvv) (syn_c0)) (syn_cmap) (.cv b)) (syn_cen) (syn_cpw (.cv b))) (syn_wbr (syn_co (syn_cpr (syn_cvv) (syn_c0)) (syn_cmap) (.cv a)) (syn_cen) (syn_cpw (.cv b))) p0024 p0025
  have p0027 :=
    @g_entr (syn_cpw (.cv a)) (syn_co (syn_cpr (syn_cvv) (syn_c0)) (syn_cmap) (.cv a)) (syn_cpw (.cv b))
  have p0028 :=
    @g_sylancr (syn_wbr (syn_co (syn_cpr (syn_cvv) (syn_c0)) (syn_cmap) (.cv a)) (syn_cen) (syn_co (syn_cpr (syn_cvv) (syn_c0)) (syn_cmap) (.cv b))) (syn_wbr (syn_cpw (.cv a)) (syn_cen) (syn_co (syn_cpr (syn_cvv) (syn_c0)) (syn_cmap) (.cv a))) (syn_wbr (syn_co (syn_cpr (syn_cvv) (syn_c0)) (syn_cmap) (.cv a)) (syn_cen) (syn_cpw (.cv b))) (syn_wbr (syn_cpw (.cv a)) (syn_cen) (syn_cpw (.cv b))) p0018 p0026 p0027
  have p0029 :=
    @g_syl (syn_wbr (.cv a) (syn_cen) (.cv b)) (syn_wbr (syn_co (syn_cpr (syn_cvv) (syn_c0)) (syn_cmap) (.cv a)) (syn_cen) (syn_co (syn_cpr (syn_cvv) (syn_c0)) (syn_cmap) (.cv b))) (syn_wbr (syn_cpw (.cv a)) (syn_cen) (syn_cpw (.cv b))) p0009 p0028
  have p0030 :=
    @g_vtocl2g (.imp (syn_wbr (.cv a) (syn_cen) (.cv b)) (syn_wbr (syn_cpw (.cv a)) (syn_cen) (syn_cpw (.cv b)))) (.imp (syn_wbr A (syn_cen) (.cv b)) (syn_wbr (syn_cpw A) (syn_cen) (syn_cpw (.cv b)))) (.imp (syn_wbr A (syn_cen) B) (syn_wbr (syn_cpw A) (syn_cen) (syn_cpw B))) a b A B (syn_cvv) (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 p0004 p0008 p0029
  have p0031 :=
    @g_mpcom (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (syn_wbr A (syn_cen) B) (syn_wbr (syn_cpw A) (syn_cen) (syn_cpw B)) p0000 p0030
  exact p0031

noncomputable def g_nceq
    (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cnc A) (syn_cnc B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_eceq1 A B (syn_cen)
  have p0001 :=
    (by simpa [syn_cnc] using (Nominal.classEqRefl (syn_cnc A)))
  have p0002 :=
    (by simpa [syn_cnc] using (Nominal.classEqRefl (syn_cnc B)))
  have p0003 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cec A (syn_cen)) (syn_cec B (syn_cen)) (syn_cnc A) (syn_cnc B) p0000 p0001 p0002
  exact p0003

noncomputable def g_nceqi
    (A : Class) (B : Class) (hyp_nceqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_cnc A) (syn_cnc B)) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  have p0000 :=
    @g_nceq A B
  have p0001 :=
    Nominal.mp hyp_nceqi_1 p0000
  exact p0001

noncomputable def g_nceqd
    (ph : Wff) (A : Class) (B : Class) (hyp_nceqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cnc A) (syn_cnc B))) := by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_nceq A B
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cnc A) (syn_cnc B)) hyp_nceqd_1 p0000
  exact p0001

noncomputable def g_ncsex
     :
    Nominal.NPrf (.classMem (syn_cncs) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  have p0000 :=
    (by simpa [syn_cncs] using (Nominal.classEqRefl (syn_cncs)))
  have p0001 :=
    @g_enex
  have p0002 :=
    @g_vvex
  have p0003 :=
    @g_qsex (syn_cvv) (syn_cen) p0001 p0002
  have p0004 :=
    @g_eqeltri (syn_cncs) (syn_cqs (syn_cvv) (syn_cen)) (syn_cvv) p0000 p0003
  exact p0004

noncomputable def g_brlecg
    (x : Var) (y : Var) (A : Class) (B : Class) (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (syn_wa (.classMem A V) (.classMem B W)) (syn_wb (syn_wbr A (syn_clec) B) (syn_wrex x A (syn_wrex y B (syn_wss (.cv x) (.cv y)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  let b : Var := freshVar proofSupport 0
  let a : Var := freshVar proofSupport 1
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_b_ne_x : b ≠ x := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_b : x ≠ b :=
    Ne.symm fresh_b_ne_x
  have fresh_b_ne_y : b ≠ y := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_y_ne_b : y ≠ b :=
    Ne.symm fresh_b_ne_y
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_b_not_V : b ∉ V.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_not_W : b ∉ W.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_a_ne_x : a ≠ x := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_a : x ≠ a :=
    Ne.symm fresh_a_ne_x
  have fresh_a_ne_y : a ≠ y := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_y_ne_a : y ≠ a :=
    Ne.symm fresh_a_ne_y
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a_not_V : a ∉ V.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_W : a ∉ W.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b_ne_a : b ≠ a := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_b : a ≠ b :=
    Ne.symm fresh_b_ne_a
  have dv_cache_0001 : x ∉ ((Class.cv a)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classEq (.cv b) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_b, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : a ≠ b := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0007 : a ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0008 : a ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show a ≠ y from (by exact fresh_a_ne_y))
  have dv_cache_0009 : b ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show b ≠ x from (by exact fresh_b_ne_x))
  have dv_cache_0010 : b ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show b ≠ y from (by exact fresh_b_ne_y))
  have dv_cache_0011 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0012 : a ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : b ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : a ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : b ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : a ∉ ((syn_wrex x A (syn_wrex y B (syn_wss (.cv x) (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_A, fresh_a_not_B, fresh_a_ne_x, fresh_a_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : b ∉ ((syn_wrex x A (syn_wrex y B (syn_wss (.cv x) (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_A, fresh_b_not_B, fresh_b_ne_x, fresh_b_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_rexeq (syn_wrex y (.cv b) (syn_wss (.cv x) (.cv y))) x (.cv a) A dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_rexeq (syn_wss (.cv x) (.cv y)) y (.cv b) B dv_cache_0003 dv_cache_0004
  have p0002 :=
    @g_rexbidv (.classEq (.cv b) B) (syn_wrex y (.cv b) (syn_wss (.cv x) (.cv y))) (syn_wrex y B (syn_wss (.cv x) (.cv y))) x A dv_cache_0005 p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_lec x y a b dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0004 :=
    @g_brabg (syn_wrex x (.cv a) (syn_wrex y (.cv b) (syn_wss (.cv x) (.cv y)))) (syn_wrex x A (syn_wrex y (.cv b) (syn_wss (.cv x) (.cv y)))) (syn_wrex x A (syn_wrex y B (syn_wss (.cv x) (.cv y)))) a b A B V W (syn_clec) dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0006 p0000 p0002 p0003
  exact p0004

#print axioms g_brlecg

end NFChoice.DirectNominalPrf.WPPReplay
