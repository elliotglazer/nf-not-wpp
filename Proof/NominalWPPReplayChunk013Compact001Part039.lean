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
import NominalWPPReplayChunk013Compact001Part038

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

noncomputable def g_enprmaplem3
    (x : Var) (y : Var) (A : Class) (B : Class) (W : Class) (r : Var) (dv_A_r : r ∉ A.fv) (dv_B_r : r ∉ B.fv) (dv_r_x : r ≠ x) (hyp_enprmaplem3_1 : Nominal.NPrf (.classEq W (syn_cmpt r (syn_co A (syn_cmap) B) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x)))))) :
    Nominal.NPrf (.imp (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wfun (syn_ccnv W))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv ∪ W.fv ∪ ({r} : Finset Var)
  let z : Var := freshVar proofSupport 0
  let p : Var := freshVar proofSupport 1
  let q : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_W : z ∉ W.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_ne_r : z ≠ r := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_z : r ≠ z :=
    Ne.symm fresh_z_ne_r
  have fresh_p : p ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
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
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_q_ne_x : q ≠ x := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_q : x ≠ q :=
    Ne.symm fresh_q_ne_x
  have fresh_q_ne_y : q ≠ y := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_y_ne_q : y ≠ q :=
    Ne.symm fresh_q_ne_y
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_q_not_B : q ∉ B.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_q_not_W : q ∉ W.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_ne_r : q ≠ r := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_q : r ≠ q :=
    Ne.symm fresh_q_ne_r
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_y_ne_w : y ≠ w :=
    Ne.symm fresh_w_ne_y
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_W : w ∉ W.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_ne_r : w ≠ r := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_w : r ≠ w :=
    Ne.symm fresh_w_ne_r
  have fresh_z_ne_p : z ≠ p := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_p_ne_z : p ≠ z :=
    Ne.symm fresh_z_ne_p
  have fresh_z_ne_q : z ≠ q := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_q_ne_z : q ≠ z :=
    Ne.symm fresh_z_ne_q
  have fresh_z_ne_w : z ≠ w := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    Ne.symm fresh_z_ne_w
  have fresh_p_ne_q : p ≠ q := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_q_ne_p : q ≠ p :=
    Ne.symm fresh_p_ne_q
  have fresh_p_ne_w : p ≠ w := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_w_ne_p : w ≠ p :=
    Ne.symm fresh_p_ne_w
  have fresh_q_ne_w : q ≠ w := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_q : w ≠ q :=
    Ne.symm fresh_q_ne_w
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
  have dv_cache_0003 : r ∉ ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : r ∉ ((syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_p, dv_r_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : r ∉ ((syn_co A (syn_cmap) B)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmap, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_r, dv_B_r, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : r ∉ ((Class.cv q)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : r ∉ ((syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_q, dv_r_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : w ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : w ∉ ((Class.cv q)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : w ∉ ((syn_wo (syn_wbr (.cv z) (.cv q) (.cv x)) (syn_wbr (.cv z) (.cv q) (.cv y)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_z, fresh_w_ne_x, fresh_w_ne_q, fresh_w_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : w ∉ ((syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, fresh_w_not_A, fresh_w_not_B, fresh_w_ne_p, fresh_w_ne_q, fresh_w_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : z ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0013 : z ∉ ((Class.cv p)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_p, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0014 : z ∉ ((Class.cv q)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0015 : z ∉ ((syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_A, fresh_z_not_B, fresh_z_ne_p, fresh_z_ne_q, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : q ∉ ((syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_x, fresh_q_ne_y, fresh_q_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : z ∉ ((syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : p ∉ ((syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_x, fresh_p_ne_y, fresh_p_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : z ∉ ((syn_ccnv W)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_W, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : p ∉ ((syn_ccnv W)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_p_not_W, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : q ∉ ((syn_ccnv W)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_not_W, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0022 : z ≠ p := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show z ≠ p from (by exact fresh_z_ne_p))
  have dv_cache_0023 : z ≠ q := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show z ≠ q from (by exact fresh_z_ne_q))
  have dv_cache_0024 : p ≠ q := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show p ≠ q from (by exact fresh_p_ne_q))
  have p0000 :=
    @g_brcnv (.cv z) (.cv p) W
  have p0001 :=
    @g_brcnv (.cv z) (.cv q) W
  have p0002 :=
    @g_breldm (.cv p) (.cv z) W
  have p0003 :=
    @g_enprmaplem2 x A B W r dv_cache_0001 dv_cache_0002 hyp_enprmaplem3_1
  have p0004 :=
    @g_fndm (syn_co A (syn_cmap) B) W
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_syl6eleq (syn_wbr (.cv p) W (.cv z)) (.cv p) (syn_cdm W) (syn_co A (syn_cmap) B) p0002 p0005
  have p0007 :=
    @g_fnfun (syn_co A (syn_cmap) B) W
  have p0008 :=
    Nominal.mp p0003 p0007
  have p0009 :=
    @g_funbrfv (.cv p) (.cv z) W
  have p0010 :=
    Nominal.mp p0008 p0009
  have p0011 :=
    @g_cnveq (.cv r) (.cv p)
  have p0012_e00_recanon : Nominal.NPrf (.imp (.objEq r p) (.classEq (syn_ccnv (.cv r)) (syn_ccnv (.cv p)))) :=
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
      p0011
  have p0012 :=
    @g_imaeq1d (.objEq r p) (syn_ccnv (.cv r)) (syn_ccnv (.cv p)) (syn_csn (.cv x)) p0012_e00_recanon
  have p0013 :=
    @g_vex p
  have p0014 :=
    @g_cnvex (.cv p) p0013
  have p0015 :=
    @g_snex (.cv x)
  have p0016 :=
    @g_imaex (syn_ccnv (.cv p)) (syn_csn (.cv x)) p0014 p0015
  have p0017_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv r) (.cv p)) (.classEq (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))))) :=
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
      p0012
  have p0017 :=
    @g_fvmpt r (.cv p) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_co A (syn_cmap) B) W dv_cache_0003 dv_cache_0004 dv_cache_0005 p0017_e00_recanon hyp_enprmaplem3_1 p0016
  have p0018 :=
    @g_syl (syn_wbr (.cv p) W (.cv z)) (.classMem (.cv p) (syn_co A (syn_cmap) B)) (.classEq (syn_cfv W (.cv p)) (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))) p0006 p0017
  have p0019 :=
    @g_eqtr3d (syn_wbr (.cv p) W (.cv z)) (syn_cfv W (.cv p)) (.cv z) (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) p0010 p0018
  have p0020 :=
    @g_jca (syn_wbr (.cv p) W (.cv z)) (.classMem (.cv p) (syn_co A (syn_cmap) B)) (.classEq (.cv z) (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))) p0006 p0019
  have p0021 :=
    @g_breldm (.cv q) (.cv z) W
  have p0022 :=
    @g_syl6eleq (syn_wbr (.cv q) W (.cv z)) (.cv q) (syn_cdm W) (syn_co A (syn_cmap) B) p0021 p0005
  have p0023 :=
    @g_funbrfv (.cv q) (.cv z) W
  have p0024 :=
    Nominal.mp p0008 p0023
  have p0025 :=
    @g_cnveq (.cv r) (.cv q)
  have p0026_e00_recanon : Nominal.NPrf (.imp (.objEq r q) (.classEq (syn_ccnv (.cv r)) (syn_ccnv (.cv q)))) :=
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
      p0025
  have p0026 :=
    @g_imaeq1d (.objEq r q) (syn_ccnv (.cv r)) (syn_ccnv (.cv q)) (syn_csn (.cv x)) p0026_e00_recanon
  have p0027 :=
    @g_vex q
  have p0028 :=
    @g_cnvex (.cv q) p0027
  have p0029 :=
    @g_imaex (syn_ccnv (.cv q)) (syn_csn (.cv x)) p0028 p0015
  have p0030_e00_recanon : Nominal.NPrf (.imp (.classEq (.cv r) (.cv q)) (.classEq (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))) :=
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
      p0026
  have p0030 :=
    @g_fvmpt r (.cv q) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))) (syn_co A (syn_cmap) B) W dv_cache_0006 dv_cache_0007 dv_cache_0005 p0030_e00_recanon hyp_enprmaplem3_1 p0029
  have p0031 :=
    @g_syl (syn_wbr (.cv q) W (.cv z)) (.classMem (.cv q) (syn_co A (syn_cmap) B)) (.classEq (syn_cfv W (.cv q)) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))) p0022 p0030
  have p0032 :=
    @g_eqtr3d (syn_wbr (.cv q) W (.cv z)) (syn_cfv W (.cv q)) (.cv z) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))) p0024 p0031
  have p0033 :=
    @g_jca (syn_wbr (.cv q) W (.cv z)) (.classMem (.cv q) (syn_co A (syn_cmap) B)) (.classEq (.cv z) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))) p0022 p0032
  have p0034 :=
    @g_anim12i (syn_wbr (.cv p) W (.cv z)) (syn_wa (.classMem (.cv p) (syn_co A (syn_cmap) B)) (.classEq (.cv z) (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))))) (syn_wbr (.cv q) W (.cv z)) (syn_wa (.classMem (.cv q) (syn_co A (syn_cmap) B)) (.classEq (.cv z) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))) p0020 p0033
  have p0035 :=
    @g_syl2anb (syn_wbr (.cv z) (syn_ccnv W) (.cv p)) (syn_wbr (.cv p) W (.cv z)) (syn_wbr (.cv q) W (.cv z)) (syn_wa (syn_wa (.classMem (.cv p) (syn_co A (syn_cmap) B)) (.classEq (.cv z) (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv q) (syn_co A (syn_cmap) B)) (.classEq (.cv z) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (syn_wbr (.cv z) (syn_ccnv W) (.cv q)) p0000 p0001 p0034
  have p0036 :=
    @g_elmapi (.cv p) A B
  have p0037 :=
    @g_elmapi (.cv q) A B
  have p0038 :=
    @g_anim12i (.classMem (.cv p) (syn_co A (syn_cmap) B)) (syn_wf (.cv p) B A) (.classMem (.cv q) (syn_co A (syn_cmap) B)) (syn_wf (.cv q) B A) p0036 p0037
  have p0039 :=
    @g_eqtr2 (.cv z) (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))
  have p0040 :=
    @g_simprll (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wf (.cv p) B A) (syn_wf (.cv q) B A) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))
  have p0041 :=
    @g_ffn B A (.cv p)
  have p0042 :=
    @g_syl (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (syn_wf (.cv p) B A) (syn_wfn (.cv p) B) p0040 p0041
  have p0043 :=
    @g_simprlr (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wf (.cv p) B A) (syn_wf (.cv q) B A) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))
  have p0044 :=
    @g_ffn B A (.cv q)
  have p0045 :=
    @g_syl (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (syn_wf (.cv q) B A) (syn_wfn (.cv q) B) p0043 p0044
  have p0046 :=
    @g_ffvelrn B A (.cv z) (.cv p)
  have p0047 :=
    @g_sylan (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (syn_wf (.cv p) B A) (.classMem (.cv z) B) (.classMem (syn_cfv (.cv p) (.cv z)) A) p0040 p0046
  have p0048 :=
    @g_simpllr (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))) (.classMem (.cv z) B)
  have p0049 :=
    @g_eleq2d (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B)) A (syn_cpr (.cv x) (.cv y)) (syn_cfv (.cv p) (.cv z)) p0048
  have p0050 :=
    @g_fvex (.cv z) (.cv p)
  have p0051 :=
    @g_elpr (syn_cfv (.cv p) (.cv z)) (.cv x) (.cv y) p0050
  have p0052 :=
    @g_syl6bb (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B)) (.classMem (syn_cfv (.cv p) (.cv z)) A) (.classMem (syn_cfv (.cv p) (.cv z)) (syn_cpr (.cv x) (.cv y))) (syn_wo (.classEq (syn_cfv (.cv p) (.cv z)) (.cv x)) (.classEq (syn_cfv (.cv p) (.cv z)) (.cv y))) p0049 p0051
  have p0053 :=
    @g_simprr (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B) (.classEq (syn_cfv (.cv p) (.cv z)) (.cv x))
  have p0054 :=
    @g_simplrr (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))) (.classMem (.cv z) B)
  have p0055 :=
    @g_eleq2d (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B)) (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))) (.cv z) p0054
  have p0056 :=
    @g_eliniseg (.cv p) (.cv x) (.cv z)
  have p0057 :=
    @g_eliniseg (.cv q) (.cv x) (.cv z)
  have p0058 :=
    @g_n_3bitr3g (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B)) (.classMem (.cv z) (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))) (.classMem (.cv z) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))) (syn_wbr (.cv z) (.cv p) (.cv x)) (syn_wbr (.cv z) (.cv q) (.cv x)) p0055 p0056 p0057
  have p0059 :=
    @g_biimpd (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B)) (syn_wbr (.cv z) (.cv p) (.cv x)) (syn_wbr (.cv z) (.cv q) (.cv x)) p0058
  have p0060 :=
    @g_fnbrfvb B (.cv z) (.cv x) (.cv p)
  have p0061 :=
    @g_sylan (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (syn_wfn (.cv p) B) (.classMem (.cv z) B) (syn_wb (.classEq (syn_cfv (.cv p) (.cv z)) (.cv x)) (syn_wbr (.cv z) (.cv p) (.cv x))) p0042 p0060
  have p0062 :=
    @g_fnbrfvb B (.cv z) (.cv x) (.cv q)
  have p0063 :=
    @g_sylan (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (syn_wfn (.cv q) B) (.classMem (.cv z) B) (syn_wb (.classEq (syn_cfv (.cv q) (.cv z)) (.cv x)) (syn_wbr (.cv z) (.cv q) (.cv x))) p0045 p0062
  have p0064 :=
    @g_n_3imtr4d (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B)) (syn_wbr (.cv z) (.cv p) (.cv x)) (syn_wbr (.cv z) (.cv q) (.cv x)) (.classEq (syn_cfv (.cv p) (.cv z)) (.cv x)) (.classEq (syn_cfv (.cv q) (.cv z)) (.cv x)) p0059 p0061 p0063
  have p0065 :=
    @g_impr (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B) (.classEq (syn_cfv (.cv p) (.cv z)) (.cv x)) (.classEq (syn_cfv (.cv q) (.cv z)) (.cv x)) p0064
  have p0066 :=
    @g_eqtr4d (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (syn_wa (.classMem (.cv z) B) (.classEq (syn_cfv (.cv p) (.cv z)) (.cv x)))) (syn_cfv (.cv p) (.cv z)) (.cv x) (syn_cfv (.cv q) (.cv z)) p0053 p0065
  have p0067 :=
    @g_expr (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B) (.classEq (syn_cfv (.cv p) (.cv z)) (.cv x)) (.classEq (syn_cfv (.cv p) (.cv z)) (syn_cfv (.cv q) (.cv z))) p0066
  have p0068 :=
    @g_simprr (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B) (.classEq (syn_cfv (.cv p) (.cv z)) (.cv y))
  have p0069 :=
    @g_simplll (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y)))
  have p0070 :=
    @g_neneqd (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y)))) (.cv x) (.cv y) p0069
  have p0071 :=
    @g_adantr (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (syn_wf (.cv p) B A) (.classMem (.cv z) B) p0040
  have p0072 :=
    @g_ffun B A (.cv p)
  have p0073 :=
    @g_fununiq (.cv z) (.cv x) (.cv y) (.cv p)
  have p0074_e00_recanon : Nominal.NPrf (.imp (syn_w3a (syn_wfun (.cv p)) (syn_wbr (.cv z) (.cv p) (.cv x)) (syn_wbr (.cv z) (.cv p) (.cv y))) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_wfun syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_ccom syn_copab syn_wex syn_ccnv syn_cid syn_wbr syn_cop syn_cun syn_wrex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0073
  have p0074 :=
    @g_n_3expib (syn_wfun (.cv p)) (syn_wbr (.cv z) (.cv p) (.cv x)) (syn_wbr (.cv z) (.cv p) (.cv y)) (.objEq x y) p0074_e00_recanon
  have p0075 :=
    @g_ancomsd (syn_wfun (.cv p)) (syn_wbr (.cv z) (.cv p) (.cv x)) (syn_wbr (.cv z) (.cv p) (.cv y)) (.objEq x y) p0074
  have p0076 :=
    @g_n_3syl (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B)) (syn_wf (.cv p) B A) (syn_wfun (.cv p)) (.imp (syn_wa (syn_wbr (.cv z) (.cv p) (.cv y)) (syn_wbr (.cv z) (.cv p) (.cv x))) (.objEq x y)) p0071 p0072 p0075
  have p0077 :=
    @g_exp3a (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B)) (syn_wbr (.cv z) (.cv p) (.cv y)) (syn_wbr (.cv z) (.cv p) (.cv x)) (.objEq x y) p0076
  have p0078 :=
    @g_impr (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y)) (.imp (syn_wbr (.cv z) (.cv p) (.cv x)) (.objEq x y)) p0077
  have p0079_e00_recanon : Nominal.NPrf (.imp (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y)))) (.neg (.objEq x y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0070
  have p0079 :=
    @g_mtod (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y)))) (syn_wbr (.cv z) (.cv p) (.cv x)) (.objEq x y) p0079_e00_recanon p0078
  have p0080 :=
    @g_expr (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y)) (.neg (syn_wbr (.cv z) (.cv p) (.cv x))) p0079
  have p0081 :=
    @g_biimprd (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B)) (syn_wbr (.cv z) (.cv p) (.cv x)) (syn_wbr (.cv z) (.cv q) (.cv x)) p0058
  have p0082 :=
    @g_nsyld (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B)) (syn_wbr (.cv z) (.cv p) (.cv y)) (syn_wbr (.cv z) (.cv p) (.cv x)) (syn_wbr (.cv z) (.cv q) (.cv x)) p0080 p0081
  have p0083 :=
    @g_impr (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y)) (.neg (syn_wbr (.cv z) (.cv q) (.cv x))) p0082
  have p0084 :=
    @g_simprl (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y))
  have p0085 :=
    @g_adantr (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (syn_wf (.cv q) B A) (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y))) p0043
  have p0086 :=
    @g_fdm B A (.cv q)
  have p0087 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y)))) (syn_wf (.cv q) B A) (.classEq (syn_cdm (.cv q)) B) p0085 p0086
  have p0088 :=
    @g_eleqtrrd (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y)))) (.cv z) B (syn_cdm (.cv q)) p0084 p0087
  have p0089 :=
    @g_eldm w (.cv z) (.cv q) dv_cache_0008 dv_cache_0009
  have p0090 :=
    @g_brelrn (.cv z) (.cv w) (.cv q)
  have p0091 :=
    @g_frn B A (.cv q)
  have p0092 :=
    @g_syl (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y)))) (syn_wf (.cv q) B A) (syn_wss (syn_crn (.cv q)) A) p0085 p0091
  have p0093 :=
    @g_sseld (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y)))) (syn_crn (.cv q)) A (.cv w) p0092
  have p0094 :=
    @g_syl5 (syn_wbr (.cv z) (.cv q) (.cv w)) (.classMem (.cv w) (syn_crn (.cv q))) (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y)))) (.classMem (.cv w) A) p0090 p0093
  have p0095 :=
    @g_simpllr (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y)))
  have p0096 :=
    @g_eleq2d (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y)))) A (syn_cpr (.cv x) (.cv y)) (.cv w) p0095
  have p0097 :=
    @g_vex w
  have p0098 :=
    @g_elpr (.cv w) (.cv x) (.cv y) p0097
  have p0099 :=
    @g_breq2 (.cv w) (.cv x) (.cv z) (.cv q)
  have p0100_e00_recanon : Nominal.NPrf (.imp (.objEq w x) (syn_wb (syn_wbr (.cv z) (.cv q) (.cv w)) (syn_wbr (.cv z) (.cv q) (.cv x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0099
  have p0100 :=
    @g_biimpcd (.objEq w x) (syn_wbr (.cv z) (.cv q) (.cv w)) (syn_wbr (.cv z) (.cv q) (.cv x)) p0100_e00_recanon
  have p0101 :=
    @g_breq2 (.cv w) (.cv y) (.cv z) (.cv q)
  have p0102_e00_recanon : Nominal.NPrf (.imp (.objEq w y) (syn_wb (syn_wbr (.cv z) (.cv q) (.cv w)) (syn_wbr (.cv z) (.cv q) (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex syn_cphi
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0101
  have p0102 :=
    @g_biimpcd (.objEq w y) (syn_wbr (.cv z) (.cv q) (.cv w)) (syn_wbr (.cv z) (.cv q) (.cv y)) p0102_e00_recanon
  have p0103 :=
    @g_orim12d (syn_wbr (.cv z) (.cv q) (.cv w)) (.objEq w x) (syn_wbr (.cv z) (.cv q) (.cv x)) (.objEq w y) (syn_wbr (.cv z) (.cv q) (.cv y)) p0100 p0102
  have p0104 :=
    @g_com12 (syn_wbr (.cv z) (.cv q) (.cv w)) (syn_wo (.objEq w x) (.objEq w y)) (syn_wo (syn_wbr (.cv z) (.cv q) (.cv x)) (syn_wbr (.cv z) (.cv q) (.cv y))) p0103
  have p0105_e00_recanon : Nominal.NPrf (syn_wb (.classMem (.cv w) (syn_cpr (.cv x) (.cv y))) (syn_wo (.objEq w x) (.objEq w y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cpr syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn syn_wo
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        ·
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          ·
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            ·
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            ·
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          ·
            exact Nominal.RecanonTransportDev.TRecanonWff.same _
      )
      p0098
  have p0105 :=
    @g_sylbi (.classMem (.cv w) (syn_cpr (.cv x) (.cv y))) (syn_wo (.objEq w x) (.objEq w y)) (.imp (syn_wbr (.cv z) (.cv q) (.cv w)) (syn_wo (syn_wbr (.cv z) (.cv q) (.cv x)) (syn_wbr (.cv z) (.cv q) (.cv y)))) p0105_e00_recanon p0104
  have p0106 :=
    @g_syl6bi (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y)))) (.classMem (.cv w) A) (.classMem (.cv w) (syn_cpr (.cv x) (.cv y))) (.imp (syn_wbr (.cv z) (.cv q) (.cv w)) (syn_wo (syn_wbr (.cv z) (.cv q) (.cv x)) (syn_wbr (.cv z) (.cv q) (.cv y)))) p0096 p0105
  have p0107 :=
    @g_com23 (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y)))) (.classMem (.cv w) A) (syn_wbr (.cv z) (.cv q) (.cv w)) (syn_wo (syn_wbr (.cv z) (.cv q) (.cv x)) (syn_wbr (.cv z) (.cv q) (.cv y))) p0106
  have p0108 :=
    @g_mpdd (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y)))) (syn_wbr (.cv z) (.cv q) (.cv w)) (.classMem (.cv w) A) (syn_wo (syn_wbr (.cv z) (.cv q) (.cv x)) (syn_wbr (.cv z) (.cv q) (.cv y))) p0094 p0107
  have p0109 :=
    @g_exlimdv (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y)))) (syn_wbr (.cv z) (.cv q) (.cv w)) (syn_wo (syn_wbr (.cv z) (.cv q) (.cv x)) (syn_wbr (.cv z) (.cv q) (.cv y))) w dv_cache_0010 dv_cache_0011 p0108
  have p0110 :=
    @g_syl5bi (.classMem (.cv z) (syn_cdm (.cv q))) (syn_wex w (syn_wbr (.cv z) (.cv q) (.cv w))) (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y)))) (syn_wo (syn_wbr (.cv z) (.cv q) (.cv x)) (syn_wbr (.cv z) (.cv q) (.cv y))) p0089 p0109
  have p0111 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y)))) (.classMem (.cv z) (syn_cdm (.cv q))) (syn_wo (syn_wbr (.cv z) (.cv q) (.cv x)) (syn_wbr (.cv z) (.cv q) (.cv y))) p0088 p0110
  have p0112 :=
    @g_orel1 (syn_wbr (.cv z) (.cv q) (.cv x)) (syn_wbr (.cv z) (.cv q) (.cv y))
  have p0113 :=
    @g_sylc (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (syn_wa (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y)))) (.neg (syn_wbr (.cv z) (.cv q) (.cv x))) (syn_wo (syn_wbr (.cv z) (.cv q) (.cv x)) (syn_wbr (.cv z) (.cv q) (.cv y))) (syn_wbr (.cv z) (.cv q) (.cv y)) p0083 p0111 p0112
  have p0114 :=
    @g_expr (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B) (syn_wbr (.cv z) (.cv p) (.cv y)) (syn_wbr (.cv z) (.cv q) (.cv y)) p0113
  have p0115 :=
    @g_fnbrfvb B (.cv z) (.cv y) (.cv p)
  have p0116 :=
    @g_sylan (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (syn_wfn (.cv p) B) (.classMem (.cv z) B) (syn_wb (.classEq (syn_cfv (.cv p) (.cv z)) (.cv y)) (syn_wbr (.cv z) (.cv p) (.cv y))) p0042 p0115
  have p0117 :=
    @g_fnbrfvb B (.cv z) (.cv y) (.cv q)
  have p0118 :=
    @g_sylan (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (syn_wfn (.cv q) B) (.classMem (.cv z) B) (syn_wb (.classEq (syn_cfv (.cv q) (.cv z)) (.cv y)) (syn_wbr (.cv z) (.cv q) (.cv y))) p0045 p0117
  have p0119 :=
    @g_n_3imtr4d (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B)) (syn_wbr (.cv z) (.cv p) (.cv y)) (syn_wbr (.cv z) (.cv q) (.cv y)) (.classEq (syn_cfv (.cv p) (.cv z)) (.cv y)) (.classEq (syn_cfv (.cv q) (.cv z)) (.cv y)) p0114 p0116 p0118
  have p0120 :=
    @g_impr (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B) (.classEq (syn_cfv (.cv p) (.cv z)) (.cv y)) (.classEq (syn_cfv (.cv q) (.cv z)) (.cv y)) p0119
  have p0121 :=
    @g_eqtr4d (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (syn_wa (.classMem (.cv z) B) (.classEq (syn_cfv (.cv p) (.cv z)) (.cv y)))) (syn_cfv (.cv p) (.cv z)) (.cv y) (syn_cfv (.cv q) (.cv z)) p0068 p0120
  have p0122 :=
    @g_expr (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B) (.classEq (syn_cfv (.cv p) (.cv z)) (.cv y)) (.classEq (syn_cfv (.cv p) (.cv z)) (syn_cfv (.cv q) (.cv z))) p0121
  have p0123 :=
    @g_jaod (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B)) (.classEq (syn_cfv (.cv p) (.cv z)) (.cv x)) (.classEq (syn_cfv (.cv p) (.cv z)) (syn_cfv (.cv q) (.cv z))) (.classEq (syn_cfv (.cv p) (.cv z)) (.cv y)) p0067 p0122
  have p0124 :=
    @g_sylbid (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B)) (.classMem (syn_cfv (.cv p) (.cv z)) A) (syn_wo (.classEq (syn_cfv (.cv p) (.cv z)) (.cv x)) (.classEq (syn_cfv (.cv p) (.cv z)) (.cv y))) (.classEq (syn_cfv (.cv p) (.cv z)) (syn_cfv (.cv q) (.cv z))) p0052 p0123
  have p0125 :=
    @g_mpd (syn_wa (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.classMem (.cv z) B)) (.classMem (syn_cfv (.cv p) (.cv z)) A) (.classEq (syn_cfv (.cv p) (.cv z)) (syn_cfv (.cv q) (.cv z))) p0047 p0124
  have p0126 :=
    @g_eqfnfvd (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) z B (.cv p) (.cv q) dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 p0042 p0045 p0125
  have p0127_e00_recanon : Nominal.NPrf (.imp (syn_wa (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (.objEq p q)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa
        simp (config := { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.same _
        ·
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
      )
      p0126
  have p0127 :=
    @g_expcom (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (syn_wa (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))) (.objEq p q) p0127_e00_recanon
  have p0128 :=
    @g_syl2an (syn_wa (.classMem (.cv p) (syn_co A (syn_cmap) B)) (.classMem (.cv q) (syn_co A (syn_cmap) B))) (syn_wa (syn_wf (.cv p) B A) (syn_wf (.cv q) B A)) (.classEq (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))) (.imp (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (.objEq p q)) (syn_wa (.classEq (.cv z) (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))) (.classEq (.cv z) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x))))) p0038 p0039 p0127
  have p0129 :=
    @g_an4s (.classMem (.cv p) (syn_co A (syn_cmap) B)) (.classMem (.cv q) (syn_co A (syn_cmap) B)) (.classEq (.cv z) (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x)))) (.classEq (.cv z) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))) (.imp (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (.objEq p q)) p0128
  have p0130 :=
    @g_com12 (syn_wa (syn_wa (.classMem (.cv p) (syn_co A (syn_cmap) B)) (.classEq (.cv z) (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv q) (syn_co A (syn_cmap) B)) (.classEq (.cv z) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (.objEq p q) p0129
  have p0131 :=
    @g_syl5 (syn_wa (syn_wbr (.cv z) (syn_ccnv W) (.cv p)) (syn_wbr (.cv z) (syn_ccnv W) (.cv q))) (syn_wa (syn_wa (.classMem (.cv p) (syn_co A (syn_cmap) B)) (.classEq (.cv z) (syn_cima (syn_ccnv (.cv p)) (syn_csn (.cv x))))) (syn_wa (.classMem (.cv q) (syn_co A (syn_cmap) B)) (.classEq (.cv z) (syn_cima (syn_ccnv (.cv q)) (syn_csn (.cv x)))))) (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (.objEq p q) p0035 p0130
  have p0132 :=
    @g_alrimiv (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (.imp (syn_wa (syn_wbr (.cv z) (syn_ccnv W) (.cv p)) (syn_wbr (.cv z) (syn_ccnv W) (.cv q))) (.objEq p q)) q dv_cache_0016 p0131
  have p0133 :=
    @g_alrimivv (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (.all q (.imp (syn_wa (syn_wbr (.cv z) (syn_ccnv W) (.cv p)) (syn_wbr (.cv z) (syn_ccnv W) (.cv q))) (.objEq p q))) z p dv_cache_0017 dv_cache_0018 p0132
  have p0134 :=
    @g_dffun2 z p q (syn_ccnv W) dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
  have p0135 :=
    @g_sylibr (syn_wa (syn_wne (.cv x) (.cv y)) (.classEq A (syn_cpr (.cv x) (.cv y)))) (.all z (.all p (.all q (.imp (syn_wa (syn_wbr (.cv z) (syn_ccnv W) (.cv p)) (syn_wbr (.cv z) (syn_ccnv W) (.cv q))) (.objEq p q))))) (syn_wfun (syn_ccnv W)) p0133 p0134
  exact p0135

#print axioms g_enprmaplem3

end NFChoice.DirectNominalPrf.WPPReplay
