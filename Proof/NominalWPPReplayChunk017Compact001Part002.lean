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
import NominalWPPReplayChunk017Compact001Part001

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

noncomputable def g_hndownexclndv
    (x : Var) (y : Var) (S : Class) (dv_S_x : x ∉ S.fv) (dv_S_y : y ∉ S.fv) (dv_x_y : x ≠ y) (hyp_hndownexclndv_1 : Nominal.NPrf (.classMem S (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (syn_cvv)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ S.fv
  let g : Var := freshVar proofSupport 0
  have fresh_g : g ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_g_ne_x : g ≠ x := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_g : x ≠ g :=
    Ne.symm fresh_g_ne_x
  have fresh_g_ne_y : g ≠ y := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_g : y ≠ g :=
    Ne.symm fresh_g_ne_y
  have fresh_g_not_S : g ∉ S.fv := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((Wff.classEq (.cv g) S)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_g, dv_S_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Wff.classEq (.cv g) S)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_g, dv_S_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : g ≠ x := by
    clear dv_cache_0001 dv_cache_0002
    exact (show g ≠ x from (by exact fresh_g_ne_x))
  have dv_cache_0004 : g ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show g ≠ y from (by exact fresh_g_ne_y))
  have dv_cache_0005 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0006 : g ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : g ∉ ((Wff.classMem (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (syn_cvv))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_x, fresh_g_ne_y, fresh_g_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_id (.classEq (.cv g) S)
  have p0001 :=
    @g_breqd (.classEq (.cv g) S) (.cv g) S (syn_csn (.cv x)) (syn_csn (.cv y)) p0000
  have p0002 :=
    @g_opabbidv (.classEq (.cv g) S) (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))) (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))) x y dv_cache_0001 dv_cache_0002 p0001
  have p0003 :=
    @g_eleq1d (.classEq (.cv g) S) (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (syn_cvv) p0002
  have p0004 :=
    @g_hndownexndv x y g dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0005 :=
    @g_vtoclg (.classMem (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (syn_cvv)) (.classMem (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (syn_cvv)) g S (syn_cvv) dv_cache_0006 dv_cache_0007 p0003 p0004
  have p0006 :=
    Nominal.mp hyp_hndownexclndv_1 p0005
  exact p0006

noncomputable def g_sidownrecoverclndv
    (x : Var) (y : Var) (D : Class) (S : Class) (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_S_x : x ∉ S.fv) (dv_S_y : y ∉ S.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (.classEq (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) S)) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ D.fv ∪ S.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let q : Var := freshVar proofSupport 2
  let r : Var := freshVar proofSupport 3
  have fresh_a : a ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_ne_x : a ≠ x := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_a : x ≠ a :=
    Ne.symm fresh_a_ne_x
  have fresh_a_ne_y : a ≠ y := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_a : y ≠ a :=
    Ne.symm fresh_a_ne_y
  have fresh_a_not_D : a ∉ D.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_S : a ∉ S.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_ne_x : b ≠ x := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_b : x ≠ b :=
    Ne.symm fresh_b_ne_x
  have fresh_b_ne_y : b ≠ y := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_b : y ≠ b :=
    Ne.symm fresh_b_ne_y
  have fresh_b_not_D : b ∉ D.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_not_S : b ∉ S.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_q : q ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_q_ne_x : q ≠ x := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_q : x ≠ q :=
    Ne.symm fresh_q_ne_x
  have fresh_q_ne_y : q ≠ y := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_q : y ≠ q :=
    Ne.symm fresh_q_ne_y
  have fresh_q_not_D : q ∉ D.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_not_S : q ∉ S.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_r : r ∉ proofSupport := by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
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
  have fresh_r_not_D : r ∉ D.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_not_S : r ∉ S.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_a_ne_b : a ≠ b := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_a : b ≠ a :=
    Ne.symm fresh_a_ne_b
  have fresh_a_ne_q : a ≠ q := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_q_ne_a : q ≠ a :=
    Ne.symm fresh_a_ne_q
  have fresh_a_ne_r : a ≠ r := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_r_ne_a : r ≠ a :=
    Ne.symm fresh_a_ne_r
  have fresh_b_ne_q : b ≠ q := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_q_ne_b : q ≠ b :=
    Ne.symm fresh_b_ne_q
  have fresh_b_ne_r : b ≠ r := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_r_ne_b : r ≠ b :=
    Ne.symm fresh_b_ne_r
  have fresh_q_ne_r : q ≠ r := by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_r_ne_q : r ≠ q :=
    Ne.symm fresh_q_ne_r
  have dv_cache_0001 : q ∉ ((Class.cv a)).fv := by
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : r ∉ ((Class.cv a)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : r ∉ ((Class.cv b)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : q ∉ ((syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_x, fresh_q_ne_y, fresh_q_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : r ∉ ((syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_x, fresh_r_ne_y, fresh_r_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : q ≠ r := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show q ≠ r from (by exact fresh_q_ne_r))
  have dv_cache_0008 : x ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_S_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_S_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : q ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show q ≠ x from (by exact fresh_q_ne_x))
  have dv_cache_0011 : q ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show q ≠ y from (by exact fresh_q_ne_y))
  have dv_cache_0012 : r ≠ x := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0013 : r ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
    exact (show r ≠ y from (by exact fresh_r_ne_y))
  have dv_cache_0014 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0015 : q ∉ ((syn_wbr (.cv a) S (.cv b))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (by
      have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_q_ne_a, fresh_q_ne_b, fresh_q_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0016 : r ∉ ((syn_wbr (.cv a) S (.cv b))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (by
      have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_r_ne_a, fresh_r_ne_b, fresh_r_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0017 : a ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0018 : b ∉ (D).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0019 : a ∉ ((syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_x, fresh_a_ne_y, fresh_a_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0020 : b ∉ ((syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_x, fresh_b_ne_y, fresh_b_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0021 : a ≠ b := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0022 : x ∉ ((syn_cuni (.cv a))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0023 : y ∉ ((syn_cuni (.cv a))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_a, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0024 : x ∉ ((syn_cuni (.cv b))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0025 : y ∉ ((syn_cuni (.cv b))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_b, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0026 : x ∉ ((syn_wbr (syn_csn (syn_cuni (.cv a))) S (syn_csn (syn_cuni (.cv b))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_a, fresh_x_ne_b, dv_S_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0027 : y ∉ ((syn_wbr (syn_csn (syn_cuni (.cv a))) S (syn_csn (syn_cuni (.cv b))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_a, fresh_y_ne_b, dv_S_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0028 : a ∉ ((syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_x, fresh_a_ne_y, fresh_a_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0029 : b ∉ ((syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_x, fresh_b_ne_y, fresh_b_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0030 : a ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0031 : b ∉ (S).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0032 : a ∉ ((syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
    exact (by
      have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_a_not_S, fresh_a_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0033 : b ∉ ((syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (by
      have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_b_not_S, fresh_b_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_brsi q r (.cv a) (.cv b) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 :=
    @g_biimpi (syn_wbr (.cv a) (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) (.cv b)) (syn_wex q (syn_wex r (syn_w3a (.classEq (.cv a) (syn_csn (.cv q))) (.classEq (.cv b) (syn_csn (.cv r))) (syn_wbr (.cv q) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (.cv r))))) p0000
  have p0002 :=
    @g_simp3 (.classEq (.cv a) (syn_csn (.cv q))) (.classEq (.cv b) (syn_csn (.cv r))) (syn_wbr (.cv q) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (.cv r))
  have p0003 :=
    @g_hndownbrclndv x y S q r dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
  have p0004 :=
    @g_biimpi (syn_wbr (.cv q) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (.cv r)) (syn_wbr (syn_csn (.cv q)) S (syn_csn (.cv r))) p0003
  have p0005 :=
    @g_syl (syn_w3a (.classEq (.cv a) (syn_csn (.cv q))) (.classEq (.cv b) (syn_csn (.cv r))) (syn_wbr (.cv q) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (.cv r))) (syn_wbr (.cv q) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (.cv r)) (syn_wbr (syn_csn (.cv q)) S (syn_csn (.cv r))) p0002 p0004
  have p0006 :=
    @g_simp1 (.classEq (.cv a) (syn_csn (.cv q))) (.classEq (.cv b) (syn_csn (.cv r))) (syn_wbr (.cv q) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (.cv r))
  have p0007 :=
    @g_simp2 (.classEq (.cv a) (syn_csn (.cv q))) (.classEq (.cv b) (syn_csn (.cv r))) (syn_wbr (.cv q) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (.cv r))
  have p0008 :=
    @g_breq12d (syn_w3a (.classEq (.cv a) (syn_csn (.cv q))) (.classEq (.cv b) (syn_csn (.cv r))) (syn_wbr (.cv q) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (.cv r))) (.cv a) (syn_csn (.cv q)) (.cv b) (syn_csn (.cv r)) S p0006 p0007
  have p0009 :=
    @g_biimprd (syn_w3a (.classEq (.cv a) (syn_csn (.cv q))) (.classEq (.cv b) (syn_csn (.cv r))) (syn_wbr (.cv q) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (.cv r))) (syn_wbr (.cv a) S (.cv b)) (syn_wbr (syn_csn (.cv q)) S (syn_csn (.cv r))) p0008
  have p0010 :=
    @g_mpd (syn_w3a (.classEq (.cv a) (syn_csn (.cv q))) (.classEq (.cv b) (syn_csn (.cv r))) (syn_wbr (.cv q) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (.cv r))) (syn_wbr (syn_csn (.cv q)) S (syn_csn (.cv r))) (syn_wbr (.cv a) S (.cv b)) p0005 p0009
  have p0011 :=
    @g_exlimivv (syn_w3a (.classEq (.cv a) (syn_csn (.cv q))) (.classEq (.cv b) (syn_csn (.cv r))) (syn_wbr (.cv q) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (.cv r))) (syn_wbr (.cv a) S (.cv b)) q r dv_cache_0015 dv_cache_0016 p0010
  have p0012 :=
    @g_syl (syn_wbr (.cv a) (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) (.cv b)) (syn_wex q (syn_wex r (syn_w3a (.classEq (.cv a) (syn_csn (.cv q))) (.classEq (.cv b) (syn_csn (.cv r))) (syn_wbr (.cv q) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (.cv r))))) (syn_wbr (.cv a) S (.cv b)) p0001 p0011
  have p0013 :=
    @g_a1i (.imp (syn_wbr (.cv a) (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) (.cv b)) (syn_wbr (.cv a) S (.cv b))) (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) p0012
  have p0014 :=
    @g_simpr (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (syn_wbr (.cv a) S (.cv b))
  have p0015 :=
    @g_simpl (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (syn_wbr (.cv a) S (.cv b))
  have p0016 :=
    @g_simpr (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (syn_wbr (.cv a) S (.cv b))
  have p0017 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv a) S (.cv b))))
  have p0018 :=
    @g_biimpi (syn_wbr (.cv a) S (.cv b)) (.classMem (syn_cop (.cv a) (.cv b)) S) p0017
  have p0019 :=
    @g_syl (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (syn_wbr (.cv a) S (.cv b))) (syn_wbr (.cv a) S (.cv b)) (.classMem (syn_cop (.cv a) (.cv b)) S) p0016 p0018
  have p0020 :=
    @g_sseldd (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (syn_wbr (.cv a) S (.cv b))) S (syn_cxp (syn_cpw1 D) (syn_cpw1 D)) (syn_cop (.cv a) (.cv b)) p0015 p0019
  have p0021 :=
    @g_opelxp (.cv a) (.cv b) (syn_cpw1 D) (syn_cpw1 D)
  have p0022 :=
    @g_biimpi (.classMem (syn_cop (.cv a) (.cv b)) (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (syn_wa (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D))) p0021
  have p0023 :=
    @g_syl (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (syn_wbr (.cv a) S (.cv b))) (.classMem (syn_cop (.cv a) (.cv b)) (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (syn_wa (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D))) p0020 p0022
  have p0024 :=
    @g_pw1typedbrndv D (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) b a dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
  have p0025 :=
    @g_simpl (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D))
  have p0026 :=
    @g_pw1argclcl D (.cv a)
  have p0027 :=
    @g_syl (syn_wa (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D))) (.classMem (.cv a) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv a)) D) (.classEq (.cv a) (syn_csn (syn_cuni (.cv a))))) p0025 p0026
  have p0028 :=
    @g_simpl (.classMem (syn_cuni (.cv a)) D) (.classEq (.cv a) (syn_csn (syn_cuni (.cv a))))
  have p0029 :=
    @g_syl (syn_wa (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D))) (syn_wa (.classMem (syn_cuni (.cv a)) D) (.classEq (.cv a) (syn_csn (syn_cuni (.cv a))))) (.classMem (syn_cuni (.cv a)) D) p0027 p0028
  have p0030 :=
    @g_elex (syn_cuni (.cv a)) D
  have p0031 :=
    @g_syl (syn_wa (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D))) (.classMem (syn_cuni (.cv a)) D) (.classMem (syn_cuni (.cv a)) (syn_cvv)) p0029 p0030
  have p0032 :=
    @g_simpr (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D))
  have p0033 :=
    @g_pw1argclcl D (.cv b)
  have p0034 :=
    @g_syl (syn_wa (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D))) (.classMem (.cv b) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv b)) D) (.classEq (.cv b) (syn_csn (syn_cuni (.cv b))))) p0032 p0033
  have p0035 :=
    @g_simpl (.classMem (syn_cuni (.cv b)) D) (.classEq (.cv b) (syn_csn (syn_cuni (.cv b))))
  have p0036 :=
    @g_syl (syn_wa (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D))) (syn_wa (.classMem (syn_cuni (.cv b)) D) (.classEq (.cv b) (syn_csn (syn_cuni (.cv b))))) (.classMem (syn_cuni (.cv b)) D) p0034 p0035
  have p0037 :=
    @g_elex (syn_cuni (.cv b)) D
  have p0038 :=
    @g_syl (syn_wa (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D))) (.classMem (syn_cuni (.cv b)) D) (.classMem (syn_cuni (.cv b)) (syn_cvv)) p0036 p0037
  have p0039 :=
    @g_jca (syn_wa (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D))) (.classMem (syn_cuni (.cv a)) (syn_cvv)) (.classMem (syn_cuni (.cv b)) (syn_cvv)) p0031 p0038
  have p0040 :=
    @g_simpl (.classEq (.cv x) (syn_cuni (.cv a))) (.classEq (.cv y) (syn_cuni (.cv b)))
  have p0041 :=
    @g_sneqd (syn_wa (.classEq (.cv x) (syn_cuni (.cv a))) (.classEq (.cv y) (syn_cuni (.cv b)))) (.cv x) (syn_cuni (.cv a)) p0040
  have p0042 :=
    @g_simpr (.classEq (.cv x) (syn_cuni (.cv a))) (.classEq (.cv y) (syn_cuni (.cv b)))
  have p0043 :=
    @g_sneqd (syn_wa (.classEq (.cv x) (syn_cuni (.cv a))) (.classEq (.cv y) (syn_cuni (.cv b)))) (.cv y) (syn_cuni (.cv b)) p0042
  have p0044 :=
    @g_breq12d (syn_wa (.classEq (.cv x) (syn_cuni (.cv a))) (.classEq (.cv y) (syn_cuni (.cv b)))) (syn_csn (.cv x)) (syn_csn (syn_cuni (.cv a))) (syn_csn (.cv y)) (syn_csn (syn_cuni (.cv b))) S p0041 p0043
  have p0045 :=
    @g_eqid (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))
  have p0046 :=
    @g_brabga (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))) (syn_wbr (syn_csn (syn_cuni (.cv a))) S (syn_csn (syn_cuni (.cv b)))) x y (syn_cuni (.cv a)) (syn_cuni (.cv b)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (syn_cvv) (syn_cvv) dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0014 p0044 p0045
  have p0047 :=
    @g_syl (syn_wa (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D))) (syn_wa (.classMem (syn_cuni (.cv a)) (syn_cvv)) (.classMem (syn_cuni (.cv b)) (syn_cvv))) (syn_wb (syn_wbr (syn_cuni (.cv a)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (syn_cuni (.cv b))) (syn_wbr (syn_csn (syn_cuni (.cv a))) S (syn_csn (syn_cuni (.cv b))))) p0039 p0046
  have p0048 :=
    @g_bitrd (syn_wa (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D))) (syn_wbr (.cv a) (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) (.cv b)) (syn_wbr (syn_cuni (.cv a)) (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))) (syn_cuni (.cv b))) (syn_wbr (syn_csn (syn_cuni (.cv a))) S (syn_csn (syn_cuni (.cv b)))) p0024 p0047
  have p0049 :=
    @g_simpl (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D))
  have p0050 :=
    @g_pw1argclcl D (.cv a)
  have p0051 :=
    @g_syl (syn_wa (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D))) (.classMem (.cv a) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv a)) D) (.classEq (.cv a) (syn_csn (syn_cuni (.cv a))))) p0049 p0050
  have p0052 :=
    @g_simpr (.classMem (syn_cuni (.cv a)) D) (.classEq (.cv a) (syn_csn (syn_cuni (.cv a))))
  have p0053 :=
    @g_syl (syn_wa (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D))) (syn_wa (.classMem (syn_cuni (.cv a)) D) (.classEq (.cv a) (syn_csn (syn_cuni (.cv a))))) (.classEq (.cv a) (syn_csn (syn_cuni (.cv a)))) p0051 p0052
  have p0054 :=
    @g_simpr (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D))
  have p0055 :=
    @g_pw1argclcl D (.cv b)
  have p0056 :=
    @g_syl (syn_wa (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D))) (.classMem (.cv b) (syn_cpw1 D)) (syn_wa (.classMem (syn_cuni (.cv b)) D) (.classEq (.cv b) (syn_csn (syn_cuni (.cv b))))) p0054 p0055
  have p0057 :=
    @g_simpr (.classMem (syn_cuni (.cv b)) D) (.classEq (.cv b) (syn_csn (syn_cuni (.cv b))))
  have p0058 :=
    @g_syl (syn_wa (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D))) (syn_wa (.classMem (syn_cuni (.cv b)) D) (.classEq (.cv b) (syn_csn (syn_cuni (.cv b))))) (.classEq (.cv b) (syn_csn (syn_cuni (.cv b)))) p0056 p0057
  have p0059 :=
    @g_breq12d (syn_wa (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D))) (.cv a) (syn_csn (syn_cuni (.cv a))) (.cv b) (syn_csn (syn_cuni (.cv b))) S p0053 p0058
  have p0060 :=
    @g_bicomd (syn_wa (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D))) (syn_wbr (.cv a) S (.cv b)) (syn_wbr (syn_csn (syn_cuni (.cv a))) S (syn_csn (syn_cuni (.cv b)))) p0059
  have p0061 :=
    @g_bitrd (syn_wa (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D))) (syn_wbr (.cv a) (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) (.cv b)) (syn_wbr (syn_csn (syn_cuni (.cv a))) S (syn_csn (syn_cuni (.cv b)))) (syn_wbr (.cv a) S (.cv b)) p0048 p0060
  have p0062 :=
    @g_syl (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (syn_wbr (.cv a) S (.cv b))) (syn_wa (.classMem (.cv a) (syn_cpw1 D)) (.classMem (.cv b) (syn_cpw1 D))) (syn_wb (syn_wbr (.cv a) (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) (.cv b)) (syn_wbr (.cv a) S (.cv b))) p0023 p0061
  have p0063 :=
    @g_biimprd (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (syn_wbr (.cv a) S (.cv b))) (syn_wbr (.cv a) (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) (.cv b)) (syn_wbr (.cv a) S (.cv b)) p0062
  have p0064 :=
    @g_mpd (syn_wa (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (syn_wbr (.cv a) S (.cv b))) (syn_wbr (.cv a) S (.cv b)) (syn_wbr (.cv a) (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) (.cv b)) p0014 p0063
  have p0065 :=
    @g_ex (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (syn_wbr (.cv a) S (.cv b)) (syn_wbr (.cv a) (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) (.cv b)) p0064
  have p0066 :=
    @g_impbid (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (syn_wbr (.cv a) (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) (.cv b)) (syn_wbr (.cv a) S (.cv b)) p0013 p0065
  have p0067 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv a) (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) (.cv b))))
  have p0068 :=
    @g_bicomi (syn_wbr (.cv a) (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) (.cv b)) (.classMem (syn_cop (.cv a) (.cv b)) (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))) p0067
  have p0069 :=
    @g_a1i (syn_wb (.classMem (syn_cop (.cv a) (.cv b)) (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))) (syn_wbr (.cv a) (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) (.cv b))) (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) p0068
  have p0070 :=
    (by simpa [syn_wb, syn_wbr] using (Nominal.biimpRefl (syn_wbr (.cv a) S (.cv b))))
  have p0071 :=
    @g_bicomi (syn_wbr (.cv a) S (.cv b)) (.classMem (syn_cop (.cv a) (.cv b)) S) p0070
  have p0072 :=
    @g_a1i (syn_wb (.classMem (syn_cop (.cv a) (.cv b)) S) (syn_wbr (.cv a) S (.cv b))) (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) p0071
  have p0073 :=
    @g_n_3bitr4d (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) (syn_wbr (.cv a) (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) (.cv b)) (syn_wbr (.cv a) S (.cv b)) (.classMem (syn_cop (.cv a) (.cv b)) (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y)))))) (.classMem (syn_cop (.cv a) (.cv b)) S) p0066 p0069 p0072
  have p0074 :=
    @g_eqrelrdv (syn_wss S (syn_cxp (syn_cpw1 D) (syn_cpw1 D))) a b (syn_csi (syn_copab x y (syn_wbr (syn_csn (.cv x)) S (syn_csn (.cv y))))) S dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0021 p0073
  exact p0074

#print axioms g_sidownrecoverclndv

end NFChoice.DirectNominalPrf.WPPReplay
