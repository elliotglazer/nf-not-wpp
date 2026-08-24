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
import NominalNFLiteralBaseFour
import NominalNFLiteralXpViaCompletenessDev003
import NominalNFLiteralRemainingViaCompletenessDev001
import NominalDefinitionLeafHandlersCanonical001
import NominalDefinitionLeafHandlersObjExtCompat001
import NominalRecanonTransportCompat001
import NominalWPPReplayChunk010Compact001Part062

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

noncomputable def g_xpundi
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.classEq (syn_cxp A (syn_cun B C)) (syn_cun (syn_cxp A B) (syn_cxp A C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cun B C)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_cun B C)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0006 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elun (.cv y) B C
  have p0001 :=
    @g_anbi2i (.classMem (.cv y) (syn_cun B C)) (syn_wo (.classMem (.cv y) B) (.classMem (.cv y) C)) (.classMem (.cv x) A) p0000
  have p0002 :=
    @g_andi (.classMem (.cv x) A) (.classMem (.cv y) B) (.classMem (.cv y) C)
  have p0003 :=
    @g_bitri (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) (syn_cun B C))) (syn_wa (.classMem (.cv x) A) (syn_wo (.classMem (.cv y) B) (.classMem (.cv y) C))) (syn_wo (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) C))) p0001 p0002
  have p0004 :=
    @g_opabbii (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) (syn_cun B C))) (syn_wo (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) C))) x y p0003
  have p0005 :=
    @g_unopab (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) C)) x y
  have p0006 :=
    @g_eqtr4i (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) (syn_cun B C)))) (syn_copab x y (syn_wo (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) C)))) (syn_cun (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))) (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) C)))) p0004 p0005
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xp x y A (syn_cun B C) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xp x y A B dv_cache_0001 dv_cache_0002 dv_cache_0006 dv_cache_0007 dv_cache_0005
  have p0009 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xp x y A C dv_cache_0001 dv_cache_0002 dv_cache_0008 dv_cache_0009 dv_cache_0005
  have p0010 :=
    @g_uneq12i (syn_cxp A B) (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))) (syn_cxp A C) (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) C))) p0008 p0009
  have p0011 :=
    @g_n_3eqtr4i (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) (syn_cun B C)))) (syn_cun (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))) (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) C)))) (syn_cxp A (syn_cun B C)) (syn_cun (syn_cxp A B) (syn_cxp A C)) p0006 p0007 p0010
  exact p0011

noncomputable def g_xpundir
    (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.classEq (syn_cxp (syn_cun A B) C) (syn_cun (syn_cxp A C) (syn_cxp B C))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ ((syn_cun A B)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cun A B)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (C).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_C, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0006 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elun (.cv x) A B
  have p0001 :=
    @g_anbi1i (.classMem (.cv x) (syn_cun A B)) (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv y) C) p0000
  have p0002 :=
    @g_andir (.classMem (.cv x) A) (.classMem (.cv x) B) (.classMem (.cv y) C)
  have p0003 :=
    @g_bitri (syn_wa (.classMem (.cv x) (syn_cun A B)) (.classMem (.cv y) C)) (syn_wa (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) B)) (.classMem (.cv y) C)) (syn_wo (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) C)) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C))) p0001 p0002
  have p0004 :=
    @g_opabbii (syn_wa (.classMem (.cv x) (syn_cun A B)) (.classMem (.cv y) C)) (syn_wo (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) C)) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C))) x y p0003
  have p0005 :=
    @g_unopab (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) C)) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C)) x y
  have p0006 :=
    @g_eqtr4i (syn_copab x y (syn_wa (.classMem (.cv x) (syn_cun A B)) (.classMem (.cv y) C))) (syn_copab x y (syn_wo (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) C)) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C)))) (syn_cun (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) C))) (syn_copab x y (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C)))) p0004 p0005
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xp x y (syn_cun A B) C dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xp x y A C dv_cache_0006 dv_cache_0007 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0009 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xp x y B C dv_cache_0008 dv_cache_0009 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0010 :=
    @g_uneq12i (syn_cxp A C) (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) C))) (syn_cxp B C) (syn_copab x y (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C))) p0008 p0009
  have p0011 :=
    @g_n_3eqtr4i (syn_copab x y (syn_wa (.classMem (.cv x) (syn_cun A B)) (.classMem (.cv y) C))) (syn_cun (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) C))) (syn_copab x y (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C)))) (syn_cxp (syn_cun A B) C) (syn_cun (syn_cxp A C) (syn_cxp B C)) p0006 p0007 p0010
  exact p0011

noncomputable def g_brinxp2
    (A : Class) (B : Class) (C : Class) (D : Class) (R : Class) :
    Nominal.NPrf (syn_wb (syn_wbr A (syn_cin R (syn_cxp C D)) B) (syn_w3a (.classMem A C) (.classMem B D) (syn_wbr A R B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv
  have p0000 :=
    @g_ancom (syn_wbr A R B) (syn_wbr A (syn_cxp C D) B)
  have p0001 :=
    @g_brxp A B C D
  have p0002 :=
    @g_anbi1i (syn_wbr A (syn_cxp C D) B) (syn_wa (.classMem A C) (.classMem B D)) (syn_wbr A R B) p0001
  have p0003 :=
    @g_bitri (syn_wa (syn_wbr A R B) (syn_wbr A (syn_cxp C D) B)) (syn_wa (syn_wbr A (syn_cxp C D) B) (syn_wbr A R B)) (syn_wa (syn_wa (.classMem A C) (.classMem B D)) (syn_wbr A R B)) p0000 p0002
  have p0004 :=
    @g_brin A B R (syn_cxp C D)
  have p0005 :=
    (by simpa [syn_wb, syn_w3a] using (Nominal.biimpRefl (syn_w3a (.classMem A C) (.classMem B D) (syn_wbr A R B))))
  have p0006 :=
    @g_n_3bitr4i (syn_wa (syn_wbr A R B) (syn_wbr A (syn_cxp C D) B)) (syn_wa (syn_wa (.classMem A C) (.classMem B D)) (syn_wbr A R B)) (syn_wbr A (syn_cin R (syn_cxp C D)) B) (syn_w3a (.classMem A C) (.classMem B D) (syn_wbr A R B)) p0003 p0004 p0005
  exact p0006

noncomputable def g_brinxp
    (A : Class) (B : Class) (C : Class) (D : Class) (R : Class) :
    Nominal.NPrf (.imp (syn_wa (.classMem A C) (.classMem B D)) (syn_wb (syn_wbr A R B) (syn_wbr A (syn_cin R (syn_cxp C D)) B))) := by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv
  have p0000 :=
    @g_brinxp2 A B C D R
  have p0001 :=
    (by simpa [syn_wb, syn_w3a] using (Nominal.biimpRefl (syn_w3a (.classMem A C) (.classMem B D) (syn_wbr A R B))))
  have p0002 :=
    @g_bitri (syn_wbr A (syn_cin R (syn_cxp C D)) B) (syn_w3a (.classMem A C) (.classMem B D) (syn_wbr A R B)) (syn_wa (syn_wa (.classMem A C) (.classMem B D)) (syn_wbr A R B)) p0000 p0001
  have p0003 :=
    @g_baibr (syn_wbr A (syn_cin R (syn_cxp C D)) B) (syn_wa (.classMem A C) (.classMem B D)) (syn_wbr A R B) p0002
  exact p0003

noncomputable def g_xp0r
    (A : Class) :
    Nominal.NPrf (.classEq (syn_cxp (syn_c0) A) (syn_c0)) := by
  let proofSupport : Finset Var := A.fv
  let z : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport := by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_z_ne_x : z ≠ x := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_x_ne_y : x ≠ y := by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ ((Class.cv z)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Class.cv z)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_c0)).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_c0)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0008 : z ∉ ((syn_cxp (syn_c0) A)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((syn_c0)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_elxp x y (.cv z) (syn_c0) A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 :=
    @g_noel (.cv x)
  have p0002 :=
    @g_simprl (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) (.classMem (.cv x) (syn_c0)) (.classMem (.cv y) A)
  have p0003 :=
    @g_mto (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_c0)) (.classMem (.cv y) A))) (.classMem (.cv x) (syn_c0)) p0001 p0002
  have p0004 :=
    @g_nex (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_c0)) (.classMem (.cv y) A))) y p0003
  have p0005 :=
    @g_nex (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_c0)) (.classMem (.cv y) A)))) x p0004
  have p0006 :=
    @g_noel (.cv z)
  have p0007 :=
    @g_n_2false (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_c0)) (.classMem (.cv y) A))))) (.classMem (.cv z) (syn_c0)) p0005 p0006
  have p0008 :=
    @g_bitri (.classMem (.cv z) (syn_cxp (syn_c0) A)) (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) (syn_wa (.classMem (.cv x) (syn_c0)) (.classMem (.cv y) A))))) (.classMem (.cv z) (syn_c0)) p0000 p0007
  have p0009 :=
    @g_eqriv z (syn_cxp (syn_c0) A) (syn_c0) dv_cache_0008 dv_cache_0009 p0008
  exact p0009

noncomputable def g_xpvv
     :
    Nominal.NPrf (.classEq (syn_cxp (syn_cvv) (syn_cvv)) (syn_cvv)) := by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have dv_cache_0001 : x ∉ ((syn_cxp (syn_cvv) (syn_cvv))).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_eqv x (syn_cxp (syn_cvv) (syn_cvv)) dv_cache_0001
  have p0001 :=
    @g_opeq (.cv x)
  have p0002 :=
    @g_vex x
  have p0003 :=
    @g_proj1ex (.cv x) p0002
  have p0004 :=
    @g_proj2ex (.cv x) p0002
  have p0005 :=
    @g_opelxp (syn_cproj1 (.cv x)) (syn_cproj2 (.cv x)) (syn_cvv) (syn_cvv)
  have p0006 :=
    @g_mpbir2an (.classMem (syn_cop (syn_cproj1 (.cv x)) (syn_cproj2 (.cv x))) (syn_cxp (syn_cvv) (syn_cvv))) (.classMem (syn_cproj1 (.cv x)) (syn_cvv)) (.classMem (syn_cproj2 (.cv x)) (syn_cvv)) p0003 p0004 p0005
  have p0007 :=
    @g_eqeltri (.cv x) (syn_cop (syn_cproj1 (.cv x)) (syn_cproj2 (.cv x))) (syn_cxp (syn_cvv) (syn_cvv)) p0001 p0006
  have p0008 :=
    @g_mpgbir (.classEq (syn_cxp (syn_cvv) (syn_cvv)) (syn_cvv)) (.classMem (.cv x) (syn_cxp (syn_cvv) (syn_cvv))) x p0000 p0007
  exact p0008

noncomputable def g_ssrel
    (x : Var) (y : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (syn_wb (syn_wss A B) (.all x (.all y (.imp (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (syn_cop (.cv x) (.cv y)) B))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_z : x ≠ z :=
    Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_z : y ≠ z :=
    Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((syn_wss A B)).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_wss A B)).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Wff.classEq (.cv x) (syn_cproj1 (.cv z)))).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, (Ne.symm dv_x_y), fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_cproj1 (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.all y (.imp (.classMem (syn_cop (syn_cproj1 (.cv z)) (.cv y)) A) (.classMem (syn_cop (syn_cproj1 (.cv z)) (.cv y)) B)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z, dv_x_y, dv_A_x, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_cproj2 (.cv z))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj2, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Wff.imp (.classMem (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))) A) (.classMem (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))) B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1, NFChoice.Compiler.CoreFVSimp.fv_class_cv, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj2, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_z, dv_A_y, dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : z ∉ (A).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : z ∉ ((Wff.all x (.all y (.imp (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (syn_cop (.cv x) (.cv y)) B))))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_A, fresh_z_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_ssel A B (syn_cop (.cv x) (.cv y))
  have p0001 :=
    @g_alrimivv (syn_wss A B) (.imp (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (syn_cop (.cv x) (.cv y)) B)) x y dv_cache_0001 dv_cache_0002 p0000
  have p0002 :=
    @g_vex z
  have p0003 :=
    @g_proj1ex (.cv z) p0002
  have p0004 :=
    @g_opeq1 (.cv x) (syn_cproj1 (.cv z)) (.cv y)
  have p0005 :=
    @g_eleq1d (.classEq (.cv x) (syn_cproj1 (.cv z))) (syn_cop (.cv x) (.cv y)) (syn_cop (syn_cproj1 (.cv z)) (.cv y)) A p0004
  have p0006 :=
    @g_eleq1d (.classEq (.cv x) (syn_cproj1 (.cv z))) (syn_cop (.cv x) (.cv y)) (syn_cop (syn_cproj1 (.cv z)) (.cv y)) B p0004
  have p0007 :=
    @g_imbi12d (.classEq (.cv x) (syn_cproj1 (.cv z))) (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (syn_cop (syn_cproj1 (.cv z)) (.cv y)) A) (.classMem (syn_cop (.cv x) (.cv y)) B) (.classMem (syn_cop (syn_cproj1 (.cv z)) (.cv y)) B) p0005 p0006
  have p0008 :=
    @g_albidv (.classEq (.cv x) (syn_cproj1 (.cv z))) (.imp (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (syn_cop (.cv x) (.cv y)) B)) (.imp (.classMem (syn_cop (syn_cproj1 (.cv z)) (.cv y)) A) (.classMem (syn_cop (syn_cproj1 (.cv z)) (.cv y)) B)) y dv_cache_0003 p0007
  have p0009 :=
    @g_spcv (.all y (.imp (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (syn_cop (.cv x) (.cv y)) B))) (.all y (.imp (.classMem (syn_cop (syn_cproj1 (.cv z)) (.cv y)) A) (.classMem (syn_cop (syn_cproj1 (.cv z)) (.cv y)) B))) x (syn_cproj1 (.cv z)) dv_cache_0004 dv_cache_0005 p0003 p0008
  have p0010 :=
    @g_proj2ex (.cv z) p0002
  have p0011 :=
    @g_opeq2 (.cv y) (syn_cproj2 (.cv z)) (syn_cproj1 (.cv z))
  have p0012 :=
    @g_eleq1d (.classEq (.cv y) (syn_cproj2 (.cv z))) (syn_cop (syn_cproj1 (.cv z)) (.cv y)) (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))) A p0011
  have p0013 :=
    @g_eleq1d (.classEq (.cv y) (syn_cproj2 (.cv z))) (syn_cop (syn_cproj1 (.cv z)) (.cv y)) (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))) B p0011
  have p0014 :=
    @g_imbi12d (.classEq (.cv y) (syn_cproj2 (.cv z))) (.classMem (syn_cop (syn_cproj1 (.cv z)) (.cv y)) A) (.classMem (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))) A) (.classMem (syn_cop (syn_cproj1 (.cv z)) (.cv y)) B) (.classMem (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))) B) p0012 p0013
  have p0015 :=
    @g_spcv (.imp (.classMem (syn_cop (syn_cproj1 (.cv z)) (.cv y)) A) (.classMem (syn_cop (syn_cproj1 (.cv z)) (.cv y)) B)) (.imp (.classMem (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))) A) (.classMem (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))) B)) y (syn_cproj2 (.cv z)) dv_cache_0006 dv_cache_0007 p0010 p0014
  have p0016 :=
    @g_syl (.all x (.all y (.imp (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (syn_cop (.cv x) (.cv y)) B)))) (.all y (.imp (.classMem (syn_cop (syn_cproj1 (.cv z)) (.cv y)) A) (.classMem (syn_cop (syn_cproj1 (.cv z)) (.cv y)) B))) (.imp (.classMem (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))) A) (.classMem (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))) B)) p0009 p0015
  have p0017 :=
    @g_opeq (.cv z)
  have p0018 :=
    @g_eleq1i (.cv z) (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))) A p0017
  have p0019 :=
    @g_eleq1i (.cv z) (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))) B p0017
  have p0020 :=
    @g_n_3imtr4g (.all x (.all y (.imp (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (syn_cop (.cv x) (.cv y)) B)))) (.classMem (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))) A) (.classMem (syn_cop (syn_cproj1 (.cv z)) (syn_cproj2 (.cv z))) B) (.classMem (.cv z) A) (.classMem (.cv z) B) p0016 p0018 p0019
  have p0021 :=
    @g_ssrdv (.all x (.all y (.imp (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (syn_cop (.cv x) (.cv y)) B)))) z A B dv_cache_0008 dv_cache_0009 dv_cache_0010 p0020
  have p0022 :=
    @g_impbii (syn_wss A B) (.all x (.all y (.imp (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (syn_cop (.cv x) (.cv y)) B)))) p0001 p0021
  exact p0022

noncomputable def g_eqrel
    (x : Var) (y : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (syn_wb (.classEq A B) (.all x (.all y (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (syn_cop (.cv x) (.cv y)) B))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ A.fv ∪ B.fv
  have dv_cache_0001 : x ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @g_ssrel x y A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @g_ssrel x y B A dv_cache_0003 dv_cache_0004 dv_cache_0001 dv_cache_0002 dv_cache_0005
  have p0002 :=
    @g_anbi12i (syn_wss A B) (.all x (.all y (.imp (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (syn_cop (.cv x) (.cv y)) B)))) (syn_wss B A) (.all x (.all y (.imp (.classMem (syn_cop (.cv x) (.cv y)) B) (.classMem (syn_cop (.cv x) (.cv y)) A)))) p0000 p0001
  have p0003 :=
    @g_eqss A B
  have p0004 :=
    @g_n_2albiim (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (syn_cop (.cv x) (.cv y)) B) x y
  have p0005 :=
    @g_n_3bitr4i (syn_wa (syn_wss A B) (syn_wss B A)) (syn_wa (.all x (.all y (.imp (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (syn_cop (.cv x) (.cv y)) B)))) (.all x (.all y (.imp (.classMem (syn_cop (.cv x) (.cv y)) B) (.classMem (syn_cop (.cv x) (.cv y)) A))))) (.classEq A B) (.all x (.all y (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (syn_cop (.cv x) (.cv y)) B)))) p0002 p0003 p0004
  exact p0005

noncomputable def g_ssopr
    (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf (syn_wb (syn_wss A B) (.all x (.all y (.all z (.imp (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A) (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B)))))) := by
  let proofSupport : Finset Var := ({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ A.fv ∪ B.fv
  let w : Var := freshVar proofSupport 0
  have fresh_w : w ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_w : x ≠ w :=
    Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_w : y ≠ w :=
    Ne.symm fresh_w_ne_y
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_z_ne_w : z ≠ w :=
    Ne.symm fresh_w_ne_z
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have dv_cache_0001 : w ∉ (A).fv := by
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_A, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ (A).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_A_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : w ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ (B).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, dv_B_z, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0005 : w ≠ z := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show w ≠ z from (by exact fresh_w_ne_z))
  have dv_cache_0006 : x ∉ ((Class.cv w)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Class.cv w)).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_w, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0008 : x ≠ y := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0009 : x ∉ ((Wff.imp (.classMem (syn_cop (.cv w) (.cv z)) A) (.classMem (syn_cop (.cv w) (.cv z)) B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_w, dv_x_z, dv_A_x, dv_B_x, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((Wff.imp (.classMem (syn_cop (.cv w) (.cv z)) A) (.classMem (syn_cop (.cv w) (.cv z)) B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (by
      have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_y_ne_w, dv_y_z, dv_A_y, dv_B_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0011 : w ∉ ((syn_cop (.cv x) (.cv y))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0012 : w ∉ ((Wff.imp (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A) (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (by
      have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, fresh_w_ne_z, fresh_w_not_A, fresh_w_not_B, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_ssrel w z A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @g_alcom (.imp (.classMem (syn_cop (.cv w) (.cv z)) A) (.classMem (syn_cop (.cv w) (.cv z)) B)) w z
  have p0002 :=
    @g_bitri (syn_wss A B) (.all w (.all z (.imp (.classMem (syn_cop (.cv w) (.cv z)) A) (.classMem (syn_cop (.cv w) (.cv z)) B)))) (.all z (.all w (.imp (.classMem (syn_cop (.cv w) (.cv z)) A) (.classMem (syn_cop (.cv w) (.cv z)) B)))) p0000 p0001
  have p0003 :=
    @g_vex w
  have p0004 :=
    @g_opeqex x y (.cv w) (syn_cvv) dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0005 :=
    Nominal.mp p0003 p0004
  have p0006 :=
    @g_a1bi (syn_wex x (syn_wex y (.classEq (.cv w) (syn_cop (.cv x) (.cv y))))) (.imp (.classMem (syn_cop (.cv w) (.cv z)) A) (.classMem (syn_cop (.cv w) (.cv z)) B)) p0005
  have p0007 :=
    @g_n_19_23vv (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) (.imp (.classMem (syn_cop (.cv w) (.cv z)) A) (.classMem (syn_cop (.cv w) (.cv z)) B)) x y dv_cache_0009 dv_cache_0010
  have p0008 :=
    @g_bitr4i (.imp (.classMem (syn_cop (.cv w) (.cv z)) A) (.classMem (syn_cop (.cv w) (.cv z)) B)) (.imp (syn_wex x (syn_wex y (.classEq (.cv w) (syn_cop (.cv x) (.cv y))))) (.imp (.classMem (syn_cop (.cv w) (.cv z)) A) (.classMem (syn_cop (.cv w) (.cv z)) B))) (.all x (.all y (.imp (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) (.imp (.classMem (syn_cop (.cv w) (.cv z)) A) (.classMem (syn_cop (.cv w) (.cv z)) B))))) p0006 p0007
  have p0009 :=
    @g_albii (.imp (.classMem (syn_cop (.cv w) (.cv z)) A) (.classMem (syn_cop (.cv w) (.cv z)) B)) (.all x (.all y (.imp (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) (.imp (.classMem (syn_cop (.cv w) (.cv z)) A) (.classMem (syn_cop (.cv w) (.cv z)) B))))) w p0008
  have p0010 :=
    @g_alrot3 (.imp (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) (.imp (.classMem (syn_cop (.cv w) (.cv z)) A) (.classMem (syn_cop (.cv w) (.cv z)) B))) w x y
  have p0011 :=
    @g_vex x
  have p0012 :=
    @g_vex y
  have p0013 :=
    @g_opex (.cv x) (.cv y) p0011 p0012
  have p0014 :=
    @g_opeq1 (.cv w) (syn_cop (.cv x) (.cv y)) (.cv z)
  have p0015 :=
    @g_eleq1d (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) (syn_cop (.cv w) (.cv z)) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A p0014
  have p0016 :=
    @g_eleq1d (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) (syn_cop (.cv w) (.cv z)) (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B p0014
  have p0017 :=
    @g_imbi12d (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) (.classMem (syn_cop (.cv w) (.cv z)) A) (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A) (.classMem (syn_cop (.cv w) (.cv z)) B) (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B) p0015 p0016
  have p0018 :=
    @g_ceqsalv (.imp (.classMem (syn_cop (.cv w) (.cv z)) A) (.classMem (syn_cop (.cv w) (.cv z)) B)) (.imp (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A) (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B)) w (syn_cop (.cv x) (.cv y)) dv_cache_0011 dv_cache_0012 p0013 p0017
  have p0019 :=
    @g_n_2albii (.all w (.imp (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) (.imp (.classMem (syn_cop (.cv w) (.cv z)) A) (.classMem (syn_cop (.cv w) (.cv z)) B)))) (.imp (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A) (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B)) x y p0018
  have p0020 :=
    @g_n_3bitri (.all w (.imp (.classMem (syn_cop (.cv w) (.cv z)) A) (.classMem (syn_cop (.cv w) (.cv z)) B))) (.all w (.all x (.all y (.imp (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) (.imp (.classMem (syn_cop (.cv w) (.cv z)) A) (.classMem (syn_cop (.cv w) (.cv z)) B)))))) (.all x (.all y (.all w (.imp (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) (.imp (.classMem (syn_cop (.cv w) (.cv z)) A) (.classMem (syn_cop (.cv w) (.cv z)) B)))))) (.all x (.all y (.imp (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A) (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B)))) p0009 p0010 p0019
  have p0021 :=
    @g_albii (.all w (.imp (.classMem (syn_cop (.cv w) (.cv z)) A) (.classMem (syn_cop (.cv w) (.cv z)) B))) (.all x (.all y (.imp (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A) (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B)))) z p0020
  have p0022 :=
    @g_alrot3 (.imp (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A) (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B)) z x y
  have p0023 :=
    @g_n_3bitri (syn_wss A B) (.all z (.all w (.imp (.classMem (syn_cop (.cv w) (.cv z)) A) (.classMem (syn_cop (.cv w) (.cv z)) B)))) (.all z (.all x (.all y (.imp (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A) (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B))))) (.all x (.all y (.all z (.imp (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) A) (.classMem (syn_cop (syn_cop (.cv x) (.cv y)) (.cv z)) B))))) p0002 p0021 p0022
  exact p0023

#print axioms g_ssopr

end NFChoice.DirectNominalPrf.WPPReplay
