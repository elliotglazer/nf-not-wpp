import NAR4C078C001Part024

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit
open NFChoice.Compiler.WPPCompactSyntaxFVExplicit
open NFChoice.Compiler.CoreFVSimp
open NFChoice.DefinitionLeaves.AlphaFocusedSupport
open NFChoice.DefinitionLeaves.AlphaFocusedFV
open NFChoice.DirectNominalPrf
open NFChoice.DirectNominalPrf.Nominal

theorem nb078_support_mem_0455 : (nb078_alpha_dummy_001) ∈ (({(nb078_alpha_dummy_287)} : Finset Var) ∪ ({(nb078_alpha_dummy_288)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_289) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_287)) (syn_ccnv (Class.cv (nb078_alpha_dummy_001))) (Class.cv (nb078_alpha_dummy_289))) (syn_wbr (Class.cv (nb078_alpha_dummy_289)) (Class.cv (nb078_alpha_dummy_001)) (Class.cv (nb078_alpha_dummy_288)))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wex]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0454) 2))
  ·
    rw [fv_syn_wa]
    apply Finset.mem_union_left
    rw [fv_syn_wbr]
    apply Finset.mem_union_right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb078_support_mem_0456 (g : Var) : g ∈ (((Class.cv g)).fv ∪ ((syn_ccnv (Class.cv g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0457 (g : Var) : g ∈ (({(nb078_alpha_dummy_290 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_291 g)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_292 g) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_290 g)) (syn_ccnv (Class.cv g)) (Class.cv (nb078_alpha_dummy_292 g))) (syn_wbr (Class.cv (nb078_alpha_dummy_292 g)) (Class.cv g) (Class.cv (nb078_alpha_dummy_291 g)))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wex]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0456 g) 2))
  ·
    rw [fv_syn_wa]
    apply Finset.mem_union_left
    rw [fv_syn_wbr]
    apply Finset.mem_union_right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb078_support_mem_0458 : (nb078_alpha_dummy_001) ∈ (({(nb078_alpha_dummy_367)} : Finset Var) ∪ ({(nb078_alpha_dummy_368)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_368)) (Class.cv (nb078_alpha_dummy_001)) (Class.cv (nb078_alpha_dummy_367)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0459 (g : Var) : g ∈ (({(nb078_alpha_dummy_369 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_370 g)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb078_alpha_dummy_370 g)) (Class.cv g) (Class.cv (nb078_alpha_dummy_369 g)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0460 : (nb078_alpha_dummy_001) ∈ (((Class.cv (nb078_alpha_dummy_001))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0461 (g : Var) : g ∈ (((Class.cv g)).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0462 : (nb078_alpha_dummy_289) ∈ (((Class.cv (nb078_alpha_dummy_289))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0463 : (nb078_alpha_dummy_289) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_445) (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_289)) (Wff.classEq (Class.cv (nb078_alpha_dummy_445)) (syn_cphi (Class.cv (nb078_alpha_dummy_446)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_445) (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_288)) (Wff.classEq (Class.cv (nb078_alpha_dummy_445)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_446))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0462) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0462) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0464 (g : Var) : (nb078_alpha_dummy_292 g) ∈ (((Class.cv (nb078_alpha_dummy_292 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_291 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0465 (g : Var) : (nb078_alpha_dummy_292 g) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_447 g) (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_292 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_447 g) (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_291 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_448 g))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0464 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0464 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0466 : (nb078_alpha_dummy_289) ∈ (((Class.cab (nb078_alpha_dummy_445) (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_289)) (Wff.classEq (Class.cv (nb078_alpha_dummy_445)) (syn_cphi (Class.cv (nb078_alpha_dummy_446))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_445) (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_289)) (Wff.classEq (Class.cv (nb078_alpha_dummy_445)) (syn_cphi (Class.cv (nb078_alpha_dummy_446))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0462) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0462) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0467 (g : Var) : (nb078_alpha_dummy_292 g) ∈ (((Class.cab (nb078_alpha_dummy_447 g) (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_292 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_448 g))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_447 g) (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_292 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_448 g))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0464 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0464 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0468 : (nb078_alpha_dummy_446) ∈ (((Class.cv (nb078_alpha_dummy_446))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0469 (g : Var) : (nb078_alpha_dummy_448 g) ∈ (((Class.cv (nb078_alpha_dummy_448 g))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0470 : (nb078_alpha_dummy_453) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_453)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_453)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_453))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0471 (g : Var) : (nb078_alpha_dummy_455 g) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_455 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_455 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_455 g))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0472 : (nb078_alpha_dummy_453) ∈ (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0473 (g : Var) : (nb078_alpha_dummy_455 g) ∈ (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0474 : (nb078_alpha_dummy_460) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_460)) (Class.cv (nb078_alpha_dummy_461)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_460)) (Class.cv (nb078_alpha_dummy_461)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0475 (g : Var) : (nb078_alpha_dummy_463 g) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_463 g)) (Class.cv (nb078_alpha_dummy_464 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_463 g)) (Class.cv (nb078_alpha_dummy_464 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0476 : (nb078_alpha_dummy_460) ∈ (((Class.cv (nb078_alpha_dummy_460))).fv ∪ ((Class.cv (nb078_alpha_dummy_461))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0477 (g : Var) : (nb078_alpha_dummy_463 g) ∈ (((Class.cv (nb078_alpha_dummy_463 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_464 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0478 : (nb078_alpha_dummy_461) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_460)) (Class.cv (nb078_alpha_dummy_461)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_460)) (Class.cv (nb078_alpha_dummy_461)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0479 (g : Var) : (nb078_alpha_dummy_464 g) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_463 g)) (Class.cv (nb078_alpha_dummy_464 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_463 g)) (Class.cv (nb078_alpha_dummy_464 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0480 : (nb078_alpha_dummy_461) ∈ (((Class.cv (nb078_alpha_dummy_460))).fv ∪ ((Class.cv (nb078_alpha_dummy_461))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0481 (g : Var) : (nb078_alpha_dummy_464 g) ∈ (((Class.cv (nb078_alpha_dummy_463 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_464 g))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0482 : (nb078_alpha_dummy_460) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_460)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_461)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0483 (g : Var) : (nb078_alpha_dummy_463 g) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_463 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_464 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0484 : (nb078_alpha_dummy_460) ∈ (((Class.cv (nb078_alpha_dummy_460))).fv ∪ ((Class.cv (nb078_alpha_dummy_460))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0485 (g : Var) : (nb078_alpha_dummy_463 g) ∈ (((Class.cv (nb078_alpha_dummy_463 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_463 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0486 : (nb078_alpha_dummy_461) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_460)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_461)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0487 (g : Var) : (nb078_alpha_dummy_464 g) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_463 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_464 g)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0488 : (nb078_alpha_dummy_461) ∈ (((Class.cv (nb078_alpha_dummy_461))).fv ∪ ((Class.cv (nb078_alpha_dummy_461))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0489 (g : Var) : (nb078_alpha_dummy_464 g) ∈ (((Class.cv (nb078_alpha_dummy_464 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_464 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0490 : (nb078_alpha_dummy_288) ∈ (((Class.cv (nb078_alpha_dummy_289))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0491 : (nb078_alpha_dummy_288) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_445) (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_289)) (Wff.classEq (Class.cv (nb078_alpha_dummy_445)) (syn_cphi (Class.cv (nb078_alpha_dummy_446)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_445) (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_288)) (Wff.classEq (Class.cv (nb078_alpha_dummy_445)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_446))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0490) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0490) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0492 (g : Var) : (nb078_alpha_dummy_291 g) ∈ (((Class.cv (nb078_alpha_dummy_292 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_291 g))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0493 (g : Var) : (nb078_alpha_dummy_291 g) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_447 g) (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_292 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_447 g) (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_291 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_448 g))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0492 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0492 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0494 : (nb078_alpha_dummy_288) ∈ (((Class.cab (nb078_alpha_dummy_445) (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_288)) (Wff.classEq (Class.cv (nb078_alpha_dummy_445)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_446))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_445) (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_288)) (Wff.classEq (Class.cv (nb078_alpha_dummy_445)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_446))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0490) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0490) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0495 (g : Var) : (nb078_alpha_dummy_291 g) ∈ (((Class.cab (nb078_alpha_dummy_447 g) (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_291 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_448 g))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_447 g) (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_291 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_448 g))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0492 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0492 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0496 : (nb078_alpha_dummy_446) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_446))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0497 (g : Var) : (nb078_alpha_dummy_448 g) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_448 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0498 : (nb078_alpha_dummy_446) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_446)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_446)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0499 (g : Var) : (nb078_alpha_dummy_448 g) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0500 : (nb078_alpha_dummy_482) ∈ (((Class.cv (nb078_alpha_dummy_482))).fv ∪ ((Class.cv (nb078_alpha_dummy_481))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0501 : (nb078_alpha_dummy_482) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_485) (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_482)) (Wff.classEq (Class.cv (nb078_alpha_dummy_485)) (syn_cphi (Class.cv (nb078_alpha_dummy_486)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_485) (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_481)) (Wff.classEq (Class.cv (nb078_alpha_dummy_485)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_486))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0500) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0500) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0502 (g : Var) : (nb078_alpha_dummy_484 g) ∈ (((Class.cv (nb078_alpha_dummy_484 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_483 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0503 (g : Var) : (nb078_alpha_dummy_484 g) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_487 g) (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_484 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_487 g) (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_483 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_488 g))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0502 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0502 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0504 : (nb078_alpha_dummy_482) ∈ (((Class.cab (nb078_alpha_dummy_485) (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_482)) (Wff.classEq (Class.cv (nb078_alpha_dummy_485)) (syn_cphi (Class.cv (nb078_alpha_dummy_486))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_485) (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_482)) (Wff.classEq (Class.cv (nb078_alpha_dummy_485)) (syn_cphi (Class.cv (nb078_alpha_dummy_486))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0500) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0500) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0505 (g : Var) : (nb078_alpha_dummy_484 g) ∈ (((Class.cab (nb078_alpha_dummy_487 g) (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_484 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_488 g))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_487 g) (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_484 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_488 g))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0502 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0502 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0506 : (nb078_alpha_dummy_486) ∈ (((Class.cv (nb078_alpha_dummy_486))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0507 (g : Var) : (nb078_alpha_dummy_488 g) ∈ (((Class.cv (nb078_alpha_dummy_488 g))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0508 : (nb078_alpha_dummy_493) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_493)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_493)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_493))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0509 (g : Var) : (nb078_alpha_dummy_495 g) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_495 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_495 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_495 g))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0510 : (nb078_alpha_dummy_493) ∈ (((Class.cv (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0511 (g : Var) : (nb078_alpha_dummy_495 g) ∈ (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0512 : (nb078_alpha_dummy_500) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_500)) (Class.cv (nb078_alpha_dummy_501)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_500)) (Class.cv (nb078_alpha_dummy_501)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0513 (g : Var) : (nb078_alpha_dummy_503 g) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_503 g)) (Class.cv (nb078_alpha_dummy_504 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_503 g)) (Class.cv (nb078_alpha_dummy_504 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0514 : (nb078_alpha_dummy_500) ∈ (((Class.cv (nb078_alpha_dummy_500))).fv ∪ ((Class.cv (nb078_alpha_dummy_501))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0515 (g : Var) : (nb078_alpha_dummy_503 g) ∈ (((Class.cv (nb078_alpha_dummy_503 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_504 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0516 : (nb078_alpha_dummy_501) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_500)) (Class.cv (nb078_alpha_dummy_501)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_500)) (Class.cv (nb078_alpha_dummy_501)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0517 (g : Var) : (nb078_alpha_dummy_504 g) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_503 g)) (Class.cv (nb078_alpha_dummy_504 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_503 g)) (Class.cv (nb078_alpha_dummy_504 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0518 : (nb078_alpha_dummy_501) ∈ (((Class.cv (nb078_alpha_dummy_500))).fv ∪ ((Class.cv (nb078_alpha_dummy_501))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0519 (g : Var) : (nb078_alpha_dummy_504 g) ∈ (((Class.cv (nb078_alpha_dummy_503 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_504 g))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0520 : (nb078_alpha_dummy_500) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_500)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_501)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0521 (g : Var) : (nb078_alpha_dummy_503 g) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_503 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_504 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0522 : (nb078_alpha_dummy_500) ∈ (((Class.cv (nb078_alpha_dummy_500))).fv ∪ ((Class.cv (nb078_alpha_dummy_500))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0523 (g : Var) : (nb078_alpha_dummy_503 g) ∈ (((Class.cv (nb078_alpha_dummy_503 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_503 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0524 : (nb078_alpha_dummy_501) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_500)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_501)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0525 (g : Var) : (nb078_alpha_dummy_504 g) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_503 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_504 g)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0526 : (nb078_alpha_dummy_501) ∈ (((Class.cv (nb078_alpha_dummy_501))).fv ∪ ((Class.cv (nb078_alpha_dummy_501))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0527 (g : Var) : (nb078_alpha_dummy_504 g) ∈ (((Class.cv (nb078_alpha_dummy_504 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_504 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0528 : (nb078_alpha_dummy_481) ∈ (((Class.cv (nb078_alpha_dummy_482))).fv ∪ ((Class.cv (nb078_alpha_dummy_481))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0529 : (nb078_alpha_dummy_481) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_485) (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_482)) (Wff.classEq (Class.cv (nb078_alpha_dummy_485)) (syn_cphi (Class.cv (nb078_alpha_dummy_486)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_485) (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_481)) (Wff.classEq (Class.cv (nb078_alpha_dummy_485)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_486))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0528) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0528) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0530 (g : Var) : (nb078_alpha_dummy_483 g) ∈ (((Class.cv (nb078_alpha_dummy_484 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_483 g))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0531 (g : Var) : (nb078_alpha_dummy_483 g) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_487 g) (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_484 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_487 g) (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_483 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_488 g))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0530 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0530 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0532 : (nb078_alpha_dummy_481) ∈ (((Class.cab (nb078_alpha_dummy_485) (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_481)) (Wff.classEq (Class.cv (nb078_alpha_dummy_485)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_486))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_485) (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_481)) (Wff.classEq (Class.cv (nb078_alpha_dummy_485)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_486))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0528) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0528) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0533 (g : Var) : (nb078_alpha_dummy_483 g) ∈ (((Class.cab (nb078_alpha_dummy_487 g) (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_483 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_488 g))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_487 g) (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_483 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_488 g))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0530 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0530 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0534 : (nb078_alpha_dummy_486) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_486))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0535 (g : Var) : (nb078_alpha_dummy_488 g) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_488 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0536 : (nb078_alpha_dummy_486) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_486)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_486)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0537 (g : Var) : (nb078_alpha_dummy_488 g) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0538 : (nb078_alpha_dummy_001) ∈ (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_cvv)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0539 (g : Var) : g ∈ (((syn_ccnv (Class.cv g))).fv ∪ ((syn_cvv)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0540 : (nb078_alpha_dummy_526) ∈ (((Class.cv (nb078_alpha_dummy_526))).fv ∪ ((Class.cv (nb078_alpha_dummy_525))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0541 : (nb078_alpha_dummy_526) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_529) (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_526)) (Wff.classEq (Class.cv (nb078_alpha_dummy_529)) (syn_cphi (Class.cv (nb078_alpha_dummy_530)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_529) (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_525)) (Wff.classEq (Class.cv (nb078_alpha_dummy_529)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_530))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0540) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0540) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0542 (g : Var) : (nb078_alpha_dummy_528 g) ∈ (((Class.cv (nb078_alpha_dummy_528 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_527 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0543 (g : Var) : (nb078_alpha_dummy_528 g) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_531 g) (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_528 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_531 g) (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_527 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_532 g))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0542 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0542 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0544 : (nb078_alpha_dummy_526) ∈ (((Class.cab (nb078_alpha_dummy_529) (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_526)) (Wff.classEq (Class.cv (nb078_alpha_dummy_529)) (syn_cphi (Class.cv (nb078_alpha_dummy_530))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_529) (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_526)) (Wff.classEq (Class.cv (nb078_alpha_dummy_529)) (syn_cphi (Class.cv (nb078_alpha_dummy_530))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0540) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0540) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0545 (g : Var) : (nb078_alpha_dummy_528 g) ∈ (((Class.cab (nb078_alpha_dummy_531 g) (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_528 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_532 g))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_531 g) (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_528 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_532 g))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0542 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0542 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0546 : (nb078_alpha_dummy_530) ∈ (((Class.cv (nb078_alpha_dummy_530))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0547 (g : Var) : (nb078_alpha_dummy_532 g) ∈ (((Class.cv (nb078_alpha_dummy_532 g))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0548 : (nb078_alpha_dummy_537) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_537)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_537)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_537))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0549 (g : Var) : (nb078_alpha_dummy_539 g) ∈ (((Wff.classMem (Class.cv (nb078_alpha_dummy_539 g)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb078_alpha_dummy_539 g)) (syn_c1c))).fv ∪ ((Class.cv (nb078_alpha_dummy_539 g))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0550 : (nb078_alpha_dummy_537) ∈ (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0551 (g : Var) : (nb078_alpha_dummy_539 g) ∈ (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0552 : (nb078_alpha_dummy_544) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_544)) (Class.cv (nb078_alpha_dummy_545)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_544)) (Class.cv (nb078_alpha_dummy_545)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0553 (g : Var) : (nb078_alpha_dummy_547 g) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_547 g)) (Class.cv (nb078_alpha_dummy_548 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_547 g)) (Class.cv (nb078_alpha_dummy_548 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0554 : (nb078_alpha_dummy_544) ∈ (((Class.cv (nb078_alpha_dummy_544))).fv ∪ ((Class.cv (nb078_alpha_dummy_545))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0555 (g : Var) : (nb078_alpha_dummy_547 g) ∈ (((Class.cv (nb078_alpha_dummy_547 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_548 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0556 : (nb078_alpha_dummy_545) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_544)) (Class.cv (nb078_alpha_dummy_545)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_544)) (Class.cv (nb078_alpha_dummy_545)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0557 (g : Var) : (nb078_alpha_dummy_548 g) ∈ (((syn_cnin (Class.cv (nb078_alpha_dummy_547 g)) (Class.cv (nb078_alpha_dummy_548 g)))).fv ∪ ((syn_cnin (Class.cv (nb078_alpha_dummy_547 g)) (Class.cv (nb078_alpha_dummy_548 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0558 : (nb078_alpha_dummy_545) ∈ (((Class.cv (nb078_alpha_dummy_544))).fv ∪ ((Class.cv (nb078_alpha_dummy_545))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0559 (g : Var) : (nb078_alpha_dummy_548 g) ∈ (((Class.cv (nb078_alpha_dummy_547 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_548 g))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0560 : (nb078_alpha_dummy_544) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_544)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_545)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0561 (g : Var) : (nb078_alpha_dummy_547 g) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_547 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_548 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0562 : (nb078_alpha_dummy_544) ∈ (((Class.cv (nb078_alpha_dummy_544))).fv ∪ ((Class.cv (nb078_alpha_dummy_544))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0563 (g : Var) : (nb078_alpha_dummy_547 g) ∈ (((Class.cv (nb078_alpha_dummy_547 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_547 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0564 : (nb078_alpha_dummy_545) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_544)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_545)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0565 (g : Var) : (nb078_alpha_dummy_548 g) ∈ (((syn_ccompl (Class.cv (nb078_alpha_dummy_547 g)))).fv ∪ ((syn_ccompl (Class.cv (nb078_alpha_dummy_548 g)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0566 : (nb078_alpha_dummy_545) ∈ (((Class.cv (nb078_alpha_dummy_545))).fv ∪ ((Class.cv (nb078_alpha_dummy_545))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0567 (g : Var) : (nb078_alpha_dummy_548 g) ∈ (((Class.cv (nb078_alpha_dummy_548 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_548 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0568 : (nb078_alpha_dummy_525) ∈ (((Class.cv (nb078_alpha_dummy_526))).fv ∪ ((Class.cv (nb078_alpha_dummy_525))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0569 : (nb078_alpha_dummy_525) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_529) (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_526)) (Wff.classEq (Class.cv (nb078_alpha_dummy_529)) (syn_cphi (Class.cv (nb078_alpha_dummy_530)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_529) (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_525)) (Wff.classEq (Class.cv (nb078_alpha_dummy_529)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_530))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0568) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0568) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0570 (g : Var) : (nb078_alpha_dummy_527 g) ∈ (((Class.cv (nb078_alpha_dummy_528 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_527 g))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0571 (g : Var) : (nb078_alpha_dummy_527 g) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_531 g) (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_528 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_531 g) (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_527 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_532 g))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0570 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0570 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0572 : (nb078_alpha_dummy_525) ∈ (((Class.cab (nb078_alpha_dummy_529) (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_525)) (Wff.classEq (Class.cv (nb078_alpha_dummy_529)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_530))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_529) (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_525)) (Wff.classEq (Class.cv (nb078_alpha_dummy_529)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_530))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0568) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0568) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0573 (g : Var) : (nb078_alpha_dummy_527 g) ∈ (((Class.cab (nb078_alpha_dummy_531 g) (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_527 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_532 g))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_531 g) (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_527 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_532 g))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0570 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0570 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0574 : (nb078_alpha_dummy_530) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_530))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0575 (g : Var) : (nb078_alpha_dummy_532 g) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_532 g))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0576 : (nb078_alpha_dummy_530) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_530)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_530)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0577 (g : Var) : (nb078_alpha_dummy_532 g) ∈ (((syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))).fv ∪ ((syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0578 : (nb078_alpha_dummy_001) ∈ (((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_001))) (Class.cv (nb078_alpha_dummy_003)))).fv ∪ ((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_001))) (Class.cv (nb078_alpha_dummy_003)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0579 (x : Var) (g : Var) : g ∈ (((syn_cnin (syn_crn (Class.cv g)) (Class.cv x))).fv ∪ ((syn_cnin (syn_crn (Class.cv g)) (Class.cv x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0580 : (nb078_alpha_dummy_001) ∈ (((syn_crn (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((Class.cv (nb078_alpha_dummy_003))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0581 (x : Var) (g : Var) : g ∈ (((syn_crn (Class.cv g))).fv ∪ ((Class.cv x)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0582 : (nb078_alpha_dummy_001) ∈ (((Class.cv (nb078_alpha_dummy_001))).fv ∪ ((syn_cvv)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0583 (g : Var) : g ∈ (((Class.cv g)).fv ∪ ((syn_cvv)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0584 : (nb078_alpha_dummy_003) ∈ (((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_001))) (Class.cv (nb078_alpha_dummy_003)))).fv ∪ ((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_001))) (Class.cv (nb078_alpha_dummy_003)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0585 (x : Var) (g : Var) : x ∈ (((syn_cnin (syn_crn (Class.cv g)) (Class.cv x))).fv ∪ ((syn_cnin (syn_crn (Class.cv g)) (Class.cv x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0586 : (nb078_alpha_dummy_003) ∈ (((syn_crn (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((Class.cv (nb078_alpha_dummy_003))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0587 (x : Var) (g : Var) : x ∈ (((syn_crn (Class.cv g))).fv ∪ ((Class.cv x)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0588 : (nb078_alpha_dummy_569) ∈ (({(nb078_alpha_dummy_569)} : Finset Var) ∪ ({(nb078_alpha_dummy_570)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_571) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_569)) (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))) (Class.cv (nb078_alpha_dummy_571))) (syn_wbr (Class.cv (nb078_alpha_dummy_571)) (syn_ccnv (Class.cv (nb078_alpha_dummy_001))) (Class.cv (nb078_alpha_dummy_570)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0589 (g : Var) : (nb078_alpha_dummy_572 g) ∈ (({(nb078_alpha_dummy_572 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_573 g)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_574 g) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_572 g)) (syn_ccnv (syn_ccnv (Class.cv g))) (Class.cv (nb078_alpha_dummy_574 g))) (syn_wbr (Class.cv (nb078_alpha_dummy_574 g)) (syn_ccnv (Class.cv g)) (Class.cv (nb078_alpha_dummy_573 g)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0590 : (nb078_alpha_dummy_570) ∈ (({(nb078_alpha_dummy_569)} : Finset Var) ∪ ({(nb078_alpha_dummy_570)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_571) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_569)) (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))) (Class.cv (nb078_alpha_dummy_571))) (syn_wbr (Class.cv (nb078_alpha_dummy_571)) (syn_ccnv (Class.cv (nb078_alpha_dummy_001))) (Class.cv (nb078_alpha_dummy_570)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0591 (g : Var) : (nb078_alpha_dummy_573 g) ∈ (({(nb078_alpha_dummy_572 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_573 g)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_574 g) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_572 g)) (syn_ccnv (syn_ccnv (Class.cv g))) (Class.cv (nb078_alpha_dummy_574 g))) (syn_wbr (Class.cv (nb078_alpha_dummy_574 g)) (syn_ccnv (Class.cv g)) (Class.cv (nb078_alpha_dummy_573 g)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0592 : (nb078_alpha_dummy_569) ∈ (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0593 : (nb078_alpha_dummy_569) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_577) (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_569)) (Wff.classEq (Class.cv (nb078_alpha_dummy_577)) (syn_cphi (Class.cv (nb078_alpha_dummy_578)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_577) (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_570)) (Wff.classEq (Class.cv (nb078_alpha_dummy_577)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_578))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0592) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0592) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0594 (g : Var) : (nb078_alpha_dummy_572 g) ∈ (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_573 g))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0595 (g : Var) : (nb078_alpha_dummy_572 g) ∈ (((syn_ccompl (Class.cab (nb078_alpha_dummy_579 g) (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_572 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g)) (syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))))))).fv ∪ ((syn_ccompl (Class.cab (nb078_alpha_dummy_579 g) (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_573 g)) (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g)) (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_580 g))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0594 g) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0594 g) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
