import NAR4C090C001Part018

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

theorem nb090_support_mem_0497 (h : Var) : (nb090_alpha_dummy_485 h) ∈ (((Class.cv (nb090_alpha_dummy_485 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_485 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0498 (A : Class) : (nb090_alpha_dummy_483 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_482 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_483 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0499 (h : Var) : (nb090_alpha_dummy_486 h) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_485 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_486 h)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0500 (A : Class) : (nb090_alpha_dummy_483 A) ∈ (((Class.cv (nb090_alpha_dummy_483 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_483 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0501 (h : Var) : (nb090_alpha_dummy_486 h) ∈ (((Class.cv (nb090_alpha_dummy_486 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_486 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0502 (A : Class) : (nb090_alpha_dummy_425 A) ∈ (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_425 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0503 (A : Class) : (nb090_alpha_dummy_425 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_467 A) (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_423 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_467 A) (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_425 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_468 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0502 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0502 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0504 (h : Var) : (nb090_alpha_dummy_428 h) ∈ (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_428 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0505 (h : Var) : (nb090_alpha_dummy_428 h) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_469 h) (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_426 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_469 h) (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_428 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_470 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0504 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0504 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0506 (A : Class) : (nb090_alpha_dummy_425 A) ∈ (((Class.cab (nb090_alpha_dummy_467 A) (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_425 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_468 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_467 A) (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_425 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_468 A))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0502 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0502 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0507 (h : Var) : (nb090_alpha_dummy_428 h) ∈ (((Class.cab (nb090_alpha_dummy_469 h) (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_428 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_470 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_469 h) (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_428 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_470 h))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0504 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0504 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0508 (A : Class) : (nb090_alpha_dummy_468 A) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_468 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0509 (h : Var) : (nb090_alpha_dummy_470 h) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_470 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0510 (A : Class) : (nb090_alpha_dummy_468 A) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0511 (h : Var) : (nb090_alpha_dummy_470 h) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0512 (A : Class) : (nb090_alpha_dummy_503 A) ∈ (({(nb090_alpha_dummy_503 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_504 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_504 A)) (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))) (Class.cv (nb090_alpha_dummy_503 A)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0513 (h : Var) : (nb090_alpha_dummy_505 h) ∈ (({(nb090_alpha_dummy_505 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_506 h)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_506 h)) (syn_ccnv (Class.cv h)) (Class.cv (nb090_alpha_dummy_505 h)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0514 (A : Class) : (nb090_alpha_dummy_504 A) ∈ (({(nb090_alpha_dummy_503 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_504 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_504 A)) (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))) (Class.cv (nb090_alpha_dummy_503 A)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0515 (h : Var) : (nb090_alpha_dummy_506 h) ∈ (({(nb090_alpha_dummy_505 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_506 h)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_506 h)) (syn_ccnv (Class.cv h)) (Class.cv (nb090_alpha_dummy_505 h)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0516 (A : Class) : (nb090_alpha_dummy_503 A) ∈ (((Class.cv (nb090_alpha_dummy_503 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_504 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0517 (A : Class) : (nb090_alpha_dummy_503 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_509 A) (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_503 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_509 A) (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_504 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_510 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0516 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0516 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0518 (h : Var) : (nb090_alpha_dummy_505 h) ∈ (((Class.cv (nb090_alpha_dummy_505 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_506 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0519 (h : Var) : (nb090_alpha_dummy_505 h) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_511 h) (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_505 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_511 h) (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_506 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_512 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0518 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0518 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0520 (A : Class) : (nb090_alpha_dummy_503 A) ∈ (((Class.cab (nb090_alpha_dummy_509 A) (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_503 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_510 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_509 A) (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_503 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_510 A))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0516 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0516 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0521 (h : Var) : (nb090_alpha_dummy_505 h) ∈ (((Class.cab (nb090_alpha_dummy_511 h) (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_505 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_512 h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_511 h) (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_505 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_512 h))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0518 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0518 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0522 (A : Class) : (nb090_alpha_dummy_510 A) ∈ (((Class.cv (nb090_alpha_dummy_510 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0523 (h : Var) : (nb090_alpha_dummy_512 h) ∈ (((Class.cv (nb090_alpha_dummy_512 h))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0524 (A : Class) : (nb090_alpha_dummy_517 A) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_517 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_517 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_517 A))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0525 (h : Var) : (nb090_alpha_dummy_519 h) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_519 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_519 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_519 h))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0526 (A : Class) : (nb090_alpha_dummy_517 A) ∈ (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0527 (h : Var) : (nb090_alpha_dummy_519 h) ∈ (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0528 (A : Class) : (nb090_alpha_dummy_524 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_524 A)) (Class.cv (nb090_alpha_dummy_525 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_524 A)) (Class.cv (nb090_alpha_dummy_525 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0529 (h : Var) : (nb090_alpha_dummy_527 h) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_527 h)) (Class.cv (nb090_alpha_dummy_528 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_527 h)) (Class.cv (nb090_alpha_dummy_528 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0530 (A : Class) : (nb090_alpha_dummy_524 A) ∈ (((Class.cv (nb090_alpha_dummy_524 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_525 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0531 (h : Var) : (nb090_alpha_dummy_527 h) ∈ (((Class.cv (nb090_alpha_dummy_527 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_528 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0532 (A : Class) : (nb090_alpha_dummy_525 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_524 A)) (Class.cv (nb090_alpha_dummy_525 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_524 A)) (Class.cv (nb090_alpha_dummy_525 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0533 (h : Var) : (nb090_alpha_dummy_528 h) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_527 h)) (Class.cv (nb090_alpha_dummy_528 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_527 h)) (Class.cv (nb090_alpha_dummy_528 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0534 (A : Class) : (nb090_alpha_dummy_525 A) ∈ (((Class.cv (nb090_alpha_dummy_524 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_525 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0535 (h : Var) : (nb090_alpha_dummy_528 h) ∈ (((Class.cv (nb090_alpha_dummy_527 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_528 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0536 (A : Class) : (nb090_alpha_dummy_524 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_524 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_525 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0537 (h : Var) : (nb090_alpha_dummy_527 h) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_527 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_528 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0538 (A : Class) : (nb090_alpha_dummy_524 A) ∈ (((Class.cv (nb090_alpha_dummy_524 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_524 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0539 (h : Var) : (nb090_alpha_dummy_527 h) ∈ (((Class.cv (nb090_alpha_dummy_527 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_527 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0540 (A : Class) : (nb090_alpha_dummy_525 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_524 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_525 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0541 (h : Var) : (nb090_alpha_dummy_528 h) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_527 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_528 h)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0542 (A : Class) : (nb090_alpha_dummy_525 A) ∈ (((Class.cv (nb090_alpha_dummy_525 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_525 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0543 (h : Var) : (nb090_alpha_dummy_528 h) ∈ (((Class.cv (nb090_alpha_dummy_528 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_528 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0544 (A : Class) : (nb090_alpha_dummy_504 A) ∈ (((Class.cv (nb090_alpha_dummy_503 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_504 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0545 (A : Class) : (nb090_alpha_dummy_504 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_509 A) (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_503 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_509 A) (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_504 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_510 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0544 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0544 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0546 (h : Var) : (nb090_alpha_dummy_506 h) ∈ (((Class.cv (nb090_alpha_dummy_505 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_506 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0547 (h : Var) : (nb090_alpha_dummy_506 h) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_511 h) (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_505 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_511 h) (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_506 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_512 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0546 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0546 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0548 (A : Class) : (nb090_alpha_dummy_504 A) ∈ (((Class.cab (nb090_alpha_dummy_509 A) (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_504 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_510 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_509 A) (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_504 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_510 A))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0544 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0544 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0549 (h : Var) : (nb090_alpha_dummy_506 h) ∈ (((Class.cab (nb090_alpha_dummy_511 h) (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_506 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_512 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_511 h) (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_506 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_512 h))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0546 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0546 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0550 (A : Class) : (nb090_alpha_dummy_510 A) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_510 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0551 (h : Var) : (nb090_alpha_dummy_512 h) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_512 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0552 (A : Class) : (nb090_alpha_dummy_510 A) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0553 (h : Var) : (nb090_alpha_dummy_512 h) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0554 (A : Class) : (nb090_alpha_dummy_504 A) ∈ (((Class.cv (nb090_alpha_dummy_504 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_503 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0555 (A : Class) : (nb090_alpha_dummy_504 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_545 A) (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_504 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_545 A) (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_503 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_546 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0554 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0554 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0556 (h : Var) : (nb090_alpha_dummy_506 h) ∈ (((Class.cv (nb090_alpha_dummy_506 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_505 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0557 (h : Var) : (nb090_alpha_dummy_506 h) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_547 h) (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_506 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_547 h) (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_505 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_548 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0556 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0556 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0558 (A : Class) : (nb090_alpha_dummy_504 A) ∈ (((Class.cab (nb090_alpha_dummy_545 A) (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_504 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_546 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_545 A) (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_504 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_546 A))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0554 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0554 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0559 (h : Var) : (nb090_alpha_dummy_506 h) ∈ (((Class.cab (nb090_alpha_dummy_547 h) (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_506 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_548 h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_547 h) (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_506 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_548 h))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0556 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0556 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0560 (A : Class) : (nb090_alpha_dummy_546 A) ∈ (((Class.cv (nb090_alpha_dummy_546 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0561 (h : Var) : (nb090_alpha_dummy_548 h) ∈ (((Class.cv (nb090_alpha_dummy_548 h))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0562 (A : Class) : (nb090_alpha_dummy_553 A) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_553 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_553 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_553 A))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0563 (h : Var) : (nb090_alpha_dummy_555 h) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_555 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_555 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_555 h))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0564 (A : Class) : (nb090_alpha_dummy_553 A) ∈ (((Class.cv (nb090_alpha_dummy_553 A))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0565 (h : Var) : (nb090_alpha_dummy_555 h) ∈ (((Class.cv (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0566 (A : Class) : (nb090_alpha_dummy_560 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_560 A)) (Class.cv (nb090_alpha_dummy_561 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_560 A)) (Class.cv (nb090_alpha_dummy_561 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0567 (h : Var) : (nb090_alpha_dummy_563 h) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_563 h)) (Class.cv (nb090_alpha_dummy_564 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_563 h)) (Class.cv (nb090_alpha_dummy_564 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0568 (A : Class) : (nb090_alpha_dummy_560 A) ∈ (((Class.cv (nb090_alpha_dummy_560 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_561 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0569 (h : Var) : (nb090_alpha_dummy_563 h) ∈ (((Class.cv (nb090_alpha_dummy_563 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_564 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0570 (A : Class) : (nb090_alpha_dummy_561 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_560 A)) (Class.cv (nb090_alpha_dummy_561 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_560 A)) (Class.cv (nb090_alpha_dummy_561 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0571 (h : Var) : (nb090_alpha_dummy_564 h) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_563 h)) (Class.cv (nb090_alpha_dummy_564 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_563 h)) (Class.cv (nb090_alpha_dummy_564 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0572 (A : Class) : (nb090_alpha_dummy_561 A) ∈ (((Class.cv (nb090_alpha_dummy_560 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_561 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0573 (h : Var) : (nb090_alpha_dummy_564 h) ∈ (((Class.cv (nb090_alpha_dummy_563 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_564 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0574 (A : Class) : (nb090_alpha_dummy_560 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_560 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_561 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0575 (h : Var) : (nb090_alpha_dummy_563 h) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_563 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_564 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0576 (A : Class) : (nb090_alpha_dummy_560 A) ∈ (((Class.cv (nb090_alpha_dummy_560 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_560 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0577 (h : Var) : (nb090_alpha_dummy_563 h) ∈ (((Class.cv (nb090_alpha_dummy_563 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_563 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0578 (A : Class) : (nb090_alpha_dummy_561 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_560 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_561 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0579 (h : Var) : (nb090_alpha_dummy_564 h) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_563 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_564 h)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0580 (A : Class) : (nb090_alpha_dummy_561 A) ∈ (((Class.cv (nb090_alpha_dummy_561 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_561 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0581 (h : Var) : (nb090_alpha_dummy_564 h) ∈ (((Class.cv (nb090_alpha_dummy_564 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_564 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0582 (A : Class) : (nb090_alpha_dummy_503 A) ∈ (((Class.cv (nb090_alpha_dummy_504 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_503 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0583 (A : Class) : (nb090_alpha_dummy_503 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_545 A) (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_504 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_545 A) (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_503 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_546 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0582 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0582 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0584 (h : Var) : (nb090_alpha_dummy_505 h) ∈ (((Class.cv (nb090_alpha_dummy_506 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_505 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0585 (h : Var) : (nb090_alpha_dummy_505 h) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_547 h) (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_506 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_547 h) (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_505 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_548 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0584 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0584 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0586 (A : Class) : (nb090_alpha_dummy_503 A) ∈ (((Class.cab (nb090_alpha_dummy_545 A) (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_503 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_546 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_545 A) (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_503 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_546 A))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0582 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0582 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0587 (h : Var) : (nb090_alpha_dummy_505 h) ∈ (((Class.cab (nb090_alpha_dummy_547 h) (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_505 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_548 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_547 h) (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_505 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_548 h))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0584 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0584 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0588 (A : Class) : (nb090_alpha_dummy_546 A) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_546 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0589 (h : Var) : (nb090_alpha_dummy_548 h) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_548 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0590 (A : Class) : (nb090_alpha_dummy_546 A) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0591 (h : Var) : (nb090_alpha_dummy_548 h) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0592 (A : Class) : (nb090_alpha_dummy_000 A) ∈ (((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))) (syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))) (syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))) (syn_cid))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0593 (h : Var) : h ∈ (((syn_cnin (syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h)))) (syn_cid))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0594 (A : Class) : (nb090_alpha_dummy_000 A) ∈ (((syn_ccom (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))) (syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))))).fv ∪ ((syn_cid)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0595 (h : Var) : h ∈ (((syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h))))).fv ∪ ((syn_cid)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccom]
  apply Finset.mem_union_left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0596 (A : Class) : (nb090_alpha_dummy_000 A) ∈ (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0597 (A : Class) : (nb090_alpha_dummy_000 A) ∈ (({(nb090_alpha_dummy_423 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_424 A)} : Finset Var) ∪ ((syn_wex (nb090_alpha_dummy_425 A) (syn_wa (syn_wbr (Class.cv (nb090_alpha_dummy_423 A)) (syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))) (Class.cv (nb090_alpha_dummy_425 A))) (syn_wbr (Class.cv (nb090_alpha_dummy_425 A)) (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))) (Class.cv (nb090_alpha_dummy_424 A)))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wex]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0596 A) 2))
  ·
    rw [fv_syn_wa]
    apply Finset.mem_union_left
    rw [fv_syn_wbr]
    apply Finset.mem_union_right
    rw [fv_syn_ccnv]
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb090_support_mem_0598 (h : Var) : h ∈ (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0599 (h : Var) : h ∈ (({(nb090_alpha_dummy_426 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_427 h)} : Finset Var) ∪ ((syn_wex (nb090_alpha_dummy_428 h) (syn_wa (syn_wbr (Class.cv (nb090_alpha_dummy_426 h)) (syn_ccnv (syn_ccnv (Class.cv h))) (Class.cv (nb090_alpha_dummy_428 h))) (syn_wbr (Class.cv (nb090_alpha_dummy_428 h)) (syn_ccnv (Class.cv h)) (Class.cv (nb090_alpha_dummy_427 h)))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wex]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0598 h) 2))
  ·
    rw [fv_syn_wa]
    apply Finset.mem_union_left
    rw [fv_syn_wbr]
    apply Finset.mem_union_right
    rw [fv_syn_ccnv]
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb090_support_mem_0600 (A : Class) : (nb090_alpha_dummy_000 A) ∈ (({(nb090_alpha_dummy_503 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_504 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_504 A)) (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))) (Class.cv (nb090_alpha_dummy_503 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_right
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0601 (h : Var) : h ∈ (({(nb090_alpha_dummy_505 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_506 h)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_506 h)) (syn_ccnv (Class.cv h)) (Class.cv (nb090_alpha_dummy_505 h)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_right
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0602 (A : Class) : (nb090_alpha_dummy_000 A) ∈ (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) := by
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0603 (h : Var) : h ∈ (((syn_ccnv (Class.cv h))).fv) := by
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0604 (A : Class) : (nb090_alpha_dummy_425 A) ∈ (((Class.cv (nb090_alpha_dummy_425 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_424 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0605 (A : Class) : (nb090_alpha_dummy_425 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_581 A) (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_425 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_581 A) (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_424 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_582 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0604 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0604 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0606 (h : Var) : (nb090_alpha_dummy_428 h) ∈ (((Class.cv (nb090_alpha_dummy_428 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_427 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0607 (h : Var) : (nb090_alpha_dummy_428 h) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_583 h) (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_428 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_583 h) (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_427 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_584 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0606 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0606 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0608 (A : Class) : (nb090_alpha_dummy_425 A) ∈ (((Class.cab (nb090_alpha_dummy_581 A) (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_425 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_582 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_581 A) (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_425 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_582 A))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0604 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0604 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0609 (h : Var) : (nb090_alpha_dummy_428 h) ∈ (((Class.cab (nb090_alpha_dummy_583 h) (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_428 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_584 h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_583 h) (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_428 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_584 h))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0606 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0606 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0610 (A : Class) : (nb090_alpha_dummy_582 A) ∈ (((Class.cv (nb090_alpha_dummy_582 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0611 (h : Var) : (nb090_alpha_dummy_584 h) ∈ (((Class.cv (nb090_alpha_dummy_584 h))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0612 (A : Class) : (nb090_alpha_dummy_589 A) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_589 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_589 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_589 A))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0613 (h : Var) : (nb090_alpha_dummy_591 h) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_591 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_591 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_591 h))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0614 (A : Class) : (nb090_alpha_dummy_589 A) ∈ (((Class.cv (nb090_alpha_dummy_589 A))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0615 (h : Var) : (nb090_alpha_dummy_591 h) ∈ (((Class.cv (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0616 (A : Class) : (nb090_alpha_dummy_596 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_596 A)) (Class.cv (nb090_alpha_dummy_597 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_596 A)) (Class.cv (nb090_alpha_dummy_597 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0617 (h : Var) : (nb090_alpha_dummy_599 h) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_599 h)) (Class.cv (nb090_alpha_dummy_600 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_599 h)) (Class.cv (nb090_alpha_dummy_600 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0618 (A : Class) : (nb090_alpha_dummy_596 A) ∈ (((Class.cv (nb090_alpha_dummy_596 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_597 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0619 (h : Var) : (nb090_alpha_dummy_599 h) ∈ (((Class.cv (nb090_alpha_dummy_599 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_600 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0620 (A : Class) : (nb090_alpha_dummy_597 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_596 A)) (Class.cv (nb090_alpha_dummy_597 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_596 A)) (Class.cv (nb090_alpha_dummy_597 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0621 (h : Var) : (nb090_alpha_dummy_600 h) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_599 h)) (Class.cv (nb090_alpha_dummy_600 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_599 h)) (Class.cv (nb090_alpha_dummy_600 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0622 (A : Class) : (nb090_alpha_dummy_597 A) ∈ (((Class.cv (nb090_alpha_dummy_596 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_597 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0623 (h : Var) : (nb090_alpha_dummy_600 h) ∈ (((Class.cv (nb090_alpha_dummy_599 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_600 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0624 (A : Class) : (nb090_alpha_dummy_596 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_596 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_597 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0625 (h : Var) : (nb090_alpha_dummy_599 h) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_599 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_600 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0626 (A : Class) : (nb090_alpha_dummy_596 A) ∈ (((Class.cv (nb090_alpha_dummy_596 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_596 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0627 (h : Var) : (nb090_alpha_dummy_599 h) ∈ (((Class.cv (nb090_alpha_dummy_599 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_599 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0628 (A : Class) : (nb090_alpha_dummy_597 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_596 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_597 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0629 (h : Var) : (nb090_alpha_dummy_600 h) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_599 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_600 h)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0630 (A : Class) : (nb090_alpha_dummy_597 A) ∈ (((Class.cv (nb090_alpha_dummy_597 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_597 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0631 (h : Var) : (nb090_alpha_dummy_600 h) ∈ (((Class.cv (nb090_alpha_dummy_600 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_600 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0632 (A : Class) : (nb090_alpha_dummy_424 A) ∈ (((Class.cv (nb090_alpha_dummy_425 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_424 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0633 (A : Class) : (nb090_alpha_dummy_424 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_581 A) (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_425 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_581 A) (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_424 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_582 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0632 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0632 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0634 (h : Var) : (nb090_alpha_dummy_427 h) ∈ (((Class.cv (nb090_alpha_dummy_428 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_427 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
