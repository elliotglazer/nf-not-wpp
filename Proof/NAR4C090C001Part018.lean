import NAR4C090C001Part017

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

theorem nb090_support_mem_0356 (A : Class) : (nb090_alpha_dummy_353 A) ∈ (((Class.cv (nb090_alpha_dummy_352 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_353 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0357 (h : Var) : (nb090_alpha_dummy_356 h) ∈ (((Class.cv (nb090_alpha_dummy_355 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_356 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0358 (A : Class) : (nb090_alpha_dummy_352 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_352 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_353 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0359 (h : Var) : (nb090_alpha_dummy_355 h) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_355 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_356 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0360 (A : Class) : (nb090_alpha_dummy_352 A) ∈ (((Class.cv (nb090_alpha_dummy_352 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_352 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0361 (h : Var) : (nb090_alpha_dummy_355 h) ∈ (((Class.cv (nb090_alpha_dummy_355 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_355 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0362 (A : Class) : (nb090_alpha_dummy_353 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_352 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_353 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0363 (h : Var) : (nb090_alpha_dummy_356 h) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_355 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_356 h)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0364 (A : Class) : (nb090_alpha_dummy_353 A) ∈ (((Class.cv (nb090_alpha_dummy_353 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_353 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0365 (h : Var) : (nb090_alpha_dummy_356 h) ∈ (((Class.cv (nb090_alpha_dummy_356 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_356 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0366 (A : Class) : (nb090_alpha_dummy_333 A) ∈ (((Class.cv (nb090_alpha_dummy_334 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_333 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0367 (A : Class) : (nb090_alpha_dummy_333 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_337 A) (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_334 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_337 A) (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_333 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_338 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0366 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0366 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0368 (h : Var) : (nb090_alpha_dummy_335 h) ∈ (((Class.cv (nb090_alpha_dummy_336 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_335 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0369 (h : Var) : (nb090_alpha_dummy_335 h) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_339 h) (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_336 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_339 h) (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_335 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_340 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0368 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0368 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0370 (A : Class) : (nb090_alpha_dummy_333 A) ∈ (((Class.cab (nb090_alpha_dummy_337 A) (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_333 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_338 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_337 A) (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_333 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_338 A))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0366 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0366 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0371 (h : Var) : (nb090_alpha_dummy_335 h) ∈ (((Class.cab (nb090_alpha_dummy_339 h) (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_335 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_340 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_339 h) (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_335 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_340 h))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0368 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0368 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0372 (A : Class) : (nb090_alpha_dummy_338 A) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_338 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0373 (h : Var) : (nb090_alpha_dummy_340 h) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_340 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0374 (A : Class) : (nb090_alpha_dummy_338 A) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0375 (h : Var) : (nb090_alpha_dummy_340 h) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0376 (A : Class) : (nb090_alpha_dummy_000 A) ∈ (((syn_cnin (syn_crn (Class.cv (nb090_alpha_dummy_000 A))) (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A))))).fv ∪ ((syn_cnin (syn_crn (Class.cv (nb090_alpha_dummy_000 A))) (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0377 (v : Var) (h : Var) : h ∈ (((syn_cnin (syn_crn (Class.cv h)) (syn_cfv (syn_c2nd) (Class.cv v)))).fv ∪ ((syn_cnin (syn_crn (Class.cv h)) (syn_cfv (syn_c2nd) (Class.cv v)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0378 (A : Class) : (nb090_alpha_dummy_000 A) ∈ (((syn_crn (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0379 (v : Var) (h : Var) : h ∈ (((syn_crn (Class.cv h))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv v))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0380 (A : Class) : (nb090_alpha_dummy_000 A) ∈ (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_cvv)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0381 (h : Var) : h ∈ (((Class.cv h)).fv ∪ ((syn_cvv)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0382 (A : Class) : (nb090_alpha_dummy_002 A) ∈ (((syn_cnin (syn_crn (Class.cv (nb090_alpha_dummy_000 A))) (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A))))).fv ∪ ((syn_cnin (syn_crn (Class.cv (nb090_alpha_dummy_000 A))) (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_syn_cfv]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0383 (v : Var) (h : Var) : v ∈ (((syn_cnin (syn_crn (Class.cv h)) (syn_cfv (syn_c2nd) (Class.cv v)))).fv ∪ ((syn_cnin (syn_crn (Class.cv h)) (syn_cfv (syn_c2nd) (Class.cv v)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_syn_cfv]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0384 (A : Class) : (nb090_alpha_dummy_002 A) ∈ (((syn_crn (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_cfv]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0385 (v : Var) (h : Var) : v ∈ (((syn_crn (Class.cv h))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv v))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_cfv]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0386 (A : Class) : (nb090_alpha_dummy_002 A) ∈ (((syn_c2nd)).fv ∪ ((Class.cv (nb090_alpha_dummy_002 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0387 (A : Class) : (nb090_alpha_dummy_002 A) ∈ (({(nb090_alpha_dummy_373 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c2nd) (Class.cv (nb090_alpha_dummy_373 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0388 (A : Class) : (nb090_alpha_dummy_002 A) ∈ (((Class.cab (nb090_alpha_dummy_375 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_373 A) (syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c2nd) (Class.cv (nb090_alpha_dummy_373 A)))) (syn_csn (Class.cv (nb090_alpha_dummy_375 A)))))).fv) := by
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0387 A) 0))
  ·
    rw [fv_wff_classEq]
    apply Finset.mem_union_left
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0386 A) 0))
    ·
      rw [fv_syn_wbr]
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0389 (v : Var) : v ∈ (((syn_c2nd)).fv ∪ ((Class.cv v)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0390 (v : Var) : v ∈ (({(nb090_alpha_dummy_374 v)} : Finset Var) ∪ ((syn_wbr (Class.cv v) (syn_c2nd) (Class.cv (nb090_alpha_dummy_374 v)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_wbr]
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0391 (v : Var) : v ∈ (((Class.cab (nb090_alpha_dummy_376 v) (Wff.classEq (Class.cab (nb090_alpha_dummy_374 v) (syn_wbr (Class.cv v) (syn_c2nd) (Class.cv (nb090_alpha_dummy_374 v)))) (syn_csn (Class.cv (nb090_alpha_dummy_376 v)))))).fv) := by
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0390 v) 0))
  ·
    rw [fv_wff_classEq]
    apply Finset.mem_union_left
    rw [fv_class_cab]
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0389 v) 0))
    ·
      rw [fv_syn_wbr]
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0392 (A : Class) : (nb090_alpha_dummy_002 A) ∈ (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_373 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0393 (A : Class) : (nb090_alpha_dummy_002 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_381 A) (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_002 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_381 A) (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_373 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_382 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0392 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0392 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0394 (v : Var) : v ∈ (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_374 v))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0395 (v : Var) : v ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_383 v) (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv v) (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v)) (syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_383 v) (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv (nb090_alpha_dummy_374 v)) (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_384 v))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0394 v) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0394 v) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0396 (A : Class) : (nb090_alpha_dummy_002 A) ∈ (((Class.cab (nb090_alpha_dummy_381 A) (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_002 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_382 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_381 A) (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_002 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_382 A))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0392 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0392 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0397 (v : Var) : v ∈ (((Class.cab (nb090_alpha_dummy_383 v) (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv v) (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v)) (syn_cphi (Class.cv (nb090_alpha_dummy_384 v))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_383 v) (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv v) (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v)) (syn_cphi (Class.cv (nb090_alpha_dummy_384 v))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0394 v) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0394 v) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0398 (A : Class) : (nb090_alpha_dummy_382 A) ∈ (((Class.cv (nb090_alpha_dummy_382 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0399 (v : Var) : (nb090_alpha_dummy_384 v) ∈ (((Class.cv (nb090_alpha_dummy_384 v))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0400 (A : Class) : (nb090_alpha_dummy_389 A) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_389 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_389 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_389 A))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0401 (v : Var) : (nb090_alpha_dummy_391 v) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_391 v)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_391 v)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_391 v))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0402 (A : Class) : (nb090_alpha_dummy_389 A) ∈ (((Class.cv (nb090_alpha_dummy_389 A))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0403 (v : Var) : (nb090_alpha_dummy_391 v) ∈ (((Class.cv (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0404 (A : Class) : (nb090_alpha_dummy_396 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_396 A)) (Class.cv (nb090_alpha_dummy_397 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_396 A)) (Class.cv (nb090_alpha_dummy_397 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0405 (v : Var) : (nb090_alpha_dummy_399 v) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_399 v)) (Class.cv (nb090_alpha_dummy_400 v)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_399 v)) (Class.cv (nb090_alpha_dummy_400 v)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0406 (A : Class) : (nb090_alpha_dummy_396 A) ∈ (((Class.cv (nb090_alpha_dummy_396 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_397 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0407 (v : Var) : (nb090_alpha_dummy_399 v) ∈ (((Class.cv (nb090_alpha_dummy_399 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_400 v))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0408 (A : Class) : (nb090_alpha_dummy_397 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_396 A)) (Class.cv (nb090_alpha_dummy_397 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_396 A)) (Class.cv (nb090_alpha_dummy_397 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0409 (v : Var) : (nb090_alpha_dummy_400 v) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_399 v)) (Class.cv (nb090_alpha_dummy_400 v)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_399 v)) (Class.cv (nb090_alpha_dummy_400 v)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0410 (A : Class) : (nb090_alpha_dummy_397 A) ∈ (((Class.cv (nb090_alpha_dummy_396 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_397 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0411 (v : Var) : (nb090_alpha_dummy_400 v) ∈ (((Class.cv (nb090_alpha_dummy_399 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_400 v))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0412 (A : Class) : (nb090_alpha_dummy_396 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_396 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_397 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0413 (v : Var) : (nb090_alpha_dummy_399 v) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_399 v)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_400 v)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0414 (A : Class) : (nb090_alpha_dummy_396 A) ∈ (((Class.cv (nb090_alpha_dummy_396 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_396 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0415 (v : Var) : (nb090_alpha_dummy_399 v) ∈ (((Class.cv (nb090_alpha_dummy_399 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_399 v))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0416 (A : Class) : (nb090_alpha_dummy_397 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_396 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_397 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0417 (v : Var) : (nb090_alpha_dummy_400 v) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_399 v)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_400 v)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0418 (A : Class) : (nb090_alpha_dummy_397 A) ∈ (((Class.cv (nb090_alpha_dummy_397 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_397 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0419 (v : Var) : (nb090_alpha_dummy_400 v) ∈ (((Class.cv (nb090_alpha_dummy_400 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_400 v))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0420 (A : Class) : (nb090_alpha_dummy_373 A) ∈ (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_373 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0421 (A : Class) : (nb090_alpha_dummy_373 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_381 A) (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_002 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_381 A) (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_373 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_382 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0420 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0420 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0422 (v : Var) : (nb090_alpha_dummy_374 v) ∈ (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_374 v))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0423 (v : Var) : (nb090_alpha_dummy_374 v) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_383 v) (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv v) (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v)) (syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_383 v) (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv (nb090_alpha_dummy_374 v)) (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_384 v))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0422 v) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0422 v) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0424 (A : Class) : (nb090_alpha_dummy_373 A) ∈ (((Class.cab (nb090_alpha_dummy_381 A) (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_373 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_382 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_381 A) (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_373 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_382 A))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0420 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0420 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0425 (v : Var) : (nb090_alpha_dummy_374 v) ∈ (((Class.cab (nb090_alpha_dummy_383 v) (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv (nb090_alpha_dummy_374 v)) (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_384 v))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_383 v) (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv (nb090_alpha_dummy_374 v)) (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_384 v))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0422 v) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0422 v) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0426 (A : Class) : (nb090_alpha_dummy_382 A) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_382 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0427 (v : Var) : (nb090_alpha_dummy_384 v) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_384 v))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0428 (A : Class) : (nb090_alpha_dummy_382 A) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0429 (v : Var) : (nb090_alpha_dummy_384 v) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0430 (A : Class) : (nb090_alpha_dummy_375 A) ∈ (((Class.cv (nb090_alpha_dummy_375 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0431 (v : Var) : (nb090_alpha_dummy_376 v) ∈ (((Class.cv (nb090_alpha_dummy_376 v))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0432 (A : Class) : (nb090_alpha_dummy_423 A) ∈ (({(nb090_alpha_dummy_423 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_424 A)} : Finset Var) ∪ ((syn_wex (nb090_alpha_dummy_425 A) (syn_wa (syn_wbr (Class.cv (nb090_alpha_dummy_423 A)) (syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))) (Class.cv (nb090_alpha_dummy_425 A))) (syn_wbr (Class.cv (nb090_alpha_dummy_425 A)) (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))) (Class.cv (nb090_alpha_dummy_424 A)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0433 (h : Var) : (nb090_alpha_dummy_426 h) ∈ (({(nb090_alpha_dummy_426 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_427 h)} : Finset Var) ∪ ((syn_wex (nb090_alpha_dummy_428 h) (syn_wa (syn_wbr (Class.cv (nb090_alpha_dummy_426 h)) (syn_ccnv (syn_ccnv (Class.cv h))) (Class.cv (nb090_alpha_dummy_428 h))) (syn_wbr (Class.cv (nb090_alpha_dummy_428 h)) (syn_ccnv (Class.cv h)) (Class.cv (nb090_alpha_dummy_427 h)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0434 (A : Class) : (nb090_alpha_dummy_424 A) ∈ (({(nb090_alpha_dummy_423 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_424 A)} : Finset Var) ∪ ((syn_wex (nb090_alpha_dummy_425 A) (syn_wa (syn_wbr (Class.cv (nb090_alpha_dummy_423 A)) (syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))) (Class.cv (nb090_alpha_dummy_425 A))) (syn_wbr (Class.cv (nb090_alpha_dummy_425 A)) (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))) (Class.cv (nb090_alpha_dummy_424 A)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0435 (h : Var) : (nb090_alpha_dummy_427 h) ∈ (({(nb090_alpha_dummy_426 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_427 h)} : Finset Var) ∪ ((syn_wex (nb090_alpha_dummy_428 h) (syn_wa (syn_wbr (Class.cv (nb090_alpha_dummy_426 h)) (syn_ccnv (syn_ccnv (Class.cv h))) (Class.cv (nb090_alpha_dummy_428 h))) (syn_wbr (Class.cv (nb090_alpha_dummy_428 h)) (syn_ccnv (Class.cv h)) (Class.cv (nb090_alpha_dummy_427 h)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0436 (A : Class) : (nb090_alpha_dummy_423 A) ∈ (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_424 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0437 (A : Class) : (nb090_alpha_dummy_423 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_431 A) (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_423 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_431 A) (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_424 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_432 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0436 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0436 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0438 (h : Var) : (nb090_alpha_dummy_426 h) ∈ (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_427 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0439 (h : Var) : (nb090_alpha_dummy_426 h) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_433 h) (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_426 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_433 h) (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_427 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_434 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0438 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0438 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0440 (A : Class) : (nb090_alpha_dummy_423 A) ∈ (((Class.cab (nb090_alpha_dummy_431 A) (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_423 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_432 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_431 A) (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_423 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_432 A))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0436 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0436 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0441 (h : Var) : (nb090_alpha_dummy_426 h) ∈ (((Class.cab (nb090_alpha_dummy_433 h) (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_426 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_434 h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_433 h) (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_426 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_434 h))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0438 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0438 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0442 (A : Class) : (nb090_alpha_dummy_432 A) ∈ (((Class.cv (nb090_alpha_dummy_432 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0443 (h : Var) : (nb090_alpha_dummy_434 h) ∈ (((Class.cv (nb090_alpha_dummy_434 h))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0444 (A : Class) : (nb090_alpha_dummy_439 A) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_439 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_439 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_439 A))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0445 (h : Var) : (nb090_alpha_dummy_441 h) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_441 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_441 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_441 h))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0446 (A : Class) : (nb090_alpha_dummy_439 A) ∈ (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0447 (h : Var) : (nb090_alpha_dummy_441 h) ∈ (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0448 (A : Class) : (nb090_alpha_dummy_446 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_446 A)) (Class.cv (nb090_alpha_dummy_447 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_446 A)) (Class.cv (nb090_alpha_dummy_447 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0449 (h : Var) : (nb090_alpha_dummy_449 h) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_449 h)) (Class.cv (nb090_alpha_dummy_450 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_449 h)) (Class.cv (nb090_alpha_dummy_450 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0450 (A : Class) : (nb090_alpha_dummy_446 A) ∈ (((Class.cv (nb090_alpha_dummy_446 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_447 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0451 (h : Var) : (nb090_alpha_dummy_449 h) ∈ (((Class.cv (nb090_alpha_dummy_449 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_450 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0452 (A : Class) : (nb090_alpha_dummy_447 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_446 A)) (Class.cv (nb090_alpha_dummy_447 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_446 A)) (Class.cv (nb090_alpha_dummy_447 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0453 (h : Var) : (nb090_alpha_dummy_450 h) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_449 h)) (Class.cv (nb090_alpha_dummy_450 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_449 h)) (Class.cv (nb090_alpha_dummy_450 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0454 (A : Class) : (nb090_alpha_dummy_447 A) ∈ (((Class.cv (nb090_alpha_dummy_446 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_447 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0455 (h : Var) : (nb090_alpha_dummy_450 h) ∈ (((Class.cv (nb090_alpha_dummy_449 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_450 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0456 (A : Class) : (nb090_alpha_dummy_446 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_446 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_447 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0457 (h : Var) : (nb090_alpha_dummy_449 h) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_449 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_450 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0458 (A : Class) : (nb090_alpha_dummy_446 A) ∈ (((Class.cv (nb090_alpha_dummy_446 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_446 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0459 (h : Var) : (nb090_alpha_dummy_449 h) ∈ (((Class.cv (nb090_alpha_dummy_449 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_449 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0460 (A : Class) : (nb090_alpha_dummy_447 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_446 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_447 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0461 (h : Var) : (nb090_alpha_dummy_450 h) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_449 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_450 h)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0462 (A : Class) : (nb090_alpha_dummy_447 A) ∈ (((Class.cv (nb090_alpha_dummy_447 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_447 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0463 (h : Var) : (nb090_alpha_dummy_450 h) ∈ (((Class.cv (nb090_alpha_dummy_450 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_450 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0464 (A : Class) : (nb090_alpha_dummy_424 A) ∈ (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_424 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0465 (A : Class) : (nb090_alpha_dummy_424 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_431 A) (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_423 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_431 A) (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_424 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_432 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0464 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0464 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0466 (h : Var) : (nb090_alpha_dummy_427 h) ∈ (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_427 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0467 (h : Var) : (nb090_alpha_dummy_427 h) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_433 h) (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_426 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_433 h) (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_427 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_434 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0466 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0466 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0468 (A : Class) : (nb090_alpha_dummy_424 A) ∈ (((Class.cab (nb090_alpha_dummy_431 A) (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_424 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_432 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_431 A) (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_424 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_432 A))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0464 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0464 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0469 (h : Var) : (nb090_alpha_dummy_427 h) ∈ (((Class.cab (nb090_alpha_dummy_433 h) (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_427 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_434 h))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_433 h) (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_427 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_434 h))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0466 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0466 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0470 (A : Class) : (nb090_alpha_dummy_432 A) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_432 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0471 (h : Var) : (nb090_alpha_dummy_434 h) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_434 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0472 (A : Class) : (nb090_alpha_dummy_432 A) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0473 (h : Var) : (nb090_alpha_dummy_434 h) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0474 (A : Class) : (nb090_alpha_dummy_423 A) ∈ (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_425 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0475 (A : Class) : (nb090_alpha_dummy_423 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_467 A) (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_423 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_467 A) (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_425 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_468 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0474 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0474 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0476 (h : Var) : (nb090_alpha_dummy_426 h) ∈ (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_428 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0477 (h : Var) : (nb090_alpha_dummy_426 h) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_469 h) (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_426 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_469 h) (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_428 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_470 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0476 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0476 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0478 (A : Class) : (nb090_alpha_dummy_423 A) ∈ (((Class.cab (nb090_alpha_dummy_467 A) (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_423 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_468 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_467 A) (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_423 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_468 A))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0474 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0474 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0479 (h : Var) : (nb090_alpha_dummy_426 h) ∈ (((Class.cab (nb090_alpha_dummy_469 h) (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_426 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_470 h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_469 h) (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_426 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_470 h))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0476 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0476 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0480 (A : Class) : (nb090_alpha_dummy_468 A) ∈ (((Class.cv (nb090_alpha_dummy_468 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0481 (h : Var) : (nb090_alpha_dummy_470 h) ∈ (((Class.cv (nb090_alpha_dummy_470 h))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0482 (A : Class) : (nb090_alpha_dummy_475 A) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_475 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_475 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_475 A))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0483 (h : Var) : (nb090_alpha_dummy_477 h) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_477 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_477 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_477 h))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0484 (A : Class) : (nb090_alpha_dummy_475 A) ∈ (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0485 (h : Var) : (nb090_alpha_dummy_477 h) ∈ (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0486 (A : Class) : (nb090_alpha_dummy_482 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_482 A)) (Class.cv (nb090_alpha_dummy_483 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_482 A)) (Class.cv (nb090_alpha_dummy_483 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0487 (h : Var) : (nb090_alpha_dummy_485 h) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_485 h)) (Class.cv (nb090_alpha_dummy_486 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_485 h)) (Class.cv (nb090_alpha_dummy_486 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0488 (A : Class) : (nb090_alpha_dummy_482 A) ∈ (((Class.cv (nb090_alpha_dummy_482 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_483 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0489 (h : Var) : (nb090_alpha_dummy_485 h) ∈ (((Class.cv (nb090_alpha_dummy_485 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_486 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0490 (A : Class) : (nb090_alpha_dummy_483 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_482 A)) (Class.cv (nb090_alpha_dummy_483 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_482 A)) (Class.cv (nb090_alpha_dummy_483 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0491 (h : Var) : (nb090_alpha_dummy_486 h) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_485 h)) (Class.cv (nb090_alpha_dummy_486 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_485 h)) (Class.cv (nb090_alpha_dummy_486 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0492 (A : Class) : (nb090_alpha_dummy_483 A) ∈ (((Class.cv (nb090_alpha_dummy_482 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_483 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0493 (h : Var) : (nb090_alpha_dummy_486 h) ∈ (((Class.cv (nb090_alpha_dummy_485 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_486 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0494 (A : Class) : (nb090_alpha_dummy_482 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_482 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_483 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0495 (h : Var) : (nb090_alpha_dummy_485 h) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_485 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_486 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0496 (A : Class) : (nb090_alpha_dummy_482 A) ∈ (((Class.cv (nb090_alpha_dummy_482 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_482 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
