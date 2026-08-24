import NAR4C077C001Part008

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

theorem nb077_support_mem_0304 (F : Class) (I : Class) : (nb077_alpha_dummy_297 F I) ∈ (((syn_ccompl (Class.cv (nb077_alpha_dummy_296 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_297 F I)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0305 (x : Var) : (nb077_alpha_dummy_300 x) ∈ (((syn_ccompl (Class.cv (nb077_alpha_dummy_299 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_300 x)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0306 (F : Class) (I : Class) : (nb077_alpha_dummy_297 F I) ∈ (((Class.cv (nb077_alpha_dummy_297 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_297 F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0307 (x : Var) : (nb077_alpha_dummy_300 x) ∈ (((Class.cv (nb077_alpha_dummy_300 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_300 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0308 (F : Class) (I : Class) : (nb077_alpha_dummy_061 F I) ∈ (((Class.cv (nb077_alpha_dummy_061 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_060 F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0309 (F : Class) (I : Class) : (nb077_alpha_dummy_061 F I) ∈ (((syn_ccompl (Class.cab (nb077_alpha_dummy_311 F I) (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_061 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_311 F I) (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_060 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0308 F I) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0308 F I) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0310 (x : Var) : (nb077_alpha_dummy_064 x) ∈ (((Class.cv (nb077_alpha_dummy_064 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_063 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0311 (x : Var) : (nb077_alpha_dummy_064 x) ∈ (((syn_ccompl (Class.cab (nb077_alpha_dummy_313 x) (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_064 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_314 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_313 x) (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_063 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_314 x))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0310 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0310 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0312 (F : Class) (I : Class) : (nb077_alpha_dummy_061 F I) ∈ (((Class.cab (nb077_alpha_dummy_311 F I) (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_061 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_311 F I) (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_061 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0308 F I) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0308 F I) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0313 (x : Var) : (nb077_alpha_dummy_064 x) ∈ (((Class.cab (nb077_alpha_dummy_313 x) (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_064 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_314 x))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_313 x) (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_064 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_314 x))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0310 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0310 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0314 (F : Class) (I : Class) : (nb077_alpha_dummy_312 F I) ∈ (((Class.cv (nb077_alpha_dummy_312 F I))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0315 (x : Var) : (nb077_alpha_dummy_314 x) ∈ (((Class.cv (nb077_alpha_dummy_314 x))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0316 (F : Class) (I : Class) : (nb077_alpha_dummy_319 F I) ∈ (((Wff.classMem (Class.cv (nb077_alpha_dummy_319 F I)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_319 F I)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_319 F I))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0317 (x : Var) : (nb077_alpha_dummy_321 x) ∈ (((Wff.classMem (Class.cv (nb077_alpha_dummy_321 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_321 x)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_321 x))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0318 (F : Class) (I : Class) : (nb077_alpha_dummy_319 F I) ∈ (((Class.cv (nb077_alpha_dummy_319 F I))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0319 (x : Var) : (nb077_alpha_dummy_321 x) ∈ (((Class.cv (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0320 (F : Class) (I : Class) : (nb077_alpha_dummy_326 F I) ∈ (((syn_cnin (Class.cv (nb077_alpha_dummy_326 F I)) (Class.cv (nb077_alpha_dummy_327 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_326 F I)) (Class.cv (nb077_alpha_dummy_327 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0321 (x : Var) : (nb077_alpha_dummy_329 x) ∈ (((syn_cnin (Class.cv (nb077_alpha_dummy_329 x)) (Class.cv (nb077_alpha_dummy_330 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_329 x)) (Class.cv (nb077_alpha_dummy_330 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0322 (F : Class) (I : Class) : (nb077_alpha_dummy_326 F I) ∈ (((Class.cv (nb077_alpha_dummy_326 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_327 F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0323 (x : Var) : (nb077_alpha_dummy_329 x) ∈ (((Class.cv (nb077_alpha_dummy_329 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_330 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0324 (F : Class) (I : Class) : (nb077_alpha_dummy_327 F I) ∈ (((syn_cnin (Class.cv (nb077_alpha_dummy_326 F I)) (Class.cv (nb077_alpha_dummy_327 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_326 F I)) (Class.cv (nb077_alpha_dummy_327 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0325 (x : Var) : (nb077_alpha_dummy_330 x) ∈ (((syn_cnin (Class.cv (nb077_alpha_dummy_329 x)) (Class.cv (nb077_alpha_dummy_330 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_329 x)) (Class.cv (nb077_alpha_dummy_330 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0326 (F : Class) (I : Class) : (nb077_alpha_dummy_327 F I) ∈ (((Class.cv (nb077_alpha_dummy_326 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_327 F I))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0327 (x : Var) : (nb077_alpha_dummy_330 x) ∈ (((Class.cv (nb077_alpha_dummy_329 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_330 x))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0328 (F : Class) (I : Class) : (nb077_alpha_dummy_326 F I) ∈ (((syn_ccompl (Class.cv (nb077_alpha_dummy_326 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_327 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0329 (x : Var) : (nb077_alpha_dummy_329 x) ∈ (((syn_ccompl (Class.cv (nb077_alpha_dummy_329 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_330 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0330 (F : Class) (I : Class) : (nb077_alpha_dummy_326 F I) ∈ (((Class.cv (nb077_alpha_dummy_326 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_326 F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0331 (x : Var) : (nb077_alpha_dummy_329 x) ∈ (((Class.cv (nb077_alpha_dummy_329 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_329 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0332 (F : Class) (I : Class) : (nb077_alpha_dummy_327 F I) ∈ (((syn_ccompl (Class.cv (nb077_alpha_dummy_326 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_327 F I)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0333 (x : Var) : (nb077_alpha_dummy_330 x) ∈ (((syn_ccompl (Class.cv (nb077_alpha_dummy_329 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_330 x)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0334 (F : Class) (I : Class) : (nb077_alpha_dummy_327 F I) ∈ (((Class.cv (nb077_alpha_dummy_327 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_327 F I))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0335 (x : Var) : (nb077_alpha_dummy_330 x) ∈ (((Class.cv (nb077_alpha_dummy_330 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_330 x))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0336 (F : Class) (I : Class) : (nb077_alpha_dummy_060 F I) ∈ (((Class.cv (nb077_alpha_dummy_061 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_060 F I))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0337 (F : Class) (I : Class) : (nb077_alpha_dummy_060 F I) ∈ (((syn_ccompl (Class.cab (nb077_alpha_dummy_311 F I) (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_061 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_311 F I) (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_060 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0336 F I) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0336 F I) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0338 (x : Var) : (nb077_alpha_dummy_063 x) ∈ (((Class.cv (nb077_alpha_dummy_064 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_063 x))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0339 (x : Var) : (nb077_alpha_dummy_063 x) ∈ (((syn_ccompl (Class.cab (nb077_alpha_dummy_313 x) (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_064 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_314 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_313 x) (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_063 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_314 x))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0338 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0338 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0340 (F : Class) (I : Class) : (nb077_alpha_dummy_060 F I) ∈ (((Class.cab (nb077_alpha_dummy_311 F I) (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_060 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_311 F I) (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_060 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0336 F I) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0336 F I) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0341 (x : Var) : (nb077_alpha_dummy_063 x) ∈ (((Class.cab (nb077_alpha_dummy_313 x) (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_063 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_314 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_313 x) (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_063 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_314 x))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0338 x) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb077_support_mem_0338 x) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb077_support_mem_0342 (F : Class) (I : Class) : (nb077_alpha_dummy_312 F I) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0343 (x : Var) : (nb077_alpha_dummy_314 x) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_314 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0344 (F : Class) (I : Class) : (nb077_alpha_dummy_312 F I) ∈ (((syn_cphi (Class.cv (nb077_alpha_dummy_312 F I)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_312 F I)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_support_mem_0345 (x : Var) : (nb077_alpha_dummy_314 x) ∈ (((syn_cphi (Class.cv (nb077_alpha_dummy_314 x)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_314 x)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb077_compact_fv_empty_0000 (F : Class) (I : Class) : (nb077_alpha_dummy_009 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_focused_notmem_0000 (F : Class) (I : Class) : (nb077_alpha_dummy_009 F I) ∉ I.fv := by
  change freshVar (((syn_csn (syn_cop (syn_c0c) I))).fv ∪ ((Class.cv (nb077_alpha_dummy_001 F I))).fv) 0 ∉ I.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_left _ (((fv_syn_csn (syn_cop (syn_c0c) I)).symm ▸ (((fv_syn_cop (syn_c0c) I).symm ▸ (Finset.mem_union_right _ (hu)))))))

theorem nb077_wpp_notmem_0000 (F : Class) (I : Class) : (nb077_alpha_dummy_009 F I) ∉ ((syn_csn (syn_cop (syn_c0c) I))).fv := by
  simpa only [nb077_alpha_dummy_009, fv_syn_csn, fv_syn_cop, Finset.mem_union, fv_syn_c0c, not_or] using (And.intro (nb077_compact_fv_empty_0000 F I) (nb077_focused_notmem_0000 F I))

theorem nb077_compact_fv_empty_0001 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_010 x F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_focused_notmem_0001 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_010 x F I) ∉ I.fv := by
  change freshVar (((syn_csn (syn_cop (syn_c0c) I))).fv ∪ ((Class.cv (nb077_alpha_dummy_002 x F I))).fv) 0 ∉ I.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_left _ (((fv_syn_csn (syn_cop (syn_c0c) I)).symm ▸ (((fv_syn_cop (syn_c0c) I).symm ▸ (Finset.mem_union_right _ (hu)))))))

theorem nb077_wpp_notmem_0001 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_010 x F I) ∉ ((syn_csn (syn_cop (syn_c0c) I))).fv := by
  simpa only [nb077_alpha_dummy_010, fv_syn_csn, fv_syn_cop, Finset.mem_union, fv_syn_c0c, not_or] using (And.intro (nb077_compact_fv_empty_0001 x F I) (nb077_focused_notmem_0001 x F I))

theorem nb077_compact_fv_empty_0002 (F : Class) (I : Class) : (nb077_alpha_dummy_007 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_focused_notmem_0002 (F : Class) (I : Class) : (nb077_alpha_dummy_007 F I) ∉ I.fv := by
  change freshVar (((syn_cnin (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I)))).fv ∪ ((syn_cnin (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I)))).fv) 0 ∉ I.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_left _ (((fv_syn_cnin (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I))).symm ▸ (Finset.mem_union_left _ (((fv_syn_csn (syn_cop (syn_c0c) I)).symm ▸ (((fv_syn_cop (syn_c0c) I).symm ▸ (Finset.mem_union_right _ (hu))))))))))

theorem nb077_wpp_notmem_0002 (F : Class) (I : Class) : (nb077_alpha_dummy_007 F I) ∉ ((syn_csn (syn_cop (syn_c0c) I))).fv := by
  simpa only [nb077_alpha_dummy_007, fv_syn_csn, fv_syn_cop, Finset.mem_union, fv_syn_c0c, not_or] using (And.intro (nb077_compact_fv_empty_0002 F I) (nb077_focused_notmem_0002 F I))

theorem nb077_compact_fv_empty_0003 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_008 x F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_focused_notmem_0003 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_008 x F I) ∉ I.fv := by
  change freshVar (((syn_cnin (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I)))).fv ∪ ((syn_cnin (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I)))).fv) 0 ∉ I.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_left _ (((fv_syn_cnin (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I))).symm ▸ (Finset.mem_union_left _ (((fv_syn_csn (syn_cop (syn_c0c) I)).symm ▸ (((fv_syn_cop (syn_c0c) I).symm ▸ (Finset.mem_union_right _ (hu))))))))))

theorem nb077_wpp_notmem_0003 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_008 x F I) ∉ ((syn_csn (syn_cop (syn_c0c) I))).fv := by
  simpa only [nb077_alpha_dummy_008, fv_syn_csn, fv_syn_cop, Finset.mem_union, fv_syn_c0c, not_or] using (And.intro (nb077_compact_fv_empty_0003 x F I) (nb077_focused_notmem_0003 x F I))

theorem nb077_compact_fv_empty_0004 (F : Class) (I : Class) : (nb077_alpha_dummy_001 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_focused_notmem_0004 (F : Class) (I : Class) : (nb077_alpha_dummy_001 F I) ∉ I.fv := by
  change freshVar (((syn_csn (syn_cop (syn_c0c) I))).fv ∪ ((syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F)).fv) 0 ∉ I.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_left _ (((fv_syn_csn (syn_cop (syn_c0c) I)).symm ▸ (((fv_syn_cop (syn_c0c) I).symm ▸ (Finset.mem_union_right _ (hu)))))))

theorem nb077_wpp_notmem_0004 (F : Class) (I : Class) : (nb077_alpha_dummy_001 F I) ∉ ((syn_csn (syn_cop (syn_c0c) I))).fv := by
  simpa only [nb077_alpha_dummy_001, fv_syn_csn, fv_syn_cop, Finset.mem_union, fv_syn_c0c, not_or] using (And.intro (nb077_compact_fv_empty_0004 F I) (nb077_focused_notmem_0004 F I))

theorem nb077_compact_fv_empty_0005 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_002 x F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_focused_notmem_0005 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_002 x F I) ∉ I.fv := by
  change freshVar (((syn_csn (syn_cop (syn_c0c) I))).fv ∪ ((syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F)).fv) 0 ∉ I.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => Finset.mem_union_left _ (((fv_syn_csn (syn_cop (syn_c0c) I)).symm ▸ (((fv_syn_cop (syn_c0c) I).symm ▸ (Finset.mem_union_right _ (hu)))))))

theorem nb077_wpp_notmem_0005 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_002 x F I) ∉ ((syn_csn (syn_cop (syn_c0c) I))).fv := by
  simpa only [nb077_alpha_dummy_002, fv_syn_csn, fv_syn_cop, Finset.mem_union, fv_syn_c0c, not_or] using (And.intro (nb077_compact_fv_empty_0005 x F I) (nb077_focused_notmem_0005 x F I))

theorem nb077_compact_fv_empty_0006 (F : Class) (I : Class) : (nb077_alpha_dummy_004 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_focused_notmem_0006 (F : Class) (I : Class) : (nb077_alpha_dummy_004 F I) ∉ I.fv := by
  change freshVar (((Class.cab (nb077_alpha_dummy_001 F I) (syn_wa (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I))) (syn_wss (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_001 F I))) (Class.cv (nb077_alpha_dummy_001 F I)))))).fv) 1 ∉ I.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 (fun u hu => ((fv_class_cab (nb077_alpha_dummy_001 F I) (syn_wa (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I))) (syn_wss (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_001 F I))) (Class.cv (nb077_alpha_dummy_001 F I))))).symm ▸ (Finset.mem_erase.mpr ⟨(fun h_eq => ((nb077_focused_notmem_0004 F I)) (h_eq ▸ hu)), (((fv_syn_wa (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I))) (syn_wss (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_001 F I))) (Class.cv (nb077_alpha_dummy_001 F I)))).symm ▸ (Finset.mem_union_left _ (((fv_syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I))).symm ▸ (Finset.mem_union_left _ (((fv_syn_csn (syn_cop (syn_c0c) I)).symm ▸ (((fv_syn_cop (syn_c0c) I).symm ▸ (Finset.mem_union_right _ (hu))))))))))))⟩)))

theorem nb077_wpp_notmem_0006 (F : Class) (I : Class) : (nb077_alpha_dummy_004 F I) ∉ ((syn_csn (syn_cop (syn_c0c) I))).fv := by
  simpa only [nb077_alpha_dummy_004, fv_syn_csn, fv_syn_cop, Finset.mem_union, fv_syn_c0c, not_or] using (And.intro (nb077_compact_fv_empty_0006 F I) (nb077_focused_notmem_0006 F I))

theorem nb077_compact_fv_empty_0007 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_006 x F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_focused_notmem_0007 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_006 x F I) ∉ I.fv := by
  change freshVar (((Class.cab (nb077_alpha_dummy_002 x F I) (syn_wa (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I))) (syn_wss (syn_cima (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_002 x F I))) (Class.cv (nb077_alpha_dummy_002 x F I)))))).fv) 1 ∉ I.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 (fun u hu => ((fv_class_cab (nb077_alpha_dummy_002 x F I) (syn_wa (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I))) (syn_wss (syn_cima (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_002 x F I))) (Class.cv (nb077_alpha_dummy_002 x F I))))).symm ▸ (Finset.mem_erase.mpr ⟨(fun h_eq => ((nb077_focused_notmem_0005 x F I)) (h_eq ▸ hu)), (((fv_syn_wa (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I))) (syn_wss (syn_cima (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_002 x F I))) (Class.cv (nb077_alpha_dummy_002 x F I)))).symm ▸ (Finset.mem_union_left _ (((fv_syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I))).symm ▸ (Finset.mem_union_left _ (((fv_syn_csn (syn_cop (syn_c0c) I)).symm ▸ (((fv_syn_cop (syn_c0c) I).symm ▸ (Finset.mem_union_right _ (hu))))))))))))⟩)))

theorem nb077_wpp_notmem_0007 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_006 x F I) ∉ ((syn_csn (syn_cop (syn_c0c) I))).fv := by
  simpa only [nb077_alpha_dummy_006, fv_syn_csn, fv_syn_cop, Finset.mem_union, fv_syn_c0c, not_or] using (And.intro (nb077_compact_fv_empty_0007 x F I) (nb077_focused_notmem_0007 x F I))

theorem nb077_compact_fv_empty_0008 (F : Class) (I : Class) : (nb077_alpha_dummy_003 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_focused_notmem_0008 (F : Class) (I : Class) : (nb077_alpha_dummy_003 F I) ∉ I.fv := by
  change freshVar (((Class.cab (nb077_alpha_dummy_001 F I) (syn_wa (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I))) (syn_wss (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_001 F I))) (Class.cv (nb077_alpha_dummy_001 F I)))))).fv) 0 ∉ I.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => ((fv_class_cab (nb077_alpha_dummy_001 F I) (syn_wa (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I))) (syn_wss (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_001 F I))) (Class.cv (nb077_alpha_dummy_001 F I))))).symm ▸ (Finset.mem_erase.mpr ⟨(fun h_eq => ((nb077_focused_notmem_0004 F I)) (h_eq ▸ hu)), (((fv_syn_wa (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I))) (syn_wss (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_001 F I))) (Class.cv (nb077_alpha_dummy_001 F I)))).symm ▸ (Finset.mem_union_left _ (((fv_syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I))).symm ▸ (Finset.mem_union_left _ (((fv_syn_csn (syn_cop (syn_c0c) I)).symm ▸ (((fv_syn_cop (syn_c0c) I).symm ▸ (Finset.mem_union_right _ (hu))))))))))))⟩)))

theorem nb077_wpp_notmem_0008 (F : Class) (I : Class) : (nb077_alpha_dummy_003 F I) ∉ ((syn_csn (syn_cop (syn_c0c) I))).fv := by
  simpa only [nb077_alpha_dummy_003, fv_syn_csn, fv_syn_cop, Finset.mem_union, fv_syn_c0c, not_or] using (And.intro (nb077_compact_fv_empty_0008 F I) (nb077_focused_notmem_0008 F I))

theorem nb077_compact_fv_empty_0009 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_005 x F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_focused_notmem_0009 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_005 x F I) ∉ I.fv := by
  change freshVar (((Class.cab (nb077_alpha_dummy_002 x F I) (syn_wa (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I))) (syn_wss (syn_cima (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_002 x F I))) (Class.cv (nb077_alpha_dummy_002 x F I)))))).fv) 0 ∉ I.fv
  exact NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 (fun u hu => ((fv_class_cab (nb077_alpha_dummy_002 x F I) (syn_wa (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I))) (syn_wss (syn_cima (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_002 x F I))) (Class.cv (nb077_alpha_dummy_002 x F I))))).symm ▸ (Finset.mem_erase.mpr ⟨(fun h_eq => ((nb077_focused_notmem_0005 x F I)) (h_eq ▸ hu)), (((fv_syn_wa (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I))) (syn_wss (syn_cima (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_002 x F I))) (Class.cv (nb077_alpha_dummy_002 x F I)))).symm ▸ (Finset.mem_union_left _ (((fv_syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I))).symm ▸ (Finset.mem_union_left _ (((fv_syn_csn (syn_cop (syn_c0c) I)).symm ▸ (((fv_syn_cop (syn_c0c) I).symm ▸ (Finset.mem_union_right _ (hu))))))))))))⟩)))

theorem nb077_wpp_notmem_0009 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_005 x F I) ∉ ((syn_csn (syn_cop (syn_c0c) I))).fv := by
  simpa only [nb077_alpha_dummy_005, fv_syn_csn, fv_syn_cop, Finset.mem_union, fv_syn_c0c, not_or] using (And.intro (nb077_compact_fv_empty_0009 x F I) (nb077_focused_notmem_0009 x F I))

theorem nb077_compact_envfresh_0000 (x : Var) (F : Class) (I : Class) : TEnvFresh [((nb077_alpha_dummy_009 F I), (nb077_alpha_dummy_010 x F I)), ((nb077_alpha_dummy_007 F I), (nb077_alpha_dummy_008 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_csn (syn_cop (syn_c0c) I))).fv := by
  exact (TEnvFresh.consFresh (nb077_alpha_dummy_009 F I) (nb077_alpha_dummy_010 x F I) (nb077_wpp_notmem_0000 F I) (nb077_wpp_notmem_0001 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_007 F I) (nb077_alpha_dummy_008 x F I) (nb077_wpp_notmem_0002 F I) (nb077_wpp_notmem_0003 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_001 F I) (nb077_alpha_dummy_002 x F I) (nb077_wpp_notmem_0004 F I) (nb077_wpp_notmem_0005 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_004 F I) (nb077_alpha_dummy_006 x F I) (nb077_wpp_notmem_0006 F I) (nb077_wpp_notmem_0007 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_003 F I) (nb077_alpha_dummy_005 x F I) (nb077_wpp_notmem_0008 F I) (nb077_wpp_notmem_0009 x F I) (TEnvFresh.nil ((syn_csn (syn_cop (syn_c0c) I))).fv))))))

noncomputable def nb077_wpp_refl_0000 (x : Var) (F : Class) (I : Class) : TReflOn [((nb077_alpha_dummy_009 F I), (nb077_alpha_dummy_010 x F I)), ((nb077_alpha_dummy_007 F I), (nb077_alpha_dummy_008 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_csn (syn_cop (syn_c0c) I))).fv :=
  TEnvFresh.reflOn (nb077_compact_envfresh_0000 x F I)

theorem nb077_compact_envfresh_0001 (x : Var) (F : Class) (I : Class) : TEnvFresh [((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_csn (syn_cop (syn_c0c) I))).fv := by
  exact (TEnvFresh.consFresh (nb077_alpha_dummy_001 F I) (nb077_alpha_dummy_002 x F I) (nb077_wpp_notmem_0004 F I) (nb077_wpp_notmem_0005 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_004 F I) (nb077_alpha_dummy_006 x F I) (nb077_wpp_notmem_0006 F I) (nb077_wpp_notmem_0007 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_003 F I) (nb077_alpha_dummy_005 x F I) (nb077_wpp_notmem_0008 F I) (nb077_wpp_notmem_0009 x F I) (TEnvFresh.nil ((syn_csn (syn_cop (syn_c0c) I))).fv))))

noncomputable def nb077_wpp_refl_0001 (x : Var) (F : Class) (I : Class) : TReflOn [((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_csn (syn_cop (syn_c0c) I))).fv :=
  TEnvFresh.reflOn (nb077_compact_envfresh_0001 x F I)

theorem nb077_compact_fv_empty_0010 (F : Class) (I : Class) : (nb077_alpha_dummy_035 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0010 (F : Class) (I : Class) : (nb077_alpha_dummy_035 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_035, fv_syn_c1c] using (nb077_compact_fv_empty_0010 F I)

theorem nb077_compact_fv_empty_0011 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_038 x F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0011 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_038 x F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_038, fv_syn_c1c] using (nb077_compact_fv_empty_0011 x F I)

theorem nb077_compact_fv_empty_0012 (F : Class) (I : Class) : (nb077_alpha_dummy_034 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0012 (F : Class) (I : Class) : (nb077_alpha_dummy_034 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_034, fv_syn_c1c] using (nb077_compact_fv_empty_0012 F I)

theorem nb077_compact_fv_empty_0013 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_037 x F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0013 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_037 x F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_037, fv_syn_c1c] using (nb077_compact_fv_empty_0013 x F I)

theorem nb077_compact_fv_empty_0014 (F : Class) (I : Class) : (nb077_alpha_dummy_033 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0014 (F : Class) (I : Class) : (nb077_alpha_dummy_033 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_033, fv_syn_c1c] using (nb077_compact_fv_empty_0014 F I)

theorem nb077_compact_fv_empty_0015 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_036 x F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0015 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_036 x F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_036, fv_syn_c1c] using (nb077_compact_fv_empty_0015 x F I)

theorem nb077_compact_fv_empty_0016 (F : Class) (I : Class) : (nb077_alpha_dummy_031 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0016 (F : Class) (I : Class) : (nb077_alpha_dummy_031 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_031, fv_syn_c1c] using (nb077_compact_fv_empty_0016 F I)

theorem nb077_compact_fv_empty_0017 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_032 x F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0017 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_032 x F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_032, fv_syn_c1c] using (nb077_compact_fv_empty_0017 x F I)

theorem nb077_compact_fv_empty_0018 (F : Class) (I : Class) : (nb077_alpha_dummy_027 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0018 (F : Class) (I : Class) : (nb077_alpha_dummy_027 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_027, fv_syn_c1c] using (nb077_compact_fv_empty_0018 F I)

theorem nb077_compact_fv_empty_0019 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_029 x F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0019 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_029 x F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_029, fv_syn_c1c] using (nb077_compact_fv_empty_0019 x F I)

theorem nb077_compact_fv_empty_0020 (F : Class) (I : Class) : (nb077_alpha_dummy_028 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0020 (F : Class) (I : Class) : (nb077_alpha_dummy_028 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_028, fv_syn_c1c] using (nb077_compact_fv_empty_0020 F I)

theorem nb077_compact_fv_empty_0021 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_030 x F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0021 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_030 x F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_030, fv_syn_c1c] using (nb077_compact_fv_empty_0021 x F I)

theorem nb077_compact_fv_empty_0022 (F : Class) (I : Class) : (nb077_alpha_dummy_020 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0022 (F : Class) (I : Class) : (nb077_alpha_dummy_020 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_020, fv_syn_c1c] using (nb077_compact_fv_empty_0022 F I)

theorem nb077_compact_fv_empty_0023 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_022 x F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0023 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_022 x F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_022, fv_syn_c1c] using (nb077_compact_fv_empty_0023 x F I)

theorem nb077_compact_fv_empty_0024 (F : Class) (I : Class) : (nb077_alpha_dummy_019 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0024 (F : Class) (I : Class) : (nb077_alpha_dummy_019 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_019, fv_syn_c1c] using (nb077_compact_fv_empty_0024 F I)

theorem nb077_compact_fv_empty_0025 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_021 x F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0025 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_021 x F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_021, fv_syn_c1c] using (nb077_compact_fv_empty_0025 x F I)

theorem nb077_compact_fv_empty_0026 (F : Class) (I : Class) : (nb077_alpha_dummy_025 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0026 (F : Class) (I : Class) : (nb077_alpha_dummy_025 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_025, fv_syn_c1c] using (nb077_compact_fv_empty_0026 F I)

theorem nb077_compact_fv_empty_0027 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_026 x F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0027 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_026 x F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_026, fv_syn_c1c] using (nb077_compact_fv_empty_0027 x F I)

theorem nb077_compact_fv_empty_0028 (F : Class) (I : Class) : (nb077_alpha_dummy_023 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0028 (F : Class) (I : Class) : (nb077_alpha_dummy_023 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_023, fv_syn_c1c] using (nb077_compact_fv_empty_0028 F I)

theorem nb077_compact_fv_empty_0029 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_024 x F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0029 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_024 x F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_024, fv_syn_c1c] using (nb077_compact_fv_empty_0029 x F I)

theorem nb077_compact_fv_empty_0030 (F : Class) (I : Class) : (nb077_alpha_dummy_016 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0030 (F : Class) (I : Class) : (nb077_alpha_dummy_016 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_016, fv_syn_c1c] using (nb077_compact_fv_empty_0030 F I)

theorem nb077_compact_fv_empty_0031 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_018 x F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0031 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_018 x F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_018, fv_syn_c1c] using (nb077_compact_fv_empty_0031 x F I)

theorem nb077_compact_fv_empty_0032 (F : Class) (I : Class) : (nb077_alpha_dummy_015 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0032 (F : Class) (I : Class) : (nb077_alpha_dummy_015 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_015, fv_syn_c1c] using (nb077_compact_fv_empty_0032 F I)

theorem nb077_compact_fv_empty_0033 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_017 x F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0033 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_017 x F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_017, fv_syn_c1c] using (nb077_compact_fv_empty_0033 x F I)

theorem nb077_compact_fv_empty_0034 (F : Class) (I : Class) : (nb077_alpha_dummy_013 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0034 (F : Class) (I : Class) : (nb077_alpha_dummy_013 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_013, fv_syn_c1c] using (nb077_compact_fv_empty_0034 F I)

theorem nb077_compact_fv_empty_0035 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_014 x F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0035 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_014 x F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_014, fv_syn_c1c] using (nb077_compact_fv_empty_0035 x F I)

theorem nb077_compact_fv_empty_0036 (F : Class) (I : Class) : (nb077_alpha_dummy_011 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0036 (F : Class) (I : Class) : (nb077_alpha_dummy_011 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_011, fv_syn_c1c] using (nb077_compact_fv_empty_0036 F I)

theorem nb077_compact_fv_empty_0037 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_012 x F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0037 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_012 x F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_012, fv_syn_c1c] using (nb077_compact_fv_empty_0037 x F I)

theorem nb077_wpp_notmem_0038 (F : Class) (I : Class) : (nb077_alpha_dummy_001 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_001, fv_syn_c1c] using (nb077_compact_fv_empty_0004 F I)

theorem nb077_wpp_notmem_0039 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_002 x F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_002, fv_syn_c1c] using (nb077_compact_fv_empty_0005 x F I)

theorem nb077_wpp_notmem_0040 (F : Class) (I : Class) : (nb077_alpha_dummy_004 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_004, fv_syn_c1c] using (nb077_compact_fv_empty_0006 F I)

theorem nb077_wpp_notmem_0041 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_006 x F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_006, fv_syn_c1c] using (nb077_compact_fv_empty_0007 x F I)

theorem nb077_wpp_notmem_0042 (F : Class) (I : Class) : (nb077_alpha_dummy_003 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_003, fv_syn_c1c] using (nb077_compact_fv_empty_0008 F I)

theorem nb077_wpp_notmem_0043 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_005 x F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_005, fv_syn_c1c] using (nb077_compact_fv_empty_0009 x F I)

theorem nb077_compact_envfresh_0002 (x : Var) (F : Class) (I : Class) : TEnvFresh [((nb077_alpha_dummy_035 F I), (nb077_alpha_dummy_038 x F I)), ((nb077_alpha_dummy_034 F I), (nb077_alpha_dummy_037 x F I)), ((nb077_alpha_dummy_033 F I), (nb077_alpha_dummy_036 x F I)), ((nb077_alpha_dummy_031 F I), (nb077_alpha_dummy_032 x F I)), ((nb077_alpha_dummy_027 F I), (nb077_alpha_dummy_029 x F I)), ((nb077_alpha_dummy_028 F I), (nb077_alpha_dummy_030 x F I)), ((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)), ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)), ((nb077_alpha_dummy_025 F I), (nb077_alpha_dummy_026 x F I)), ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb077_alpha_dummy_035 F I) (nb077_alpha_dummy_038 x F I) (nb077_wpp_notmem_0010 F I) (nb077_wpp_notmem_0011 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_034 F I) (nb077_alpha_dummy_037 x F I) (nb077_wpp_notmem_0012 F I) (nb077_wpp_notmem_0013 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_033 F I) (nb077_alpha_dummy_036 x F I) (nb077_wpp_notmem_0014 F I) (nb077_wpp_notmem_0015 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_031 F I) (nb077_alpha_dummy_032 x F I) (nb077_wpp_notmem_0016 F I) (nb077_wpp_notmem_0017 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_027 F I) (nb077_alpha_dummy_029 x F I) (nb077_wpp_notmem_0018 F I) (nb077_wpp_notmem_0019 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_028 F I) (nb077_alpha_dummy_030 x F I) (nb077_wpp_notmem_0020 F I) (nb077_wpp_notmem_0021 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_020 F I) (nb077_alpha_dummy_022 x F I) (nb077_wpp_notmem_0022 F I) (nb077_wpp_notmem_0023 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_019 F I) (nb077_alpha_dummy_021 x F I) (nb077_wpp_notmem_0024 F I) (nb077_wpp_notmem_0025 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_025 F I) (nb077_alpha_dummy_026 x F I) (nb077_wpp_notmem_0026 F I) (nb077_wpp_notmem_0027 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_023 F I) (nb077_alpha_dummy_024 x F I) (nb077_wpp_notmem_0028 F I) (nb077_wpp_notmem_0029 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_016 F I) (nb077_alpha_dummy_018 x F I) (nb077_wpp_notmem_0030 F I) (nb077_wpp_notmem_0031 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_015 F I) (nb077_alpha_dummy_017 x F I) (nb077_wpp_notmem_0032 F I) (nb077_wpp_notmem_0033 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_013 F I) (nb077_alpha_dummy_014 x F I) (nb077_wpp_notmem_0034 F I) (nb077_wpp_notmem_0035 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_011 F I) (nb077_alpha_dummy_012 x F I) (nb077_wpp_notmem_0036 F I) (nb077_wpp_notmem_0037 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_001 F I) (nb077_alpha_dummy_002 x F I) (nb077_wpp_notmem_0038 F I) (nb077_wpp_notmem_0039 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_004 F I) (nb077_alpha_dummy_006 x F I) (nb077_wpp_notmem_0040 F I) (nb077_wpp_notmem_0041 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_003 F I) (nb077_alpha_dummy_005 x F I) (nb077_wpp_notmem_0042 F I) (nb077_wpp_notmem_0043 x F I) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))

noncomputable def nb077_wpp_refl_0002 (x : Var) (F : Class) (I : Class) : TReflOn [((nb077_alpha_dummy_035 F I), (nb077_alpha_dummy_038 x F I)), ((nb077_alpha_dummy_034 F I), (nb077_alpha_dummy_037 x F I)), ((nb077_alpha_dummy_033 F I), (nb077_alpha_dummy_036 x F I)), ((nb077_alpha_dummy_031 F I), (nb077_alpha_dummy_032 x F I)), ((nb077_alpha_dummy_027 F I), (nb077_alpha_dummy_029 x F I)), ((nb077_alpha_dummy_028 F I), (nb077_alpha_dummy_030 x F I)), ((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)), ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)), ((nb077_alpha_dummy_025 F I), (nb077_alpha_dummy_026 x F I)), ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb077_compact_envfresh_0002 x F I)

theorem nb077_wpp_notmem_0044 (F : Class) (I : Class) : (nb077_alpha_dummy_035 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_035, fv_syn_c0] using (nb077_compact_fv_empty_0010 F I)

theorem nb077_wpp_notmem_0045 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_038 x F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_038, fv_syn_c0] using (nb077_compact_fv_empty_0011 x F I)

theorem nb077_wpp_notmem_0046 (F : Class) (I : Class) : (nb077_alpha_dummy_034 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_034, fv_syn_c0] using (nb077_compact_fv_empty_0012 F I)

theorem nb077_wpp_notmem_0047 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_037 x F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_037, fv_syn_c0] using (nb077_compact_fv_empty_0013 x F I)

theorem nb077_wpp_notmem_0048 (F : Class) (I : Class) : (nb077_alpha_dummy_033 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_033, fv_syn_c0] using (nb077_compact_fv_empty_0014 F I)

theorem nb077_wpp_notmem_0049 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_036 x F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_036, fv_syn_c0] using (nb077_compact_fv_empty_0015 x F I)

theorem nb077_wpp_notmem_0050 (F : Class) (I : Class) : (nb077_alpha_dummy_031 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_031, fv_syn_c0] using (nb077_compact_fv_empty_0016 F I)

theorem nb077_wpp_notmem_0051 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_032 x F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_032, fv_syn_c0] using (nb077_compact_fv_empty_0017 x F I)

theorem nb077_wpp_notmem_0052 (F : Class) (I : Class) : (nb077_alpha_dummy_027 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_027, fv_syn_c0] using (nb077_compact_fv_empty_0018 F I)

theorem nb077_wpp_notmem_0053 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_029 x F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_029, fv_syn_c0] using (nb077_compact_fv_empty_0019 x F I)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
