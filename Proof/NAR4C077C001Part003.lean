import NAR4C077C001Part002

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

noncomputable def nb077_alpha_dummy_300 (x : Var) : Var := (freshVar (((Class.cv x)).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb077_alpha_dummy_301 (F : Class) (I : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb077_alpha_dummy_296 F I)) (Class.cv (nb077_alpha_dummy_297 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_296 F I)) (Class.cv (nb077_alpha_dummy_297 F I)))).fv) 0)

noncomputable def nb077_alpha_dummy_302 (x : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb077_alpha_dummy_299 x)) (Class.cv (nb077_alpha_dummy_300 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_299 x)) (Class.cv (nb077_alpha_dummy_300 x)))).fv) 0)

noncomputable def nb077_alpha_dummy_303 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_296 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_297 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_304 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_299 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_300 x))).fv) 0)

noncomputable def nb077_alpha_dummy_305 (F : Class) (I : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb077_alpha_dummy_296 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_297 F I)))).fv) 0)

noncomputable def nb077_alpha_dummy_306 (x : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb077_alpha_dummy_299 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_300 x)))).fv) 0)

noncomputable def nb077_alpha_dummy_307 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_296 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_296 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_308 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_299 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_299 x))).fv) 0)

noncomputable def nb077_alpha_dummy_309 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_297 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_297 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_310 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_300 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_300 x))).fv) 0)

noncomputable def nb077_alpha_dummy_311 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_061 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_060 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_312 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_061 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_060 F I))).fv) 1)

noncomputable def nb077_alpha_dummy_313 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_064 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_063 x))).fv) 0)

noncomputable def nb077_alpha_dummy_314 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_064 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_063 x))).fv) 1)

noncomputable def nb077_alpha_dummy_315 (F : Class) (I : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb077_alpha_dummy_311 F I) (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_061 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_311 F I) (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_060 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb077_alpha_dummy_316 (x : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb077_alpha_dummy_313 x) (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_064 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_314 x)))))))).fv ∪ ((syn_ccompl (Class.cab (nb077_alpha_dummy_313 x) (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_063 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_314 x))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb077_alpha_dummy_317 (F : Class) (I : Class) : Var := (freshVar (((Class.cab (nb077_alpha_dummy_311 F I) (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_061 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_311 F I) (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_061 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I))))))).fv) 0)

noncomputable def nb077_alpha_dummy_318 (x : Var) : Var := (freshVar (((Class.cab (nb077_alpha_dummy_313 x) (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_064 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_314 x))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_313 x) (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_064 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_314 x))))))).fv) 0)

noncomputable def nb077_alpha_dummy_319 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_312 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_320 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_312 F I))).fv) 1)

noncomputable def nb077_alpha_dummy_321 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_314 x))).fv) 0)

noncomputable def nb077_alpha_dummy_322 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_314 x))).fv) 1)

noncomputable def nb077_alpha_dummy_323 (F : Class) (I : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb077_alpha_dummy_319 F I)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_319 F I)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_319 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_324 (x : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb077_alpha_dummy_321 x)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb077_alpha_dummy_321 x)) (syn_c1c))).fv ∪ ((Class.cv (nb077_alpha_dummy_321 x))).fv) 0)

noncomputable def nb077_alpha_dummy_325 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_319 F I))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb077_alpha_dummy_326 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_319 F I))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb077_alpha_dummy_327 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_319 F I))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb077_alpha_dummy_328 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb077_alpha_dummy_329 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb077_alpha_dummy_330 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_321 x))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb077_alpha_dummy_331 (F : Class) (I : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb077_alpha_dummy_326 F I)) (Class.cv (nb077_alpha_dummy_327 F I)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_326 F I)) (Class.cv (nb077_alpha_dummy_327 F I)))).fv) 0)

noncomputable def nb077_alpha_dummy_332 (x : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb077_alpha_dummy_329 x)) (Class.cv (nb077_alpha_dummy_330 x)))).fv ∪ ((syn_cnin (Class.cv (nb077_alpha_dummy_329 x)) (Class.cv (nb077_alpha_dummy_330 x)))).fv) 0)

noncomputable def nb077_alpha_dummy_333 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_326 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_327 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_334 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_329 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_330 x))).fv) 0)

noncomputable def nb077_alpha_dummy_335 (F : Class) (I : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb077_alpha_dummy_326 F I)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_327 F I)))).fv) 0)

noncomputable def nb077_alpha_dummy_336 (x : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb077_alpha_dummy_329 x)))).fv ∪ ((syn_ccompl (Class.cv (nb077_alpha_dummy_330 x)))).fv) 0)

noncomputable def nb077_alpha_dummy_337 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_326 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_326 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_338 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_329 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_329 x))).fv) 0)

noncomputable def nb077_alpha_dummy_339 (F : Class) (I : Class) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_327 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_327 F I))).fv) 0)

noncomputable def nb077_alpha_dummy_340 (x : Var) : Var := (freshVar (((Class.cv (nb077_alpha_dummy_330 x))).fv ∪ ((Class.cv (nb077_alpha_dummy_330 x))).fv) 0)

noncomputable def nb077_alpha_dummy_341 (F : Class) (I : Class) : Var := (freshVar (((Class.cab (nb077_alpha_dummy_311 F I) (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_060 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_311 F I) (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_060 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb077_alpha_dummy_342 (x : Var) : Var := (freshVar (((Class.cab (nb077_alpha_dummy_313 x) (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_063 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_314 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_313 x) (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_063 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_314 x))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb077_alpha_dummy_343 (F : Class) (I : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb077_alpha_dummy_344 (x : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_314 x))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb077_alpha_dummy_345 (F : Class) (I : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb077_alpha_dummy_312 F I)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_312 F I)))).fv) 0)

noncomputable def nb077_alpha_dummy_346 (x : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb077_alpha_dummy_314 x)))).fv ∪ ((syn_cphi (Class.cv (nb077_alpha_dummy_314 x)))).fv) 0)

theorem nb077_fresh_000 (F : Class) (I : Class) : (nb077_alpha_dummy_003 F I) ∉ (((Class.cab (nb077_alpha_dummy_001 F I) (syn_wa (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I))) (syn_wss (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_001 F I))) (Class.cv (nb077_alpha_dummy_001 F I)))))).fv) := by
  simpa only [nb077_alpha_dummy_003] using freshVar_not_mem (((Class.cab (nb077_alpha_dummy_001 F I) (syn_wa (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I))) (syn_wss (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_001 F I))) (Class.cv (nb077_alpha_dummy_001 F I)))))).fv) 0

theorem nb077_fresh_001 (F : Class) (I : Class) : (nb077_alpha_dummy_004 F I) ∉ (((Class.cab (nb077_alpha_dummy_001 F I) (syn_wa (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I))) (syn_wss (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_001 F I))) (Class.cv (nb077_alpha_dummy_001 F I)))))).fv) := by
  simpa only [nb077_alpha_dummy_004] using freshVar_not_mem (((Class.cab (nb077_alpha_dummy_001 F I) (syn_wa (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I))) (syn_wss (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_001 F I))) (Class.cv (nb077_alpha_dummy_001 F I)))))).fv) 1

theorem nb077_distinct_002 (F : Class) (I : Class) : (nb077_alpha_dummy_003 F I) ≠ (nb077_alpha_dummy_004 F I) := by
  simpa only [nb077_alpha_dummy_003, nb077_alpha_dummy_004] using
    (freshVar_injective (((Class.cab (nb077_alpha_dummy_001 F I) (syn_wa (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_001 F I))) (syn_wss (syn_cima (syn_cpprod (syn_cmpt (nb077_alpha_dummy_000 F I) (syn_cvv) (syn_cplc (Class.cv (nb077_alpha_dummy_000 F I)) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_001 F I))) (Class.cv (nb077_alpha_dummy_001 F I)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_003 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_005 x F I) ∉ (((Class.cab (nb077_alpha_dummy_002 x F I) (syn_wa (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I))) (syn_wss (syn_cima (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_002 x F I))) (Class.cv (nb077_alpha_dummy_002 x F I)))))).fv) := by
  simpa only [nb077_alpha_dummy_005] using freshVar_not_mem (((Class.cab (nb077_alpha_dummy_002 x F I) (syn_wa (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I))) (syn_wss (syn_cima (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_002 x F I))) (Class.cv (nb077_alpha_dummy_002 x F I)))))).fv) 0

theorem nb077_fresh_004 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_006 x F I) ∉ (((Class.cab (nb077_alpha_dummy_002 x F I) (syn_wa (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I))) (syn_wss (syn_cima (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_002 x F I))) (Class.cv (nb077_alpha_dummy_002 x F I)))))).fv) := by
  simpa only [nb077_alpha_dummy_006] using freshVar_not_mem (((Class.cab (nb077_alpha_dummy_002 x F I) (syn_wa (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I))) (syn_wss (syn_cima (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_002 x F I))) (Class.cv (nb077_alpha_dummy_002 x F I)))))).fv) 1

theorem nb077_distinct_005 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_005 x F I) ≠ (nb077_alpha_dummy_006 x F I) := by
  simpa only [nb077_alpha_dummy_005, nb077_alpha_dummy_006] using
    (freshVar_injective (((Class.cab (nb077_alpha_dummy_002 x F I) (syn_wa (syn_wss (syn_csn (syn_cop (syn_c0c) I)) (Class.cv (nb077_alpha_dummy_002 x F I))) (syn_wss (syn_cima (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (Class.cv x) (syn_c1c))) F) (Class.cv (nb077_alpha_dummy_002 x F I))) (Class.cv (nb077_alpha_dummy_002 x F I)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_006 (F : Class) (I : Class) : (nb077_alpha_dummy_049 F I) ∉ (((Class.cab (nb077_alpha_dummy_019 F I) (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_015 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_019 F I) (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_015 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb077_alpha_dummy_049] using freshVar_not_mem (((Class.cab (nb077_alpha_dummy_019 F I) (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_015 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_019 F I) (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_015 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb077_fresh_007 (F : Class) (I : Class) : (nb077_alpha_dummy_025 F I) ∉ (((Class.cab (nb077_alpha_dummy_019 F I) (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_016 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_019 F I) (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_016 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))))))).fv) := by
  simpa only [nb077_alpha_dummy_025] using freshVar_not_mem (((Class.cab (nb077_alpha_dummy_019 F I) (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_016 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_019 F I) (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_016 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))))))).fv) 0

theorem nb077_fresh_008 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_050 x F I) ∉ (((Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_017 x F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_017 x F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb077_alpha_dummy_050] using freshVar_not_mem (((Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_017 x F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_017 x F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb077_fresh_009 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_026 x F I) ∉ (((Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_018 x F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_018 x F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))))))).fv) := by
  simpa only [nb077_alpha_dummy_026] using freshVar_not_mem (((Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_018 x F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I) (Class.cv (nb077_alpha_dummy_018 x F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))))))).fv) 0

theorem nb077_fresh_010 (F : Class) (I : Class) : (nb077_alpha_dummy_073 F I) ∉ (((Class.cab (nb077_alpha_dummy_067 F I) (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_059 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_067 F I) (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_059 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))))))).fv) := by
  simpa only [nb077_alpha_dummy_073] using freshVar_not_mem (((Class.cab (nb077_alpha_dummy_067 F I) (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_059 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_067 F I) (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_059 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))))))).fv) 0

theorem nb077_fresh_011 (F : Class) (I : Class) : (nb077_alpha_dummy_097 F I) ∉ (((Class.cab (nb077_alpha_dummy_067 F I) (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_060 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_067 F I) (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_060 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb077_alpha_dummy_097] using freshVar_not_mem (((Class.cab (nb077_alpha_dummy_067 F I) (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_060 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_067 F I) (syn_wrex (nb077_alpha_dummy_068 F I) (Class.cv (nb077_alpha_dummy_060 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_067 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_068 F I))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb077_fresh_012 (x : Var) : (nb077_alpha_dummy_074 x) ∉ (((Class.cab (nb077_alpha_dummy_069 x) (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_062 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_069 x) (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_062 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))))))).fv) := by
  simpa only [nb077_alpha_dummy_074] using freshVar_not_mem (((Class.cab (nb077_alpha_dummy_069 x) (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_062 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_069 x) (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_062 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))))))).fv) 0

theorem nb077_fresh_013 (x : Var) : (nb077_alpha_dummy_098 x) ∉ (((Class.cab (nb077_alpha_dummy_069 x) (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_063 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_069 x) (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_063 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb077_alpha_dummy_098] using freshVar_not_mem (((Class.cab (nb077_alpha_dummy_069 x) (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_063 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_069 x) (syn_wrex (nb077_alpha_dummy_070 x) (Class.cv (nb077_alpha_dummy_063 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_069 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_070 x))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb077_fresh_014 (F : Class) (I : Class) : (nb077_alpha_dummy_109 F I) ∉ (((Class.cab (nb077_alpha_dummy_103 F I) (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_059 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_103 F I) (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_059 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))))))).fv) := by
  simpa only [nb077_alpha_dummy_109] using freshVar_not_mem (((Class.cab (nb077_alpha_dummy_103 F I) (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_059 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_103 F I) (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_059 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))))))).fv) 0

theorem nb077_fresh_015 (F : Class) (I : Class) : (nb077_alpha_dummy_133 F I) ∉ (((Class.cab (nb077_alpha_dummy_103 F I) (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_061 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_103 F I) (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_061 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb077_alpha_dummy_133] using freshVar_not_mem (((Class.cab (nb077_alpha_dummy_103 F I) (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_061 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_103 F I) (syn_wrex (nb077_alpha_dummy_104 F I) (Class.cv (nb077_alpha_dummy_061 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_103 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_104 F I))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb077_fresh_016 (x : Var) : (nb077_alpha_dummy_110 x) ∉ (((Class.cab (nb077_alpha_dummy_105 x) (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_062 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_105 x) (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_062 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))))))).fv) := by
  simpa only [nb077_alpha_dummy_110] using freshVar_not_mem (((Class.cab (nb077_alpha_dummy_105 x) (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_062 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_105 x) (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_062 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))))))).fv) 0

theorem nb077_fresh_017 (x : Var) : (nb077_alpha_dummy_134 x) ∉ (((Class.cab (nb077_alpha_dummy_105 x) (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_064 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_105 x) (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_064 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb077_alpha_dummy_134] using freshVar_not_mem (((Class.cab (nb077_alpha_dummy_105 x) (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_064 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_105 x) (syn_wrex (nb077_alpha_dummy_106 x) (Class.cv (nb077_alpha_dummy_064 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_105 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_106 x))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb077_fresh_018 (F : Class) (I : Class) : (nb077_alpha_dummy_153 F I) ∉ (((Class.cab (nb077_alpha_dummy_147 F I) (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_139 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_147 F I) (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_139 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))))))).fv) := by
  simpa only [nb077_alpha_dummy_153] using freshVar_not_mem (((Class.cab (nb077_alpha_dummy_147 F I) (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_139 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_147 F I) (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_139 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))))))).fv) 0

theorem nb077_fresh_019 (F : Class) (I : Class) : (nb077_alpha_dummy_177 F I) ∉ (((Class.cab (nb077_alpha_dummy_147 F I) (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_140 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_147 F I) (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_140 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb077_alpha_dummy_177] using freshVar_not_mem (((Class.cab (nb077_alpha_dummy_147 F I) (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_140 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_147 F I) (syn_wrex (nb077_alpha_dummy_148 F I) (Class.cv (nb077_alpha_dummy_140 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_147 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_148 F I))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb077_fresh_020 (x : Var) : (nb077_alpha_dummy_154 x) ∉ (((Class.cab (nb077_alpha_dummy_149 x) (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_142 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_149 x) (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_142 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))))))).fv) := by
  simpa only [nb077_alpha_dummy_154] using freshVar_not_mem (((Class.cab (nb077_alpha_dummy_149 x) (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_142 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_149 x) (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_142 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))))))).fv) 0

theorem nb077_fresh_021 (x : Var) : (nb077_alpha_dummy_178 x) ∉ (((Class.cab (nb077_alpha_dummy_149 x) (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_143 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_149 x) (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_143 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb077_alpha_dummy_178] using freshVar_not_mem (((Class.cab (nb077_alpha_dummy_149 x) (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_143 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_149 x) (syn_wrex (nb077_alpha_dummy_150 x) (Class.cv (nb077_alpha_dummy_143 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_149 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_150 x))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb077_fresh_022 (F : Class) (I : Class) : (nb077_alpha_dummy_189 F I) ∉ (((Class.cab (nb077_alpha_dummy_183 F I) (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_139 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_183 F I) (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_139 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))))))).fv) := by
  simpa only [nb077_alpha_dummy_189] using freshVar_not_mem (((Class.cab (nb077_alpha_dummy_183 F I) (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_139 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_183 F I) (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_139 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))))))).fv) 0

theorem nb077_fresh_023 (F : Class) (I : Class) : (nb077_alpha_dummy_213 F I) ∉ (((Class.cab (nb077_alpha_dummy_183 F I) (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_141 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_183 F I) (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_141 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb077_alpha_dummy_213] using freshVar_not_mem (((Class.cab (nb077_alpha_dummy_183 F I) (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_141 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_183 F I) (syn_wrex (nb077_alpha_dummy_184 F I) (Class.cv (nb077_alpha_dummy_141 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_183 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_184 F I))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb077_fresh_024 (x : Var) : (nb077_alpha_dummy_190 x) ∉ (((Class.cab (nb077_alpha_dummy_185 x) (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_142 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_185 x) (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_142 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))))))).fv) := by
  simpa only [nb077_alpha_dummy_190] using freshVar_not_mem (((Class.cab (nb077_alpha_dummy_185 x) (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_142 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_185 x) (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_142 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))))))).fv) 0

theorem nb077_fresh_025 (x : Var) : (nb077_alpha_dummy_214 x) ∉ (((Class.cab (nb077_alpha_dummy_185 x) (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_144 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_185 x) (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_144 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb077_alpha_dummy_214] using freshVar_not_mem (((Class.cab (nb077_alpha_dummy_185 x) (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_144 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_185 x) (syn_wrex (nb077_alpha_dummy_186 x) (Class.cv (nb077_alpha_dummy_144 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_185 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_186 x))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb077_fresh_026 (F : Class) (I : Class) : (nb077_alpha_dummy_249 F I) ∉ (((Class.cab (nb077_alpha_dummy_219 F I) (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_140 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_219 F I) (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_140 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb077_alpha_dummy_249] using freshVar_not_mem (((Class.cab (nb077_alpha_dummy_219 F I) (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_140 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_219 F I) (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_140 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb077_fresh_027 (F : Class) (I : Class) : (nb077_alpha_dummy_225 F I) ∉ (((Class.cab (nb077_alpha_dummy_219 F I) (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_141 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_219 F I) (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_141 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))))))).fv) := by
  simpa only [nb077_alpha_dummy_225] using freshVar_not_mem (((Class.cab (nb077_alpha_dummy_219 F I) (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_141 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_219 F I) (syn_wrex (nb077_alpha_dummy_220 F I) (Class.cv (nb077_alpha_dummy_141 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_219 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_220 F I))))))).fv) 0

theorem nb077_fresh_028 (x : Var) : (nb077_alpha_dummy_250 x) ∉ (((Class.cab (nb077_alpha_dummy_221 x) (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_143 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_221 x) (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_143 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb077_alpha_dummy_250] using freshVar_not_mem (((Class.cab (nb077_alpha_dummy_221 x) (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_143 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_221 x) (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_143 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb077_fresh_029 (x : Var) : (nb077_alpha_dummy_226 x) ∉ (((Class.cab (nb077_alpha_dummy_221 x) (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_144 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_221 x) (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_144 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))))))).fv) := by
  simpa only [nb077_alpha_dummy_226] using freshVar_not_mem (((Class.cab (nb077_alpha_dummy_221 x) (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_144 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_221 x) (syn_wrex (nb077_alpha_dummy_222 x) (Class.cv (nb077_alpha_dummy_144 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_221 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_222 x))))))).fv) 0

theorem nb077_fresh_030 (F : Class) (I : Class) : (nb077_alpha_dummy_265 F I) ∉ (((Class.cab (nb077_alpha_dummy_259 F I) (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_000 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_259 F I) (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_000 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))))))).fv) := by
  simpa only [nb077_alpha_dummy_265] using freshVar_not_mem (((Class.cab (nb077_alpha_dummy_259 F I) (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_000 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_259 F I) (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_000 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))))))).fv) 0

theorem nb077_fresh_031 (F : Class) (I : Class) : (nb077_alpha_dummy_289 F I) ∉ (((Class.cab (nb077_alpha_dummy_259 F I) (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_255 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_259 F I) (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_255 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb077_alpha_dummy_289] using freshVar_not_mem (((Class.cab (nb077_alpha_dummy_259 F I) (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_255 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_259 F I) (syn_wrex (nb077_alpha_dummy_260 F I) (Class.cv (nb077_alpha_dummy_255 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_259 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_260 F I))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb077_fresh_032 (x : Var) : (nb077_alpha_dummy_290 x) ∉ (((Class.cab (nb077_alpha_dummy_261 x) (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv (nb077_alpha_dummy_256 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_261 x) (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv (nb077_alpha_dummy_256 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb077_alpha_dummy_290] using freshVar_not_mem (((Class.cab (nb077_alpha_dummy_261 x) (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv (nb077_alpha_dummy_256 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_261 x) (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv (nb077_alpha_dummy_256 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb077_fresh_033 (x : Var) : (nb077_alpha_dummy_266 x) ∉ (((Class.cab (nb077_alpha_dummy_261 x) (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv x) (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_261 x) (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv x) (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))))))).fv) := by
  simpa only [nb077_alpha_dummy_266] using freshVar_not_mem (((Class.cab (nb077_alpha_dummy_261 x) (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv x) (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_261 x) (syn_wrex (nb077_alpha_dummy_262 x) (Class.cv x) (Wff.classEq (Class.cv (nb077_alpha_dummy_261 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_262 x))))))).fv) 0

theorem nb077_fresh_034 (F : Class) (I : Class) : (nb077_alpha_dummy_341 F I) ∉ (((Class.cab (nb077_alpha_dummy_311 F I) (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_060 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_311 F I) (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_060 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb077_alpha_dummy_341] using freshVar_not_mem (((Class.cab (nb077_alpha_dummy_311 F I) (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_060 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_311 F I) (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_060 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb077_fresh_035 (F : Class) (I : Class) : (nb077_alpha_dummy_317 F I) ∉ (((Class.cab (nb077_alpha_dummy_311 F I) (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_061 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_311 F I) (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_061 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I))))))).fv) := by
  simpa only [nb077_alpha_dummy_317] using freshVar_not_mem (((Class.cab (nb077_alpha_dummy_311 F I) (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_061 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_311 F I) (syn_wrex (nb077_alpha_dummy_312 F I) (Class.cv (nb077_alpha_dummy_061 F I)) (Wff.classEq (Class.cv (nb077_alpha_dummy_311 F I)) (syn_cphi (Class.cv (nb077_alpha_dummy_312 F I))))))).fv) 0

theorem nb077_fresh_036 (x : Var) : (nb077_alpha_dummy_342 x) ∉ (((Class.cab (nb077_alpha_dummy_313 x) (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_063 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_314 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_313 x) (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_063 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_314 x))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb077_alpha_dummy_342] using freshVar_not_mem (((Class.cab (nb077_alpha_dummy_313 x) (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_063 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_314 x))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_313 x) (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_063 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x)) (syn_cun (syn_cphi (Class.cv (nb077_alpha_dummy_314 x))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb077_fresh_037 (x : Var) : (nb077_alpha_dummy_318 x) ∉ (((Class.cab (nb077_alpha_dummy_313 x) (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_064 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_314 x))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_313 x) (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_064 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_314 x))))))).fv) := by
  simpa only [nb077_alpha_dummy_318] using freshVar_not_mem (((Class.cab (nb077_alpha_dummy_313 x) (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_064 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_314 x))))))).fv ∪ ((Class.cab (nb077_alpha_dummy_313 x) (syn_wrex (nb077_alpha_dummy_314 x) (Class.cv (nb077_alpha_dummy_064 x)) (Wff.classEq (Class.cv (nb077_alpha_dummy_313 x)) (syn_cphi (Class.cv (nb077_alpha_dummy_314 x))))))).fv) 0

theorem nb077_fresh_038 (F : Class) (I : Class) : (nb077_alpha_dummy_259 F I) ∉ (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_255 F I))).fv) := by
  simpa only [nb077_alpha_dummy_259] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_255 F I))).fv) 0

theorem nb077_fresh_039 (F : Class) (I : Class) : (nb077_alpha_dummy_260 F I) ∉ (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_255 F I))).fv) := by
  simpa only [nb077_alpha_dummy_260] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_255 F I))).fv) 1

theorem nb077_distinct_040 (F : Class) (I : Class) : (nb077_alpha_dummy_259 F I) ≠ (nb077_alpha_dummy_260 F I) := by
  simpa only [nb077_alpha_dummy_259, nb077_alpha_dummy_260] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_255 F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_041 (F : Class) (I : Class) : (nb077_alpha_dummy_295 F I) ∉ (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_295] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪ ((syn_c1c)).fv) 0

theorem nb077_fresh_042 (F : Class) (I : Class) : (nb077_alpha_dummy_296 F I) ∉ (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_296] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪ ((syn_c1c)).fv) 1

theorem nb077_fresh_043 (F : Class) (I : Class) : (nb077_alpha_dummy_297 F I) ∉ (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_297] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪ ((syn_c1c)).fv) 2

theorem nb077_distinct_044 (F : Class) (I : Class) : (nb077_alpha_dummy_295 F I) ≠ (nb077_alpha_dummy_296 F I) := by
  simpa only [nb077_alpha_dummy_295, nb077_alpha_dummy_296] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb077_distinct_045 (F : Class) (I : Class) : (nb077_alpha_dummy_295 F I) ≠ (nb077_alpha_dummy_297 F I) := by
  simpa only [nb077_alpha_dummy_295, nb077_alpha_dummy_297] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb077_distinct_046 (F : Class) (I : Class) : (nb077_alpha_dummy_296 F I) ≠ (nb077_alpha_dummy_297 F I) := by
  simpa only [nb077_alpha_dummy_296, nb077_alpha_dummy_297] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_000 F I))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb077_fresh_047 (F : Class) (I : Class) : (nb077_alpha_dummy_019 F I) ∉ (((Class.cv (nb077_alpha_dummy_016 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_015 F I))).fv) := by
  simpa only [nb077_alpha_dummy_019] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_016 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_015 F I))).fv) 0

theorem nb077_fresh_048 (F : Class) (I : Class) : (nb077_alpha_dummy_020 F I) ∉ (((Class.cv (nb077_alpha_dummy_016 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_015 F I))).fv) := by
  simpa only [nb077_alpha_dummy_020] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_016 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_015 F I))).fv) 1

theorem nb077_distinct_049 (F : Class) (I : Class) : (nb077_alpha_dummy_019 F I) ≠ (nb077_alpha_dummy_020 F I) := by
  simpa only [nb077_alpha_dummy_019, nb077_alpha_dummy_020] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_016 F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_015 F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_050 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_021 x F I) ∉ (((Class.cv (nb077_alpha_dummy_018 x F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_017 x F I))).fv) := by
  simpa only [nb077_alpha_dummy_021] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_018 x F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_017 x F I))).fv) 0

theorem nb077_fresh_051 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_022 x F I) ∉ (((Class.cv (nb077_alpha_dummy_018 x F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_017 x F I))).fv) := by
  simpa only [nb077_alpha_dummy_022] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_018 x F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_017 x F I))).fv) 1

theorem nb077_distinct_052 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_021 x F I) ≠ (nb077_alpha_dummy_022 x F I) := by
  simpa only [nb077_alpha_dummy_021, nb077_alpha_dummy_022] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_018 x F I))).fv ∪ ((Class.cv (nb077_alpha_dummy_017 x F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_053 (F : Class) (I : Class) : (nb077_alpha_dummy_027 F I) ∉ (((Class.cv (nb077_alpha_dummy_020 F I))).fv) := by
  simpa only [nb077_alpha_dummy_027] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_020 F I))).fv) 0

theorem nb077_fresh_054 (F : Class) (I : Class) : (nb077_alpha_dummy_028 F I) ∉ (((Class.cv (nb077_alpha_dummy_020 F I))).fv) := by
  simpa only [nb077_alpha_dummy_028] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_020 F I))).fv) 1

theorem nb077_distinct_055 (F : Class) (I : Class) : (nb077_alpha_dummy_027 F I) ≠ (nb077_alpha_dummy_028 F I) := by
  simpa only [nb077_alpha_dummy_027, nb077_alpha_dummy_028] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_020 F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_056 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_029 x F I) ∉ (((Class.cv (nb077_alpha_dummy_022 x F I))).fv) := by
  simpa only [nb077_alpha_dummy_029] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_022 x F I))).fv) 0

theorem nb077_fresh_057 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_030 x F I) ∉ (((Class.cv (nb077_alpha_dummy_022 x F I))).fv) := by
  simpa only [nb077_alpha_dummy_030] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_022 x F I))).fv) 1

theorem nb077_distinct_058 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_029 x F I) ≠ (nb077_alpha_dummy_030 x F I) := by
  simpa only [nb077_alpha_dummy_029, nb077_alpha_dummy_030] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_022 x F I))).fv) (i := 0) (j := 1) (by decide))

theorem nb077_fresh_059 (F : Class) (I : Class) : (nb077_alpha_dummy_033 F I) ∉ (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_033] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) 0

theorem nb077_fresh_060 (F : Class) (I : Class) : (nb077_alpha_dummy_034 F I) ∉ (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_034] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) 1

theorem nb077_fresh_061 (F : Class) (I : Class) : (nb077_alpha_dummy_035 F I) ∉ (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_035] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) 2

theorem nb077_distinct_062 (F : Class) (I : Class) : (nb077_alpha_dummy_033 F I) ≠ (nb077_alpha_dummy_034 F I) := by
  simpa only [nb077_alpha_dummy_033, nb077_alpha_dummy_034] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb077_distinct_063 (F : Class) (I : Class) : (nb077_alpha_dummy_033 F I) ≠ (nb077_alpha_dummy_035 F I) := by
  simpa only [nb077_alpha_dummy_033, nb077_alpha_dummy_035] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb077_distinct_064 (F : Class) (I : Class) : (nb077_alpha_dummy_034 F I) ≠ (nb077_alpha_dummy_035 F I) := by
  simpa only [nb077_alpha_dummy_034, nb077_alpha_dummy_035] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb077_fresh_065 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_036 x F I) ∉ (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_036] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) 0

theorem nb077_fresh_066 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_037 x F I) ∉ (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_037] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) 1

theorem nb077_fresh_067 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_038 x F I) ∉ (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb077_alpha_dummy_038] using freshVar_not_mem (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) 2

theorem nb077_distinct_068 (x : Var) (F : Class) (I : Class) : (nb077_alpha_dummy_036 x F I) ≠ (nb077_alpha_dummy_037 x F I) := by
  simpa only [nb077_alpha_dummy_036, nb077_alpha_dummy_037] using
    (freshVar_injective (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
