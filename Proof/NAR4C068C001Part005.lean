import NAR4C068C001Part004

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

theorem nb068_fresh_042 (f : Var) : (nb068_alpha_dummy_420 f) ∉ (((Class.cab (nb068_alpha_dummy_415 f) (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_409 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_416 f))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_415 f) (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_409 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_416 f))))))).fv) := by
  simpa only [nb068_alpha_dummy_420] using freshVar_not_mem (((Class.cab (nb068_alpha_dummy_415 f) (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_409 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_416 f))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_415 f) (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_409 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_416 f))))))).fv) 0

theorem nb068_fresh_043 (f : Var) : (nb068_alpha_dummy_444 f) ∉ (((Class.cab (nb068_alpha_dummy_415 f) (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_410 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_416 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_415 f) (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_410 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_416 f))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb068_alpha_dummy_444] using freshVar_not_mem (((Class.cab (nb068_alpha_dummy_415 f) (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_410 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_416 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_415 f) (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_410 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_416 f))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb068_fresh_044 : (nb068_alpha_dummy_479) ∉ (((Class.cab (nb068_alpha_dummy_449) (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_407)) (Wff.classEq (Class.cv (nb068_alpha_dummy_449)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_450))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_449) (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_407)) (Wff.classEq (Class.cv (nb068_alpha_dummy_449)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_450))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb068_alpha_dummy_479] using freshVar_not_mem (((Class.cab (nb068_alpha_dummy_449) (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_407)) (Wff.classEq (Class.cv (nb068_alpha_dummy_449)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_450))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_449) (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_407)) (Wff.classEq (Class.cv (nb068_alpha_dummy_449)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_450))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb068_fresh_045 : (nb068_alpha_dummy_455) ∉ (((Class.cab (nb068_alpha_dummy_449) (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_408)) (Wff.classEq (Class.cv (nb068_alpha_dummy_449)) (syn_cphi (Class.cv (nb068_alpha_dummy_450))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_449) (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_408)) (Wff.classEq (Class.cv (nb068_alpha_dummy_449)) (syn_cphi (Class.cv (nb068_alpha_dummy_450))))))).fv) := by
  simpa only [nb068_alpha_dummy_455] using freshVar_not_mem (((Class.cab (nb068_alpha_dummy_449) (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_408)) (Wff.classEq (Class.cv (nb068_alpha_dummy_449)) (syn_cphi (Class.cv (nb068_alpha_dummy_450))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_449) (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_408)) (Wff.classEq (Class.cv (nb068_alpha_dummy_449)) (syn_cphi (Class.cv (nb068_alpha_dummy_450))))))).fv) 0

theorem nb068_fresh_046 (f : Var) : (nb068_alpha_dummy_480 f) ∉ (((Class.cab (nb068_alpha_dummy_451 f) (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_409 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_452 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_451 f) (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_409 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_452 f))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb068_alpha_dummy_480] using freshVar_not_mem (((Class.cab (nb068_alpha_dummy_451 f) (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_409 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_452 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_451 f) (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_409 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_452 f))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb068_fresh_047 (f : Var) : (nb068_alpha_dummy_456 f) ∉ (((Class.cab (nb068_alpha_dummy_451 f) (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_410 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_452 f))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_451 f) (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_410 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_452 f))))))).fv) := by
  simpa only [nb068_alpha_dummy_456] using freshVar_not_mem (((Class.cab (nb068_alpha_dummy_451 f) (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_410 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_452 f))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_451 f) (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_410 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_452 f))))))).fv) 0

theorem nb068_fresh_048 : (nb068_alpha_dummy_515) ∉ (((Class.cab (nb068_alpha_dummy_485) (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_328)) (Wff.classEq (Class.cv (nb068_alpha_dummy_485)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_486))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_485) (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_328)) (Wff.classEq (Class.cv (nb068_alpha_dummy_485)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_486))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb068_alpha_dummy_515] using freshVar_not_mem (((Class.cab (nb068_alpha_dummy_485) (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_328)) (Wff.classEq (Class.cv (nb068_alpha_dummy_485)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_486))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_485) (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_328)) (Wff.classEq (Class.cv (nb068_alpha_dummy_485)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_486))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb068_fresh_049 : (nb068_alpha_dummy_491) ∉ (((Class.cab (nb068_alpha_dummy_485) (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_329)) (Wff.classEq (Class.cv (nb068_alpha_dummy_485)) (syn_cphi (Class.cv (nb068_alpha_dummy_486))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_485) (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_329)) (Wff.classEq (Class.cv (nb068_alpha_dummy_485)) (syn_cphi (Class.cv (nb068_alpha_dummy_486))))))).fv) := by
  simpa only [nb068_alpha_dummy_491] using freshVar_not_mem (((Class.cab (nb068_alpha_dummy_485) (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_329)) (Wff.classEq (Class.cv (nb068_alpha_dummy_485)) (syn_cphi (Class.cv (nb068_alpha_dummy_486))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_485) (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_329)) (Wff.classEq (Class.cv (nb068_alpha_dummy_485)) (syn_cphi (Class.cv (nb068_alpha_dummy_486))))))).fv) 0

theorem nb068_fresh_050 (f : Var) : (nb068_alpha_dummy_516 f) ∉ (((Class.cab (nb068_alpha_dummy_487 f) (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_331 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_488 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_487 f) (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_331 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_488 f))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb068_alpha_dummy_516] using freshVar_not_mem (((Class.cab (nb068_alpha_dummy_487 f) (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_331 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_488 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_487 f) (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_331 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_488 f))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb068_fresh_051 (f : Var) : (nb068_alpha_dummy_492 f) ∉ (((Class.cab (nb068_alpha_dummy_487 f) (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_332 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_488 f))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_487 f) (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_332 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_488 f))))))).fv) := by
  simpa only [nb068_alpha_dummy_492] using freshVar_not_mem (((Class.cab (nb068_alpha_dummy_487 f) (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_332 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_488 f))))))).fv ∪ ((Class.cab (nb068_alpha_dummy_487 f) (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_332 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_488 f))))))).fv) 0

theorem nb068_fresh_052 : (nb068_alpha_dummy_125) ∉ (((Class.cv (nb068_alpha_dummy_000))).fv) := by
  simpa only [nb068_alpha_dummy_125] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_000))).fv) 0

theorem nb068_fresh_053 : (nb068_alpha_dummy_126) ∉ (((Class.cv (nb068_alpha_dummy_000))).fv) := by
  simpa only [nb068_alpha_dummy_126] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_000))).fv) 1

theorem nb068_distinct_054 : (nb068_alpha_dummy_125) ≠ (nb068_alpha_dummy_126) := by
  simpa only [nb068_alpha_dummy_125, nb068_alpha_dummy_126] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_000))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_055 : (nb068_alpha_dummy_045) ∉ (((Class.cv (nb068_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) := by
  simpa only [nb068_alpha_dummy_045] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) 0

theorem nb068_fresh_056 : (nb068_alpha_dummy_046) ∉ (((Class.cv (nb068_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) := by
  simpa only [nb068_alpha_dummy_046] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) 1

theorem nb068_fresh_057 : (nb068_alpha_dummy_047) ∉ (((Class.cv (nb068_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) := by
  simpa only [nb068_alpha_dummy_047] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) 2

theorem nb068_distinct_058 : (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_046) := by
  simpa only [nb068_alpha_dummy_045, nb068_alpha_dummy_046] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_distinct_059 : (nb068_alpha_dummy_045) ≠ (nb068_alpha_dummy_047) := by
  simpa only [nb068_alpha_dummy_045, nb068_alpha_dummy_047] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) (i := 0) (j := 2) (by decide))

theorem nb068_distinct_060 : (nb068_alpha_dummy_046) ≠ (nb068_alpha_dummy_047) := by
  simpa only [nb068_alpha_dummy_046, nb068_alpha_dummy_047] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) (i := 1) (j := 2) (by decide))

theorem nb068_fresh_061 : (nb068_alpha_dummy_283) ∉ (((Class.cv (nb068_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb068_alpha_dummy_283] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) 0

theorem nb068_fresh_062 : (nb068_alpha_dummy_284) ∉ (((Class.cv (nb068_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb068_alpha_dummy_284] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) 1

theorem nb068_distinct_063 : (nb068_alpha_dummy_283) ≠ (nb068_alpha_dummy_284) := by
  simpa only [nb068_alpha_dummy_283, nb068_alpha_dummy_284] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_064 : (nb068_alpha_dummy_005) ∉ (((Class.cv (nb068_alpha_dummy_001))).fv ∪ ((Class.cv (nb068_alpha_dummy_002))).fv) := by
  simpa only [nb068_alpha_dummy_005] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_001))).fv ∪ ((Class.cv (nb068_alpha_dummy_002))).fv) 0

theorem nb068_fresh_065 : (nb068_alpha_dummy_006) ∉ (((Class.cv (nb068_alpha_dummy_001))).fv ∪ ((Class.cv (nb068_alpha_dummy_002))).fv) := by
  simpa only [nb068_alpha_dummy_006] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_001))).fv ∪ ((Class.cv (nb068_alpha_dummy_002))).fv) 1

theorem nb068_distinct_066 : (nb068_alpha_dummy_005) ≠ (nb068_alpha_dummy_006) := by
  simpa only [nb068_alpha_dummy_005, nb068_alpha_dummy_006] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_001))).fv ∪ ((Class.cv (nb068_alpha_dummy_002))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_067 : (nb068_alpha_dummy_013) ∉ (((Class.cv (nb068_alpha_dummy_006))).fv) := by
  simpa only [nb068_alpha_dummy_013] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_006))).fv) 0

theorem nb068_fresh_068 : (nb068_alpha_dummy_014) ∉ (((Class.cv (nb068_alpha_dummy_006))).fv) := by
  simpa only [nb068_alpha_dummy_014] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_006))).fv) 1

theorem nb068_distinct_069 : (nb068_alpha_dummy_013) ≠ (nb068_alpha_dummy_014) := by
  simpa only [nb068_alpha_dummy_013, nb068_alpha_dummy_014] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_006))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_070 (x : Var) (y : Var) : (nb068_alpha_dummy_015 x y) ∉ (((Class.cv (nb068_alpha_dummy_008 x y))).fv) := by
  simpa only [nb068_alpha_dummy_015] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_008 x y))).fv) 0

theorem nb068_fresh_071 (x : Var) (y : Var) : (nb068_alpha_dummy_016 x y) ∉ (((Class.cv (nb068_alpha_dummy_008 x y))).fv) := by
  simpa only [nb068_alpha_dummy_016] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_008 x y))).fv) 1

theorem nb068_distinct_072 (x : Var) (y : Var) : (nb068_alpha_dummy_015 x y) ≠ (nb068_alpha_dummy_016 x y) := by
  simpa only [nb068_alpha_dummy_015, nb068_alpha_dummy_016] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_008 x y))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_073 : (nb068_alpha_dummy_019) ∉ (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_019] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_074 : (nb068_alpha_dummy_020) ∉ (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_020] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_075 : (nb068_alpha_dummy_021) ∉ (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_021] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_076 : (nb068_alpha_dummy_019) ≠ (nb068_alpha_dummy_020) := by
  simpa only [nb068_alpha_dummy_019, nb068_alpha_dummy_020] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_distinct_077 : (nb068_alpha_dummy_019) ≠ (nb068_alpha_dummy_021) := by
  simpa only [nb068_alpha_dummy_019, nb068_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb068_distinct_078 : (nb068_alpha_dummy_020) ≠ (nb068_alpha_dummy_021) := by
  simpa only [nb068_alpha_dummy_020, nb068_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb068_fresh_079 (x : Var) (y : Var) : (nb068_alpha_dummy_022 x y) ∉ (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_022] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_080 (x : Var) (y : Var) : (nb068_alpha_dummy_023 x y) ∉ (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_023] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_081 (x : Var) (y : Var) : (nb068_alpha_dummy_024 x y) ∉ (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_024] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_082 (x : Var) (y : Var) : (nb068_alpha_dummy_022 x y) ≠ (nb068_alpha_dummy_023 x y) := by
  simpa only [nb068_alpha_dummy_022, nb068_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_distinct_083 (x : Var) (y : Var) : (nb068_alpha_dummy_022 x y) ≠ (nb068_alpha_dummy_024 x y) := by
  simpa only [nb068_alpha_dummy_022, nb068_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb068_distinct_084 (x : Var) (y : Var) : (nb068_alpha_dummy_023 x y) ≠ (nb068_alpha_dummy_024 x y) := by
  simpa only [nb068_alpha_dummy_023, nb068_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_015 x y))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb068_fresh_085 : (nb068_alpha_dummy_031) ∉ (((Class.cv (nb068_alpha_dummy_020))).fv ∪ ((Class.cv (nb068_alpha_dummy_020))).fv) := by
  simpa only [nb068_alpha_dummy_031] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_020))).fv ∪ ((Class.cv (nb068_alpha_dummy_020))).fv) 0

theorem nb068_fresh_086 : (nb068_alpha_dummy_027) ∉ (((Class.cv (nb068_alpha_dummy_020))).fv ∪ ((Class.cv (nb068_alpha_dummy_021))).fv) := by
  simpa only [nb068_alpha_dummy_027] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_020))).fv ∪ ((Class.cv (nb068_alpha_dummy_021))).fv) 0

theorem nb068_fresh_087 : (nb068_alpha_dummy_033) ∉ (((Class.cv (nb068_alpha_dummy_021))).fv ∪ ((Class.cv (nb068_alpha_dummy_021))).fv) := by
  simpa only [nb068_alpha_dummy_033] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_021))).fv ∪ ((Class.cv (nb068_alpha_dummy_021))).fv) 0

theorem nb068_fresh_088 (x : Var) (y : Var) : (nb068_alpha_dummy_032 x y) ∉ (((Class.cv (nb068_alpha_dummy_023 x y))).fv ∪ ((Class.cv (nb068_alpha_dummy_023 x y))).fv) := by
  simpa only [nb068_alpha_dummy_032] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_023 x y))).fv ∪ ((Class.cv (nb068_alpha_dummy_023 x y))).fv) 0

theorem nb068_fresh_089 (x : Var) (y : Var) : (nb068_alpha_dummy_028 x y) ∉ (((Class.cv (nb068_alpha_dummy_023 x y))).fv ∪ ((Class.cv (nb068_alpha_dummy_024 x y))).fv) := by
  simpa only [nb068_alpha_dummy_028] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_023 x y))).fv ∪ ((Class.cv (nb068_alpha_dummy_024 x y))).fv) 0

theorem nb068_fresh_090 (x : Var) (y : Var) : (nb068_alpha_dummy_034 x y) ∉ (((Class.cv (nb068_alpha_dummy_024 x y))).fv ∪ ((Class.cv (nb068_alpha_dummy_024 x y))).fv) := by
  simpa only [nb068_alpha_dummy_034] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_024 x y))).fv ∪ ((Class.cv (nb068_alpha_dummy_024 x y))).fv) 0

theorem nb068_fresh_091 : (nb068_alpha_dummy_053) ∉ (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv) := by
  simpa only [nb068_alpha_dummy_053] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv) 0

theorem nb068_fresh_092 : (nb068_alpha_dummy_054) ∉ (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv) := by
  simpa only [nb068_alpha_dummy_054] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv) 1

theorem nb068_distinct_093 : (nb068_alpha_dummy_053) ≠ (nb068_alpha_dummy_054) := by
  simpa only [nb068_alpha_dummy_053, nb068_alpha_dummy_054] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_094 : (nb068_alpha_dummy_089) ∉ (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_047))).fv) := by
  simpa only [nb068_alpha_dummy_089] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_047))).fv) 0

theorem nb068_fresh_095 : (nb068_alpha_dummy_090) ∉ (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_047))).fv) := by
  simpa only [nb068_alpha_dummy_090] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_047))).fv) 1

theorem nb068_distinct_096 : (nb068_alpha_dummy_089) ≠ (nb068_alpha_dummy_090) := by
  simpa only [nb068_alpha_dummy_089, nb068_alpha_dummy_090] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_045))).fv ∪ ((Class.cv (nb068_alpha_dummy_047))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_097 : (nb068_alpha_dummy_203) ∉ (((Class.cv (nb068_alpha_dummy_047))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv) := by
  simpa only [nb068_alpha_dummy_203] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_047))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv) 0

theorem nb068_fresh_098 : (nb068_alpha_dummy_204) ∉ (((Class.cv (nb068_alpha_dummy_047))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv) := by
  simpa only [nb068_alpha_dummy_204] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_047))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv) 1

theorem nb068_distinct_099 : (nb068_alpha_dummy_203) ≠ (nb068_alpha_dummy_204) := by
  simpa only [nb068_alpha_dummy_203, nb068_alpha_dummy_204] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_047))).fv ∪ ((Class.cv (nb068_alpha_dummy_046))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_100 (f : Var) : (nb068_alpha_dummy_055 f) ∉ (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_049 f))).fv) := by
  simpa only [nb068_alpha_dummy_055] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_049 f))).fv) 0

theorem nb068_fresh_101 (f : Var) : (nb068_alpha_dummy_056 f) ∉ (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_049 f))).fv) := by
  simpa only [nb068_alpha_dummy_056] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_049 f))).fv) 1

theorem nb068_distinct_102 (f : Var) : (nb068_alpha_dummy_055 f) ≠ (nb068_alpha_dummy_056 f) := by
  simpa only [nb068_alpha_dummy_055, nb068_alpha_dummy_056] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_049 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_103 (f : Var) : (nb068_alpha_dummy_091 f) ∉ (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_050 f))).fv) := by
  simpa only [nb068_alpha_dummy_091] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_050 f))).fv) 0

theorem nb068_fresh_104 (f : Var) : (nb068_alpha_dummy_092 f) ∉ (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_050 f))).fv) := by
  simpa only [nb068_alpha_dummy_092] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_050 f))).fv) 1

theorem nb068_distinct_105 (f : Var) : (nb068_alpha_dummy_091 f) ≠ (nb068_alpha_dummy_092 f) := by
  simpa only [nb068_alpha_dummy_091, nb068_alpha_dummy_092] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_048 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_050 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_106 (f : Var) : (nb068_alpha_dummy_205 f) ∉ (((Class.cv (nb068_alpha_dummy_050 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_049 f))).fv) := by
  simpa only [nb068_alpha_dummy_205] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_050 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_049 f))).fv) 0

theorem nb068_fresh_107 (f : Var) : (nb068_alpha_dummy_206 f) ∉ (((Class.cv (nb068_alpha_dummy_050 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_049 f))).fv) := by
  simpa only [nb068_alpha_dummy_206] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_050 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_049 f))).fv) 1

theorem nb068_distinct_108 (f : Var) : (nb068_alpha_dummy_205 f) ≠ (nb068_alpha_dummy_206 f) := by
  simpa only [nb068_alpha_dummy_205, nb068_alpha_dummy_206] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_050 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_049 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_109 : (nb068_alpha_dummy_061) ∉ (((Class.cv (nb068_alpha_dummy_054))).fv) := by
  simpa only [nb068_alpha_dummy_061] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_054))).fv) 0

theorem nb068_fresh_110 : (nb068_alpha_dummy_062) ∉ (((Class.cv (nb068_alpha_dummy_054))).fv) := by
  simpa only [nb068_alpha_dummy_062] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_054))).fv) 1

theorem nb068_distinct_111 : (nb068_alpha_dummy_061) ≠ (nb068_alpha_dummy_062) := by
  simpa only [nb068_alpha_dummy_061, nb068_alpha_dummy_062] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_054))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_112 (f : Var) : (nb068_alpha_dummy_063 f) ∉ (((Class.cv (nb068_alpha_dummy_056 f))).fv) := by
  simpa only [nb068_alpha_dummy_063] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_056 f))).fv) 0

theorem nb068_fresh_113 (f : Var) : (nb068_alpha_dummy_064 f) ∉ (((Class.cv (nb068_alpha_dummy_056 f))).fv) := by
  simpa only [nb068_alpha_dummy_064] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_056 f))).fv) 1

theorem nb068_distinct_114 (f : Var) : (nb068_alpha_dummy_063 f) ≠ (nb068_alpha_dummy_064 f) := by
  simpa only [nb068_alpha_dummy_063, nb068_alpha_dummy_064] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_056 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_115 : (nb068_alpha_dummy_067) ∉ (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_067] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_116 : (nb068_alpha_dummy_068) ∉ (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_068] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_117 : (nb068_alpha_dummy_069) ∉ (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_069] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_118 : (nb068_alpha_dummy_067) ≠ (nb068_alpha_dummy_068) := by
  simpa only [nb068_alpha_dummy_067, nb068_alpha_dummy_068] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_distinct_119 : (nb068_alpha_dummy_067) ≠ (nb068_alpha_dummy_069) := by
  simpa only [nb068_alpha_dummy_067, nb068_alpha_dummy_069] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb068_distinct_120 : (nb068_alpha_dummy_068) ≠ (nb068_alpha_dummy_069) := by
  simpa only [nb068_alpha_dummy_068, nb068_alpha_dummy_069] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb068_fresh_121 (f : Var) : (nb068_alpha_dummy_070 f) ∉ (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_070] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_122 (f : Var) : (nb068_alpha_dummy_071 f) ∉ (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_071] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_123 (f : Var) : (nb068_alpha_dummy_072 f) ∉ (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_072] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_124 (f : Var) : (nb068_alpha_dummy_070 f) ≠ (nb068_alpha_dummy_071 f) := by
  simpa only [nb068_alpha_dummy_070, nb068_alpha_dummy_071] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_distinct_125 (f : Var) : (nb068_alpha_dummy_070 f) ≠ (nb068_alpha_dummy_072 f) := by
  simpa only [nb068_alpha_dummy_070, nb068_alpha_dummy_072] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb068_distinct_126 (f : Var) : (nb068_alpha_dummy_071 f) ≠ (nb068_alpha_dummy_072 f) := by
  simpa only [nb068_alpha_dummy_071, nb068_alpha_dummy_072] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb068_fresh_127 : (nb068_alpha_dummy_079) ∉ (((Class.cv (nb068_alpha_dummy_068))).fv ∪ ((Class.cv (nb068_alpha_dummy_068))).fv) := by
  simpa only [nb068_alpha_dummy_079] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_068))).fv ∪ ((Class.cv (nb068_alpha_dummy_068))).fv) 0

theorem nb068_fresh_128 : (nb068_alpha_dummy_075) ∉ (((Class.cv (nb068_alpha_dummy_068))).fv ∪ ((Class.cv (nb068_alpha_dummy_069))).fv) := by
  simpa only [nb068_alpha_dummy_075] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_068))).fv ∪ ((Class.cv (nb068_alpha_dummy_069))).fv) 0

theorem nb068_fresh_129 : (nb068_alpha_dummy_081) ∉ (((Class.cv (nb068_alpha_dummy_069))).fv ∪ ((Class.cv (nb068_alpha_dummy_069))).fv) := by
  simpa only [nb068_alpha_dummy_081] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_069))).fv ∪ ((Class.cv (nb068_alpha_dummy_069))).fv) 0

theorem nb068_fresh_130 (f : Var) : (nb068_alpha_dummy_080 f) ∉ (((Class.cv (nb068_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_071 f))).fv) := by
  simpa only [nb068_alpha_dummy_080] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_071 f))).fv) 0

theorem nb068_fresh_131 (f : Var) : (nb068_alpha_dummy_076 f) ∉ (((Class.cv (nb068_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_072 f))).fv) := by
  simpa only [nb068_alpha_dummy_076] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_072 f))).fv) 0

theorem nb068_fresh_132 (f : Var) : (nb068_alpha_dummy_082 f) ∉ (((Class.cv (nb068_alpha_dummy_072 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_072 f))).fv) := by
  simpa only [nb068_alpha_dummy_082] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_072 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_072 f))).fv) 0

theorem nb068_fresh_133 : (nb068_alpha_dummy_097) ∉ (((Class.cv (nb068_alpha_dummy_090))).fv) := by
  simpa only [nb068_alpha_dummy_097] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_090))).fv) 0

theorem nb068_fresh_134 : (nb068_alpha_dummy_098) ∉ (((Class.cv (nb068_alpha_dummy_090))).fv) := by
  simpa only [nb068_alpha_dummy_098] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_090))).fv) 1

theorem nb068_distinct_135 : (nb068_alpha_dummy_097) ≠ (nb068_alpha_dummy_098) := by
  simpa only [nb068_alpha_dummy_097, nb068_alpha_dummy_098] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_090))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_136 (f : Var) : (nb068_alpha_dummy_099 f) ∉ (((Class.cv (nb068_alpha_dummy_092 f))).fv) := by
  simpa only [nb068_alpha_dummy_099] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_092 f))).fv) 0

theorem nb068_fresh_137 (f : Var) : (nb068_alpha_dummy_100 f) ∉ (((Class.cv (nb068_alpha_dummy_092 f))).fv) := by
  simpa only [nb068_alpha_dummy_100] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_092 f))).fv) 1

theorem nb068_distinct_138 (f : Var) : (nb068_alpha_dummy_099 f) ≠ (nb068_alpha_dummy_100 f) := by
  simpa only [nb068_alpha_dummy_099, nb068_alpha_dummy_100] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_092 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_139 : (nb068_alpha_dummy_103) ∉ (((Class.cv (nb068_alpha_dummy_097))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_103] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_097))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_140 : (nb068_alpha_dummy_104) ∉ (((Class.cv (nb068_alpha_dummy_097))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_104] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_097))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_141 : (nb068_alpha_dummy_105) ∉ (((Class.cv (nb068_alpha_dummy_097))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_105] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_097))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_142 : (nb068_alpha_dummy_103) ≠ (nb068_alpha_dummy_104) := by
  simpa only [nb068_alpha_dummy_103, nb068_alpha_dummy_104] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_097))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_distinct_143 : (nb068_alpha_dummy_103) ≠ (nb068_alpha_dummy_105) := by
  simpa only [nb068_alpha_dummy_103, nb068_alpha_dummy_105] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_097))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb068_distinct_144 : (nb068_alpha_dummy_104) ≠ (nb068_alpha_dummy_105) := by
  simpa only [nb068_alpha_dummy_104, nb068_alpha_dummy_105] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_097))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb068_fresh_145 (f : Var) : (nb068_alpha_dummy_106 f) ∉ (((Class.cv (nb068_alpha_dummy_099 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_106] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_099 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_146 (f : Var) : (nb068_alpha_dummy_107 f) ∉ (((Class.cv (nb068_alpha_dummy_099 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_107] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_099 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_147 (f : Var) : (nb068_alpha_dummy_108 f) ∉ (((Class.cv (nb068_alpha_dummy_099 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_108] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_099 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_148 (f : Var) : (nb068_alpha_dummy_106 f) ≠ (nb068_alpha_dummy_107 f) := by
  simpa only [nb068_alpha_dummy_106, nb068_alpha_dummy_107] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_099 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_distinct_149 (f : Var) : (nb068_alpha_dummy_106 f) ≠ (nb068_alpha_dummy_108 f) := by
  simpa only [nb068_alpha_dummy_106, nb068_alpha_dummy_108] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_099 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb068_distinct_150 (f : Var) : (nb068_alpha_dummy_107 f) ≠ (nb068_alpha_dummy_108 f) := by
  simpa only [nb068_alpha_dummy_107, nb068_alpha_dummy_108] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_099 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb068_fresh_151 : (nb068_alpha_dummy_115) ∉ (((Class.cv (nb068_alpha_dummy_104))).fv ∪ ((Class.cv (nb068_alpha_dummy_104))).fv) := by
  simpa only [nb068_alpha_dummy_115] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_104))).fv ∪ ((Class.cv (nb068_alpha_dummy_104))).fv) 0

theorem nb068_fresh_152 : (nb068_alpha_dummy_111) ∉ (((Class.cv (nb068_alpha_dummy_104))).fv ∪ ((Class.cv (nb068_alpha_dummy_105))).fv) := by
  simpa only [nb068_alpha_dummy_111] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_104))).fv ∪ ((Class.cv (nb068_alpha_dummy_105))).fv) 0

theorem nb068_fresh_153 : (nb068_alpha_dummy_117) ∉ (((Class.cv (nb068_alpha_dummy_105))).fv ∪ ((Class.cv (nb068_alpha_dummy_105))).fv) := by
  simpa only [nb068_alpha_dummy_117] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_105))).fv ∪ ((Class.cv (nb068_alpha_dummy_105))).fv) 0

theorem nb068_fresh_154 (f : Var) : (nb068_alpha_dummy_116 f) ∉ (((Class.cv (nb068_alpha_dummy_107 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_107 f))).fv) := by
  simpa only [nb068_alpha_dummy_116] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_107 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_107 f))).fv) 0

theorem nb068_fresh_155 (f : Var) : (nb068_alpha_dummy_112 f) ∉ (((Class.cv (nb068_alpha_dummy_107 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_108 f))).fv) := by
  simpa only [nb068_alpha_dummy_112] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_107 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_108 f))).fv) 0

theorem nb068_fresh_156 (f : Var) : (nb068_alpha_dummy_118 f) ∉ (((Class.cv (nb068_alpha_dummy_108 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_108 f))).fv) := by
  simpa only [nb068_alpha_dummy_118] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_108 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_108 f))).fv) 0

theorem nb068_fresh_157 : (nb068_alpha_dummy_131) ∉ (((Class.cv (nb068_alpha_dummy_125))).fv ∪ ((Class.cv (nb068_alpha_dummy_126))).fv) := by
  simpa only [nb068_alpha_dummy_131] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_125))).fv ∪ ((Class.cv (nb068_alpha_dummy_126))).fv) 0

theorem nb068_fresh_158 : (nb068_alpha_dummy_132) ∉ (((Class.cv (nb068_alpha_dummy_125))).fv ∪ ((Class.cv (nb068_alpha_dummy_126))).fv) := by
  simpa only [nb068_alpha_dummy_132] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_125))).fv ∪ ((Class.cv (nb068_alpha_dummy_126))).fv) 1

theorem nb068_distinct_159 : (nb068_alpha_dummy_131) ≠ (nb068_alpha_dummy_132) := by
  simpa only [nb068_alpha_dummy_131, nb068_alpha_dummy_132] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_125))).fv ∪ ((Class.cv (nb068_alpha_dummy_126))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_160 : (nb068_alpha_dummy_167) ∉ (((Class.cv (nb068_alpha_dummy_126))).fv ∪ ((Class.cv (nb068_alpha_dummy_125))).fv) := by
  simpa only [nb068_alpha_dummy_167] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_126))).fv ∪ ((Class.cv (nb068_alpha_dummy_125))).fv) 0

theorem nb068_fresh_161 : (nb068_alpha_dummy_168) ∉ (((Class.cv (nb068_alpha_dummy_126))).fv ∪ ((Class.cv (nb068_alpha_dummy_125))).fv) := by
  simpa only [nb068_alpha_dummy_168] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_126))).fv ∪ ((Class.cv (nb068_alpha_dummy_125))).fv) 1

theorem nb068_distinct_162 : (nb068_alpha_dummy_167) ≠ (nb068_alpha_dummy_168) := by
  simpa only [nb068_alpha_dummy_167, nb068_alpha_dummy_168] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_126))).fv ∪ ((Class.cv (nb068_alpha_dummy_125))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_163 (f : Var) : (nb068_alpha_dummy_133 f) ∉ (((Class.cv (nb068_alpha_dummy_127 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_128 f))).fv) := by
  simpa only [nb068_alpha_dummy_133] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_127 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_128 f))).fv) 0

theorem nb068_fresh_164 (f : Var) : (nb068_alpha_dummy_134 f) ∉ (((Class.cv (nb068_alpha_dummy_127 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_128 f))).fv) := by
  simpa only [nb068_alpha_dummy_134] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_127 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_128 f))).fv) 1

theorem nb068_distinct_165 (f : Var) : (nb068_alpha_dummy_133 f) ≠ (nb068_alpha_dummy_134 f) := by
  simpa only [nb068_alpha_dummy_133, nb068_alpha_dummy_134] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_127 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_128 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_166 (f : Var) : (nb068_alpha_dummy_169 f) ∉ (((Class.cv (nb068_alpha_dummy_128 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_127 f))).fv) := by
  simpa only [nb068_alpha_dummy_169] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_128 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_127 f))).fv) 0

theorem nb068_fresh_167 (f : Var) : (nb068_alpha_dummy_170 f) ∉ (((Class.cv (nb068_alpha_dummy_128 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_127 f))).fv) := by
  simpa only [nb068_alpha_dummy_170] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_128 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_127 f))).fv) 1

theorem nb068_distinct_168 (f : Var) : (nb068_alpha_dummy_169 f) ≠ (nb068_alpha_dummy_170 f) := by
  simpa only [nb068_alpha_dummy_169, nb068_alpha_dummy_170] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_128 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_127 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_169 : (nb068_alpha_dummy_139) ∉ (((Class.cv (nb068_alpha_dummy_132))).fv) := by
  simpa only [nb068_alpha_dummy_139] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_132))).fv) 0

theorem nb068_fresh_170 : (nb068_alpha_dummy_140) ∉ (((Class.cv (nb068_alpha_dummy_132))).fv) := by
  simpa only [nb068_alpha_dummy_140] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_132))).fv) 1

theorem nb068_distinct_171 : (nb068_alpha_dummy_139) ≠ (nb068_alpha_dummy_140) := by
  simpa only [nb068_alpha_dummy_139, nb068_alpha_dummy_140] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_132))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_172 (f : Var) : (nb068_alpha_dummy_141 f) ∉ (((Class.cv (nb068_alpha_dummy_134 f))).fv) := by
  simpa only [nb068_alpha_dummy_141] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_134 f))).fv) 0

theorem nb068_fresh_173 (f : Var) : (nb068_alpha_dummy_142 f) ∉ (((Class.cv (nb068_alpha_dummy_134 f))).fv) := by
  simpa only [nb068_alpha_dummy_142] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_134 f))).fv) 1

theorem nb068_distinct_174 (f : Var) : (nb068_alpha_dummy_141 f) ≠ (nb068_alpha_dummy_142 f) := by
  simpa only [nb068_alpha_dummy_141, nb068_alpha_dummy_142] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_134 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_175 : (nb068_alpha_dummy_145) ∉ (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_145] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_176 : (nb068_alpha_dummy_146) ∉ (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_146] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_177 : (nb068_alpha_dummy_147) ∉ (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_147] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_178 : (nb068_alpha_dummy_145) ≠ (nb068_alpha_dummy_146) := by
  simpa only [nb068_alpha_dummy_145, nb068_alpha_dummy_146] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_distinct_179 : (nb068_alpha_dummy_145) ≠ (nb068_alpha_dummy_147) := by
  simpa only [nb068_alpha_dummy_145, nb068_alpha_dummy_147] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb068_distinct_180 : (nb068_alpha_dummy_146) ≠ (nb068_alpha_dummy_147) := by
  simpa only [nb068_alpha_dummy_146, nb068_alpha_dummy_147] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb068_fresh_181 (f : Var) : (nb068_alpha_dummy_148 f) ∉ (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_148] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb068_fresh_182 (f : Var) : (nb068_alpha_dummy_149 f) ∉ (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_149] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb068_fresh_183 (f : Var) : (nb068_alpha_dummy_150 f) ∉ (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb068_alpha_dummy_150] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb068_distinct_184 (f : Var) : (nb068_alpha_dummy_148 f) ≠ (nb068_alpha_dummy_149 f) := by
  simpa only [nb068_alpha_dummy_148, nb068_alpha_dummy_149] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_distinct_185 (f : Var) : (nb068_alpha_dummy_148 f) ≠ (nb068_alpha_dummy_150 f) := by
  simpa only [nb068_alpha_dummy_148, nb068_alpha_dummy_150] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb068_distinct_186 (f : Var) : (nb068_alpha_dummy_149 f) ≠ (nb068_alpha_dummy_150 f) := by
  simpa only [nb068_alpha_dummy_149, nb068_alpha_dummy_150] using
    (freshVar_injective (((Class.cv (nb068_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb068_fresh_187 : (nb068_alpha_dummy_157) ∉ (((Class.cv (nb068_alpha_dummy_146))).fv ∪ ((Class.cv (nb068_alpha_dummy_146))).fv) := by
  simpa only [nb068_alpha_dummy_157] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_146))).fv ∪ ((Class.cv (nb068_alpha_dummy_146))).fv) 0

theorem nb068_fresh_188 : (nb068_alpha_dummy_153) ∉ (((Class.cv (nb068_alpha_dummy_146))).fv ∪ ((Class.cv (nb068_alpha_dummy_147))).fv) := by
  simpa only [nb068_alpha_dummy_153] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_146))).fv ∪ ((Class.cv (nb068_alpha_dummy_147))).fv) 0

theorem nb068_fresh_189 : (nb068_alpha_dummy_159) ∉ (((Class.cv (nb068_alpha_dummy_147))).fv ∪ ((Class.cv (nb068_alpha_dummy_147))).fv) := by
  simpa only [nb068_alpha_dummy_159] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_147))).fv ∪ ((Class.cv (nb068_alpha_dummy_147))).fv) 0

theorem nb068_fresh_190 (f : Var) : (nb068_alpha_dummy_158 f) ∉ (((Class.cv (nb068_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_149 f))).fv) := by
  simpa only [nb068_alpha_dummy_158] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_149 f))).fv) 0

theorem nb068_fresh_191 (f : Var) : (nb068_alpha_dummy_154 f) ∉ (((Class.cv (nb068_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_150 f))).fv) := by
  simpa only [nb068_alpha_dummy_154] using freshVar_not_mem (((Class.cv (nb068_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_150 f))).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
