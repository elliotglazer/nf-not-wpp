import NAR4C068C001Part007

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

theorem nb068_fresh_492 : (nb068_alpha_dummy_407) ∉ (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) := by
  simpa only [nb068_alpha_dummy_407] using freshVar_not_mem (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) 0

theorem nb068_fresh_493 : (nb068_alpha_dummy_408) ∉ (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) := by
  simpa only [nb068_alpha_dummy_408] using freshVar_not_mem (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) 1

theorem nb068_distinct_494 : (nb068_alpha_dummy_407) ≠ (nb068_alpha_dummy_408) := by
  simpa only [nb068_alpha_dummy_407, nb068_alpha_dummy_408] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_495 : (nb068_alpha_dummy_327) ∉ (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))).fv) := by
  simpa only [nb068_alpha_dummy_327] using freshVar_not_mem (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))).fv) 0

theorem nb068_fresh_496 : (nb068_alpha_dummy_328) ∉ (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))).fv) := by
  simpa only [nb068_alpha_dummy_328] using freshVar_not_mem (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))).fv) 1

theorem nb068_fresh_497 : (nb068_alpha_dummy_329) ∉ (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))).fv) := by
  simpa only [nb068_alpha_dummy_329] using freshVar_not_mem (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))).fv) 2

theorem nb068_distinct_498 : (nb068_alpha_dummy_327) ≠ (nb068_alpha_dummy_328) := by
  simpa only [nb068_alpha_dummy_327, nb068_alpha_dummy_328] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_distinct_499 : (nb068_alpha_dummy_327) ≠ (nb068_alpha_dummy_329) := by
  simpa only [nb068_alpha_dummy_327, nb068_alpha_dummy_329] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))).fv) (i := 0) (j := 2) (by decide))

theorem nb068_distinct_500 : (nb068_alpha_dummy_328) ≠ (nb068_alpha_dummy_329) := by
  simpa only [nb068_alpha_dummy_328, nb068_alpha_dummy_329] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))).fv) (i := 1) (j := 2) (by decide))

theorem nb068_fresh_501 : (nb068_alpha_dummy_239) ∉ (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb068_alpha_dummy_239] using freshVar_not_mem (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) 0

theorem nb068_fresh_502 : (nb068_alpha_dummy_240) ∉ (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb068_alpha_dummy_240] using freshVar_not_mem (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) 1

theorem nb068_distinct_503 : (nb068_alpha_dummy_239) ≠ (nb068_alpha_dummy_240) := by
  simpa only [nb068_alpha_dummy_239, nb068_alpha_dummy_240] using
    (freshVar_injective (((syn_ccnv (Class.cv (nb068_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_504 (f : Var) : (nb068_alpha_dummy_409 f) ∉ (((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb068_alpha_dummy_409] using freshVar_not_mem (((syn_ccnv (Class.cv f))).fv) 0

theorem nb068_fresh_505 (f : Var) : (nb068_alpha_dummy_410 f) ∉ (((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb068_alpha_dummy_410] using freshVar_not_mem (((syn_ccnv (Class.cv f))).fv) 1

theorem nb068_distinct_506 (f : Var) : (nb068_alpha_dummy_409 f) ≠ (nb068_alpha_dummy_410 f) := by
  simpa only [nb068_alpha_dummy_409, nb068_alpha_dummy_410] using
    (freshVar_injective (((syn_ccnv (Class.cv f))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_507 (f : Var) : (nb068_alpha_dummy_330 f) ∉ (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) := by
  simpa only [nb068_alpha_dummy_330] using freshVar_not_mem (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) 0

theorem nb068_fresh_508 (f : Var) : (nb068_alpha_dummy_331 f) ∉ (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) := by
  simpa only [nb068_alpha_dummy_331] using freshVar_not_mem (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) 1

theorem nb068_fresh_509 (f : Var) : (nb068_alpha_dummy_332 f) ∉ (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) := by
  simpa only [nb068_alpha_dummy_332] using freshVar_not_mem (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) 2

theorem nb068_distinct_510 (f : Var) : (nb068_alpha_dummy_330 f) ≠ (nb068_alpha_dummy_331 f) := by
  simpa only [nb068_alpha_dummy_330, nb068_alpha_dummy_331] using
    (freshVar_injective (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) (i := 0) (j := 1) (by decide))

theorem nb068_distinct_511 (f : Var) : (nb068_alpha_dummy_330 f) ≠ (nb068_alpha_dummy_332 f) := by
  simpa only [nb068_alpha_dummy_330, nb068_alpha_dummy_332] using
    (freshVar_injective (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) (i := 0) (j := 2) (by decide))

theorem nb068_distinct_512 (f : Var) : (nb068_alpha_dummy_331 f) ≠ (nb068_alpha_dummy_332 f) := by
  simpa only [nb068_alpha_dummy_331, nb068_alpha_dummy_332] using
    (freshVar_injective (((syn_ccnv (Class.cv f))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) (i := 1) (j := 2) (by decide))

theorem nb068_fresh_513 (f : Var) : (nb068_alpha_dummy_241 f) ∉ (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb068_alpha_dummy_241] using freshVar_not_mem (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) 0

theorem nb068_fresh_514 (f : Var) : (nb068_alpha_dummy_242 f) ∉ (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb068_alpha_dummy_242] using freshVar_not_mem (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) 1

theorem nb068_distinct_515 (f : Var) : (nb068_alpha_dummy_241 f) ≠ (nb068_alpha_dummy_242 f) := by
  simpa only [nb068_alpha_dummy_241, nb068_alpha_dummy_242] using
    (freshVar_injective (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1) (by decide))

theorem nb068_fresh_516 : (nb068_alpha_dummy_043) ∉ (((syn_ccom (Class.cv (nb068_alpha_dummy_000)) (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))).fv ∪ ((syn_cid)).fv) := by
  simpa only [nb068_alpha_dummy_043] using freshVar_not_mem (((syn_ccom (Class.cv (nb068_alpha_dummy_000)) (syn_ccnv (Class.cv (nb068_alpha_dummy_000))))).fv ∪ ((syn_cid)).fv) 0

theorem nb068_fresh_517 (f : Var) : (nb068_alpha_dummy_044 f) ∉ (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) := by
  simpa only [nb068_alpha_dummy_044] using freshVar_not_mem (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) 0

theorem nb068_fresh_518 : (nb068_alpha_dummy_325) ∉ (((syn_ccom (syn_ccnv (Class.cv (nb068_alpha_dummy_000))) (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))))).fv ∪ ((syn_cid)).fv) := by
  simpa only [nb068_alpha_dummy_325] using freshVar_not_mem (((syn_ccom (syn_ccnv (Class.cv (nb068_alpha_dummy_000))) (syn_ccnv (syn_ccnv (Class.cv (nb068_alpha_dummy_000)))))).fv ∪ ((syn_cid)).fv) 0

theorem nb068_fresh_519 (f : Var) : (nb068_alpha_dummy_326 f) ∉ (((syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f))))).fv ∪ ((syn_cid)).fv) := by
  simpa only [nb068_alpha_dummy_326] using freshVar_not_mem (((syn_ccom (syn_ccnv (Class.cv f)) (syn_ccnv (syn_ccnv (Class.cv f))))).fv ∪ ((syn_cid)).fv) 0

theorem nb068_fresh_520 : (nb068_alpha_dummy_009) ∉ (((syn_ccompl (Class.cab (nb068_alpha_dummy_005) (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_001)) (Wff.classEq (Class.cv (nb068_alpha_dummy_005)) (syn_cphi (Class.cv (nb068_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_005) (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_002)) (Wff.classEq (Class.cv (nb068_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_006))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb068_alpha_dummy_009] using freshVar_not_mem (((syn_ccompl (Class.cab (nb068_alpha_dummy_005) (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_001)) (Wff.classEq (Class.cv (nb068_alpha_dummy_005)) (syn_cphi (Class.cv (nb068_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_005) (syn_wrex (nb068_alpha_dummy_006) (Class.cv (nb068_alpha_dummy_002)) (Wff.classEq (Class.cv (nb068_alpha_dummy_005)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_006))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb068_fresh_521 (x : Var) (y : Var) : (nb068_alpha_dummy_010 x y) ∉ (((syn_ccompl (Class.cab (nb068_alpha_dummy_007 x y) (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv x) (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y)) (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_007 x y) (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv y) (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb068_alpha_dummy_010] using freshVar_not_mem (((syn_ccompl (Class.cab (nb068_alpha_dummy_007 x y) (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv x) (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y)) (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_007 x y) (syn_wrex (nb068_alpha_dummy_008 x y) (Class.cv y) (Wff.classEq (Class.cv (nb068_alpha_dummy_007 x y)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb068_fresh_522 : (nb068_alpha_dummy_057) ∉ (((syn_ccompl (Class.cab (nb068_alpha_dummy_053) (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_045)) (Wff.classEq (Class.cv (nb068_alpha_dummy_053)) (syn_cphi (Class.cv (nb068_alpha_dummy_054)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_053) (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_046)) (Wff.classEq (Class.cv (nb068_alpha_dummy_053)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_054))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb068_alpha_dummy_057] using freshVar_not_mem (((syn_ccompl (Class.cab (nb068_alpha_dummy_053) (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_045)) (Wff.classEq (Class.cv (nb068_alpha_dummy_053)) (syn_cphi (Class.cv (nb068_alpha_dummy_054)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_053) (syn_wrex (nb068_alpha_dummy_054) (Class.cv (nb068_alpha_dummy_046)) (Wff.classEq (Class.cv (nb068_alpha_dummy_053)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_054))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb068_fresh_523 (f : Var) : (nb068_alpha_dummy_058 f) ∉ (((syn_ccompl (Class.cab (nb068_alpha_dummy_055 f) (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_055 f) (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_056 f))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb068_alpha_dummy_058] using freshVar_not_mem (((syn_ccompl (Class.cab (nb068_alpha_dummy_055 f) (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_056 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_055 f) (syn_wrex (nb068_alpha_dummy_056 f) (Class.cv (nb068_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_055 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_056 f))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb068_fresh_524 : (nb068_alpha_dummy_093) ∉ (((syn_ccompl (Class.cab (nb068_alpha_dummy_089) (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_045)) (Wff.classEq (Class.cv (nb068_alpha_dummy_089)) (syn_cphi (Class.cv (nb068_alpha_dummy_090)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_089) (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_047)) (Wff.classEq (Class.cv (nb068_alpha_dummy_089)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_090))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb068_alpha_dummy_093] using freshVar_not_mem (((syn_ccompl (Class.cab (nb068_alpha_dummy_089) (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_045)) (Wff.classEq (Class.cv (nb068_alpha_dummy_089)) (syn_cphi (Class.cv (nb068_alpha_dummy_090)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_089) (syn_wrex (nb068_alpha_dummy_090) (Class.cv (nb068_alpha_dummy_047)) (Wff.classEq (Class.cv (nb068_alpha_dummy_089)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_090))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb068_fresh_525 (f : Var) : (nb068_alpha_dummy_094 f) ∉ (((syn_ccompl (Class.cab (nb068_alpha_dummy_091 f) (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_091 f) (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_050 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_092 f))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb068_alpha_dummy_094] using freshVar_not_mem (((syn_ccompl (Class.cab (nb068_alpha_dummy_091 f) (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_092 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_091 f) (syn_wrex (nb068_alpha_dummy_092 f) (Class.cv (nb068_alpha_dummy_050 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_091 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_092 f))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb068_fresh_526 : (nb068_alpha_dummy_135) ∉ (((syn_ccompl (Class.cab (nb068_alpha_dummy_131) (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_125)) (Wff.classEq (Class.cv (nb068_alpha_dummy_131)) (syn_cphi (Class.cv (nb068_alpha_dummy_132)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_131) (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_126)) (Wff.classEq (Class.cv (nb068_alpha_dummy_131)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_132))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb068_alpha_dummy_135] using freshVar_not_mem (((syn_ccompl (Class.cab (nb068_alpha_dummy_131) (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_125)) (Wff.classEq (Class.cv (nb068_alpha_dummy_131)) (syn_cphi (Class.cv (nb068_alpha_dummy_132)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_131) (syn_wrex (nb068_alpha_dummy_132) (Class.cv (nb068_alpha_dummy_126)) (Wff.classEq (Class.cv (nb068_alpha_dummy_131)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_132))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb068_fresh_527 (f : Var) : (nb068_alpha_dummy_136 f) ∉ (((syn_ccompl (Class.cab (nb068_alpha_dummy_133 f) (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_133 f) (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_128 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_134 f))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb068_alpha_dummy_136] using freshVar_not_mem (((syn_ccompl (Class.cab (nb068_alpha_dummy_133 f) (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_134 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_133 f) (syn_wrex (nb068_alpha_dummy_134 f) (Class.cv (nb068_alpha_dummy_128 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_133 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_134 f))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb068_fresh_528 : (nb068_alpha_dummy_171) ∉ (((syn_ccompl (Class.cab (nb068_alpha_dummy_167) (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_126)) (Wff.classEq (Class.cv (nb068_alpha_dummy_167)) (syn_cphi (Class.cv (nb068_alpha_dummy_168)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_167) (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_125)) (Wff.classEq (Class.cv (nb068_alpha_dummy_167)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_168))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb068_alpha_dummy_171] using freshVar_not_mem (((syn_ccompl (Class.cab (nb068_alpha_dummy_167) (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_126)) (Wff.classEq (Class.cv (nb068_alpha_dummy_167)) (syn_cphi (Class.cv (nb068_alpha_dummy_168)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_167) (syn_wrex (nb068_alpha_dummy_168) (Class.cv (nb068_alpha_dummy_125)) (Wff.classEq (Class.cv (nb068_alpha_dummy_167)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_168))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb068_fresh_529 (f : Var) : (nb068_alpha_dummy_172 f) ∉ (((syn_ccompl (Class.cab (nb068_alpha_dummy_169 f) (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_128 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_169 f) (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_170 f))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb068_alpha_dummy_172] using freshVar_not_mem (((syn_ccompl (Class.cab (nb068_alpha_dummy_169 f) (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_128 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_170 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_169 f) (syn_wrex (nb068_alpha_dummy_170 f) (Class.cv (nb068_alpha_dummy_127 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_169 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_170 f))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb068_fresh_530 : (nb068_alpha_dummy_207) ∉ (((syn_ccompl (Class.cab (nb068_alpha_dummy_203) (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_047)) (Wff.classEq (Class.cv (nb068_alpha_dummy_203)) (syn_cphi (Class.cv (nb068_alpha_dummy_204)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_203) (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_046)) (Wff.classEq (Class.cv (nb068_alpha_dummy_203)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_204))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb068_alpha_dummy_207] using freshVar_not_mem (((syn_ccompl (Class.cab (nb068_alpha_dummy_203) (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_047)) (Wff.classEq (Class.cv (nb068_alpha_dummy_203)) (syn_cphi (Class.cv (nb068_alpha_dummy_204)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_203) (syn_wrex (nb068_alpha_dummy_204) (Class.cv (nb068_alpha_dummy_046)) (Wff.classEq (Class.cv (nb068_alpha_dummy_203)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_204))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb068_fresh_531 (f : Var) : (nb068_alpha_dummy_208 f) ∉ (((syn_ccompl (Class.cab (nb068_alpha_dummy_205 f) (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_050 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_205 f) (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_206 f))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb068_alpha_dummy_208] using freshVar_not_mem (((syn_ccompl (Class.cab (nb068_alpha_dummy_205 f) (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_050 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_206 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_205 f) (syn_wrex (nb068_alpha_dummy_206 f) (Class.cv (nb068_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_205 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_206 f))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb068_fresh_532 : (nb068_alpha_dummy_247) ∉ (((syn_ccompl (Class.cab (nb068_alpha_dummy_243) (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_240)) (Wff.classEq (Class.cv (nb068_alpha_dummy_243)) (syn_cphi (Class.cv (nb068_alpha_dummy_244)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_243) (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_239)) (Wff.classEq (Class.cv (nb068_alpha_dummy_243)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_244))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb068_alpha_dummy_247] using freshVar_not_mem (((syn_ccompl (Class.cab (nb068_alpha_dummy_243) (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_240)) (Wff.classEq (Class.cv (nb068_alpha_dummy_243)) (syn_cphi (Class.cv (nb068_alpha_dummy_244)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_243) (syn_wrex (nb068_alpha_dummy_244) (Class.cv (nb068_alpha_dummy_239)) (Wff.classEq (Class.cv (nb068_alpha_dummy_243)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_244))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb068_fresh_533 (f : Var) : (nb068_alpha_dummy_248 f) ∉ (((syn_ccompl (Class.cab (nb068_alpha_dummy_245 f) (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_242 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_245 f) (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_241 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_246 f))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb068_alpha_dummy_248] using freshVar_not_mem (((syn_ccompl (Class.cab (nb068_alpha_dummy_245 f) (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_242 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_245 f) (syn_wrex (nb068_alpha_dummy_246 f) (Class.cv (nb068_alpha_dummy_241 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_246 f))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb068_fresh_534 : (nb068_alpha_dummy_291) ∉ (((syn_ccompl (Class.cab (nb068_alpha_dummy_287) (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_284)) (Wff.classEq (Class.cv (nb068_alpha_dummy_287)) (syn_cphi (Class.cv (nb068_alpha_dummy_288)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_287) (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_283)) (Wff.classEq (Class.cv (nb068_alpha_dummy_287)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_288))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb068_alpha_dummy_291] using freshVar_not_mem (((syn_ccompl (Class.cab (nb068_alpha_dummy_287) (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_284)) (Wff.classEq (Class.cv (nb068_alpha_dummy_287)) (syn_cphi (Class.cv (nb068_alpha_dummy_288)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_287) (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_283)) (Wff.classEq (Class.cv (nb068_alpha_dummy_287)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_288))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb068_fresh_535 (f : Var) : (nb068_alpha_dummy_292 f) ∉ (((syn_ccompl (Class.cab (nb068_alpha_dummy_289 f) (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_286 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_289 f) (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_285 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_290 f))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb068_alpha_dummy_292] using freshVar_not_mem (((syn_ccompl (Class.cab (nb068_alpha_dummy_289 f) (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_286 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_289 f) (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_285 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_290 f))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb068_fresh_536 : (nb068_alpha_dummy_339) ∉ (((syn_ccompl (Class.cab (nb068_alpha_dummy_335) (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_327)) (Wff.classEq (Class.cv (nb068_alpha_dummy_335)) (syn_cphi (Class.cv (nb068_alpha_dummy_336)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_335) (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_328)) (Wff.classEq (Class.cv (nb068_alpha_dummy_335)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_336))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb068_alpha_dummy_339] using freshVar_not_mem (((syn_ccompl (Class.cab (nb068_alpha_dummy_335) (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_327)) (Wff.classEq (Class.cv (nb068_alpha_dummy_335)) (syn_cphi (Class.cv (nb068_alpha_dummy_336)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_335) (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_328)) (Wff.classEq (Class.cv (nb068_alpha_dummy_335)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_336))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb068_fresh_537 (f : Var) : (nb068_alpha_dummy_340 f) ∉ (((syn_ccompl (Class.cab (nb068_alpha_dummy_337 f) (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_330 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_337 f) (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_331 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_338 f))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb068_alpha_dummy_340] using freshVar_not_mem (((syn_ccompl (Class.cab (nb068_alpha_dummy_337 f) (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_330 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_338 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_337 f) (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_331 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_338 f))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb068_fresh_538 : (nb068_alpha_dummy_375) ∉ (((syn_ccompl (Class.cab (nb068_alpha_dummy_371) (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_327)) (Wff.classEq (Class.cv (nb068_alpha_dummy_371)) (syn_cphi (Class.cv (nb068_alpha_dummy_372)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_371) (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_329)) (Wff.classEq (Class.cv (nb068_alpha_dummy_371)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_372))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb068_alpha_dummy_375] using freshVar_not_mem (((syn_ccompl (Class.cab (nb068_alpha_dummy_371) (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_327)) (Wff.classEq (Class.cv (nb068_alpha_dummy_371)) (syn_cphi (Class.cv (nb068_alpha_dummy_372)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_371) (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_329)) (Wff.classEq (Class.cv (nb068_alpha_dummy_371)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_372))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb068_fresh_539 (f : Var) : (nb068_alpha_dummy_376 f) ∉ (((syn_ccompl (Class.cab (nb068_alpha_dummy_373 f) (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_330 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_373 f) (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_332 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_374 f))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb068_alpha_dummy_376] using freshVar_not_mem (((syn_ccompl (Class.cab (nb068_alpha_dummy_373 f) (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_330 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_374 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_373 f) (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_332 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_374 f))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb068_fresh_540 : (nb068_alpha_dummy_417) ∉ (((syn_ccompl (Class.cab (nb068_alpha_dummy_413) (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_407)) (Wff.classEq (Class.cv (nb068_alpha_dummy_413)) (syn_cphi (Class.cv (nb068_alpha_dummy_414)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_413) (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_408)) (Wff.classEq (Class.cv (nb068_alpha_dummy_413)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_414))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb068_alpha_dummy_417] using freshVar_not_mem (((syn_ccompl (Class.cab (nb068_alpha_dummy_413) (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_407)) (Wff.classEq (Class.cv (nb068_alpha_dummy_413)) (syn_cphi (Class.cv (nb068_alpha_dummy_414)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_413) (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_408)) (Wff.classEq (Class.cv (nb068_alpha_dummy_413)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_414))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb068_fresh_541 (f : Var) : (nb068_alpha_dummy_418 f) ∉ (((syn_ccompl (Class.cab (nb068_alpha_dummy_415 f) (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_409 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_415 f) (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_410 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_416 f))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb068_alpha_dummy_418] using freshVar_not_mem (((syn_ccompl (Class.cab (nb068_alpha_dummy_415 f) (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_409 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_416 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_415 f) (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_410 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_416 f))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb068_fresh_542 : (nb068_alpha_dummy_453) ∉ (((syn_ccompl (Class.cab (nb068_alpha_dummy_449) (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_408)) (Wff.classEq (Class.cv (nb068_alpha_dummy_449)) (syn_cphi (Class.cv (nb068_alpha_dummy_450)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_449) (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_407)) (Wff.classEq (Class.cv (nb068_alpha_dummy_449)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_450))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb068_alpha_dummy_453] using freshVar_not_mem (((syn_ccompl (Class.cab (nb068_alpha_dummy_449) (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_408)) (Wff.classEq (Class.cv (nb068_alpha_dummy_449)) (syn_cphi (Class.cv (nb068_alpha_dummy_450)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_449) (syn_wrex (nb068_alpha_dummy_450) (Class.cv (nb068_alpha_dummy_407)) (Wff.classEq (Class.cv (nb068_alpha_dummy_449)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_450))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb068_fresh_543 (f : Var) : (nb068_alpha_dummy_454 f) ∉ (((syn_ccompl (Class.cab (nb068_alpha_dummy_451 f) (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_410 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_452 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_451 f) (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_409 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_452 f))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb068_alpha_dummy_454] using freshVar_not_mem (((syn_ccompl (Class.cab (nb068_alpha_dummy_451 f) (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_410 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_452 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_451 f) (syn_wrex (nb068_alpha_dummy_452 f) (Class.cv (nb068_alpha_dummy_409 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_451 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_452 f))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb068_fresh_544 : (nb068_alpha_dummy_489) ∉ (((syn_ccompl (Class.cab (nb068_alpha_dummy_485) (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_329)) (Wff.classEq (Class.cv (nb068_alpha_dummy_485)) (syn_cphi (Class.cv (nb068_alpha_dummy_486)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_485) (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_328)) (Wff.classEq (Class.cv (nb068_alpha_dummy_485)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_486))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb068_alpha_dummy_489] using freshVar_not_mem (((syn_ccompl (Class.cab (nb068_alpha_dummy_485) (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_329)) (Wff.classEq (Class.cv (nb068_alpha_dummy_485)) (syn_cphi (Class.cv (nb068_alpha_dummy_486)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_485) (syn_wrex (nb068_alpha_dummy_486) (Class.cv (nb068_alpha_dummy_328)) (Wff.classEq (Class.cv (nb068_alpha_dummy_485)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_486))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb068_fresh_545 (f : Var) : (nb068_alpha_dummy_490 f) ∉ (((syn_ccompl (Class.cab (nb068_alpha_dummy_487 f) (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_332 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_487 f) (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_331 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_488 f))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb068_alpha_dummy_490] using freshVar_not_mem (((syn_ccompl (Class.cab (nb068_alpha_dummy_487 f) (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_332 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_488 f)))))))).fv ∪ ((syn_ccompl (Class.cab (nb068_alpha_dummy_487 f) (syn_wrex (nb068_alpha_dummy_488 f) (Class.cv (nb068_alpha_dummy_331 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_487 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_488 f))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb068_fresh_546 : (nb068_alpha_dummy_029) ∉ (((syn_ccompl (Class.cv (nb068_alpha_dummy_020)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_021)))).fv) := by
  simpa only [nb068_alpha_dummy_029] using freshVar_not_mem (((syn_ccompl (Class.cv (nb068_alpha_dummy_020)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_021)))).fv) 0

theorem nb068_fresh_547 (x : Var) (y : Var) : (nb068_alpha_dummy_030 x y) ∉ (((syn_ccompl (Class.cv (nb068_alpha_dummy_023 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_024 x y)))).fv) := by
  simpa only [nb068_alpha_dummy_030] using freshVar_not_mem (((syn_ccompl (Class.cv (nb068_alpha_dummy_023 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_024 x y)))).fv) 0

theorem nb068_fresh_548 : (nb068_alpha_dummy_077) ∉ (((syn_ccompl (Class.cv (nb068_alpha_dummy_068)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_069)))).fv) := by
  simpa only [nb068_alpha_dummy_077] using freshVar_not_mem (((syn_ccompl (Class.cv (nb068_alpha_dummy_068)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_069)))).fv) 0

theorem nb068_fresh_549 (f : Var) : (nb068_alpha_dummy_078 f) ∉ (((syn_ccompl (Class.cv (nb068_alpha_dummy_071 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_072 f)))).fv) := by
  simpa only [nb068_alpha_dummy_078] using freshVar_not_mem (((syn_ccompl (Class.cv (nb068_alpha_dummy_071 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_072 f)))).fv) 0

theorem nb068_fresh_550 : (nb068_alpha_dummy_113) ∉ (((syn_ccompl (Class.cv (nb068_alpha_dummy_104)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_105)))).fv) := by
  simpa only [nb068_alpha_dummy_113] using freshVar_not_mem (((syn_ccompl (Class.cv (nb068_alpha_dummy_104)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_105)))).fv) 0

theorem nb068_fresh_551 (f : Var) : (nb068_alpha_dummy_114 f) ∉ (((syn_ccompl (Class.cv (nb068_alpha_dummy_107 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_108 f)))).fv) := by
  simpa only [nb068_alpha_dummy_114] using freshVar_not_mem (((syn_ccompl (Class.cv (nb068_alpha_dummy_107 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_108 f)))).fv) 0

theorem nb068_fresh_552 : (nb068_alpha_dummy_155) ∉ (((syn_ccompl (Class.cv (nb068_alpha_dummy_146)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_147)))).fv) := by
  simpa only [nb068_alpha_dummy_155] using freshVar_not_mem (((syn_ccompl (Class.cv (nb068_alpha_dummy_146)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_147)))).fv) 0

theorem nb068_fresh_553 (f : Var) : (nb068_alpha_dummy_156 f) ∉ (((syn_ccompl (Class.cv (nb068_alpha_dummy_149 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_150 f)))).fv) := by
  simpa only [nb068_alpha_dummy_156] using freshVar_not_mem (((syn_ccompl (Class.cv (nb068_alpha_dummy_149 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_150 f)))).fv) 0

theorem nb068_fresh_554 : (nb068_alpha_dummy_191) ∉ (((syn_ccompl (Class.cv (nb068_alpha_dummy_182)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_183)))).fv) := by
  simpa only [nb068_alpha_dummy_191] using freshVar_not_mem (((syn_ccompl (Class.cv (nb068_alpha_dummy_182)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_183)))).fv) 0

theorem nb068_fresh_555 (f : Var) : (nb068_alpha_dummy_192 f) ∉ (((syn_ccompl (Class.cv (nb068_alpha_dummy_185 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_186 f)))).fv) := by
  simpa only [nb068_alpha_dummy_192] using freshVar_not_mem (((syn_ccompl (Class.cv (nb068_alpha_dummy_185 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_186 f)))).fv) 0

theorem nb068_fresh_556 : (nb068_alpha_dummy_227) ∉ (((syn_ccompl (Class.cv (nb068_alpha_dummy_218)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_219)))).fv) := by
  simpa only [nb068_alpha_dummy_227] using freshVar_not_mem (((syn_ccompl (Class.cv (nb068_alpha_dummy_218)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_219)))).fv) 0

theorem nb068_fresh_557 (f : Var) : (nb068_alpha_dummy_228 f) ∉ (((syn_ccompl (Class.cv (nb068_alpha_dummy_221 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_222 f)))).fv) := by
  simpa only [nb068_alpha_dummy_228] using freshVar_not_mem (((syn_ccompl (Class.cv (nb068_alpha_dummy_221 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_222 f)))).fv) 0

theorem nb068_fresh_558 : (nb068_alpha_dummy_267) ∉ (((syn_ccompl (Class.cv (nb068_alpha_dummy_258)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_259)))).fv) := by
  simpa only [nb068_alpha_dummy_267] using freshVar_not_mem (((syn_ccompl (Class.cv (nb068_alpha_dummy_258)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_259)))).fv) 0

theorem nb068_fresh_559 (f : Var) : (nb068_alpha_dummy_268 f) ∉ (((syn_ccompl (Class.cv (nb068_alpha_dummy_261 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_262 f)))).fv) := by
  simpa only [nb068_alpha_dummy_268] using freshVar_not_mem (((syn_ccompl (Class.cv (nb068_alpha_dummy_261 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_262 f)))).fv) 0

theorem nb068_fresh_560 : (nb068_alpha_dummy_311) ∉ (((syn_ccompl (Class.cv (nb068_alpha_dummy_302)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_303)))).fv) := by
  simpa only [nb068_alpha_dummy_311] using freshVar_not_mem (((syn_ccompl (Class.cv (nb068_alpha_dummy_302)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_303)))).fv) 0

theorem nb068_fresh_561 (f : Var) : (nb068_alpha_dummy_312 f) ∉ (((syn_ccompl (Class.cv (nb068_alpha_dummy_305 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_306 f)))).fv) := by
  simpa only [nb068_alpha_dummy_312] using freshVar_not_mem (((syn_ccompl (Class.cv (nb068_alpha_dummy_305 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_306 f)))).fv) 0

theorem nb068_fresh_562 : (nb068_alpha_dummy_359) ∉ (((syn_ccompl (Class.cv (nb068_alpha_dummy_350)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_351)))).fv) := by
  simpa only [nb068_alpha_dummy_359] using freshVar_not_mem (((syn_ccompl (Class.cv (nb068_alpha_dummy_350)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_351)))).fv) 0

theorem nb068_fresh_563 (f : Var) : (nb068_alpha_dummy_360 f) ∉ (((syn_ccompl (Class.cv (nb068_alpha_dummy_353 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_354 f)))).fv) := by
  simpa only [nb068_alpha_dummy_360] using freshVar_not_mem (((syn_ccompl (Class.cv (nb068_alpha_dummy_353 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_354 f)))).fv) 0

theorem nb068_fresh_564 : (nb068_alpha_dummy_395) ∉ (((syn_ccompl (Class.cv (nb068_alpha_dummy_386)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_387)))).fv) := by
  simpa only [nb068_alpha_dummy_395] using freshVar_not_mem (((syn_ccompl (Class.cv (nb068_alpha_dummy_386)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_387)))).fv) 0

theorem nb068_fresh_565 (f : Var) : (nb068_alpha_dummy_396 f) ∉ (((syn_ccompl (Class.cv (nb068_alpha_dummy_389 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_390 f)))).fv) := by
  simpa only [nb068_alpha_dummy_396] using freshVar_not_mem (((syn_ccompl (Class.cv (nb068_alpha_dummy_389 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_390 f)))).fv) 0

theorem nb068_fresh_566 : (nb068_alpha_dummy_437) ∉ (((syn_ccompl (Class.cv (nb068_alpha_dummy_428)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_429)))).fv) := by
  simpa only [nb068_alpha_dummy_437] using freshVar_not_mem (((syn_ccompl (Class.cv (nb068_alpha_dummy_428)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_429)))).fv) 0

theorem nb068_fresh_567 (f : Var) : (nb068_alpha_dummy_438 f) ∉ (((syn_ccompl (Class.cv (nb068_alpha_dummy_431 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_432 f)))).fv) := by
  simpa only [nb068_alpha_dummy_438] using freshVar_not_mem (((syn_ccompl (Class.cv (nb068_alpha_dummy_431 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_432 f)))).fv) 0

theorem nb068_fresh_568 : (nb068_alpha_dummy_473) ∉ (((syn_ccompl (Class.cv (nb068_alpha_dummy_464)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_465)))).fv) := by
  simpa only [nb068_alpha_dummy_473] using freshVar_not_mem (((syn_ccompl (Class.cv (nb068_alpha_dummy_464)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_465)))).fv) 0

theorem nb068_fresh_569 (f : Var) : (nb068_alpha_dummy_474 f) ∉ (((syn_ccompl (Class.cv (nb068_alpha_dummy_467 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_468 f)))).fv) := by
  simpa only [nb068_alpha_dummy_474] using freshVar_not_mem (((syn_ccompl (Class.cv (nb068_alpha_dummy_467 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_468 f)))).fv) 0

theorem nb068_fresh_570 : (nb068_alpha_dummy_509) ∉ (((syn_ccompl (Class.cv (nb068_alpha_dummy_500)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_501)))).fv) := by
  simpa only [nb068_alpha_dummy_509] using freshVar_not_mem (((syn_ccompl (Class.cv (nb068_alpha_dummy_500)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_501)))).fv) 0

theorem nb068_fresh_571 (f : Var) : (nb068_alpha_dummy_510 f) ∉ (((syn_ccompl (Class.cv (nb068_alpha_dummy_503 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_504 f)))).fv) := by
  simpa only [nb068_alpha_dummy_510] using freshVar_not_mem (((syn_ccompl (Class.cv (nb068_alpha_dummy_503 f)))).fv ∪ ((syn_ccompl (Class.cv (nb068_alpha_dummy_504 f)))).fv) 0

theorem nb068_fresh_572 : (nb068_alpha_dummy_037) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_006))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb068_alpha_dummy_037] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_006))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb068_fresh_573 (x : Var) (y : Var) : (nb068_alpha_dummy_038 x y) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb068_alpha_dummy_038] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_008 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb068_fresh_574 : (nb068_alpha_dummy_085) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_054))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb068_alpha_dummy_085] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_054))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb068_fresh_575 (f : Var) : (nb068_alpha_dummy_086 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_056 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb068_alpha_dummy_086] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_056 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb068_fresh_576 : (nb068_alpha_dummy_121) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_090))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb068_alpha_dummy_121] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_090))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb068_fresh_577 (f : Var) : (nb068_alpha_dummy_122 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_092 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb068_alpha_dummy_122] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_092 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb068_fresh_578 : (nb068_alpha_dummy_163) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_132))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb068_alpha_dummy_163] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_132))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb068_fresh_579 (f : Var) : (nb068_alpha_dummy_164 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_134 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb068_alpha_dummy_164] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_134 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb068_fresh_580 : (nb068_alpha_dummy_199) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_168))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb068_alpha_dummy_199] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_168))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb068_fresh_581 (f : Var) : (nb068_alpha_dummy_200 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_170 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb068_alpha_dummy_200] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_170 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb068_fresh_582 : (nb068_alpha_dummy_235) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_204))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb068_alpha_dummy_235] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_204))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb068_fresh_583 (f : Var) : (nb068_alpha_dummy_236 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_206 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb068_alpha_dummy_236] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_206 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb068_fresh_584 : (nb068_alpha_dummy_275) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_244))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb068_alpha_dummy_275] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_244))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb068_fresh_585 (f : Var) : (nb068_alpha_dummy_276 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_246 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb068_alpha_dummy_276] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_246 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb068_fresh_586 : (nb068_alpha_dummy_319) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_288))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb068_alpha_dummy_319] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_288))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb068_fresh_587 (f : Var) : (nb068_alpha_dummy_320 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_290 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb068_alpha_dummy_320] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_290 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb068_fresh_588 : (nb068_alpha_dummy_367) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_336))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb068_alpha_dummy_367] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_336))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb068_fresh_589 (f : Var) : (nb068_alpha_dummy_368 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_338 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb068_alpha_dummy_368] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_338 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb068_fresh_590 : (nb068_alpha_dummy_403) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_372))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb068_alpha_dummy_403] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_372))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb068_fresh_591 (f : Var) : (nb068_alpha_dummy_404 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_374 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb068_alpha_dummy_404] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_374 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb068_fresh_592 : (nb068_alpha_dummy_445) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_414))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb068_alpha_dummy_445] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_414))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb068_fresh_593 (f : Var) : (nb068_alpha_dummy_446 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_416 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb068_alpha_dummy_446] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_416 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb068_fresh_594 : (nb068_alpha_dummy_481) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_450))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb068_alpha_dummy_481] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_450))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb068_fresh_595 (f : Var) : (nb068_alpha_dummy_482 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_452 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb068_alpha_dummy_482] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_452 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb068_fresh_596 : (nb068_alpha_dummy_517) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_486))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb068_alpha_dummy_517] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_486))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb068_fresh_597 (f : Var) : (nb068_alpha_dummy_518 f) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_488 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb068_alpha_dummy_518] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb068_alpha_dummy_488 f))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb068_fresh_598 : (nb068_alpha_dummy_025) ∉ (((syn_cnin (Class.cv (nb068_alpha_dummy_020)) (Class.cv (nb068_alpha_dummy_021)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_020)) (Class.cv (nb068_alpha_dummy_021)))).fv) := by
  simpa only [nb068_alpha_dummy_025] using freshVar_not_mem (((syn_cnin (Class.cv (nb068_alpha_dummy_020)) (Class.cv (nb068_alpha_dummy_021)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_020)) (Class.cv (nb068_alpha_dummy_021)))).fv) 0

theorem nb068_fresh_599 (x : Var) (y : Var) : (nb068_alpha_dummy_026 x y) ∉ (((syn_cnin (Class.cv (nb068_alpha_dummy_023 x y)) (Class.cv (nb068_alpha_dummy_024 x y)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_023 x y)) (Class.cv (nb068_alpha_dummy_024 x y)))).fv) := by
  simpa only [nb068_alpha_dummy_026] using freshVar_not_mem (((syn_cnin (Class.cv (nb068_alpha_dummy_023 x y)) (Class.cv (nb068_alpha_dummy_024 x y)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_023 x y)) (Class.cv (nb068_alpha_dummy_024 x y)))).fv) 0

theorem nb068_fresh_600 : (nb068_alpha_dummy_073) ∉ (((syn_cnin (Class.cv (nb068_alpha_dummy_068)) (Class.cv (nb068_alpha_dummy_069)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_068)) (Class.cv (nb068_alpha_dummy_069)))).fv) := by
  simpa only [nb068_alpha_dummy_073] using freshVar_not_mem (((syn_cnin (Class.cv (nb068_alpha_dummy_068)) (Class.cv (nb068_alpha_dummy_069)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_068)) (Class.cv (nb068_alpha_dummy_069)))).fv) 0

theorem nb068_fresh_601 (f : Var) : (nb068_alpha_dummy_074 f) ∉ (((syn_cnin (Class.cv (nb068_alpha_dummy_071 f)) (Class.cv (nb068_alpha_dummy_072 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_071 f)) (Class.cv (nb068_alpha_dummy_072 f)))).fv) := by
  simpa only [nb068_alpha_dummy_074] using freshVar_not_mem (((syn_cnin (Class.cv (nb068_alpha_dummy_071 f)) (Class.cv (nb068_alpha_dummy_072 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_071 f)) (Class.cv (nb068_alpha_dummy_072 f)))).fv) 0

theorem nb068_fresh_602 : (nb068_alpha_dummy_109) ∉ (((syn_cnin (Class.cv (nb068_alpha_dummy_104)) (Class.cv (nb068_alpha_dummy_105)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_104)) (Class.cv (nb068_alpha_dummy_105)))).fv) := by
  simpa only [nb068_alpha_dummy_109] using freshVar_not_mem (((syn_cnin (Class.cv (nb068_alpha_dummy_104)) (Class.cv (nb068_alpha_dummy_105)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_104)) (Class.cv (nb068_alpha_dummy_105)))).fv) 0

theorem nb068_fresh_603 (f : Var) : (nb068_alpha_dummy_110 f) ∉ (((syn_cnin (Class.cv (nb068_alpha_dummy_107 f)) (Class.cv (nb068_alpha_dummy_108 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_107 f)) (Class.cv (nb068_alpha_dummy_108 f)))).fv) := by
  simpa only [nb068_alpha_dummy_110] using freshVar_not_mem (((syn_cnin (Class.cv (nb068_alpha_dummy_107 f)) (Class.cv (nb068_alpha_dummy_108 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_107 f)) (Class.cv (nb068_alpha_dummy_108 f)))).fv) 0

theorem nb068_fresh_604 : (nb068_alpha_dummy_151) ∉ (((syn_cnin (Class.cv (nb068_alpha_dummy_146)) (Class.cv (nb068_alpha_dummy_147)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_146)) (Class.cv (nb068_alpha_dummy_147)))).fv) := by
  simpa only [nb068_alpha_dummy_151] using freshVar_not_mem (((syn_cnin (Class.cv (nb068_alpha_dummy_146)) (Class.cv (nb068_alpha_dummy_147)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_146)) (Class.cv (nb068_alpha_dummy_147)))).fv) 0

theorem nb068_fresh_605 (f : Var) : (nb068_alpha_dummy_152 f) ∉ (((syn_cnin (Class.cv (nb068_alpha_dummy_149 f)) (Class.cv (nb068_alpha_dummy_150 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_149 f)) (Class.cv (nb068_alpha_dummy_150 f)))).fv) := by
  simpa only [nb068_alpha_dummy_152] using freshVar_not_mem (((syn_cnin (Class.cv (nb068_alpha_dummy_149 f)) (Class.cv (nb068_alpha_dummy_150 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_149 f)) (Class.cv (nb068_alpha_dummy_150 f)))).fv) 0

theorem nb068_fresh_606 : (nb068_alpha_dummy_187) ∉ (((syn_cnin (Class.cv (nb068_alpha_dummy_182)) (Class.cv (nb068_alpha_dummy_183)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_182)) (Class.cv (nb068_alpha_dummy_183)))).fv) := by
  simpa only [nb068_alpha_dummy_187] using freshVar_not_mem (((syn_cnin (Class.cv (nb068_alpha_dummy_182)) (Class.cv (nb068_alpha_dummy_183)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_182)) (Class.cv (nb068_alpha_dummy_183)))).fv) 0

theorem nb068_fresh_607 (f : Var) : (nb068_alpha_dummy_188 f) ∉ (((syn_cnin (Class.cv (nb068_alpha_dummy_185 f)) (Class.cv (nb068_alpha_dummy_186 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_185 f)) (Class.cv (nb068_alpha_dummy_186 f)))).fv) := by
  simpa only [nb068_alpha_dummy_188] using freshVar_not_mem (((syn_cnin (Class.cv (nb068_alpha_dummy_185 f)) (Class.cv (nb068_alpha_dummy_186 f)))).fv ∪ ((syn_cnin (Class.cv (nb068_alpha_dummy_185 f)) (Class.cv (nb068_alpha_dummy_186 f)))).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
