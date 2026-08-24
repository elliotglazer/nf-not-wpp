import NAR4C090C001Part013

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

theorem nb090_fresh_922 (A : Class) : (nb090_alpha_dummy_271 A) ∉ (((syn_ccompl (Class.cv (nb090_alpha_dummy_262 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_263 A)))).fv) := by
  simpa only [nb090_alpha_dummy_271] using freshVar_not_mem (((syn_ccompl (Class.cv (nb090_alpha_dummy_262 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_263 A)))).fv) 0

theorem nb090_fresh_923 (h : Var) : (nb090_alpha_dummy_272 h) ∉ (((syn_ccompl (Class.cv (nb090_alpha_dummy_265 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_266 h)))).fv) := by
  simpa only [nb090_alpha_dummy_272] using freshVar_not_mem (((syn_ccompl (Class.cv (nb090_alpha_dummy_265 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_266 h)))).fv) 0

theorem nb090_fresh_924 (A : Class) : (nb090_alpha_dummy_315 A) ∉ (((syn_ccompl (Class.cv (nb090_alpha_dummy_306 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_307 A)))).fv) := by
  simpa only [nb090_alpha_dummy_315] using freshVar_not_mem (((syn_ccompl (Class.cv (nb090_alpha_dummy_306 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_307 A)))).fv) 0

theorem nb090_fresh_925 (u : Var) : (nb090_alpha_dummy_316 u) ∉ (((syn_ccompl (Class.cv (nb090_alpha_dummy_309 u)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_310 u)))).fv) := by
  simpa only [nb090_alpha_dummy_316] using freshVar_not_mem (((syn_ccompl (Class.cv (nb090_alpha_dummy_309 u)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_310 u)))).fv) 0

theorem nb090_fresh_926 (A : Class) : (nb090_alpha_dummy_361 A) ∉ (((syn_ccompl (Class.cv (nb090_alpha_dummy_352 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_353 A)))).fv) := by
  simpa only [nb090_alpha_dummy_361] using freshVar_not_mem (((syn_ccompl (Class.cv (nb090_alpha_dummy_352 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_353 A)))).fv) 0

theorem nb090_fresh_927 (h : Var) : (nb090_alpha_dummy_362 h) ∉ (((syn_ccompl (Class.cv (nb090_alpha_dummy_355 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_356 h)))).fv) := by
  simpa only [nb090_alpha_dummy_362] using freshVar_not_mem (((syn_ccompl (Class.cv (nb090_alpha_dummy_355 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_356 h)))).fv) 0

theorem nb090_fresh_928 (A : Class) : (nb090_alpha_dummy_405 A) ∉ (((syn_ccompl (Class.cv (nb090_alpha_dummy_396 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_397 A)))).fv) := by
  simpa only [nb090_alpha_dummy_405] using freshVar_not_mem (((syn_ccompl (Class.cv (nb090_alpha_dummy_396 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_397 A)))).fv) 0

theorem nb090_fresh_929 (v : Var) : (nb090_alpha_dummy_406 v) ∉ (((syn_ccompl (Class.cv (nb090_alpha_dummy_399 v)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_400 v)))).fv) := by
  simpa only [nb090_alpha_dummy_406] using freshVar_not_mem (((syn_ccompl (Class.cv (nb090_alpha_dummy_399 v)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_400 v)))).fv) 0

theorem nb090_fresh_930 (A : Class) : (nb090_alpha_dummy_455 A) ∉ (((syn_ccompl (Class.cv (nb090_alpha_dummy_446 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_447 A)))).fv) := by
  simpa only [nb090_alpha_dummy_455] using freshVar_not_mem (((syn_ccompl (Class.cv (nb090_alpha_dummy_446 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_447 A)))).fv) 0

theorem nb090_fresh_931 (h : Var) : (nb090_alpha_dummy_456 h) ∉ (((syn_ccompl (Class.cv (nb090_alpha_dummy_449 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_450 h)))).fv) := by
  simpa only [nb090_alpha_dummy_456] using freshVar_not_mem (((syn_ccompl (Class.cv (nb090_alpha_dummy_449 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_450 h)))).fv) 0

theorem nb090_fresh_932 (A : Class) : (nb090_alpha_dummy_491 A) ∉ (((syn_ccompl (Class.cv (nb090_alpha_dummy_482 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_483 A)))).fv) := by
  simpa only [nb090_alpha_dummy_491] using freshVar_not_mem (((syn_ccompl (Class.cv (nb090_alpha_dummy_482 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_483 A)))).fv) 0

theorem nb090_fresh_933 (h : Var) : (nb090_alpha_dummy_492 h) ∉ (((syn_ccompl (Class.cv (nb090_alpha_dummy_485 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_486 h)))).fv) := by
  simpa only [nb090_alpha_dummy_492] using freshVar_not_mem (((syn_ccompl (Class.cv (nb090_alpha_dummy_485 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_486 h)))).fv) 0

theorem nb090_fresh_934 (A : Class) : (nb090_alpha_dummy_533 A) ∉ (((syn_ccompl (Class.cv (nb090_alpha_dummy_524 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_525 A)))).fv) := by
  simpa only [nb090_alpha_dummy_533] using freshVar_not_mem (((syn_ccompl (Class.cv (nb090_alpha_dummy_524 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_525 A)))).fv) 0

theorem nb090_fresh_935 (h : Var) : (nb090_alpha_dummy_534 h) ∉ (((syn_ccompl (Class.cv (nb090_alpha_dummy_527 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_528 h)))).fv) := by
  simpa only [nb090_alpha_dummy_534] using freshVar_not_mem (((syn_ccompl (Class.cv (nb090_alpha_dummy_527 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_528 h)))).fv) 0

theorem nb090_fresh_936 (A : Class) : (nb090_alpha_dummy_569 A) ∉ (((syn_ccompl (Class.cv (nb090_alpha_dummy_560 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_561 A)))).fv) := by
  simpa only [nb090_alpha_dummy_569] using freshVar_not_mem (((syn_ccompl (Class.cv (nb090_alpha_dummy_560 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_561 A)))).fv) 0

theorem nb090_fresh_937 (h : Var) : (nb090_alpha_dummy_570 h) ∉ (((syn_ccompl (Class.cv (nb090_alpha_dummy_563 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_564 h)))).fv) := by
  simpa only [nb090_alpha_dummy_570] using freshVar_not_mem (((syn_ccompl (Class.cv (nb090_alpha_dummy_563 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_564 h)))).fv) 0

theorem nb090_fresh_938 (A : Class) : (nb090_alpha_dummy_605 A) ∉ (((syn_ccompl (Class.cv (nb090_alpha_dummy_596 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_597 A)))).fv) := by
  simpa only [nb090_alpha_dummy_605] using freshVar_not_mem (((syn_ccompl (Class.cv (nb090_alpha_dummy_596 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_597 A)))).fv) 0

theorem nb090_fresh_939 (h : Var) : (nb090_alpha_dummy_606 h) ∉ (((syn_ccompl (Class.cv (nb090_alpha_dummy_599 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_600 h)))).fv) := by
  simpa only [nb090_alpha_dummy_606] using freshVar_not_mem (((syn_ccompl (Class.cv (nb090_alpha_dummy_599 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_600 h)))).fv) 0

theorem nb090_fresh_940 (A : Class) : (nb090_alpha_dummy_641 A) ∉ (((syn_ccompl (Class.cv (nb090_alpha_dummy_632 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_633 A)))).fv) := by
  simpa only [nb090_alpha_dummy_641] using freshVar_not_mem (((syn_ccompl (Class.cv (nb090_alpha_dummy_632 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_633 A)))).fv) 0

theorem nb090_fresh_941 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_642 v u h) ∉ (((syn_ccompl (Class.cv (nb090_alpha_dummy_635 v u h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_636 v u h)))).fv) := by
  simpa only [nb090_alpha_dummy_642] using freshVar_not_mem (((syn_ccompl (Class.cv (nb090_alpha_dummy_635 v u h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_636 v u h)))).fv) 0

theorem nb090_fresh_942 (A : Class) : (nb090_alpha_dummy_685 A) ∉ (((syn_ccompl (Class.cv (nb090_alpha_dummy_676 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_677 A)))).fv) := by
  simpa only [nb090_alpha_dummy_685] using freshVar_not_mem (((syn_ccompl (Class.cv (nb090_alpha_dummy_676 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_677 A)))).fv) 0

theorem nb090_fresh_943 (u : Var) : (nb090_alpha_dummy_686 u) ∉ (((syn_ccompl (Class.cv (nb090_alpha_dummy_679 u)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_680 u)))).fv) := by
  simpa only [nb090_alpha_dummy_686] using freshVar_not_mem (((syn_ccompl (Class.cv (nb090_alpha_dummy_679 u)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_680 u)))).fv) 0

theorem nb090_fresh_944 (A : Class) : (nb090_alpha_dummy_739 A) ∉ (((syn_ccompl (Class.cv (nb090_alpha_dummy_730 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_731 A)))).fv) := by
  simpa only [nb090_alpha_dummy_739] using freshVar_not_mem (((syn_ccompl (Class.cv (nb090_alpha_dummy_730 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_731 A)))).fv) 0

theorem nb090_fresh_945 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_740 v u h) ∉ (((syn_ccompl (Class.cv (nb090_alpha_dummy_733 v u h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_734 v u h)))).fv) := by
  simpa only [nb090_alpha_dummy_740] using freshVar_not_mem (((syn_ccompl (Class.cv (nb090_alpha_dummy_733 v u h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_734 v u h)))).fv) 0

theorem nb090_fresh_946 (A : Class) : (nb090_alpha_dummy_769 A) ∉ (((syn_ccompl (Class.cv (nb090_alpha_dummy_760 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_761 A)))).fv) := by
  simpa only [nb090_alpha_dummy_769] using freshVar_not_mem (((syn_ccompl (Class.cv (nb090_alpha_dummy_760 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_761 A)))).fv) 0

theorem nb090_fresh_947 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_770 v u h) ∉ (((syn_ccompl (Class.cv (nb090_alpha_dummy_763 v u h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_764 v u h)))).fv) := by
  simpa only [nb090_alpha_dummy_770] using freshVar_not_mem (((syn_ccompl (Class.cv (nb090_alpha_dummy_763 v u h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_764 v u h)))).fv) 0

theorem nb090_fresh_948 (A : Class) : (nb090_alpha_dummy_809 A) ∉ (((syn_ccompl (Class.cv (nb090_alpha_dummy_800 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_801 A)))).fv) := by
  simpa only [nb090_alpha_dummy_809] using freshVar_not_mem (((syn_ccompl (Class.cv (nb090_alpha_dummy_800 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_801 A)))).fv) 0

theorem nb090_fresh_949 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_810 v u h) ∉ (((syn_ccompl (Class.cv (nb090_alpha_dummy_803 v u h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_804 v u h)))).fv) := by
  simpa only [nb090_alpha_dummy_810] using freshVar_not_mem (((syn_ccompl (Class.cv (nb090_alpha_dummy_803 v u h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_804 v u h)))).fv) 0

theorem nb090_fresh_950 (A : Class) : (nb090_alpha_dummy_859 A) ∉ (((syn_ccompl (Class.cv (nb090_alpha_dummy_850 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_851 A)))).fv) := by
  simpa only [nb090_alpha_dummy_859] using freshVar_not_mem (((syn_ccompl (Class.cv (nb090_alpha_dummy_850 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_851 A)))).fv) 0

theorem nb090_fresh_951 (v : Var) : (nb090_alpha_dummy_860 v) ∉ (((syn_ccompl (Class.cv (nb090_alpha_dummy_853 v)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_854 v)))).fv) := by
  simpa only [nb090_alpha_dummy_860] using freshVar_not_mem (((syn_ccompl (Class.cv (nb090_alpha_dummy_853 v)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_854 v)))).fv) 0

theorem nb090_fresh_952 (A : Class) : (nb090_alpha_dummy_037 A) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_006 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_037] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_006 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_953 (v : Var) (u : Var) : (nb090_alpha_dummy_038 v u) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_038] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_954 (A : Class) : (nb090_alpha_dummy_089 A) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_089] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_955 (h : Var) : (nb090_alpha_dummy_090 h) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_090] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_956 (A : Class) : (nb090_alpha_dummy_125 A) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_125] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_957 (h : Var) : (nb090_alpha_dummy_126 h) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_126] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_958 (A : Class) : (nb090_alpha_dummy_167 A) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_167] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_959 (h : Var) : (nb090_alpha_dummy_168 h) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_168] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_960 (A : Class) : (nb090_alpha_dummy_203 A) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_203] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_961 (h : Var) : (nb090_alpha_dummy_204 h) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_204] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_962 (A : Class) : (nb090_alpha_dummy_239 A) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_239] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_963 (h : Var) : (nb090_alpha_dummy_240 h) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_240] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_964 (A : Class) : (nb090_alpha_dummy_279 A) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_279] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_965 (h : Var) : (nb090_alpha_dummy_280 h) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_250 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_280] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_250 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_966 (A : Class) : (nb090_alpha_dummy_323 A) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_292 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_323] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_292 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_967 (u : Var) : (nb090_alpha_dummy_324 u) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_294 u))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_324] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_294 u))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_968 (A : Class) : (nb090_alpha_dummy_369 A) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_338 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_369] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_338 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_969 (h : Var) : (nb090_alpha_dummy_370 h) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_340 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_370] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_340 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_970 (A : Class) : (nb090_alpha_dummy_413 A) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_382 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_413] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_382 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_971 (v : Var) : (nb090_alpha_dummy_414 v) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_384 v))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_414] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_384 v))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_972 (A : Class) : (nb090_alpha_dummy_463 A) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_432 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_463] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_432 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_973 (h : Var) : (nb090_alpha_dummy_464 h) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_434 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_464] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_434 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_974 (A : Class) : (nb090_alpha_dummy_499 A) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_468 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_499] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_468 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_975 (h : Var) : (nb090_alpha_dummy_500 h) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_470 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_500] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_470 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_976 (A : Class) : (nb090_alpha_dummy_541 A) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_510 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_541] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_510 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_977 (h : Var) : (nb090_alpha_dummy_542 h) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_512 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_542] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_512 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_978 (A : Class) : (nb090_alpha_dummy_577 A) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_546 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_577] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_546 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_979 (h : Var) : (nb090_alpha_dummy_578 h) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_548 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_578] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_548 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_980 (A : Class) : (nb090_alpha_dummy_613 A) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_582 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_613] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_582 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_981 (h : Var) : (nb090_alpha_dummy_614 h) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_584 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_614] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_584 h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_982 (A : Class) : (nb090_alpha_dummy_649 A) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_618 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_649] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_618 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_983 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_650 v u h) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_650] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_984 (A : Class) : (nb090_alpha_dummy_693 A) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_662 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_693] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_662 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_985 (u : Var) : (nb090_alpha_dummy_694 u) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_664 u))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_694] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_664 u))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_986 (A : Class) : (nb090_alpha_dummy_823 A) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_700 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_823] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_700 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_987 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_824 v u h) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_824] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_988 (A : Class) : (nb090_alpha_dummy_747 A) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_747] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_989 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_748 v u h) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_748] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_990 (A : Class) : (nb090_alpha_dummy_817 A) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_786 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_817] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_786 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_991 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_818 v u h) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_818] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_992 (A : Class) : (nb090_alpha_dummy_867 A) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_867] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_993 (v : Var) : (nb090_alpha_dummy_868 v) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb090_alpha_dummy_868] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb090_fresh_994 (A : Class) : (nb090_alpha_dummy_699 A) ∉ (((syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_041 A)))).fv ∪ ((syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_042 A)))).fv) := by
  simpa only [nb090_alpha_dummy_699] using freshVar_not_mem (((syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_041 A)))).fv ∪ ((syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_042 A)))).fv) 0

theorem nb090_fresh_995 (A : Class) : (nb090_alpha_dummy_700 A) ∉ (((syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_041 A)))).fv ∪ ((syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_042 A)))).fv) := by
  simpa only [nb090_alpha_dummy_700] using freshVar_not_mem (((syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_041 A)))).fv ∪ ((syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_042 A)))).fv) 1

theorem nb090_distinct_996 (A : Class) : (nb090_alpha_dummy_699 A) ≠ (nb090_alpha_dummy_700 A) := by
  simpa only [nb090_alpha_dummy_699, nb090_alpha_dummy_700] using
    (freshVar_injective (((syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_041 A)))).fv ∪ ((syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_042 A)))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_997 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_701 v u h) ∉ (((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))).fv ∪ ((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))).fv) := by
  simpa only [nb090_alpha_dummy_701] using freshVar_not_mem (((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))).fv ∪ ((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))).fv) 0

theorem nb090_fresh_998 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_702 v u h) ∉ (((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))).fv ∪ ((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))).fv) := by
  simpa only [nb090_alpha_dummy_702] using freshVar_not_mem (((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))).fv ∪ ((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))).fv) 1

theorem nb090_distinct_999 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_701 v u h) ≠ (nb090_alpha_dummy_702 v u h) := by
  simpa only [nb090_alpha_dummy_701, nb090_alpha_dummy_702] using
    (freshVar_injective (((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))).fv ∪ ((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_1000 (A : Class) : (nb090_alpha_dummy_025 A) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_020 A)) (Class.cv (nb090_alpha_dummy_021 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_020 A)) (Class.cv (nb090_alpha_dummy_021 A)))).fv) := by
  simpa only [nb090_alpha_dummy_025] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_020 A)) (Class.cv (nb090_alpha_dummy_021 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_020 A)) (Class.cv (nb090_alpha_dummy_021 A)))).fv) 0

theorem nb090_fresh_1001 (v : Var) (u : Var) : (nb090_alpha_dummy_026 v u) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_023 v u)) (Class.cv (nb090_alpha_dummy_024 v u)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_023 v u)) (Class.cv (nb090_alpha_dummy_024 v u)))).fv) := by
  simpa only [nb090_alpha_dummy_026] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_023 v u)) (Class.cv (nb090_alpha_dummy_024 v u)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_023 v u)) (Class.cv (nb090_alpha_dummy_024 v u)))).fv) 0

theorem nb090_fresh_1002 (A : Class) : (nb090_alpha_dummy_077 A) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_072 A)) (Class.cv (nb090_alpha_dummy_073 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_072 A)) (Class.cv (nb090_alpha_dummy_073 A)))).fv) := by
  simpa only [nb090_alpha_dummy_077] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_072 A)) (Class.cv (nb090_alpha_dummy_073 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_072 A)) (Class.cv (nb090_alpha_dummy_073 A)))).fv) 0

theorem nb090_fresh_1003 (h : Var) : (nb090_alpha_dummy_078 h) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_075 h)) (Class.cv (nb090_alpha_dummy_076 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_075 h)) (Class.cv (nb090_alpha_dummy_076 h)))).fv) := by
  simpa only [nb090_alpha_dummy_078] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_075 h)) (Class.cv (nb090_alpha_dummy_076 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_075 h)) (Class.cv (nb090_alpha_dummy_076 h)))).fv) 0

theorem nb090_fresh_1004 (A : Class) : (nb090_alpha_dummy_113 A) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_108 A)) (Class.cv (nb090_alpha_dummy_109 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_108 A)) (Class.cv (nb090_alpha_dummy_109 A)))).fv) := by
  simpa only [nb090_alpha_dummy_113] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_108 A)) (Class.cv (nb090_alpha_dummy_109 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_108 A)) (Class.cv (nb090_alpha_dummy_109 A)))).fv) 0

theorem nb090_fresh_1005 (h : Var) : (nb090_alpha_dummy_114 h) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_111 h)) (Class.cv (nb090_alpha_dummy_112 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_111 h)) (Class.cv (nb090_alpha_dummy_112 h)))).fv) := by
  simpa only [nb090_alpha_dummy_114] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_111 h)) (Class.cv (nb090_alpha_dummy_112 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_111 h)) (Class.cv (nb090_alpha_dummy_112 h)))).fv) 0

theorem nb090_fresh_1006 (A : Class) : (nb090_alpha_dummy_155 A) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_150 A)) (Class.cv (nb090_alpha_dummy_151 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_150 A)) (Class.cv (nb090_alpha_dummy_151 A)))).fv) := by
  simpa only [nb090_alpha_dummy_155] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_150 A)) (Class.cv (nb090_alpha_dummy_151 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_150 A)) (Class.cv (nb090_alpha_dummy_151 A)))).fv) 0

theorem nb090_fresh_1007 (h : Var) : (nb090_alpha_dummy_156 h) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_153 h)) (Class.cv (nb090_alpha_dummy_154 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_153 h)) (Class.cv (nb090_alpha_dummy_154 h)))).fv) := by
  simpa only [nb090_alpha_dummy_156] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_153 h)) (Class.cv (nb090_alpha_dummy_154 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_153 h)) (Class.cv (nb090_alpha_dummy_154 h)))).fv) 0

theorem nb090_fresh_1008 (A : Class) : (nb090_alpha_dummy_191 A) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_186 A)) (Class.cv (nb090_alpha_dummy_187 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_186 A)) (Class.cv (nb090_alpha_dummy_187 A)))).fv) := by
  simpa only [nb090_alpha_dummy_191] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_186 A)) (Class.cv (nb090_alpha_dummy_187 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_186 A)) (Class.cv (nb090_alpha_dummy_187 A)))).fv) 0

theorem nb090_fresh_1009 (h : Var) : (nb090_alpha_dummy_192 h) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_189 h)) (Class.cv (nb090_alpha_dummy_190 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_189 h)) (Class.cv (nb090_alpha_dummy_190 h)))).fv) := by
  simpa only [nb090_alpha_dummy_192] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_189 h)) (Class.cv (nb090_alpha_dummy_190 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_189 h)) (Class.cv (nb090_alpha_dummy_190 h)))).fv) 0

theorem nb090_fresh_1010 (A : Class) : (nb090_alpha_dummy_227 A) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_222 A)) (Class.cv (nb090_alpha_dummy_223 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_222 A)) (Class.cv (nb090_alpha_dummy_223 A)))).fv) := by
  simpa only [nb090_alpha_dummy_227] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_222 A)) (Class.cv (nb090_alpha_dummy_223 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_222 A)) (Class.cv (nb090_alpha_dummy_223 A)))).fv) 0

theorem nb090_fresh_1011 (h : Var) : (nb090_alpha_dummy_228 h) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_225 h)) (Class.cv (nb090_alpha_dummy_226 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_225 h)) (Class.cv (nb090_alpha_dummy_226 h)))).fv) := by
  simpa only [nb090_alpha_dummy_228] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_225 h)) (Class.cv (nb090_alpha_dummy_226 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_225 h)) (Class.cv (nb090_alpha_dummy_226 h)))).fv) 0

theorem nb090_fresh_1012 (A : Class) : (nb090_alpha_dummy_267 A) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_262 A)) (Class.cv (nb090_alpha_dummy_263 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_262 A)) (Class.cv (nb090_alpha_dummy_263 A)))).fv) := by
  simpa only [nb090_alpha_dummy_267] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_262 A)) (Class.cv (nb090_alpha_dummy_263 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_262 A)) (Class.cv (nb090_alpha_dummy_263 A)))).fv) 0

theorem nb090_fresh_1013 (h : Var) : (nb090_alpha_dummy_268 h) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_265 h)) (Class.cv (nb090_alpha_dummy_266 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_265 h)) (Class.cv (nb090_alpha_dummy_266 h)))).fv) := by
  simpa only [nb090_alpha_dummy_268] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_265 h)) (Class.cv (nb090_alpha_dummy_266 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_265 h)) (Class.cv (nb090_alpha_dummy_266 h)))).fv) 0

theorem nb090_fresh_1014 (A : Class) : (nb090_alpha_dummy_311 A) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_306 A)) (Class.cv (nb090_alpha_dummy_307 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_306 A)) (Class.cv (nb090_alpha_dummy_307 A)))).fv) := by
  simpa only [nb090_alpha_dummy_311] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_306 A)) (Class.cv (nb090_alpha_dummy_307 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_306 A)) (Class.cv (nb090_alpha_dummy_307 A)))).fv) 0

theorem nb090_fresh_1015 (u : Var) : (nb090_alpha_dummy_312 u) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_309 u)) (Class.cv (nb090_alpha_dummy_310 u)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_309 u)) (Class.cv (nb090_alpha_dummy_310 u)))).fv) := by
  simpa only [nb090_alpha_dummy_312] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_309 u)) (Class.cv (nb090_alpha_dummy_310 u)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_309 u)) (Class.cv (nb090_alpha_dummy_310 u)))).fv) 0

theorem nb090_fresh_1016 (A : Class) : (nb090_alpha_dummy_357 A) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_352 A)) (Class.cv (nb090_alpha_dummy_353 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_352 A)) (Class.cv (nb090_alpha_dummy_353 A)))).fv) := by
  simpa only [nb090_alpha_dummy_357] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_352 A)) (Class.cv (nb090_alpha_dummy_353 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_352 A)) (Class.cv (nb090_alpha_dummy_353 A)))).fv) 0

theorem nb090_fresh_1017 (h : Var) : (nb090_alpha_dummy_358 h) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_355 h)) (Class.cv (nb090_alpha_dummy_356 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_355 h)) (Class.cv (nb090_alpha_dummy_356 h)))).fv) := by
  simpa only [nb090_alpha_dummy_358] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_355 h)) (Class.cv (nb090_alpha_dummy_356 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_355 h)) (Class.cv (nb090_alpha_dummy_356 h)))).fv) 0

theorem nb090_fresh_1018 (A : Class) : (nb090_alpha_dummy_401 A) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_396 A)) (Class.cv (nb090_alpha_dummy_397 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_396 A)) (Class.cv (nb090_alpha_dummy_397 A)))).fv) := by
  simpa only [nb090_alpha_dummy_401] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_396 A)) (Class.cv (nb090_alpha_dummy_397 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_396 A)) (Class.cv (nb090_alpha_dummy_397 A)))).fv) 0

theorem nb090_fresh_1019 (v : Var) : (nb090_alpha_dummy_402 v) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_399 v)) (Class.cv (nb090_alpha_dummy_400 v)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_399 v)) (Class.cv (nb090_alpha_dummy_400 v)))).fv) := by
  simpa only [nb090_alpha_dummy_402] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_399 v)) (Class.cv (nb090_alpha_dummy_400 v)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_399 v)) (Class.cv (nb090_alpha_dummy_400 v)))).fv) 0

theorem nb090_fresh_1020 (A : Class) : (nb090_alpha_dummy_451 A) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_446 A)) (Class.cv (nb090_alpha_dummy_447 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_446 A)) (Class.cv (nb090_alpha_dummy_447 A)))).fv) := by
  simpa only [nb090_alpha_dummy_451] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_446 A)) (Class.cv (nb090_alpha_dummy_447 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_446 A)) (Class.cv (nb090_alpha_dummy_447 A)))).fv) 0

theorem nb090_fresh_1021 (h : Var) : (nb090_alpha_dummy_452 h) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_449 h)) (Class.cv (nb090_alpha_dummy_450 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_449 h)) (Class.cv (nb090_alpha_dummy_450 h)))).fv) := by
  simpa only [nb090_alpha_dummy_452] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_449 h)) (Class.cv (nb090_alpha_dummy_450 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_449 h)) (Class.cv (nb090_alpha_dummy_450 h)))).fv) 0

theorem nb090_fresh_1022 (A : Class) : (nb090_alpha_dummy_487 A) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_482 A)) (Class.cv (nb090_alpha_dummy_483 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_482 A)) (Class.cv (nb090_alpha_dummy_483 A)))).fv) := by
  simpa only [nb090_alpha_dummy_487] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_482 A)) (Class.cv (nb090_alpha_dummy_483 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_482 A)) (Class.cv (nb090_alpha_dummy_483 A)))).fv) 0

theorem nb090_fresh_1023 (h : Var) : (nb090_alpha_dummy_488 h) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_485 h)) (Class.cv (nb090_alpha_dummy_486 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_485 h)) (Class.cv (nb090_alpha_dummy_486 h)))).fv) := by
  simpa only [nb090_alpha_dummy_488] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_485 h)) (Class.cv (nb090_alpha_dummy_486 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_485 h)) (Class.cv (nb090_alpha_dummy_486 h)))).fv) 0

theorem nb090_fresh_1024 (A : Class) : (nb090_alpha_dummy_529 A) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_524 A)) (Class.cv (nb090_alpha_dummy_525 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_524 A)) (Class.cv (nb090_alpha_dummy_525 A)))).fv) := by
  simpa only [nb090_alpha_dummy_529] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_524 A)) (Class.cv (nb090_alpha_dummy_525 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_524 A)) (Class.cv (nb090_alpha_dummy_525 A)))).fv) 0

theorem nb090_fresh_1025 (h : Var) : (nb090_alpha_dummy_530 h) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_527 h)) (Class.cv (nb090_alpha_dummy_528 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_527 h)) (Class.cv (nb090_alpha_dummy_528 h)))).fv) := by
  simpa only [nb090_alpha_dummy_530] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_527 h)) (Class.cv (nb090_alpha_dummy_528 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_527 h)) (Class.cv (nb090_alpha_dummy_528 h)))).fv) 0

theorem nb090_fresh_1026 (A : Class) : (nb090_alpha_dummy_565 A) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_560 A)) (Class.cv (nb090_alpha_dummy_561 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_560 A)) (Class.cv (nb090_alpha_dummy_561 A)))).fv) := by
  simpa only [nb090_alpha_dummy_565] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_560 A)) (Class.cv (nb090_alpha_dummy_561 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_560 A)) (Class.cv (nb090_alpha_dummy_561 A)))).fv) 0

theorem nb090_fresh_1027 (h : Var) : (nb090_alpha_dummy_566 h) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_563 h)) (Class.cv (nb090_alpha_dummy_564 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_563 h)) (Class.cv (nb090_alpha_dummy_564 h)))).fv) := by
  simpa only [nb090_alpha_dummy_566] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_563 h)) (Class.cv (nb090_alpha_dummy_564 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_563 h)) (Class.cv (nb090_alpha_dummy_564 h)))).fv) 0

theorem nb090_fresh_1028 (A : Class) : (nb090_alpha_dummy_601 A) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_596 A)) (Class.cv (nb090_alpha_dummy_597 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_596 A)) (Class.cv (nb090_alpha_dummy_597 A)))).fv) := by
  simpa only [nb090_alpha_dummy_601] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_596 A)) (Class.cv (nb090_alpha_dummy_597 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_596 A)) (Class.cv (nb090_alpha_dummy_597 A)))).fv) 0

theorem nb090_fresh_1029 (h : Var) : (nb090_alpha_dummy_602 h) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_599 h)) (Class.cv (nb090_alpha_dummy_600 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_599 h)) (Class.cv (nb090_alpha_dummy_600 h)))).fv) := by
  simpa only [nb090_alpha_dummy_602] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_599 h)) (Class.cv (nb090_alpha_dummy_600 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_599 h)) (Class.cv (nb090_alpha_dummy_600 h)))).fv) 0

theorem nb090_fresh_1030 (A : Class) : (nb090_alpha_dummy_637 A) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_632 A)) (Class.cv (nb090_alpha_dummy_633 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_632 A)) (Class.cv (nb090_alpha_dummy_633 A)))).fv) := by
  simpa only [nb090_alpha_dummy_637] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_632 A)) (Class.cv (nb090_alpha_dummy_633 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_632 A)) (Class.cv (nb090_alpha_dummy_633 A)))).fv) 0

theorem nb090_fresh_1031 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_638 v u h) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_635 v u h)) (Class.cv (nb090_alpha_dummy_636 v u h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_635 v u h)) (Class.cv (nb090_alpha_dummy_636 v u h)))).fv) := by
  simpa only [nb090_alpha_dummy_638] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_635 v u h)) (Class.cv (nb090_alpha_dummy_636 v u h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_635 v u h)) (Class.cv (nb090_alpha_dummy_636 v u h)))).fv) 0

theorem nb090_fresh_1032 (A : Class) : (nb090_alpha_dummy_681 A) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_676 A)) (Class.cv (nb090_alpha_dummy_677 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_676 A)) (Class.cv (nb090_alpha_dummy_677 A)))).fv) := by
  simpa only [nb090_alpha_dummy_681] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_676 A)) (Class.cv (nb090_alpha_dummy_677 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_676 A)) (Class.cv (nb090_alpha_dummy_677 A)))).fv) 0

theorem nb090_fresh_1033 (u : Var) : (nb090_alpha_dummy_682 u) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_679 u)) (Class.cv (nb090_alpha_dummy_680 u)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_679 u)) (Class.cv (nb090_alpha_dummy_680 u)))).fv) := by
  simpa only [nb090_alpha_dummy_682] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_679 u)) (Class.cv (nb090_alpha_dummy_680 u)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_679 u)) (Class.cv (nb090_alpha_dummy_680 u)))).fv) 0

theorem nb090_fresh_1034 (A : Class) : (nb090_alpha_dummy_735 A) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_730 A)) (Class.cv (nb090_alpha_dummy_731 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_730 A)) (Class.cv (nb090_alpha_dummy_731 A)))).fv) := by
  simpa only [nb090_alpha_dummy_735] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_730 A)) (Class.cv (nb090_alpha_dummy_731 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_730 A)) (Class.cv (nb090_alpha_dummy_731 A)))).fv) 0

theorem nb090_fresh_1035 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_736 v u h) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_733 v u h)) (Class.cv (nb090_alpha_dummy_734 v u h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_733 v u h)) (Class.cv (nb090_alpha_dummy_734 v u h)))).fv) := by
  simpa only [nb090_alpha_dummy_736] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_733 v u h)) (Class.cv (nb090_alpha_dummy_734 v u h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_733 v u h)) (Class.cv (nb090_alpha_dummy_734 v u h)))).fv) 0

theorem nb090_fresh_1036 (A : Class) : (nb090_alpha_dummy_765 A) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_760 A)) (Class.cv (nb090_alpha_dummy_761 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_760 A)) (Class.cv (nb090_alpha_dummy_761 A)))).fv) := by
  simpa only [nb090_alpha_dummy_765] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_760 A)) (Class.cv (nb090_alpha_dummy_761 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_760 A)) (Class.cv (nb090_alpha_dummy_761 A)))).fv) 0

theorem nb090_fresh_1037 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_766 v u h) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_763 v u h)) (Class.cv (nb090_alpha_dummy_764 v u h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_763 v u h)) (Class.cv (nb090_alpha_dummy_764 v u h)))).fv) := by
  simpa only [nb090_alpha_dummy_766] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_763 v u h)) (Class.cv (nb090_alpha_dummy_764 v u h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_763 v u h)) (Class.cv (nb090_alpha_dummy_764 v u h)))).fv) 0

theorem nb090_fresh_1038 (A : Class) : (nb090_alpha_dummy_805 A) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_800 A)) (Class.cv (nb090_alpha_dummy_801 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_800 A)) (Class.cv (nb090_alpha_dummy_801 A)))).fv) := by
  simpa only [nb090_alpha_dummy_805] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_800 A)) (Class.cv (nb090_alpha_dummy_801 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_800 A)) (Class.cv (nb090_alpha_dummy_801 A)))).fv) 0

theorem nb090_fresh_1039 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_806 v u h) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_803 v u h)) (Class.cv (nb090_alpha_dummy_804 v u h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_803 v u h)) (Class.cv (nb090_alpha_dummy_804 v u h)))).fv) := by
  simpa only [nb090_alpha_dummy_806] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_803 v u h)) (Class.cv (nb090_alpha_dummy_804 v u h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_803 v u h)) (Class.cv (nb090_alpha_dummy_804 v u h)))).fv) 0

theorem nb090_fresh_1040 (A : Class) : (nb090_alpha_dummy_855 A) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_850 A)) (Class.cv (nb090_alpha_dummy_851 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_850 A)) (Class.cv (nb090_alpha_dummy_851 A)))).fv) := by
  simpa only [nb090_alpha_dummy_855] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_850 A)) (Class.cv (nb090_alpha_dummy_851 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_850 A)) (Class.cv (nb090_alpha_dummy_851 A)))).fv) 0

theorem nb090_fresh_1041 (v : Var) : (nb090_alpha_dummy_856 v) ∉ (((syn_cnin (Class.cv (nb090_alpha_dummy_853 v)) (Class.cv (nb090_alpha_dummy_854 v)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_853 v)) (Class.cv (nb090_alpha_dummy_854 v)))).fv) := by
  simpa only [nb090_alpha_dummy_856] using freshVar_not_mem (((syn_cnin (Class.cv (nb090_alpha_dummy_853 v)) (Class.cv (nb090_alpha_dummy_854 v)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_853 v)) (Class.cv (nb090_alpha_dummy_854 v)))).fv) 0

theorem nb090_fresh_1042 (A : Class) : (nb090_alpha_dummy_045 A) ∉ (((syn_cnin (syn_ccom (Class.cv (nb090_alpha_dummy_000 A)) (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv (nb090_alpha_dummy_000 A)) (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))) (syn_cid))).fv) := by
  simpa only [nb090_alpha_dummy_045] using freshVar_not_mem (((syn_cnin (syn_ccom (Class.cv (nb090_alpha_dummy_000 A)) (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv (nb090_alpha_dummy_000 A)) (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))) (syn_cid))).fv) 0

theorem nb090_fresh_1043 (h : Var) : (nb090_alpha_dummy_046 h) ∉ (((syn_cnin (syn_ccom (Class.cv h) (syn_ccnv (Class.cv h))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv h) (syn_ccnv (Class.cv h))) (syn_cid))).fv) := by
  simpa only [nb090_alpha_dummy_046] using freshVar_not_mem (((syn_cnin (syn_ccom (Class.cv h) (syn_ccnv (Class.cv h))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (Class.cv h) (syn_ccnv (Class.cv h))) (syn_cid))).fv) 0

theorem nb090_fresh_1044 (A : Class) : (nb090_alpha_dummy_419 A) ∉ (((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))) (syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))) (syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))) (syn_cid))).fv) := by
  simpa only [nb090_alpha_dummy_419] using freshVar_not_mem (((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))) (syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))) (syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))) (syn_cid))).fv) 0

theorem nb090_fresh_1045 (h : Var) : (nb090_alpha_dummy_420 h) ∉ (((syn_cnin (syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h)))) (syn_cid))).fv) := by
  simpa only [nb090_alpha_dummy_420] using freshVar_not_mem (((syn_cnin (syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h)))) (syn_cid))).fv ∪ ((syn_cnin (syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h)))) (syn_cid))).fv) 0

theorem nb090_fresh_1046 (A : Class) : (nb090_alpha_dummy_329 A) ∉ (((syn_cnin (syn_crn (Class.cv (nb090_alpha_dummy_000 A))) (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A))))).fv ∪ ((syn_cnin (syn_crn (Class.cv (nb090_alpha_dummy_000 A))) (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A))))).fv) := by
  simpa only [nb090_alpha_dummy_329] using freshVar_not_mem (((syn_cnin (syn_crn (Class.cv (nb090_alpha_dummy_000 A))) (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A))))).fv ∪ ((syn_cnin (syn_crn (Class.cv (nb090_alpha_dummy_000 A))) (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A))))).fv) 0

theorem nb090_fresh_1047 (v : Var) (h : Var) : (nb090_alpha_dummy_330 v h) ∉ (((syn_cnin (syn_crn (Class.cv h)) (syn_cfv (syn_c2nd) (Class.cv v)))).fv ∪ ((syn_cnin (syn_crn (Class.cv h)) (syn_cfv (syn_c2nd) (Class.cv v)))).fv) := by
  simpa only [nb090_alpha_dummy_330] using freshVar_not_mem (((syn_cnin (syn_crn (Class.cv h)) (syn_cfv (syn_c2nd) (Class.cv v)))).fv ∪ ((syn_cnin (syn_crn (Class.cv h)) (syn_cfv (syn_c2nd) (Class.cv v)))).fv) 0

theorem nb090_fresh_1048 (A : Class) : (nb090_alpha_dummy_039 A) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))).fv) := by
  simpa only [nb090_alpha_dummy_039] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))).fv) 0

theorem nb090_fresh_1049 (v : Var) (u : Var) : (nb090_alpha_dummy_040 v u) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))).fv) := by
  simpa only [nb090_alpha_dummy_040] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))).fv) 0

theorem nb090_fresh_1050 (A : Class) : (nb090_alpha_dummy_091 A) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))).fv) := by
  simpa only [nb090_alpha_dummy_091] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))).fv) 0

theorem nb090_fresh_1051 (h : Var) : (nb090_alpha_dummy_092 h) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))).fv) := by
  simpa only [nb090_alpha_dummy_092] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))).fv) 0

theorem nb090_fresh_1052 (A : Class) : (nb090_alpha_dummy_127 A) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))).fv) := by
  simpa only [nb090_alpha_dummy_127] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))).fv) 0

theorem nb090_fresh_1053 (h : Var) : (nb090_alpha_dummy_128 h) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))).fv) := by
  simpa only [nb090_alpha_dummy_128] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))).fv) 0

theorem nb090_fresh_1054 (A : Class) : (nb090_alpha_dummy_169 A) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))).fv) := by
  simpa only [nb090_alpha_dummy_169] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))).fv) 0

theorem nb090_fresh_1055 (h : Var) : (nb090_alpha_dummy_170 h) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))).fv) := by
  simpa only [nb090_alpha_dummy_170] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))).fv) 0

theorem nb090_fresh_1056 (A : Class) : (nb090_alpha_dummy_205 A) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))).fv) := by
  simpa only [nb090_alpha_dummy_205] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))).fv) 0

theorem nb090_fresh_1057 (h : Var) : (nb090_alpha_dummy_206 h) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))).fv) := by
  simpa only [nb090_alpha_dummy_206] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))).fv) 0

theorem nb090_fresh_1058 (A : Class) : (nb090_alpha_dummy_241 A) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))).fv) := by
  simpa only [nb090_alpha_dummy_241] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))).fv) 0

theorem nb090_fresh_1059 (h : Var) : (nb090_alpha_dummy_242 h) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))).fv) := by
  simpa only [nb090_alpha_dummy_242] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))).fv) 0

theorem nb090_fresh_1060 (A : Class) : (nb090_alpha_dummy_281 A) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))).fv) := by
  simpa only [nb090_alpha_dummy_281] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))).fv) 0

theorem nb090_fresh_1061 (h : Var) : (nb090_alpha_dummy_282 h) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))).fv) := by
  simpa only [nb090_alpha_dummy_282] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))).fv) 0

theorem nb090_fresh_1062 (A : Class) : (nb090_alpha_dummy_325 A) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))).fv) := by
  simpa only [nb090_alpha_dummy_325] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))).fv) 0

theorem nb090_fresh_1063 (u : Var) : (nb090_alpha_dummy_326 u) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))).fv) := by
  simpa only [nb090_alpha_dummy_326] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))).fv) 0

theorem nb090_fresh_1064 (A : Class) : (nb090_alpha_dummy_371 A) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))).fv) := by
  simpa only [nb090_alpha_dummy_371] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
