import NAR4C090C001Part014

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

theorem nb090_fresh_1065 (h : Var) : (nb090_alpha_dummy_372 h) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))).fv) := by
  simpa only [nb090_alpha_dummy_372] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))).fv) 0

theorem nb090_fresh_1066 (A : Class) : (nb090_alpha_dummy_415 A) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))).fv) := by
  simpa only [nb090_alpha_dummy_415] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))).fv) 0

theorem nb090_fresh_1067 (v : Var) : (nb090_alpha_dummy_416 v) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))).fv) := by
  simpa only [nb090_alpha_dummy_416] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))).fv) 0

theorem nb090_fresh_1068 (A : Class) : (nb090_alpha_dummy_465 A) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))).fv) := by
  simpa only [nb090_alpha_dummy_465] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))).fv) 0

theorem nb090_fresh_1069 (h : Var) : (nb090_alpha_dummy_466 h) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))).fv) := by
  simpa only [nb090_alpha_dummy_466] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))).fv) 0

theorem nb090_fresh_1070 (A : Class) : (nb090_alpha_dummy_501 A) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))).fv) := by
  simpa only [nb090_alpha_dummy_501] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))).fv) 0

theorem nb090_fresh_1071 (h : Var) : (nb090_alpha_dummy_502 h) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))).fv) := by
  simpa only [nb090_alpha_dummy_502] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))).fv) 0

theorem nb090_fresh_1072 (A : Class) : (nb090_alpha_dummy_543 A) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))).fv) := by
  simpa only [nb090_alpha_dummy_543] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))).fv) 0

theorem nb090_fresh_1073 (h : Var) : (nb090_alpha_dummy_544 h) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))).fv) := by
  simpa only [nb090_alpha_dummy_544] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))).fv) 0

theorem nb090_fresh_1074 (A : Class) : (nb090_alpha_dummy_579 A) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))).fv) := by
  simpa only [nb090_alpha_dummy_579] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))).fv) 0

theorem nb090_fresh_1075 (h : Var) : (nb090_alpha_dummy_580 h) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))).fv) := by
  simpa only [nb090_alpha_dummy_580] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))).fv) 0

theorem nb090_fresh_1076 (A : Class) : (nb090_alpha_dummy_615 A) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))).fv) := by
  simpa only [nb090_alpha_dummy_615] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))).fv) 0

theorem nb090_fresh_1077 (h : Var) : (nb090_alpha_dummy_616 h) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))).fv) := by
  simpa only [nb090_alpha_dummy_616] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))).fv) 0

theorem nb090_fresh_1078 (A : Class) : (nb090_alpha_dummy_651 A) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))).fv) := by
  simpa only [nb090_alpha_dummy_651] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))).fv) 0

theorem nb090_fresh_1079 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_652 v u h) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))).fv) := by
  simpa only [nb090_alpha_dummy_652] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))).fv) 0

theorem nb090_fresh_1080 (A : Class) : (nb090_alpha_dummy_695 A) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))).fv) := by
  simpa only [nb090_alpha_dummy_695] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))).fv) 0

theorem nb090_fresh_1081 (u : Var) : (nb090_alpha_dummy_696 u) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))).fv) := by
  simpa only [nb090_alpha_dummy_696] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))).fv) 0

theorem nb090_fresh_1082 (A : Class) : (nb090_alpha_dummy_825 A) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))).fv) := by
  simpa only [nb090_alpha_dummy_825] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))).fv) 0

theorem nb090_fresh_1083 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_826 v u h) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))).fv) := by
  simpa only [nb090_alpha_dummy_826] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))).fv) 0

theorem nb090_fresh_1084 (A : Class) : (nb090_alpha_dummy_749 A) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))).fv) := by
  simpa only [nb090_alpha_dummy_749] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))).fv) 0

theorem nb090_fresh_1085 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_750 v u h) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))).fv) := by
  simpa only [nb090_alpha_dummy_750] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))).fv) 0

theorem nb090_fresh_1086 (A : Class) : (nb090_alpha_dummy_819 A) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))).fv) := by
  simpa only [nb090_alpha_dummy_819] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))).fv) 0

theorem nb090_fresh_1087 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_820 v u h) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))).fv) := by
  simpa only [nb090_alpha_dummy_820] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))).fv) 0

theorem nb090_fresh_1088 (A : Class) : (nb090_alpha_dummy_869 A) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))).fv) := by
  simpa only [nb090_alpha_dummy_869] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))).fv) 0

theorem nb090_fresh_1089 (v : Var) : (nb090_alpha_dummy_870 v) ∉ (((syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))).fv) := by
  simpa only [nb090_alpha_dummy_870] using freshVar_not_mem (((syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))).fv) 0

theorem nb090_fresh_1090 (A : Class) : (nb090_alpha_dummy_331 A) ∉ (((syn_crn (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A)))).fv) := by
  simpa only [nb090_alpha_dummy_331] using freshVar_not_mem (((syn_crn (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A)))).fv) 0

theorem nb090_fresh_1091 (v : Var) (h : Var) : (nb090_alpha_dummy_332 v h) ∉ (((syn_crn (Class.cv h))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv v))).fv) := by
  simpa only [nb090_alpha_dummy_332] using freshVar_not_mem (((syn_crn (Class.cv h))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv v))).fv) 0

theorem nb090_fresh_1092 (A : Class) : (nb090_alpha_dummy_000 A) ∉ ((A).fv) := by
  simpa only [nb090_alpha_dummy_000] using freshVar_not_mem ((A).fv) 0

theorem nb090_fresh_1093 (A : Class) : (nb090_alpha_dummy_001 A) ∉ ((A).fv) := by
  simpa only [nb090_alpha_dummy_001] using freshVar_not_mem ((A).fv) 1

theorem nb090_fresh_1094 (A : Class) : (nb090_alpha_dummy_002 A) ∉ ((A).fv) := by
  simpa only [nb090_alpha_dummy_002] using freshVar_not_mem ((A).fv) 2

theorem nb090_distinct_1095 (A : Class) : (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_001 A) := by
  simpa only [nb090_alpha_dummy_000, nb090_alpha_dummy_001] using
    (freshVar_injective ((A).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_1096 (A : Class) : (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_002 A) := by
  simpa only [nb090_alpha_dummy_000, nb090_alpha_dummy_002] using
    (freshVar_injective ((A).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_1097 (A : Class) : (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_002 A) := by
  simpa only [nb090_alpha_dummy_001, nb090_alpha_dummy_002] using
    (freshVar_injective ((A).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_1098 (A : Class) : (nb090_alpha_dummy_003 A) ∉ (({(nb090_alpha_dummy_001 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_002 A)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv (nb090_alpha_dummy_001 A)) (syn_chwcodes A)) (Wff.classMem (Class.cv (nb090_alpha_dummy_002 A)) (syn_chwcodes A))) (syn_wex (nb090_alpha_dummy_000 A) (syn_wiso (Class.cv (nb090_alpha_dummy_000 A)) (syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_001 A))) (syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002 A))) (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A))) (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A))))))).fv) := by
  simpa only [nb090_alpha_dummy_003] using freshVar_not_mem (({(nb090_alpha_dummy_001 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_002 A)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv (nb090_alpha_dummy_001 A)) (syn_chwcodes A)) (Wff.classMem (Class.cv (nb090_alpha_dummy_002 A)) (syn_chwcodes A))) (syn_wex (nb090_alpha_dummy_000 A) (syn_wiso (Class.cv (nb090_alpha_dummy_000 A)) (syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_001 A))) (syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002 A))) (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A))) (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A))))))).fv) 0

theorem nb090_fresh_1099 (A : Class) : (nb090_alpha_dummy_055 A) ∉ (({(nb090_alpha_dummy_049 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_050 A)} : Finset Var) ∪ ((syn_wex (nb090_alpha_dummy_051 A) (syn_wa (syn_wbr (Class.cv (nb090_alpha_dummy_049 A)) (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))) (Class.cv (nb090_alpha_dummy_051 A))) (syn_wbr (Class.cv (nb090_alpha_dummy_051 A)) (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_050 A)))))).fv) := by
  simpa only [nb090_alpha_dummy_055] using freshVar_not_mem (({(nb090_alpha_dummy_049 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_050 A)} : Finset Var) ∪ ((syn_wex (nb090_alpha_dummy_051 A) (syn_wa (syn_wbr (Class.cv (nb090_alpha_dummy_049 A)) (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))) (Class.cv (nb090_alpha_dummy_051 A))) (syn_wbr (Class.cv (nb090_alpha_dummy_051 A)) (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_050 A)))))).fv) 0

theorem nb090_fresh_1100 (h : Var) : (nb090_alpha_dummy_056 h) ∉ (({(nb090_alpha_dummy_052 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_053 h)} : Finset Var) ∪ ((syn_wex (nb090_alpha_dummy_054 h) (syn_wa (syn_wbr (Class.cv (nb090_alpha_dummy_052 h)) (syn_ccnv (Class.cv h)) (Class.cv (nb090_alpha_dummy_054 h))) (syn_wbr (Class.cv (nb090_alpha_dummy_054 h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_053 h)))))).fv) := by
  simpa only [nb090_alpha_dummy_056] using freshVar_not_mem (({(nb090_alpha_dummy_052 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_053 h)} : Finset Var) ∪ ((syn_wex (nb090_alpha_dummy_054 h) (syn_wa (syn_wbr (Class.cv (nb090_alpha_dummy_052 h)) (syn_ccnv (Class.cv h)) (Class.cv (nb090_alpha_dummy_054 h))) (syn_wbr (Class.cv (nb090_alpha_dummy_054 h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_053 h)))))).fv) 0

theorem nb090_fresh_1101 (A : Class) : (nb090_alpha_dummy_133 A) ∉ (({(nb090_alpha_dummy_129 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_130 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_130 A)) (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_129 A)))).fv) := by
  simpa only [nb090_alpha_dummy_133] using freshVar_not_mem (({(nb090_alpha_dummy_129 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_130 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_130 A)) (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_129 A)))).fv) 0

theorem nb090_fresh_1102 (h : Var) : (nb090_alpha_dummy_134 h) ∉ (({(nb090_alpha_dummy_131 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_132 h)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_132 h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_131 h)))).fv) := by
  simpa only [nb090_alpha_dummy_134] using freshVar_not_mem (({(nb090_alpha_dummy_131 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_132 h)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_132 h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_131 h)))).fv) 0

theorem nb090_fresh_1103 (A : Class) : (nb090_alpha_dummy_285 A) ∉ (({(nb090_alpha_dummy_283 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c2nd) (Class.cv (nb090_alpha_dummy_283 A)))).fv) := by
  simpa only [nb090_alpha_dummy_285] using freshVar_not_mem (({(nb090_alpha_dummy_283 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c2nd) (Class.cv (nb090_alpha_dummy_283 A)))).fv) 0

theorem nb090_fresh_1104 (u : Var) : (nb090_alpha_dummy_286 u) ∉ (({(nb090_alpha_dummy_284 u)} : Finset Var) ∪ ((syn_wbr (Class.cv u) (syn_c2nd) (Class.cv (nb090_alpha_dummy_284 u)))).fv) := by
  simpa only [nb090_alpha_dummy_286] using freshVar_not_mem (({(nb090_alpha_dummy_284 u)} : Finset Var) ∪ ((syn_wbr (Class.cv u) (syn_c2nd) (Class.cv (nb090_alpha_dummy_284 u)))).fv) 0

theorem nb090_fresh_1105 (A : Class) : (nb090_alpha_dummy_375 A) ∉ (({(nb090_alpha_dummy_373 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c2nd) (Class.cv (nb090_alpha_dummy_373 A)))).fv) := by
  simpa only [nb090_alpha_dummy_375] using freshVar_not_mem (({(nb090_alpha_dummy_373 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c2nd) (Class.cv (nb090_alpha_dummy_373 A)))).fv) 0

theorem nb090_fresh_1106 (v : Var) : (nb090_alpha_dummy_376 v) ∉ (({(nb090_alpha_dummy_374 v)} : Finset Var) ∪ ((syn_wbr (Class.cv v) (syn_c2nd) (Class.cv (nb090_alpha_dummy_374 v)))).fv) := by
  simpa only [nb090_alpha_dummy_376] using freshVar_not_mem (({(nb090_alpha_dummy_374 v)} : Finset Var) ∪ ((syn_wbr (Class.cv v) (syn_c2nd) (Class.cv (nb090_alpha_dummy_374 v)))).fv) 0

theorem nb090_fresh_1107 (A : Class) : (nb090_alpha_dummy_429 A) ∉ (({(nb090_alpha_dummy_423 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_424 A)} : Finset Var) ∪ ((syn_wex (nb090_alpha_dummy_425 A) (syn_wa (syn_wbr (Class.cv (nb090_alpha_dummy_423 A)) (syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))) (Class.cv (nb090_alpha_dummy_425 A))) (syn_wbr (Class.cv (nb090_alpha_dummy_425 A)) (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))) (Class.cv (nb090_alpha_dummy_424 A)))))).fv) := by
  simpa only [nb090_alpha_dummy_429] using freshVar_not_mem (({(nb090_alpha_dummy_423 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_424 A)} : Finset Var) ∪ ((syn_wex (nb090_alpha_dummy_425 A) (syn_wa (syn_wbr (Class.cv (nb090_alpha_dummy_423 A)) (syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))) (Class.cv (nb090_alpha_dummy_425 A))) (syn_wbr (Class.cv (nb090_alpha_dummy_425 A)) (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))) (Class.cv (nb090_alpha_dummy_424 A)))))).fv) 0

theorem nb090_fresh_1108 (h : Var) : (nb090_alpha_dummy_430 h) ∉ (({(nb090_alpha_dummy_426 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_427 h)} : Finset Var) ∪ ((syn_wex (nb090_alpha_dummy_428 h) (syn_wa (syn_wbr (Class.cv (nb090_alpha_dummy_426 h)) (syn_ccnv (syn_ccnv (Class.cv h))) (Class.cv (nb090_alpha_dummy_428 h))) (syn_wbr (Class.cv (nb090_alpha_dummy_428 h)) (syn_ccnv (Class.cv h)) (Class.cv (nb090_alpha_dummy_427 h)))))).fv) := by
  simpa only [nb090_alpha_dummy_430] using freshVar_not_mem (({(nb090_alpha_dummy_426 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_427 h)} : Finset Var) ∪ ((syn_wex (nb090_alpha_dummy_428 h) (syn_wa (syn_wbr (Class.cv (nb090_alpha_dummy_426 h)) (syn_ccnv (syn_ccnv (Class.cv h))) (Class.cv (nb090_alpha_dummy_428 h))) (syn_wbr (Class.cv (nb090_alpha_dummy_428 h)) (syn_ccnv (Class.cv h)) (Class.cv (nb090_alpha_dummy_427 h)))))).fv) 0

theorem nb090_fresh_1109 (A : Class) : (nb090_alpha_dummy_507 A) ∉ (({(nb090_alpha_dummy_503 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_504 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_504 A)) (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))) (Class.cv (nb090_alpha_dummy_503 A)))).fv) := by
  simpa only [nb090_alpha_dummy_507] using freshVar_not_mem (({(nb090_alpha_dummy_503 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_504 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_504 A)) (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))) (Class.cv (nb090_alpha_dummy_503 A)))).fv) 0

theorem nb090_fresh_1110 (h : Var) : (nb090_alpha_dummy_508 h) ∉ (({(nb090_alpha_dummy_505 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_506 h)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_506 h)) (syn_ccnv (Class.cv h)) (Class.cv (nb090_alpha_dummy_505 h)))).fv) := by
  simpa only [nb090_alpha_dummy_508] using freshVar_not_mem (({(nb090_alpha_dummy_505 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_506 h)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_506 h)) (syn_ccnv (Class.cv h)) (Class.cv (nb090_alpha_dummy_505 h)))).fv) 0

theorem nb090_fresh_1111 (A : Class) : (nb090_alpha_dummy_655 A) ∉ (({(nb090_alpha_dummy_653 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c1st) (Class.cv (nb090_alpha_dummy_653 A)))).fv) := by
  simpa only [nb090_alpha_dummy_655] using freshVar_not_mem (({(nb090_alpha_dummy_653 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c1st) (Class.cv (nb090_alpha_dummy_653 A)))).fv) 0

theorem nb090_fresh_1112 (u : Var) : (nb090_alpha_dummy_656 u) ∉ (({(nb090_alpha_dummy_654 u)} : Finset Var) ∪ ((syn_wbr (Class.cv u) (syn_c1st) (Class.cv (nb090_alpha_dummy_654 u)))).fv) := by
  simpa only [nb090_alpha_dummy_656] using freshVar_not_mem (({(nb090_alpha_dummy_654 u)} : Finset Var) ∪ ((syn_wbr (Class.cv u) (syn_c1st) (Class.cv (nb090_alpha_dummy_654 u)))).fv) 0

theorem nb090_fresh_1113 (A : Class) : (nb090_alpha_dummy_709 A) ∉ (({(nb090_alpha_dummy_707 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_041 A)) (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_707 A)))).fv) := by
  simpa only [nb090_alpha_dummy_709] using freshVar_not_mem (({(nb090_alpha_dummy_707 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_041 A)) (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_707 A)))).fv) 0

theorem nb090_fresh_1114 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_710 v u h) ∉ (({(nb090_alpha_dummy_708 v u h)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_043 v u h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_708 v u h)))).fv) := by
  simpa only [nb090_alpha_dummy_710] using freshVar_not_mem (({(nb090_alpha_dummy_708 v u h)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_043 v u h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_708 v u h)))).fv) 0

theorem nb090_fresh_1115 (A : Class) : (nb090_alpha_dummy_779 A) ∉ (({(nb090_alpha_dummy_777 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_042 A)) (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_777 A)))).fv) := by
  simpa only [nb090_alpha_dummy_779] using freshVar_not_mem (({(nb090_alpha_dummy_777 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_042 A)) (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_777 A)))).fv) 0

theorem nb090_fresh_1116 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_780 v u h) ∉ (({(nb090_alpha_dummy_778 v u h)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_044 v u h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_778 v u h)))).fv) := by
  simpa only [nb090_alpha_dummy_780] using freshVar_not_mem (({(nb090_alpha_dummy_778 v u h)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_044 v u h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_778 v u h)))).fv) 0

theorem nb090_fresh_1117 (A : Class) : (nb090_alpha_dummy_829 A) ∉ (({(nb090_alpha_dummy_827 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c1st) (Class.cv (nb090_alpha_dummy_827 A)))).fv) := by
  simpa only [nb090_alpha_dummy_829] using freshVar_not_mem (({(nb090_alpha_dummy_827 A)} : Finset Var) ∪ ((syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c1st) (Class.cv (nb090_alpha_dummy_827 A)))).fv) 0

theorem nb090_fresh_1118 (v : Var) : (nb090_alpha_dummy_830 v) ∉ (({(nb090_alpha_dummy_828 v)} : Finset Var) ∪ ((syn_wbr (Class.cv v) (syn_c1st) (Class.cv (nb090_alpha_dummy_828 v)))).fv) := by
  simpa only [nb090_alpha_dummy_830] using freshVar_not_mem (({(nb090_alpha_dummy_828 v)} : Finset Var) ∪ ((syn_wbr (Class.cv v) (syn_c1st) (Class.cv (nb090_alpha_dummy_828 v)))).fv) 0

theorem nb090_fresh_1119 (v : Var) (u : Var) (A : Class) (h : Var) : (nb090_alpha_dummy_004 v u A h) ∉ (({u} : Finset Var) ∪ ({v} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv u) (syn_chwcodes A)) (Wff.classMem (Class.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (Class.cv h) (syn_cfv (syn_c1st) (Class.cv u)) (syn_cfv (syn_c1st) (Class.cv v)) (syn_cfv (syn_c2nd) (Class.cv u)) (syn_cfv (syn_c2nd) (Class.cv v)))))).fv) := by
  simpa only [nb090_alpha_dummy_004] using freshVar_not_mem (({u} : Finset Var) ∪ ({v} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv u) (syn_chwcodes A)) (Wff.classMem (Class.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (Class.cv h) (syn_cfv (syn_c1st) (Class.cv u)) (syn_cfv (syn_c1st) (Class.cv v)) (syn_cfv (syn_c2nd) (Class.cv u)) (syn_cfv (syn_c2nd) (Class.cv v)))))).fv) 0

theorem nb090_support_mem_0000 (A : Class) : (nb090_alpha_dummy_001 A) ∈ (({(nb090_alpha_dummy_001 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_002 A)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv (nb090_alpha_dummy_001 A)) (syn_chwcodes A)) (Wff.classMem (Class.cv (nb090_alpha_dummy_002 A)) (syn_chwcodes A))) (syn_wex (nb090_alpha_dummy_000 A) (syn_wiso (Class.cv (nb090_alpha_dummy_000 A)) (syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_001 A))) (syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002 A))) (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A))) (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A))))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0001 (v : Var) (u : Var) (A : Class) (h : Var) : u ∈ (({u} : Finset Var) ∪ ({v} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv u) (syn_chwcodes A)) (Wff.classMem (Class.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (Class.cv h) (syn_cfv (syn_c1st) (Class.cv u)) (syn_cfv (syn_c1st) (Class.cv v)) (syn_cfv (syn_c2nd) (Class.cv u)) (syn_cfv (syn_c2nd) (Class.cv v)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0002 (A : Class) : (nb090_alpha_dummy_002 A) ∈ (({(nb090_alpha_dummy_001 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_002 A)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv (nb090_alpha_dummy_001 A)) (syn_chwcodes A)) (Wff.classMem (Class.cv (nb090_alpha_dummy_002 A)) (syn_chwcodes A))) (syn_wex (nb090_alpha_dummy_000 A) (syn_wiso (Class.cv (nb090_alpha_dummy_000 A)) (syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_001 A))) (syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002 A))) (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A))) (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A))))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0003 (v : Var) (u : Var) (A : Class) (h : Var) : v ∈ (({u} : Finset Var) ∪ ({v} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv u) (syn_chwcodes A)) (Wff.classMem (Class.cv v) (syn_chwcodes A))) (syn_wex h (syn_wiso (Class.cv h) (syn_cfv (syn_c1st) (Class.cv u)) (syn_cfv (syn_c1st) (Class.cv v)) (syn_cfv (syn_c2nd) (Class.cv u)) (syn_cfv (syn_c2nd) (Class.cv v)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0004 (A : Class) : (nb090_alpha_dummy_001 A) ∈ (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_002 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0005 (A : Class) : (nb090_alpha_dummy_001 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_005 A) (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_001 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_005 A) (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_002 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_006 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0004 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0004 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0006 (v : Var) (u : Var) : u ∈ (((Class.cv u)).fv ∪ ((Class.cv v)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0007 (v : Var) (u : Var) : u ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_007 v u) (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv u) (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u)) (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_007 v u) (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv v) (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0006 v u) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0006 v u) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0008 (A : Class) : (nb090_alpha_dummy_001 A) ∈ (((Class.cab (nb090_alpha_dummy_005 A) (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_001 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_006 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_005 A) (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_001 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_006 A))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0004 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0004 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0009 (v : Var) (u : Var) : u ∈ (((Class.cab (nb090_alpha_dummy_007 v u) (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv u) (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u)) (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_007 v u) (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv u) (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u)) (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0006 v u) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0006 v u) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0010 (A : Class) : (nb090_alpha_dummy_006 A) ∈ (((Class.cv (nb090_alpha_dummy_006 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0011 (v : Var) (u : Var) : (nb090_alpha_dummy_008 v u) ∈ (((Class.cv (nb090_alpha_dummy_008 v u))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0012 (A : Class) : (nb090_alpha_dummy_013 A) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_013 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_013 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_013 A))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0013 (v : Var) (u : Var) : (nb090_alpha_dummy_015 v u) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_015 v u)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_015 v u)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_015 v u))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0014 (A : Class) : (nb090_alpha_dummy_013 A) ∈ (((Class.cv (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0015 (v : Var) (u : Var) : (nb090_alpha_dummy_015 v u) ∈ (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0016 (A : Class) : (nb090_alpha_dummy_020 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_020 A)) (Class.cv (nb090_alpha_dummy_021 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_020 A)) (Class.cv (nb090_alpha_dummy_021 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0017 (v : Var) (u : Var) : (nb090_alpha_dummy_023 v u) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_023 v u)) (Class.cv (nb090_alpha_dummy_024 v u)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_023 v u)) (Class.cv (nb090_alpha_dummy_024 v u)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0018 (A : Class) : (nb090_alpha_dummy_020 A) ∈ (((Class.cv (nb090_alpha_dummy_020 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_021 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0019 (v : Var) (u : Var) : (nb090_alpha_dummy_023 v u) ∈ (((Class.cv (nb090_alpha_dummy_023 v u))).fv ∪ ((Class.cv (nb090_alpha_dummy_024 v u))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0020 (A : Class) : (nb090_alpha_dummy_021 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_020 A)) (Class.cv (nb090_alpha_dummy_021 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_020 A)) (Class.cv (nb090_alpha_dummy_021 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0021 (v : Var) (u : Var) : (nb090_alpha_dummy_024 v u) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_023 v u)) (Class.cv (nb090_alpha_dummy_024 v u)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_023 v u)) (Class.cv (nb090_alpha_dummy_024 v u)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0022 (A : Class) : (nb090_alpha_dummy_021 A) ∈ (((Class.cv (nb090_alpha_dummy_020 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_021 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0023 (v : Var) (u : Var) : (nb090_alpha_dummy_024 v u) ∈ (((Class.cv (nb090_alpha_dummy_023 v u))).fv ∪ ((Class.cv (nb090_alpha_dummy_024 v u))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0024 (A : Class) : (nb090_alpha_dummy_020 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_020 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_021 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0025 (v : Var) (u : Var) : (nb090_alpha_dummy_023 v u) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_023 v u)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_024 v u)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0026 (A : Class) : (nb090_alpha_dummy_020 A) ∈ (((Class.cv (nb090_alpha_dummy_020 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_020 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0027 (v : Var) (u : Var) : (nb090_alpha_dummy_023 v u) ∈ (((Class.cv (nb090_alpha_dummy_023 v u))).fv ∪ ((Class.cv (nb090_alpha_dummy_023 v u))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0028 (A : Class) : (nb090_alpha_dummy_021 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_020 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_021 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0029 (v : Var) (u : Var) : (nb090_alpha_dummy_024 v u) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_023 v u)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_024 v u)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0030 (A : Class) : (nb090_alpha_dummy_021 A) ∈ (((Class.cv (nb090_alpha_dummy_021 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_021 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0031 (v : Var) (u : Var) : (nb090_alpha_dummy_024 v u) ∈ (((Class.cv (nb090_alpha_dummy_024 v u))).fv ∪ ((Class.cv (nb090_alpha_dummy_024 v u))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0032 (A : Class) : (nb090_alpha_dummy_002 A) ∈ (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_002 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0033 (A : Class) : (nb090_alpha_dummy_002 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_005 A) (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_001 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_005 A) (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_002 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_006 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0032 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0032 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0034 (v : Var) (u : Var) : v ∈ (((Class.cv u)).fv ∪ ((Class.cv v)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0035 (v : Var) (u : Var) : v ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_007 v u) (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv u) (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u)) (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_007 v u) (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv v) (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0034 v u) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0034 v u) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0036 (A : Class) : (nb090_alpha_dummy_002 A) ∈ (((Class.cab (nb090_alpha_dummy_005 A) (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_002 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_006 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_005 A) (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_002 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_006 A))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0032 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0032 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0037 (v : Var) (u : Var) : v ∈ (((Class.cab (nb090_alpha_dummy_007 v u) (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv v) (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_007 v u) (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv v) (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0034 v u) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0034 v u) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0038 (A : Class) : (nb090_alpha_dummy_006 A) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_006 A))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0039 (v : Var) (u : Var) : (nb090_alpha_dummy_008 v u) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0040 (A : Class) : (nb090_alpha_dummy_006 A) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0041 (v : Var) (u : Var) : (nb090_alpha_dummy_008 v u) ∈ (((syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))).fv ∪ ((syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0042 (A : Class) : (nb090_alpha_dummy_049 A) ∈ (({(nb090_alpha_dummy_049 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_050 A)} : Finset Var) ∪ ((syn_wex (nb090_alpha_dummy_051 A) (syn_wa (syn_wbr (Class.cv (nb090_alpha_dummy_049 A)) (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))) (Class.cv (nb090_alpha_dummy_051 A))) (syn_wbr (Class.cv (nb090_alpha_dummy_051 A)) (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_050 A)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0043 (h : Var) : (nb090_alpha_dummy_052 h) ∈ (({(nb090_alpha_dummy_052 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_053 h)} : Finset Var) ∪ ((syn_wex (nb090_alpha_dummy_054 h) (syn_wa (syn_wbr (Class.cv (nb090_alpha_dummy_052 h)) (syn_ccnv (Class.cv h)) (Class.cv (nb090_alpha_dummy_054 h))) (syn_wbr (Class.cv (nb090_alpha_dummy_054 h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_053 h)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0044 (A : Class) : (nb090_alpha_dummy_050 A) ∈ (({(nb090_alpha_dummy_049 A)} : Finset Var) ∪ ({(nb090_alpha_dummy_050 A)} : Finset Var) ∪ ((syn_wex (nb090_alpha_dummy_051 A) (syn_wa (syn_wbr (Class.cv (nb090_alpha_dummy_049 A)) (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))) (Class.cv (nb090_alpha_dummy_051 A))) (syn_wbr (Class.cv (nb090_alpha_dummy_051 A)) (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_050 A)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0045 (h : Var) : (nb090_alpha_dummy_053 h) ∈ (({(nb090_alpha_dummy_052 h)} : Finset Var) ∪ ({(nb090_alpha_dummy_053 h)} : Finset Var) ∪ ((syn_wex (nb090_alpha_dummy_054 h) (syn_wa (syn_wbr (Class.cv (nb090_alpha_dummy_052 h)) (syn_ccnv (Class.cv h)) (Class.cv (nb090_alpha_dummy_054 h))) (syn_wbr (Class.cv (nb090_alpha_dummy_054 h)) (Class.cv h) (Class.cv (nb090_alpha_dummy_053 h)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0046 (A : Class) : (nb090_alpha_dummy_049 A) ∈ (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_050 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0047 (A : Class) : (nb090_alpha_dummy_049 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_057 A) (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_049 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_057 A) (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_050 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0046 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0046 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0048 (h : Var) : (nb090_alpha_dummy_052 h) ∈ (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_053 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0049 (h : Var) : (nb090_alpha_dummy_052 h) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_059 h) (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_052 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_059 h) (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_053 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0048 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0048 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0050 (A : Class) : (nb090_alpha_dummy_049 A) ∈ (((Class.cab (nb090_alpha_dummy_057 A) (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_049 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_057 A) (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_049 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0046 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0046 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0051 (h : Var) : (nb090_alpha_dummy_052 h) ∈ (((Class.cab (nb090_alpha_dummy_059 h) (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_052 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_059 h) (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_052 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0048 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0048 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0052 (A : Class) : (nb090_alpha_dummy_058 A) ∈ (((Class.cv (nb090_alpha_dummy_058 A))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0053 (h : Var) : (nb090_alpha_dummy_060 h) ∈ (((Class.cv (nb090_alpha_dummy_060 h))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0054 (A : Class) : (nb090_alpha_dummy_065 A) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_065 A)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_065 A)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_065 A))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0055 (h : Var) : (nb090_alpha_dummy_067 h) ∈ (((Wff.classMem (Class.cv (nb090_alpha_dummy_067 h)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb090_alpha_dummy_067 h)) (syn_c1c))).fv ∪ ((Class.cv (nb090_alpha_dummy_067 h))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0056 (A : Class) : (nb090_alpha_dummy_065 A) ∈ (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0057 (h : Var) : (nb090_alpha_dummy_067 h) ∈ (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0058 (A : Class) : (nb090_alpha_dummy_072 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_072 A)) (Class.cv (nb090_alpha_dummy_073 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_072 A)) (Class.cv (nb090_alpha_dummy_073 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0059 (h : Var) : (nb090_alpha_dummy_075 h) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_075 h)) (Class.cv (nb090_alpha_dummy_076 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_075 h)) (Class.cv (nb090_alpha_dummy_076 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0060 (A : Class) : (nb090_alpha_dummy_072 A) ∈ (((Class.cv (nb090_alpha_dummy_072 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_073 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0061 (h : Var) : (nb090_alpha_dummy_075 h) ∈ (((Class.cv (nb090_alpha_dummy_075 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_076 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0062 (A : Class) : (nb090_alpha_dummy_073 A) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_072 A)) (Class.cv (nb090_alpha_dummy_073 A)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_072 A)) (Class.cv (nb090_alpha_dummy_073 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0063 (h : Var) : (nb090_alpha_dummy_076 h) ∈ (((syn_cnin (Class.cv (nb090_alpha_dummy_075 h)) (Class.cv (nb090_alpha_dummy_076 h)))).fv ∪ ((syn_cnin (Class.cv (nb090_alpha_dummy_075 h)) (Class.cv (nb090_alpha_dummy_076 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0064 (A : Class) : (nb090_alpha_dummy_073 A) ∈ (((Class.cv (nb090_alpha_dummy_072 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_073 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0065 (h : Var) : (nb090_alpha_dummy_076 h) ∈ (((Class.cv (nb090_alpha_dummy_075 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_076 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0066 (A : Class) : (nb090_alpha_dummy_072 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_072 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_073 A)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0067 (h : Var) : (nb090_alpha_dummy_075 h) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_075 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_076 h)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0068 (A : Class) : (nb090_alpha_dummy_072 A) ∈ (((Class.cv (nb090_alpha_dummy_072 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_072 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0069 (h : Var) : (nb090_alpha_dummy_075 h) ∈ (((Class.cv (nb090_alpha_dummy_075 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_075 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0070 (A : Class) : (nb090_alpha_dummy_073 A) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_072 A)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_073 A)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0071 (h : Var) : (nb090_alpha_dummy_076 h) ∈ (((syn_ccompl (Class.cv (nb090_alpha_dummy_075 h)))).fv ∪ ((syn_ccompl (Class.cv (nb090_alpha_dummy_076 h)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0072 (A : Class) : (nb090_alpha_dummy_073 A) ∈ (((Class.cv (nb090_alpha_dummy_073 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_073 A))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0073 (h : Var) : (nb090_alpha_dummy_076 h) ∈ (((Class.cv (nb090_alpha_dummy_076 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_076 h))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0074 (A : Class) : (nb090_alpha_dummy_050 A) ∈ (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_050 A))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0075 (A : Class) : (nb090_alpha_dummy_050 A) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_057 A) (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_049 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_057 A) (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_050 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0074 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0074 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0076 (h : Var) : (nb090_alpha_dummy_053 h) ∈ (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_053 h))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0077 (h : Var) : (nb090_alpha_dummy_053 h) ∈ (((syn_ccompl (Class.cab (nb090_alpha_dummy_059 h) (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_052 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))))))).fv ∪ ((syn_ccompl (Class.cab (nb090_alpha_dummy_059 h) (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_053 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0076 h) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0076 h) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0078 (A : Class) : (nb090_alpha_dummy_050 A) ∈ (((Class.cab (nb090_alpha_dummy_057 A) (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_050 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_057 A) (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_050 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A)) (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0074 A) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0074 A) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
