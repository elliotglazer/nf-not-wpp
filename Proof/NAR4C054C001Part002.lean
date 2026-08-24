import NAR4C054C001Part001

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

theorem nb054_fresh_060 : (nb054_alpha_dummy_068) ∉ (((Class.cv (nb054_alpha_dummy_057))).fv ∪ ((Class.cv (nb054_alpha_dummy_057))).fv) := by
  simpa only [nb054_alpha_dummy_068] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_057))).fv ∪ ((Class.cv (nb054_alpha_dummy_057))).fv) 0

theorem nb054_fresh_061 : (nb054_alpha_dummy_064) ∉ (((Class.cv (nb054_alpha_dummy_057))).fv ∪ ((Class.cv (nb054_alpha_dummy_058))).fv) := by
  simpa only [nb054_alpha_dummy_064] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_057))).fv ∪ ((Class.cv (nb054_alpha_dummy_058))).fv) 0

theorem nb054_fresh_062 : (nb054_alpha_dummy_070) ∉ (((Class.cv (nb054_alpha_dummy_058))).fv ∪ ((Class.cv (nb054_alpha_dummy_058))).fv) := by
  simpa only [nb054_alpha_dummy_070] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_058))).fv ∪ ((Class.cv (nb054_alpha_dummy_058))).fv) 0

theorem nb054_fresh_063 (x : Var) (y : Var) : (nb054_alpha_dummy_069 x y) ∉ (((Class.cv (nb054_alpha_dummy_060 x y))).fv ∪ ((Class.cv (nb054_alpha_dummy_060 x y))).fv) := by
  simpa only [nb054_alpha_dummy_069] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_060 x y))).fv ∪ ((Class.cv (nb054_alpha_dummy_060 x y))).fv) 0

theorem nb054_fresh_064 (x : Var) (y : Var) : (nb054_alpha_dummy_065 x y) ∉ (((Class.cv (nb054_alpha_dummy_060 x y))).fv ∪ ((Class.cv (nb054_alpha_dummy_061 x y))).fv) := by
  simpa only [nb054_alpha_dummy_065] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_060 x y))).fv ∪ ((Class.cv (nb054_alpha_dummy_061 x y))).fv) 0

theorem nb054_fresh_065 (x : Var) (y : Var) : (nb054_alpha_dummy_071 x y) ∉ (((Class.cv (nb054_alpha_dummy_061 x y))).fv ∪ ((Class.cv (nb054_alpha_dummy_061 x y))).fv) := by
  simpa only [nb054_alpha_dummy_071] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_061 x y))).fv ∪ ((Class.cv (nb054_alpha_dummy_061 x y))).fv) 0

theorem nb054_fresh_066 : (nb054_alpha_dummy_088) ∉ (((Class.cv (nb054_alpha_dummy_078))).fv ∪ ((Class.cv (nb054_alpha_dummy_078))).fv) := by
  simpa only [nb054_alpha_dummy_088] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_078))).fv ∪ ((Class.cv (nb054_alpha_dummy_078))).fv) 0

theorem nb054_fresh_067 (x : Var) (y : Var) : (nb054_alpha_dummy_089 x y) ∉ (((Class.cv (nb054_alpha_dummy_079 x y))).fv ∪ ((Class.cv (nb054_alpha_dummy_079 x y))).fv) := by
  simpa only [nb054_alpha_dummy_089] using freshVar_not_mem (((Class.cv (nb054_alpha_dummy_079 x y))).fv ∪ ((Class.cv (nb054_alpha_dummy_079 x y))).fv) 0

theorem nb054_fresh_068 (x : Var) (y : Var) : (nb054_alpha_dummy_016 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb054_alpha_dummy_016] using freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb054_fresh_069 (x : Var) (y : Var) : (nb054_alpha_dummy_017 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb054_alpha_dummy_017] using freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb054_fresh_070 (x : Var) (y : Var) : (nb054_alpha_dummy_079 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb054_alpha_dummy_079] using freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 2

theorem nb054_distinct_071 (x : Var) (y : Var) : (nb054_alpha_dummy_016 x y) ≠ (nb054_alpha_dummy_017 x y) := by
  simpa only [nb054_alpha_dummy_016, nb054_alpha_dummy_017] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))

theorem nb054_distinct_072 (x : Var) (y : Var) : (nb054_alpha_dummy_016 x y) ≠ (nb054_alpha_dummy_079 x y) := by
  simpa only [nb054_alpha_dummy_016, nb054_alpha_dummy_079] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 2) (by decide))

theorem nb054_distinct_073 (x : Var) (y : Var) : (nb054_alpha_dummy_017 x y) ≠ (nb054_alpha_dummy_079 x y) := by
  simpa only [nb054_alpha_dummy_017, nb054_alpha_dummy_079] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 1) (j := 2) (by decide))

theorem nb054_fresh_074 : (nb054_alpha_dummy_026) ∉ (((Wff.classMem (Class.cv (nb054_alpha_dummy_022)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb054_alpha_dummy_022)) (syn_c1c))).fv ∪ ((Class.cv (nb054_alpha_dummy_022))).fv) := by
  simpa only [nb054_alpha_dummy_026] using freshVar_not_mem (((Wff.classMem (Class.cv (nb054_alpha_dummy_022)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb054_alpha_dummy_022)) (syn_c1c))).fv ∪ ((Class.cv (nb054_alpha_dummy_022))).fv) 0

theorem nb054_fresh_075 (x : Var) (y : Var) : (nb054_alpha_dummy_027 x y) ∉ (((Wff.classMem (Class.cv (nb054_alpha_dummy_024 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb054_alpha_dummy_024 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb054_alpha_dummy_024 x y))).fv) := by
  simpa only [nb054_alpha_dummy_027] using freshVar_not_mem (((Wff.classMem (Class.cv (nb054_alpha_dummy_024 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb054_alpha_dummy_024 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb054_alpha_dummy_024 x y))).fv) 0

theorem nb054_fresh_076 : (nb054_alpha_dummy_054) ∉ (((Wff.classMem (Class.cv (nb054_alpha_dummy_050)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb054_alpha_dummy_050)) (syn_c1c))).fv ∪ ((Class.cv (nb054_alpha_dummy_050))).fv) := by
  simpa only [nb054_alpha_dummy_054] using freshVar_not_mem (((Wff.classMem (Class.cv (nb054_alpha_dummy_050)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb054_alpha_dummy_050)) (syn_c1c))).fv ∪ ((Class.cv (nb054_alpha_dummy_050))).fv) 0

theorem nb054_fresh_077 (x : Var) (y : Var) : (nb054_alpha_dummy_055 x y) ∉ (((Wff.classMem (Class.cv (nb054_alpha_dummy_052 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb054_alpha_dummy_052 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb054_alpha_dummy_052 x y))).fv) := by
  simpa only [nb054_alpha_dummy_055] using freshVar_not_mem (((Wff.classMem (Class.cv (nb054_alpha_dummy_052 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb054_alpha_dummy_052 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb054_alpha_dummy_052 x y))).fv) 0

theorem nb054_fresh_078 : (nb054_alpha_dummy_010) ∉ (((syn_ccompl (Class.cab (nb054_alpha_dummy_006) (syn_wrex (nb054_alpha_dummy_007) (syn_cop (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001))) (Wff.classEq (Class.cv (nb054_alpha_dummy_006)) (syn_cphi (Class.cv (nb054_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl (Class.cab (nb054_alpha_dummy_006) (syn_wrex (nb054_alpha_dummy_007) (Class.cv (nb054_alpha_dummy_002)) (Wff.classEq (Class.cv (nb054_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_007))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb054_alpha_dummy_010] using freshVar_not_mem (((syn_ccompl (Class.cab (nb054_alpha_dummy_006) (syn_wrex (nb054_alpha_dummy_007) (syn_cop (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001))) (Wff.classEq (Class.cv (nb054_alpha_dummy_006)) (syn_cphi (Class.cv (nb054_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl (Class.cab (nb054_alpha_dummy_006) (syn_wrex (nb054_alpha_dummy_007) (Class.cv (nb054_alpha_dummy_002)) (Wff.classEq (Class.cv (nb054_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_007))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb054_fresh_079 (x : Var) (y : Var) : (nb054_alpha_dummy_011 x y) ∉ (((syn_ccompl (Class.cab (nb054_alpha_dummy_008 x y) (syn_wrex (nb054_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb054_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb054_alpha_dummy_008 x y) (syn_wrex (nb054_alpha_dummy_009 x y) (Class.cv (nb054_alpha_dummy_003 x y)) (Wff.classEq (Class.cv (nb054_alpha_dummy_008 x y)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb054_alpha_dummy_011] using freshVar_not_mem (((syn_ccompl (Class.cab (nb054_alpha_dummy_008 x y) (syn_wrex (nb054_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb054_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb054_alpha_dummy_008 x y) (syn_wrex (nb054_alpha_dummy_009 x y) (Class.cv (nb054_alpha_dummy_003 x y)) (Wff.classEq (Class.cv (nb054_alpha_dummy_008 x y)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb054_fresh_080 : (nb054_alpha_dummy_018) ∉ (((syn_ccompl (Class.cab (nb054_alpha_dummy_014) (syn_wrex (nb054_alpha_dummy_015) (Class.cv (nb054_alpha_dummy_000)) (Wff.classEq (Class.cv (nb054_alpha_dummy_014)) (syn_cphi (Class.cv (nb054_alpha_dummy_015)))))))).fv ∪ ((syn_ccompl (Class.cab (nb054_alpha_dummy_014) (syn_wrex (nb054_alpha_dummy_015) (Class.cv (nb054_alpha_dummy_001)) (Wff.classEq (Class.cv (nb054_alpha_dummy_014)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_015))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb054_alpha_dummy_018] using freshVar_not_mem (((syn_ccompl (Class.cab (nb054_alpha_dummy_014) (syn_wrex (nb054_alpha_dummy_015) (Class.cv (nb054_alpha_dummy_000)) (Wff.classEq (Class.cv (nb054_alpha_dummy_014)) (syn_cphi (Class.cv (nb054_alpha_dummy_015)))))))).fv ∪ ((syn_ccompl (Class.cab (nb054_alpha_dummy_014) (syn_wrex (nb054_alpha_dummy_015) (Class.cv (nb054_alpha_dummy_001)) (Wff.classEq (Class.cv (nb054_alpha_dummy_014)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_015))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb054_fresh_081 (x : Var) (y : Var) : (nb054_alpha_dummy_019 x y) ∉ (((syn_ccompl (Class.cab (nb054_alpha_dummy_016 x y) (syn_wrex (nb054_alpha_dummy_017 x y) (Class.cv x) (Wff.classEq (Class.cv (nb054_alpha_dummy_016 x y)) (syn_cphi (Class.cv (nb054_alpha_dummy_017 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb054_alpha_dummy_016 x y) (syn_wrex (nb054_alpha_dummy_017 x y) (Class.cv y) (Wff.classEq (Class.cv (nb054_alpha_dummy_016 x y)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_017 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb054_alpha_dummy_019] using freshVar_not_mem (((syn_ccompl (Class.cab (nb054_alpha_dummy_016 x y) (syn_wrex (nb054_alpha_dummy_017 x y) (Class.cv x) (Wff.classEq (Class.cv (nb054_alpha_dummy_016 x y)) (syn_cphi (Class.cv (nb054_alpha_dummy_017 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb054_alpha_dummy_016 x y) (syn_wrex (nb054_alpha_dummy_017 x y) (Class.cv y) (Wff.classEq (Class.cv (nb054_alpha_dummy_016 x y)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_017 x y))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb054_fresh_082 : (nb054_alpha_dummy_084) ∉ (((syn_ccompl (Class.cv (nb054_alpha_dummy_015)))).fv ∪ ((syn_ccompl (Class.cv (nb054_alpha_dummy_078)))).fv) := by
  simpa only [nb054_alpha_dummy_084] using freshVar_not_mem (((syn_ccompl (Class.cv (nb054_alpha_dummy_015)))).fv ∪ ((syn_ccompl (Class.cv (nb054_alpha_dummy_078)))).fv) 0

theorem nb054_fresh_083 (x : Var) (y : Var) : (nb054_alpha_dummy_085 x y) ∉ (((syn_ccompl (Class.cv (nb054_alpha_dummy_017 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb054_alpha_dummy_079 x y)))).fv) := by
  simpa only [nb054_alpha_dummy_085] using freshVar_not_mem (((syn_ccompl (Class.cv (nb054_alpha_dummy_017 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb054_alpha_dummy_079 x y)))).fv) 0

theorem nb054_fresh_084 : (nb054_alpha_dummy_038) ∉ (((syn_ccompl (Class.cv (nb054_alpha_dummy_029)))).fv ∪ ((syn_ccompl (Class.cv (nb054_alpha_dummy_030)))).fv) := by
  simpa only [nb054_alpha_dummy_038] using freshVar_not_mem (((syn_ccompl (Class.cv (nb054_alpha_dummy_029)))).fv ∪ ((syn_ccompl (Class.cv (nb054_alpha_dummy_030)))).fv) 0

theorem nb054_fresh_085 (x : Var) (y : Var) : (nb054_alpha_dummy_039 x y) ∉ (((syn_ccompl (Class.cv (nb054_alpha_dummy_032 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb054_alpha_dummy_033 x y)))).fv) := by
  simpa only [nb054_alpha_dummy_039] using freshVar_not_mem (((syn_ccompl (Class.cv (nb054_alpha_dummy_032 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb054_alpha_dummy_033 x y)))).fv) 0

theorem nb054_fresh_086 : (nb054_alpha_dummy_066) ∉ (((syn_ccompl (Class.cv (nb054_alpha_dummy_057)))).fv ∪ ((syn_ccompl (Class.cv (nb054_alpha_dummy_058)))).fv) := by
  simpa only [nb054_alpha_dummy_066] using freshVar_not_mem (((syn_ccompl (Class.cv (nb054_alpha_dummy_057)))).fv ∪ ((syn_ccompl (Class.cv (nb054_alpha_dummy_058)))).fv) 0

theorem nb054_fresh_087 (x : Var) (y : Var) : (nb054_alpha_dummy_067 x y) ∉ (((syn_ccompl (Class.cv (nb054_alpha_dummy_060 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb054_alpha_dummy_061 x y)))).fv) := by
  simpa only [nb054_alpha_dummy_067] using freshVar_not_mem (((syn_ccompl (Class.cv (nb054_alpha_dummy_060 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb054_alpha_dummy_061 x y)))).fv) 0

theorem nb054_fresh_088 : (nb054_alpha_dummy_074) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb054_alpha_dummy_007))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb054_alpha_dummy_074] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb054_alpha_dummy_007))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb054_fresh_089 (x : Var) (y : Var) : (nb054_alpha_dummy_075 x y) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb054_alpha_dummy_075] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb054_fresh_090 : (nb054_alpha_dummy_046) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb054_alpha_dummy_015))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb054_alpha_dummy_046] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb054_alpha_dummy_015))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb054_fresh_091 (x : Var) (y : Var) : (nb054_alpha_dummy_047 x y) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb054_alpha_dummy_017 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb054_alpha_dummy_047] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb054_alpha_dummy_017 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb054_fresh_092 : (nb054_alpha_dummy_080) ∉ (((syn_cnin (Class.cv (nb054_alpha_dummy_015)) (Class.cv (nb054_alpha_dummy_078)))).fv ∪ ((syn_cnin (Class.cv (nb054_alpha_dummy_015)) (Class.cv (nb054_alpha_dummy_078)))).fv) := by
  simpa only [nb054_alpha_dummy_080] using freshVar_not_mem (((syn_cnin (Class.cv (nb054_alpha_dummy_015)) (Class.cv (nb054_alpha_dummy_078)))).fv ∪ ((syn_cnin (Class.cv (nb054_alpha_dummy_015)) (Class.cv (nb054_alpha_dummy_078)))).fv) 0

theorem nb054_fresh_093 (x : Var) (y : Var) : (nb054_alpha_dummy_081 x y) ∉ (((syn_cnin (Class.cv (nb054_alpha_dummy_017 x y)) (Class.cv (nb054_alpha_dummy_079 x y)))).fv ∪ ((syn_cnin (Class.cv (nb054_alpha_dummy_017 x y)) (Class.cv (nb054_alpha_dummy_079 x y)))).fv) := by
  simpa only [nb054_alpha_dummy_081] using freshVar_not_mem (((syn_cnin (Class.cv (nb054_alpha_dummy_017 x y)) (Class.cv (nb054_alpha_dummy_079 x y)))).fv ∪ ((syn_cnin (Class.cv (nb054_alpha_dummy_017 x y)) (Class.cv (nb054_alpha_dummy_079 x y)))).fv) 0

theorem nb054_fresh_094 : (nb054_alpha_dummy_034) ∉ (((syn_cnin (Class.cv (nb054_alpha_dummy_029)) (Class.cv (nb054_alpha_dummy_030)))).fv ∪ ((syn_cnin (Class.cv (nb054_alpha_dummy_029)) (Class.cv (nb054_alpha_dummy_030)))).fv) := by
  simpa only [nb054_alpha_dummy_034] using freshVar_not_mem (((syn_cnin (Class.cv (nb054_alpha_dummy_029)) (Class.cv (nb054_alpha_dummy_030)))).fv ∪ ((syn_cnin (Class.cv (nb054_alpha_dummy_029)) (Class.cv (nb054_alpha_dummy_030)))).fv) 0

theorem nb054_fresh_095 (x : Var) (y : Var) : (nb054_alpha_dummy_035 x y) ∉ (((syn_cnin (Class.cv (nb054_alpha_dummy_032 x y)) (Class.cv (nb054_alpha_dummy_033 x y)))).fv ∪ ((syn_cnin (Class.cv (nb054_alpha_dummy_032 x y)) (Class.cv (nb054_alpha_dummy_033 x y)))).fv) := by
  simpa only [nb054_alpha_dummy_035] using freshVar_not_mem (((syn_cnin (Class.cv (nb054_alpha_dummy_032 x y)) (Class.cv (nb054_alpha_dummy_033 x y)))).fv ∪ ((syn_cnin (Class.cv (nb054_alpha_dummy_032 x y)) (Class.cv (nb054_alpha_dummy_033 x y)))).fv) 0

theorem nb054_fresh_096 : (nb054_alpha_dummy_062) ∉ (((syn_cnin (Class.cv (nb054_alpha_dummy_057)) (Class.cv (nb054_alpha_dummy_058)))).fv ∪ ((syn_cnin (Class.cv (nb054_alpha_dummy_057)) (Class.cv (nb054_alpha_dummy_058)))).fv) := by
  simpa only [nb054_alpha_dummy_062] using freshVar_not_mem (((syn_cnin (Class.cv (nb054_alpha_dummy_057)) (Class.cv (nb054_alpha_dummy_058)))).fv ∪ ((syn_cnin (Class.cv (nb054_alpha_dummy_057)) (Class.cv (nb054_alpha_dummy_058)))).fv) 0

theorem nb054_fresh_097 (x : Var) (y : Var) : (nb054_alpha_dummy_063 x y) ∉ (((syn_cnin (Class.cv (nb054_alpha_dummy_060 x y)) (Class.cv (nb054_alpha_dummy_061 x y)))).fv ∪ ((syn_cnin (Class.cv (nb054_alpha_dummy_060 x y)) (Class.cv (nb054_alpha_dummy_061 x y)))).fv) := by
  simpa only [nb054_alpha_dummy_063] using freshVar_not_mem (((syn_cnin (Class.cv (nb054_alpha_dummy_060 x y)) (Class.cv (nb054_alpha_dummy_061 x y)))).fv ∪ ((syn_cnin (Class.cv (nb054_alpha_dummy_060 x y)) (Class.cv (nb054_alpha_dummy_061 x y)))).fv) 0

theorem nb054_fresh_098 : (nb054_alpha_dummy_006) ∉ (((syn_cop (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001)))).fv ∪ ((Class.cv (nb054_alpha_dummy_002))).fv) := by
  simpa only [nb054_alpha_dummy_006] using freshVar_not_mem (((syn_cop (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001)))).fv ∪ ((Class.cv (nb054_alpha_dummy_002))).fv) 0

theorem nb054_fresh_099 : (nb054_alpha_dummy_007) ∉ (((syn_cop (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001)))).fv ∪ ((Class.cv (nb054_alpha_dummy_002))).fv) := by
  simpa only [nb054_alpha_dummy_007] using freshVar_not_mem (((syn_cop (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001)))).fv ∪ ((Class.cv (nb054_alpha_dummy_002))).fv) 1

theorem nb054_distinct_100 : (nb054_alpha_dummy_006) ≠ (nb054_alpha_dummy_007) := by
  simpa only [nb054_alpha_dummy_006, nb054_alpha_dummy_007] using
    (freshVar_injective (((syn_cop (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001)))).fv ∪ ((Class.cv (nb054_alpha_dummy_002))).fv) (i := 0) (j := 1) (by decide))

theorem nb054_fresh_101 (x : Var) (y : Var) : (nb054_alpha_dummy_008 x y) ∉ (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb054_alpha_dummy_003 x y))).fv) := by
  simpa only [nb054_alpha_dummy_008] using freshVar_not_mem (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb054_alpha_dummy_003 x y))).fv) 0

theorem nb054_fresh_102 (x : Var) (y : Var) : (nb054_alpha_dummy_009 x y) ∉ (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb054_alpha_dummy_003 x y))).fv) := by
  simpa only [nb054_alpha_dummy_009] using freshVar_not_mem (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb054_alpha_dummy_003 x y))).fv) 1

theorem nb054_distinct_103 (x : Var) (y : Var) : (nb054_alpha_dummy_008 x y) ≠ (nb054_alpha_dummy_009 x y) := by
  simpa only [nb054_alpha_dummy_008, nb054_alpha_dummy_009] using
    (freshVar_injective (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb054_alpha_dummy_003 x y))).fv) (i := 0) (j := 1) (by decide))

theorem nb054_fresh_104 : (nb054_alpha_dummy_076) ∉ (((syn_cphi (Class.cv (nb054_alpha_dummy_007)))).fv ∪ ((syn_cphi (Class.cv (nb054_alpha_dummy_007)))).fv) := by
  simpa only [nb054_alpha_dummy_076] using freshVar_not_mem (((syn_cphi (Class.cv (nb054_alpha_dummy_007)))).fv ∪ ((syn_cphi (Class.cv (nb054_alpha_dummy_007)))).fv) 0

theorem nb054_fresh_105 (x : Var) (y : Var) : (nb054_alpha_dummy_077 x y) ∉ (((syn_cphi (Class.cv (nb054_alpha_dummy_009 x y)))).fv ∪ ((syn_cphi (Class.cv (nb054_alpha_dummy_009 x y)))).fv) := by
  simpa only [nb054_alpha_dummy_077] using freshVar_not_mem (((syn_cphi (Class.cv (nb054_alpha_dummy_009 x y)))).fv ∪ ((syn_cphi (Class.cv (nb054_alpha_dummy_009 x y)))).fv) 0

theorem nb054_fresh_106 : (nb054_alpha_dummy_048) ∉ (((syn_cphi (Class.cv (nb054_alpha_dummy_015)))).fv ∪ ((syn_cphi (Class.cv (nb054_alpha_dummy_015)))).fv) := by
  simpa only [nb054_alpha_dummy_048] using freshVar_not_mem (((syn_cphi (Class.cv (nb054_alpha_dummy_015)))).fv ∪ ((syn_cphi (Class.cv (nb054_alpha_dummy_015)))).fv) 0

theorem nb054_fresh_107 (x : Var) (y : Var) : (nb054_alpha_dummy_049 x y) ∉ (((syn_cphi (Class.cv (nb054_alpha_dummy_017 x y)))).fv ∪ ((syn_cphi (Class.cv (nb054_alpha_dummy_017 x y)))).fv) := by
  simpa only [nb054_alpha_dummy_049] using freshVar_not_mem (((syn_cphi (Class.cv (nb054_alpha_dummy_017 x y)))).fv ∪ ((syn_cphi (Class.cv (nb054_alpha_dummy_017 x y)))).fv) 0

theorem nb054_fresh_108 : (nb054_alpha_dummy_002) ∉ (({(nb054_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ({(nb054_alpha_dummy_001)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_cplc (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001)))).fv) := by
  simpa only [nb054_alpha_dummy_002] using freshVar_not_mem (({(nb054_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ({(nb054_alpha_dummy_001)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_cplc (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001)))).fv) 0

theorem nb054_fresh_109 : (nb054_alpha_dummy_004) ∉ (({(nb054_alpha_dummy_000)} : Finset Var) ∪ ({(nb054_alpha_dummy_001)} : Finset Var) ∪ ({(nb054_alpha_dummy_002)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv (nb054_alpha_dummy_000)) (syn_cvv)) (Wff.classMem (Class.cv (nb054_alpha_dummy_001)) (syn_cvv))) (Wff.classEq (Class.cv (nb054_alpha_dummy_002)) (syn_cplc (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001)))))).fv) := by
  simpa only [nb054_alpha_dummy_004] using freshVar_not_mem (({(nb054_alpha_dummy_000)} : Finset Var) ∪ ({(nb054_alpha_dummy_001)} : Finset Var) ∪ ({(nb054_alpha_dummy_002)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv (nb054_alpha_dummy_000)) (syn_cvv)) (Wff.classMem (Class.cv (nb054_alpha_dummy_001)) (syn_cvv))) (Wff.classEq (Class.cv (nb054_alpha_dummy_002)) (syn_cplc (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001)))))).fv) 0

theorem nb054_fresh_110 (x : Var) (y : Var) : (nb054_alpha_dummy_003 x y) ∉ (({x} : Finset Var) ∪ ((syn_cvv)).fv ∪ ({y} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_cplc (Class.cv x) (Class.cv y))).fv) := by
  simpa only [nb054_alpha_dummy_003] using freshVar_not_mem (({x} : Finset Var) ∪ ((syn_cvv)).fv ∪ ({y} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_cplc (Class.cv x) (Class.cv y))).fv) 0

theorem nb054_fresh_111 (x : Var) (y : Var) : (nb054_alpha_dummy_005 x y) ∉ (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({(nb054_alpha_dummy_003 x y)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv))) (Wff.classEq (Class.cv (nb054_alpha_dummy_003 x y)) (syn_cplc (Class.cv x) (Class.cv y))))).fv) := by
  simpa only [nb054_alpha_dummy_005] using freshVar_not_mem (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({(nb054_alpha_dummy_003 x y)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv))) (Wff.classEq (Class.cv (nb054_alpha_dummy_003 x y)) (syn_cplc (Class.cv x) (Class.cv y))))).fv) 0

theorem nb054_fresh_112 : (nb054_alpha_dummy_000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb054_alpha_dummy_000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb054_fresh_113 : (nb054_alpha_dummy_001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb054_alpha_dummy_001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb054_distinct_114 : (nb054_alpha_dummy_000) ≠ (nb054_alpha_dummy_001) := by
  simpa only [nb054_alpha_dummy_000, nb054_alpha_dummy_001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb054_support_mem_0000 : (nb054_alpha_dummy_000) ∈ (({(nb054_alpha_dummy_000)} : Finset Var) ∪ ({(nb054_alpha_dummy_001)} : Finset Var) ∪ ({(nb054_alpha_dummy_002)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv (nb054_alpha_dummy_000)) (syn_cvv)) (Wff.classMem (Class.cv (nb054_alpha_dummy_001)) (syn_cvv))) (Wff.classEq (Class.cv (nb054_alpha_dummy_002)) (syn_cplc (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0001 (x : Var) (y : Var) : x ∈ (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({(nb054_alpha_dummy_003 x y)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv))) (Wff.classEq (Class.cv (nb054_alpha_dummy_003 x y)) (syn_cplc (Class.cv x) (Class.cv y))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0002 : (nb054_alpha_dummy_001) ∈ (({(nb054_alpha_dummy_000)} : Finset Var) ∪ ({(nb054_alpha_dummy_001)} : Finset Var) ∪ ({(nb054_alpha_dummy_002)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv (nb054_alpha_dummy_000)) (syn_cvv)) (Wff.classMem (Class.cv (nb054_alpha_dummy_001)) (syn_cvv))) (Wff.classEq (Class.cv (nb054_alpha_dummy_002)) (syn_cplc (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0003 (x : Var) (y : Var) : y ∈ (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({(nb054_alpha_dummy_003 x y)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv))) (Wff.classEq (Class.cv (nb054_alpha_dummy_003 x y)) (syn_cplc (Class.cv x) (Class.cv y))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0004 : (nb054_alpha_dummy_002) ∈ (({(nb054_alpha_dummy_000)} : Finset Var) ∪ ({(nb054_alpha_dummy_001)} : Finset Var) ∪ ({(nb054_alpha_dummy_002)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv (nb054_alpha_dummy_000)) (syn_cvv)) (Wff.classMem (Class.cv (nb054_alpha_dummy_001)) (syn_cvv))) (Wff.classEq (Class.cv (nb054_alpha_dummy_002)) (syn_cplc (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0005 (x : Var) (y : Var) : (nb054_alpha_dummy_003 x y) ∈ (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({(nb054_alpha_dummy_003 x y)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv x) (syn_cvv)) (Wff.classMem (Class.cv y) (syn_cvv))) (Wff.classEq (Class.cv (nb054_alpha_dummy_003 x y)) (syn_cplc (Class.cv x) (Class.cv y))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0006 : (nb054_alpha_dummy_000) ∈ (({(nb054_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ({(nb054_alpha_dummy_001)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_cplc (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0007 (x : Var) (y : Var) : x ∈ (({x} : Finset Var) ∪ ((syn_cvv)).fv ∪ ({y} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_cplc (Class.cv x) (Class.cv y))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0008 : (nb054_alpha_dummy_000) ∈ (((syn_cop (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001)))).fv ∪ ((Class.cv (nb054_alpha_dummy_002))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cop]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0009 : (nb054_alpha_dummy_000) ∈ (((syn_ccompl (Class.cab (nb054_alpha_dummy_006) (syn_wrex (nb054_alpha_dummy_007) (syn_cop (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001))) (Wff.classEq (Class.cv (nb054_alpha_dummy_006)) (syn_cphi (Class.cv (nb054_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl (Class.cab (nb054_alpha_dummy_006) (syn_wrex (nb054_alpha_dummy_007) (Class.cv (nb054_alpha_dummy_002)) (Wff.classEq (Class.cv (nb054_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_007))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0008) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0008) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0010 (x : Var) (y : Var) : x ∈ (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb054_alpha_dummy_003 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cop]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0011 (x : Var) (y : Var) : x ∈ (((syn_ccompl (Class.cab (nb054_alpha_dummy_008 x y) (syn_wrex (nb054_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb054_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb054_alpha_dummy_008 x y) (syn_wrex (nb054_alpha_dummy_009 x y) (Class.cv (nb054_alpha_dummy_003 x y)) (Wff.classEq (Class.cv (nb054_alpha_dummy_008 x y)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0010 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0010 x y) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0012 : (nb054_alpha_dummy_000) ∈ (((Class.cab (nb054_alpha_dummy_006) (syn_wrex (nb054_alpha_dummy_007) (syn_cop (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001))) (Wff.classEq (Class.cv (nb054_alpha_dummy_006)) (syn_cphi (Class.cv (nb054_alpha_dummy_007))))))).fv ∪ ((Class.cab (nb054_alpha_dummy_006) (syn_wrex (nb054_alpha_dummy_007) (syn_cop (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001))) (Wff.classEq (Class.cv (nb054_alpha_dummy_006)) (syn_cphi (Class.cv (nb054_alpha_dummy_007))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0008) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0008) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0013 (x : Var) (y : Var) : x ∈ (((Class.cab (nb054_alpha_dummy_008 x y) (syn_wrex (nb054_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb054_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y))))))).fv ∪ ((Class.cab (nb054_alpha_dummy_008 x y) (syn_wrex (nb054_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb054_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0010 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0010 x y) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0014 : (nb054_alpha_dummy_000) ∈ (((Class.cv (nb054_alpha_dummy_000))).fv ∪ ((Class.cv (nb054_alpha_dummy_001))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0015 : (nb054_alpha_dummy_000) ∈ (((syn_ccompl (Class.cab (nb054_alpha_dummy_014) (syn_wrex (nb054_alpha_dummy_015) (Class.cv (nb054_alpha_dummy_000)) (Wff.classEq (Class.cv (nb054_alpha_dummy_014)) (syn_cphi (Class.cv (nb054_alpha_dummy_015)))))))).fv ∪ ((syn_ccompl (Class.cab (nb054_alpha_dummy_014) (syn_wrex (nb054_alpha_dummy_015) (Class.cv (nb054_alpha_dummy_001)) (Wff.classEq (Class.cv (nb054_alpha_dummy_014)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_015))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0014) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0014) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0016 (x : Var) (y : Var) : x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0017 (x : Var) (y : Var) : x ∈ (((syn_ccompl (Class.cab (nb054_alpha_dummy_016 x y) (syn_wrex (nb054_alpha_dummy_017 x y) (Class.cv x) (Wff.classEq (Class.cv (nb054_alpha_dummy_016 x y)) (syn_cphi (Class.cv (nb054_alpha_dummy_017 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb054_alpha_dummy_016 x y) (syn_wrex (nb054_alpha_dummy_017 x y) (Class.cv y) (Wff.classEq (Class.cv (nb054_alpha_dummy_016 x y)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_017 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0016 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0016 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0018 : (nb054_alpha_dummy_000) ∈ (((Class.cab (nb054_alpha_dummy_014) (syn_wrex (nb054_alpha_dummy_015) (Class.cv (nb054_alpha_dummy_000)) (Wff.classEq (Class.cv (nb054_alpha_dummy_014)) (syn_cphi (Class.cv (nb054_alpha_dummy_015))))))).fv ∪ ((Class.cab (nb054_alpha_dummy_014) (syn_wrex (nb054_alpha_dummy_015) (Class.cv (nb054_alpha_dummy_000)) (Wff.classEq (Class.cv (nb054_alpha_dummy_014)) (syn_cphi (Class.cv (nb054_alpha_dummy_015))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0014) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0014) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0019 (x : Var) (y : Var) : x ∈ (((Class.cab (nb054_alpha_dummy_016 x y) (syn_wrex (nb054_alpha_dummy_017 x y) (Class.cv x) (Wff.classEq (Class.cv (nb054_alpha_dummy_016 x y)) (syn_cphi (Class.cv (nb054_alpha_dummy_017 x y))))))).fv ∪ ((Class.cab (nb054_alpha_dummy_016 x y) (syn_wrex (nb054_alpha_dummy_017 x y) (Class.cv x) (Wff.classEq (Class.cv (nb054_alpha_dummy_016 x y)) (syn_cphi (Class.cv (nb054_alpha_dummy_017 x y))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0016 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0016 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0020 : (nb054_alpha_dummy_015) ∈ (((Class.cv (nb054_alpha_dummy_015))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0021 (x : Var) (y : Var) : (nb054_alpha_dummy_017 x y) ∈ (((Class.cv (nb054_alpha_dummy_017 x y))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0022 : (nb054_alpha_dummy_022) ∈ (((Wff.classMem (Class.cv (nb054_alpha_dummy_022)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb054_alpha_dummy_022)) (syn_c1c))).fv ∪ ((Class.cv (nb054_alpha_dummy_022))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0023 (x : Var) (y : Var) : (nb054_alpha_dummy_024 x y) ∈ (((Wff.classMem (Class.cv (nb054_alpha_dummy_024 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb054_alpha_dummy_024 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb054_alpha_dummy_024 x y))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0024 : (nb054_alpha_dummy_022) ∈ (((Class.cv (nb054_alpha_dummy_022))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0025 (x : Var) (y : Var) : (nb054_alpha_dummy_024 x y) ∈ (((Class.cv (nb054_alpha_dummy_024 x y))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0026 : (nb054_alpha_dummy_029) ∈ (((syn_cnin (Class.cv (nb054_alpha_dummy_029)) (Class.cv (nb054_alpha_dummy_030)))).fv ∪ ((syn_cnin (Class.cv (nb054_alpha_dummy_029)) (Class.cv (nb054_alpha_dummy_030)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0027 (x : Var) (y : Var) : (nb054_alpha_dummy_032 x y) ∈ (((syn_cnin (Class.cv (nb054_alpha_dummy_032 x y)) (Class.cv (nb054_alpha_dummy_033 x y)))).fv ∪ ((syn_cnin (Class.cv (nb054_alpha_dummy_032 x y)) (Class.cv (nb054_alpha_dummy_033 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0028 : (nb054_alpha_dummy_029) ∈ (((Class.cv (nb054_alpha_dummy_029))).fv ∪ ((Class.cv (nb054_alpha_dummy_030))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0029 (x : Var) (y : Var) : (nb054_alpha_dummy_032 x y) ∈ (((Class.cv (nb054_alpha_dummy_032 x y))).fv ∪ ((Class.cv (nb054_alpha_dummy_033 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0030 : (nb054_alpha_dummy_030) ∈ (((syn_cnin (Class.cv (nb054_alpha_dummy_029)) (Class.cv (nb054_alpha_dummy_030)))).fv ∪ ((syn_cnin (Class.cv (nb054_alpha_dummy_029)) (Class.cv (nb054_alpha_dummy_030)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0031 (x : Var) (y : Var) : (nb054_alpha_dummy_033 x y) ∈ (((syn_cnin (Class.cv (nb054_alpha_dummy_032 x y)) (Class.cv (nb054_alpha_dummy_033 x y)))).fv ∪ ((syn_cnin (Class.cv (nb054_alpha_dummy_032 x y)) (Class.cv (nb054_alpha_dummy_033 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0032 : (nb054_alpha_dummy_030) ∈ (((Class.cv (nb054_alpha_dummy_029))).fv ∪ ((Class.cv (nb054_alpha_dummy_030))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0033 (x : Var) (y : Var) : (nb054_alpha_dummy_033 x y) ∈ (((Class.cv (nb054_alpha_dummy_032 x y))).fv ∪ ((Class.cv (nb054_alpha_dummy_033 x y))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0034 : (nb054_alpha_dummy_029) ∈ (((syn_ccompl (Class.cv (nb054_alpha_dummy_029)))).fv ∪ ((syn_ccompl (Class.cv (nb054_alpha_dummy_030)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0035 (x : Var) (y : Var) : (nb054_alpha_dummy_032 x y) ∈ (((syn_ccompl (Class.cv (nb054_alpha_dummy_032 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb054_alpha_dummy_033 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0036 : (nb054_alpha_dummy_029) ∈ (((Class.cv (nb054_alpha_dummy_029))).fv ∪ ((Class.cv (nb054_alpha_dummy_029))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0037 (x : Var) (y : Var) : (nb054_alpha_dummy_032 x y) ∈ (((Class.cv (nb054_alpha_dummy_032 x y))).fv ∪ ((Class.cv (nb054_alpha_dummy_032 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0038 : (nb054_alpha_dummy_030) ∈ (((syn_ccompl (Class.cv (nb054_alpha_dummy_029)))).fv ∪ ((syn_ccompl (Class.cv (nb054_alpha_dummy_030)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0039 (x : Var) (y : Var) : (nb054_alpha_dummy_033 x y) ∈ (((syn_ccompl (Class.cv (nb054_alpha_dummy_032 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb054_alpha_dummy_033 x y)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0040 : (nb054_alpha_dummy_030) ∈ (((Class.cv (nb054_alpha_dummy_030))).fv ∪ ((Class.cv (nb054_alpha_dummy_030))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0041 (x : Var) (y : Var) : (nb054_alpha_dummy_033 x y) ∈ (((Class.cv (nb054_alpha_dummy_033 x y))).fv ∪ ((Class.cv (nb054_alpha_dummy_033 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0042 : (nb054_alpha_dummy_001) ∈ (({(nb054_alpha_dummy_000)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ({(nb054_alpha_dummy_001)} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_cplc (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0043 (x : Var) (y : Var) : y ∈ (({x} : Finset Var) ∪ ((syn_cvv)).fv ∪ ({y} : Finset Var) ∪ ((syn_cvv)).fv ∪ ((syn_cplc (Class.cv x) (Class.cv y))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0044 : (nb054_alpha_dummy_001) ∈ (((syn_cop (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001)))).fv ∪ ((Class.cv (nb054_alpha_dummy_002))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cop]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0045 : (nb054_alpha_dummy_001) ∈ (((syn_ccompl (Class.cab (nb054_alpha_dummy_006) (syn_wrex (nb054_alpha_dummy_007) (syn_cop (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001))) (Wff.classEq (Class.cv (nb054_alpha_dummy_006)) (syn_cphi (Class.cv (nb054_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl (Class.cab (nb054_alpha_dummy_006) (syn_wrex (nb054_alpha_dummy_007) (Class.cv (nb054_alpha_dummy_002)) (Wff.classEq (Class.cv (nb054_alpha_dummy_006)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_007))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0044) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0044) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0046 (x : Var) (y : Var) : y ∈ (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb054_alpha_dummy_003 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cop]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0047 (x : Var) (y : Var) : y ∈ (((syn_ccompl (Class.cab (nb054_alpha_dummy_008 x y) (syn_wrex (nb054_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb054_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb054_alpha_dummy_008 x y) (syn_wrex (nb054_alpha_dummy_009 x y) (Class.cv (nb054_alpha_dummy_003 x y)) (Wff.classEq (Class.cv (nb054_alpha_dummy_008 x y)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0046 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0046 x y) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0048 : (nb054_alpha_dummy_001) ∈ (((Class.cab (nb054_alpha_dummy_006) (syn_wrex (nb054_alpha_dummy_007) (syn_cop (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001))) (Wff.classEq (Class.cv (nb054_alpha_dummy_006)) (syn_cphi (Class.cv (nb054_alpha_dummy_007))))))).fv ∪ ((Class.cab (nb054_alpha_dummy_006) (syn_wrex (nb054_alpha_dummy_007) (syn_cop (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001))) (Wff.classEq (Class.cv (nb054_alpha_dummy_006)) (syn_cphi (Class.cv (nb054_alpha_dummy_007))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0044) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0044) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0049 (x : Var) (y : Var) : y ∈ (((Class.cab (nb054_alpha_dummy_008 x y) (syn_wrex (nb054_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb054_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y))))))).fv ∪ ((Class.cab (nb054_alpha_dummy_008 x y) (syn_wrex (nb054_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb054_alpha_dummy_008 x y)) (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0046 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0046 x y) 1))
    ·
      rw [fv_syn_cop]
      apply Finset.mem_union_right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0050 : (nb054_alpha_dummy_001) ∈ (((Class.cv (nb054_alpha_dummy_000))).fv ∪ ((Class.cv (nb054_alpha_dummy_001))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0051 : (nb054_alpha_dummy_001) ∈ (((syn_ccompl (Class.cab (nb054_alpha_dummy_014) (syn_wrex (nb054_alpha_dummy_015) (Class.cv (nb054_alpha_dummy_000)) (Wff.classEq (Class.cv (nb054_alpha_dummy_014)) (syn_cphi (Class.cv (nb054_alpha_dummy_015)))))))).fv ∪ ((syn_ccompl (Class.cab (nb054_alpha_dummy_014) (syn_wrex (nb054_alpha_dummy_015) (Class.cv (nb054_alpha_dummy_001)) (Wff.classEq (Class.cv (nb054_alpha_dummy_014)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_015))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0050) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0050) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0052 (x : Var) (y : Var) : y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0053 (x : Var) (y : Var) : y ∈ (((syn_ccompl (Class.cab (nb054_alpha_dummy_016 x y) (syn_wrex (nb054_alpha_dummy_017 x y) (Class.cv x) (Wff.classEq (Class.cv (nb054_alpha_dummy_016 x y)) (syn_cphi (Class.cv (nb054_alpha_dummy_017 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb054_alpha_dummy_016 x y) (syn_wrex (nb054_alpha_dummy_017 x y) (Class.cv y) (Wff.classEq (Class.cv (nb054_alpha_dummy_016 x y)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_017 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0052 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0052 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0054 : (nb054_alpha_dummy_001) ∈ (((Class.cab (nb054_alpha_dummy_014) (syn_wrex (nb054_alpha_dummy_015) (Class.cv (nb054_alpha_dummy_001)) (Wff.classEq (Class.cv (nb054_alpha_dummy_014)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_015))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb054_alpha_dummy_014) (syn_wrex (nb054_alpha_dummy_015) (Class.cv (nb054_alpha_dummy_001)) (Wff.classEq (Class.cv (nb054_alpha_dummy_014)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_015))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0050) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0050) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0055 (x : Var) (y : Var) : y ∈ (((Class.cab (nb054_alpha_dummy_016 x y) (syn_wrex (nb054_alpha_dummy_017 x y) (Class.cv y) (Wff.classEq (Class.cv (nb054_alpha_dummy_016 x y)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_017 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb054_alpha_dummy_016 x y) (syn_wrex (nb054_alpha_dummy_017 x y) (Class.cv y) (Wff.classEq (Class.cv (nb054_alpha_dummy_016 x y)) (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_017 x y))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0052 x y) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0052 x y) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0056 : (nb054_alpha_dummy_015) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb054_alpha_dummy_015))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0057 (x : Var) (y : Var) : (nb054_alpha_dummy_017 x y) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb054_alpha_dummy_017 x y))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0058 : (nb054_alpha_dummy_015) ∈ (((syn_cphi (Class.cv (nb054_alpha_dummy_015)))).fv ∪ ((syn_cphi (Class.cv (nb054_alpha_dummy_015)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0059 (x : Var) (y : Var) : (nb054_alpha_dummy_017 x y) ∈ (((syn_cphi (Class.cv (nb054_alpha_dummy_017 x y)))).fv ∪ ((syn_cphi (Class.cv (nb054_alpha_dummy_017 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0060 : (nb054_alpha_dummy_007) ∈ (((Class.cv (nb054_alpha_dummy_007))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0061 (x : Var) (y : Var) : (nb054_alpha_dummy_009 x y) ∈ (((Class.cv (nb054_alpha_dummy_009 x y))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0062 : (nb054_alpha_dummy_050) ∈ (((Wff.classMem (Class.cv (nb054_alpha_dummy_050)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb054_alpha_dummy_050)) (syn_c1c))).fv ∪ ((Class.cv (nb054_alpha_dummy_050))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0063 (x : Var) (y : Var) : (nb054_alpha_dummy_052 x y) ∈ (((Wff.classMem (Class.cv (nb054_alpha_dummy_052 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb054_alpha_dummy_052 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb054_alpha_dummy_052 x y))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0064 : (nb054_alpha_dummy_050) ∈ (((Class.cv (nb054_alpha_dummy_050))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0065 (x : Var) (y : Var) : (nb054_alpha_dummy_052 x y) ∈ (((Class.cv (nb054_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0066 : (nb054_alpha_dummy_057) ∈ (((syn_cnin (Class.cv (nb054_alpha_dummy_057)) (Class.cv (nb054_alpha_dummy_058)))).fv ∪ ((syn_cnin (Class.cv (nb054_alpha_dummy_057)) (Class.cv (nb054_alpha_dummy_058)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0067 (x : Var) (y : Var) : (nb054_alpha_dummy_060 x y) ∈ (((syn_cnin (Class.cv (nb054_alpha_dummy_060 x y)) (Class.cv (nb054_alpha_dummy_061 x y)))).fv ∪ ((syn_cnin (Class.cv (nb054_alpha_dummy_060 x y)) (Class.cv (nb054_alpha_dummy_061 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0068 : (nb054_alpha_dummy_057) ∈ (((Class.cv (nb054_alpha_dummy_057))).fv ∪ ((Class.cv (nb054_alpha_dummy_058))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0069 (x : Var) (y : Var) : (nb054_alpha_dummy_060 x y) ∈ (((Class.cv (nb054_alpha_dummy_060 x y))).fv ∪ ((Class.cv (nb054_alpha_dummy_061 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0070 : (nb054_alpha_dummy_058) ∈ (((syn_cnin (Class.cv (nb054_alpha_dummy_057)) (Class.cv (nb054_alpha_dummy_058)))).fv ∪ ((syn_cnin (Class.cv (nb054_alpha_dummy_057)) (Class.cv (nb054_alpha_dummy_058)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0071 (x : Var) (y : Var) : (nb054_alpha_dummy_061 x y) ∈ (((syn_cnin (Class.cv (nb054_alpha_dummy_060 x y)) (Class.cv (nb054_alpha_dummy_061 x y)))).fv ∪ ((syn_cnin (Class.cv (nb054_alpha_dummy_060 x y)) (Class.cv (nb054_alpha_dummy_061 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0072 : (nb054_alpha_dummy_058) ∈ (((Class.cv (nb054_alpha_dummy_057))).fv ∪ ((Class.cv (nb054_alpha_dummy_058))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0073 (x : Var) (y : Var) : (nb054_alpha_dummy_061 x y) ∈ (((Class.cv (nb054_alpha_dummy_060 x y))).fv ∪ ((Class.cv (nb054_alpha_dummy_061 x y))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0074 : (nb054_alpha_dummy_057) ∈ (((syn_ccompl (Class.cv (nb054_alpha_dummy_057)))).fv ∪ ((syn_ccompl (Class.cv (nb054_alpha_dummy_058)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0075 (x : Var) (y : Var) : (nb054_alpha_dummy_060 x y) ∈ (((syn_ccompl (Class.cv (nb054_alpha_dummy_060 x y)))).fv ∪ ((syn_ccompl (Class.cv (nb054_alpha_dummy_061 x y)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0076 : (nb054_alpha_dummy_057) ∈ (((Class.cv (nb054_alpha_dummy_057))).fv ∪ ((Class.cv (nb054_alpha_dummy_057))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0077 (x : Var) (y : Var) : (nb054_alpha_dummy_060 x y) ∈ (((Class.cv (nb054_alpha_dummy_060 x y))).fv ∪ ((Class.cv (nb054_alpha_dummy_060 x y))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0078 : (nb054_alpha_dummy_058) ∈ (((syn_ccompl (Class.cv (nb054_alpha_dummy_057)))).fv ∪ ((syn_ccompl (Class.cv (nb054_alpha_dummy_058)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
