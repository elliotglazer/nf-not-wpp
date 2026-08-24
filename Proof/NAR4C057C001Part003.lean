import NAR4C057C001Part002

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

theorem nb057_fresh_022 (f : Var) : (nb057_alpha_dummy_233 f) ∉ (((Class.cab (nb057_alpha_dummy_204 f) (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_204 f) (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb057_alpha_dummy_233] using freshVar_not_mem (((Class.cab (nb057_alpha_dummy_204 f) (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_204 f) (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_048 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb057_fresh_023 (f : Var) : (nb057_alpha_dummy_209 f) ∉ (((Class.cab (nb057_alpha_dummy_204 f) (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_204 f) (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))))))).fv) := by
  simpa only [nb057_alpha_dummy_209] using freshVar_not_mem (((Class.cab (nb057_alpha_dummy_204 f) (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_204 f) (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_049 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))))))).fv) 0

theorem nb057_fresh_024 : (nb057_alpha_dummy_272) ∉ (((Class.cab (nb057_alpha_dummy_242) (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_238)) (Wff.classEq (Class.cv (nb057_alpha_dummy_242)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_243))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_242) (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_238)) (Wff.classEq (Class.cv (nb057_alpha_dummy_242)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_243))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb057_alpha_dummy_272] using freshVar_not_mem (((Class.cab (nb057_alpha_dummy_242) (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_238)) (Wff.classEq (Class.cv (nb057_alpha_dummy_242)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_243))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_242) (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_238)) (Wff.classEq (Class.cv (nb057_alpha_dummy_242)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_243))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb057_fresh_025 : (nb057_alpha_dummy_248) ∉ (((Class.cab (nb057_alpha_dummy_242) (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_239)) (Wff.classEq (Class.cv (nb057_alpha_dummy_242)) (syn_cphi (Class.cv (nb057_alpha_dummy_243))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_242) (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_239)) (Wff.classEq (Class.cv (nb057_alpha_dummy_242)) (syn_cphi (Class.cv (nb057_alpha_dummy_243))))))).fv) := by
  simpa only [nb057_alpha_dummy_248] using freshVar_not_mem (((Class.cab (nb057_alpha_dummy_242) (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_239)) (Wff.classEq (Class.cv (nb057_alpha_dummy_242)) (syn_cphi (Class.cv (nb057_alpha_dummy_243))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_242) (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_239)) (Wff.classEq (Class.cv (nb057_alpha_dummy_242)) (syn_cphi (Class.cv (nb057_alpha_dummy_243))))))).fv) 0

theorem nb057_fresh_026 (f : Var) : (nb057_alpha_dummy_273 f) ∉ (((Class.cab (nb057_alpha_dummy_244 f) (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_240 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_244 f) (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_240 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb057_alpha_dummy_273] using freshVar_not_mem (((Class.cab (nb057_alpha_dummy_244 f) (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_240 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_244 f) (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_240 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f)) (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb057_fresh_027 (f : Var) : (nb057_alpha_dummy_249 f) ∉ (((Class.cab (nb057_alpha_dummy_244 f) (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_241 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_244 f) (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_241 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))))))).fv) := by
  simpa only [nb057_alpha_dummy_249] using freshVar_not_mem (((Class.cab (nb057_alpha_dummy_244 f) (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_241 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_244 f) (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_241 f)) (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f)) (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))))))).fv) 0

theorem nb057_fresh_028 : (nb057_alpha_dummy_124) ∉ (((Class.cv (nb057_alpha_dummy_001))).fv) := by
  simpa only [nb057_alpha_dummy_124] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_001))).fv) 0

theorem nb057_fresh_029 : (nb057_alpha_dummy_125) ∉ (((Class.cv (nb057_alpha_dummy_001))).fv) := by
  simpa only [nb057_alpha_dummy_125] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_001))).fv) 1

theorem nb057_distinct_030 : (nb057_alpha_dummy_124) ≠ (nb057_alpha_dummy_125) := by
  simpa only [nb057_alpha_dummy_124, nb057_alpha_dummy_125] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_001))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_031 : (nb057_alpha_dummy_004) ∉ (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((Class.cv (nb057_alpha_dummy_000))).fv) := by
  simpa only [nb057_alpha_dummy_004] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((Class.cv (nb057_alpha_dummy_000))).fv) 0

theorem nb057_fresh_032 : (nb057_alpha_dummy_005) ∉ (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((Class.cv (nb057_alpha_dummy_000))).fv) := by
  simpa only [nb057_alpha_dummy_005] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((Class.cv (nb057_alpha_dummy_000))).fv) 1

theorem nb057_distinct_033 : (nb057_alpha_dummy_004) ≠ (nb057_alpha_dummy_005) := by
  simpa only [nb057_alpha_dummy_004, nb057_alpha_dummy_005] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((Class.cv (nb057_alpha_dummy_000))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_034 : (nb057_alpha_dummy_044) ∉ (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv) := by
  simpa only [nb057_alpha_dummy_044] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv) 0

theorem nb057_fresh_035 : (nb057_alpha_dummy_045) ∉ (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv) := by
  simpa only [nb057_alpha_dummy_045] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv) 1

theorem nb057_fresh_036 : (nb057_alpha_dummy_046) ∉ (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv) := by
  simpa only [nb057_alpha_dummy_046] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv) 2

theorem nb057_distinct_037 : (nb057_alpha_dummy_044) ≠ (nb057_alpha_dummy_045) := by
  simpa only [nb057_alpha_dummy_044, nb057_alpha_dummy_045] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_distinct_038 : (nb057_alpha_dummy_044) ≠ (nb057_alpha_dummy_046) := by
  simpa only [nb057_alpha_dummy_044, nb057_alpha_dummy_046] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv) (i := 0) (j := 2) (by decide))

theorem nb057_distinct_039 : (nb057_alpha_dummy_045) ≠ (nb057_alpha_dummy_046) := by
  simpa only [nb057_alpha_dummy_045, nb057_alpha_dummy_046] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv) (i := 1) (j := 2) (by decide))

theorem nb057_fresh_040 : (nb057_alpha_dummy_012) ∉ (((Class.cv (nb057_alpha_dummy_005))).fv) := by
  simpa only [nb057_alpha_dummy_012] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_005))).fv) 0

theorem nb057_fresh_041 : (nb057_alpha_dummy_013) ∉ (((Class.cv (nb057_alpha_dummy_005))).fv) := by
  simpa only [nb057_alpha_dummy_013] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_005))).fv) 1

theorem nb057_distinct_042 : (nb057_alpha_dummy_012) ≠ (nb057_alpha_dummy_013) := by
  simpa only [nb057_alpha_dummy_012, nb057_alpha_dummy_013] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_005))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_043 (f : Var) (a : Var) : (nb057_alpha_dummy_014 f a) ∉ (((Class.cv (nb057_alpha_dummy_007 f a))).fv) := by
  simpa only [nb057_alpha_dummy_014] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_007 f a))).fv) 0

theorem nb057_fresh_044 (f : Var) (a : Var) : (nb057_alpha_dummy_015 f a) ∉ (((Class.cv (nb057_alpha_dummy_007 f a))).fv) := by
  simpa only [nb057_alpha_dummy_015] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_007 f a))).fv) 1

theorem nb057_distinct_045 (f : Var) (a : Var) : (nb057_alpha_dummy_014 f a) ≠ (nb057_alpha_dummy_015 f a) := by
  simpa only [nb057_alpha_dummy_014, nb057_alpha_dummy_015] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_007 f a))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_046 : (nb057_alpha_dummy_018) ∉ (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_018] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) 0

theorem nb057_fresh_047 : (nb057_alpha_dummy_019) ∉ (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_019] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) 1

theorem nb057_fresh_048 : (nb057_alpha_dummy_020) ∉ (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_020] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) 2

theorem nb057_distinct_049 : (nb057_alpha_dummy_018) ≠ (nb057_alpha_dummy_019) := by
  simpa only [nb057_alpha_dummy_018, nb057_alpha_dummy_019] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb057_distinct_050 : (nb057_alpha_dummy_018) ≠ (nb057_alpha_dummy_020) := by
  simpa only [nb057_alpha_dummy_018, nb057_alpha_dummy_020] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb057_distinct_051 : (nb057_alpha_dummy_019) ≠ (nb057_alpha_dummy_020) := by
  simpa only [nb057_alpha_dummy_019, nb057_alpha_dummy_020] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb057_fresh_052 (f : Var) (a : Var) : (nb057_alpha_dummy_021 f a) ∉ (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_021] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) 0

theorem nb057_fresh_053 (f : Var) (a : Var) : (nb057_alpha_dummy_022 f a) ∉ (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_022] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) 1

theorem nb057_fresh_054 (f : Var) (a : Var) : (nb057_alpha_dummy_023 f a) ∉ (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_023] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) 2

theorem nb057_distinct_055 (f : Var) (a : Var) : (nb057_alpha_dummy_021 f a) ≠ (nb057_alpha_dummy_022 f a) := by
  simpa only [nb057_alpha_dummy_021, nb057_alpha_dummy_022] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb057_distinct_056 (f : Var) (a : Var) : (nb057_alpha_dummy_021 f a) ≠ (nb057_alpha_dummy_023 f a) := by
  simpa only [nb057_alpha_dummy_021, nb057_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb057_distinct_057 (f : Var) (a : Var) : (nb057_alpha_dummy_022 f a) ≠ (nb057_alpha_dummy_023 f a) := by
  simpa only [nb057_alpha_dummy_022, nb057_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb057_fresh_058 : (nb057_alpha_dummy_030) ∉ (((Class.cv (nb057_alpha_dummy_019))).fv ∪ ((Class.cv (nb057_alpha_dummy_019))).fv) := by
  simpa only [nb057_alpha_dummy_030] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_019))).fv ∪ ((Class.cv (nb057_alpha_dummy_019))).fv) 0

theorem nb057_fresh_059 : (nb057_alpha_dummy_026) ∉ (((Class.cv (nb057_alpha_dummy_019))).fv ∪ ((Class.cv (nb057_alpha_dummy_020))).fv) := by
  simpa only [nb057_alpha_dummy_026] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_019))).fv ∪ ((Class.cv (nb057_alpha_dummy_020))).fv) 0

theorem nb057_fresh_060 : (nb057_alpha_dummy_032) ∉ (((Class.cv (nb057_alpha_dummy_020))).fv ∪ ((Class.cv (nb057_alpha_dummy_020))).fv) := by
  simpa only [nb057_alpha_dummy_032] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_020))).fv ∪ ((Class.cv (nb057_alpha_dummy_020))).fv) 0

theorem nb057_fresh_061 (f : Var) (a : Var) : (nb057_alpha_dummy_031 f a) ∉ (((Class.cv (nb057_alpha_dummy_022 f a))).fv ∪ ((Class.cv (nb057_alpha_dummy_022 f a))).fv) := by
  simpa only [nb057_alpha_dummy_031] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_022 f a))).fv ∪ ((Class.cv (nb057_alpha_dummy_022 f a))).fv) 0

theorem nb057_fresh_062 (f : Var) (a : Var) : (nb057_alpha_dummy_027 f a) ∉ (((Class.cv (nb057_alpha_dummy_022 f a))).fv ∪ ((Class.cv (nb057_alpha_dummy_023 f a))).fv) := by
  simpa only [nb057_alpha_dummy_027] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_022 f a))).fv ∪ ((Class.cv (nb057_alpha_dummy_023 f a))).fv) 0

theorem nb057_fresh_063 (f : Var) (a : Var) : (nb057_alpha_dummy_033 f a) ∉ (((Class.cv (nb057_alpha_dummy_023 f a))).fv ∪ ((Class.cv (nb057_alpha_dummy_023 f a))).fv) := by
  simpa only [nb057_alpha_dummy_033] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_023 f a))).fv ∪ ((Class.cv (nb057_alpha_dummy_023 f a))).fv) 0

theorem nb057_fresh_064 : (nb057_alpha_dummy_052) ∉ (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv) := by
  simpa only [nb057_alpha_dummy_052] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv) 0

theorem nb057_fresh_065 : (nb057_alpha_dummy_053) ∉ (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv) := by
  simpa only [nb057_alpha_dummy_053] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv) 1

theorem nb057_distinct_066 : (nb057_alpha_dummy_052) ≠ (nb057_alpha_dummy_053) := by
  simpa only [nb057_alpha_dummy_052, nb057_alpha_dummy_053] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_067 : (nb057_alpha_dummy_088) ∉ (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_046))).fv) := by
  simpa only [nb057_alpha_dummy_088] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_046))).fv) 0

theorem nb057_fresh_068 : (nb057_alpha_dummy_089) ∉ (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_046))).fv) := by
  simpa only [nb057_alpha_dummy_089] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_046))).fv) 1

theorem nb057_distinct_069 : (nb057_alpha_dummy_088) ≠ (nb057_alpha_dummy_089) := by
  simpa only [nb057_alpha_dummy_088, nb057_alpha_dummy_089] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_046))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_070 : (nb057_alpha_dummy_202) ∉ (((Class.cv (nb057_alpha_dummy_046))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv) := by
  simpa only [nb057_alpha_dummy_202] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_046))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv) 0

theorem nb057_fresh_071 : (nb057_alpha_dummy_203) ∉ (((Class.cv (nb057_alpha_dummy_046))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv) := by
  simpa only [nb057_alpha_dummy_203] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_046))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv) 1

theorem nb057_distinct_072 : (nb057_alpha_dummy_202) ≠ (nb057_alpha_dummy_203) := by
  simpa only [nb057_alpha_dummy_202, nb057_alpha_dummy_203] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_046))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_073 (f : Var) : (nb057_alpha_dummy_054 f) ∉ (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_048 f))).fv) := by
  simpa only [nb057_alpha_dummy_054] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_048 f))).fv) 0

theorem nb057_fresh_074 (f : Var) : (nb057_alpha_dummy_055 f) ∉ (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_048 f))).fv) := by
  simpa only [nb057_alpha_dummy_055] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_048 f))).fv) 1

theorem nb057_distinct_075 (f : Var) : (nb057_alpha_dummy_054 f) ≠ (nb057_alpha_dummy_055 f) := by
  simpa only [nb057_alpha_dummy_054, nb057_alpha_dummy_055] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_048 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_076 (f : Var) : (nb057_alpha_dummy_090 f) ∉ (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_049 f))).fv) := by
  simpa only [nb057_alpha_dummy_090] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_049 f))).fv) 0

theorem nb057_fresh_077 (f : Var) : (nb057_alpha_dummy_091 f) ∉ (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_049 f))).fv) := by
  simpa only [nb057_alpha_dummy_091] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_049 f))).fv) 1

theorem nb057_distinct_078 (f : Var) : (nb057_alpha_dummy_090 f) ≠ (nb057_alpha_dummy_091 f) := by
  simpa only [nb057_alpha_dummy_090, nb057_alpha_dummy_091] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_049 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_079 (f : Var) : (nb057_alpha_dummy_204 f) ∉ (((Class.cv (nb057_alpha_dummy_049 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_048 f))).fv) := by
  simpa only [nb057_alpha_dummy_204] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_049 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_048 f))).fv) 0

theorem nb057_fresh_080 (f : Var) : (nb057_alpha_dummy_205 f) ∉ (((Class.cv (nb057_alpha_dummy_049 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_048 f))).fv) := by
  simpa only [nb057_alpha_dummy_205] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_049 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_048 f))).fv) 1

theorem nb057_distinct_081 (f : Var) : (nb057_alpha_dummy_204 f) ≠ (nb057_alpha_dummy_205 f) := by
  simpa only [nb057_alpha_dummy_204, nb057_alpha_dummy_205] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_049 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_048 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_082 : (nb057_alpha_dummy_060) ∉ (((Class.cv (nb057_alpha_dummy_053))).fv) := by
  simpa only [nb057_alpha_dummy_060] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_053))).fv) 0

theorem nb057_fresh_083 : (nb057_alpha_dummy_061) ∉ (((Class.cv (nb057_alpha_dummy_053))).fv) := by
  simpa only [nb057_alpha_dummy_061] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_053))).fv) 1

theorem nb057_distinct_084 : (nb057_alpha_dummy_060) ≠ (nb057_alpha_dummy_061) := by
  simpa only [nb057_alpha_dummy_060, nb057_alpha_dummy_061] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_053))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_085 (f : Var) : (nb057_alpha_dummy_062 f) ∉ (((Class.cv (nb057_alpha_dummy_055 f))).fv) := by
  simpa only [nb057_alpha_dummy_062] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_055 f))).fv) 0

theorem nb057_fresh_086 (f : Var) : (nb057_alpha_dummy_063 f) ∉ (((Class.cv (nb057_alpha_dummy_055 f))).fv) := by
  simpa only [nb057_alpha_dummy_063] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_055 f))).fv) 1

theorem nb057_distinct_087 (f : Var) : (nb057_alpha_dummy_062 f) ≠ (nb057_alpha_dummy_063 f) := by
  simpa only [nb057_alpha_dummy_062, nb057_alpha_dummy_063] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_055 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_088 : (nb057_alpha_dummy_066) ∉ (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_066] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) 0

theorem nb057_fresh_089 : (nb057_alpha_dummy_067) ∉ (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_067] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) 1

theorem nb057_fresh_090 : (nb057_alpha_dummy_068) ∉ (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_068] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) 2

theorem nb057_distinct_091 : (nb057_alpha_dummy_066) ≠ (nb057_alpha_dummy_067) := by
  simpa only [nb057_alpha_dummy_066, nb057_alpha_dummy_067] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb057_distinct_092 : (nb057_alpha_dummy_066) ≠ (nb057_alpha_dummy_068) := by
  simpa only [nb057_alpha_dummy_066, nb057_alpha_dummy_068] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb057_distinct_093 : (nb057_alpha_dummy_067) ≠ (nb057_alpha_dummy_068) := by
  simpa only [nb057_alpha_dummy_067, nb057_alpha_dummy_068] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb057_fresh_094 (f : Var) : (nb057_alpha_dummy_069 f) ∉ (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_069] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb057_fresh_095 (f : Var) : (nb057_alpha_dummy_070 f) ∉ (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_070] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb057_fresh_096 (f : Var) : (nb057_alpha_dummy_071 f) ∉ (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_071] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb057_distinct_097 (f : Var) : (nb057_alpha_dummy_069 f) ≠ (nb057_alpha_dummy_070 f) := by
  simpa only [nb057_alpha_dummy_069, nb057_alpha_dummy_070] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb057_distinct_098 (f : Var) : (nb057_alpha_dummy_069 f) ≠ (nb057_alpha_dummy_071 f) := by
  simpa only [nb057_alpha_dummy_069, nb057_alpha_dummy_071] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb057_distinct_099 (f : Var) : (nb057_alpha_dummy_070 f) ≠ (nb057_alpha_dummy_071 f) := by
  simpa only [nb057_alpha_dummy_070, nb057_alpha_dummy_071] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb057_fresh_100 : (nb057_alpha_dummy_078) ∉ (((Class.cv (nb057_alpha_dummy_067))).fv ∪ ((Class.cv (nb057_alpha_dummy_067))).fv) := by
  simpa only [nb057_alpha_dummy_078] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_067))).fv ∪ ((Class.cv (nb057_alpha_dummy_067))).fv) 0

theorem nb057_fresh_101 : (nb057_alpha_dummy_074) ∉ (((Class.cv (nb057_alpha_dummy_067))).fv ∪ ((Class.cv (nb057_alpha_dummy_068))).fv) := by
  simpa only [nb057_alpha_dummy_074] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_067))).fv ∪ ((Class.cv (nb057_alpha_dummy_068))).fv) 0

theorem nb057_fresh_102 : (nb057_alpha_dummy_080) ∉ (((Class.cv (nb057_alpha_dummy_068))).fv ∪ ((Class.cv (nb057_alpha_dummy_068))).fv) := by
  simpa only [nb057_alpha_dummy_080] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_068))).fv ∪ ((Class.cv (nb057_alpha_dummy_068))).fv) 0

theorem nb057_fresh_103 (f : Var) : (nb057_alpha_dummy_079 f) ∉ (((Class.cv (nb057_alpha_dummy_070 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_070 f))).fv) := by
  simpa only [nb057_alpha_dummy_079] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_070 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_070 f))).fv) 0

theorem nb057_fresh_104 (f : Var) : (nb057_alpha_dummy_075 f) ∉ (((Class.cv (nb057_alpha_dummy_070 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_071 f))).fv) := by
  simpa only [nb057_alpha_dummy_075] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_070 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_071 f))).fv) 0

theorem nb057_fresh_105 (f : Var) : (nb057_alpha_dummy_081 f) ∉ (((Class.cv (nb057_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_071 f))).fv) := by
  simpa only [nb057_alpha_dummy_081] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_071 f))).fv) 0

theorem nb057_fresh_106 : (nb057_alpha_dummy_096) ∉ (((Class.cv (nb057_alpha_dummy_089))).fv) := by
  simpa only [nb057_alpha_dummy_096] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_089))).fv) 0

theorem nb057_fresh_107 : (nb057_alpha_dummy_097) ∉ (((Class.cv (nb057_alpha_dummy_089))).fv) := by
  simpa only [nb057_alpha_dummy_097] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_089))).fv) 1

theorem nb057_distinct_108 : (nb057_alpha_dummy_096) ≠ (nb057_alpha_dummy_097) := by
  simpa only [nb057_alpha_dummy_096, nb057_alpha_dummy_097] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_089))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_109 (f : Var) : (nb057_alpha_dummy_098 f) ∉ (((Class.cv (nb057_alpha_dummy_091 f))).fv) := by
  simpa only [nb057_alpha_dummy_098] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_091 f))).fv) 0

theorem nb057_fresh_110 (f : Var) : (nb057_alpha_dummy_099 f) ∉ (((Class.cv (nb057_alpha_dummy_091 f))).fv) := by
  simpa only [nb057_alpha_dummy_099] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_091 f))).fv) 1

theorem nb057_distinct_111 (f : Var) : (nb057_alpha_dummy_098 f) ≠ (nb057_alpha_dummy_099 f) := by
  simpa only [nb057_alpha_dummy_098, nb057_alpha_dummy_099] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_091 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_112 : (nb057_alpha_dummy_102) ∉ (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_102] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) 0

theorem nb057_fresh_113 : (nb057_alpha_dummy_103) ∉ (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_103] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) 1

theorem nb057_fresh_114 : (nb057_alpha_dummy_104) ∉ (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_104] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) 2

theorem nb057_distinct_115 : (nb057_alpha_dummy_102) ≠ (nb057_alpha_dummy_103) := by
  simpa only [nb057_alpha_dummy_102, nb057_alpha_dummy_103] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb057_distinct_116 : (nb057_alpha_dummy_102) ≠ (nb057_alpha_dummy_104) := by
  simpa only [nb057_alpha_dummy_102, nb057_alpha_dummy_104] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb057_distinct_117 : (nb057_alpha_dummy_103) ≠ (nb057_alpha_dummy_104) := by
  simpa only [nb057_alpha_dummy_103, nb057_alpha_dummy_104] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb057_fresh_118 (f : Var) : (nb057_alpha_dummy_105 f) ∉ (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_105] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb057_fresh_119 (f : Var) : (nb057_alpha_dummy_106 f) ∉ (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_106] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb057_fresh_120 (f : Var) : (nb057_alpha_dummy_107 f) ∉ (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_107] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb057_distinct_121 (f : Var) : (nb057_alpha_dummy_105 f) ≠ (nb057_alpha_dummy_106 f) := by
  simpa only [nb057_alpha_dummy_105, nb057_alpha_dummy_106] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb057_distinct_122 (f : Var) : (nb057_alpha_dummy_105 f) ≠ (nb057_alpha_dummy_107 f) := by
  simpa only [nb057_alpha_dummy_105, nb057_alpha_dummy_107] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb057_distinct_123 (f : Var) : (nb057_alpha_dummy_106 f) ≠ (nb057_alpha_dummy_107 f) := by
  simpa only [nb057_alpha_dummy_106, nb057_alpha_dummy_107] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb057_fresh_124 : (nb057_alpha_dummy_114) ∉ (((Class.cv (nb057_alpha_dummy_103))).fv ∪ ((Class.cv (nb057_alpha_dummy_103))).fv) := by
  simpa only [nb057_alpha_dummy_114] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_103))).fv ∪ ((Class.cv (nb057_alpha_dummy_103))).fv) 0

theorem nb057_fresh_125 : (nb057_alpha_dummy_110) ∉ (((Class.cv (nb057_alpha_dummy_103))).fv ∪ ((Class.cv (nb057_alpha_dummy_104))).fv) := by
  simpa only [nb057_alpha_dummy_110] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_103))).fv ∪ ((Class.cv (nb057_alpha_dummy_104))).fv) 0

theorem nb057_fresh_126 : (nb057_alpha_dummy_116) ∉ (((Class.cv (nb057_alpha_dummy_104))).fv ∪ ((Class.cv (nb057_alpha_dummy_104))).fv) := by
  simpa only [nb057_alpha_dummy_116] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_104))).fv ∪ ((Class.cv (nb057_alpha_dummy_104))).fv) 0

theorem nb057_fresh_127 (f : Var) : (nb057_alpha_dummy_115 f) ∉ (((Class.cv (nb057_alpha_dummy_106 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_106 f))).fv) := by
  simpa only [nb057_alpha_dummy_115] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_106 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_106 f))).fv) 0

theorem nb057_fresh_128 (f : Var) : (nb057_alpha_dummy_111 f) ∉ (((Class.cv (nb057_alpha_dummy_106 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_107 f))).fv) := by
  simpa only [nb057_alpha_dummy_111] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_106 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_107 f))).fv) 0

theorem nb057_fresh_129 (f : Var) : (nb057_alpha_dummy_117 f) ∉ (((Class.cv (nb057_alpha_dummy_107 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_107 f))).fv) := by
  simpa only [nb057_alpha_dummy_117] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_107 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_107 f))).fv) 0

theorem nb057_fresh_130 : (nb057_alpha_dummy_130) ∉ (((Class.cv (nb057_alpha_dummy_124))).fv ∪ ((Class.cv (nb057_alpha_dummy_125))).fv) := by
  simpa only [nb057_alpha_dummy_130] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_124))).fv ∪ ((Class.cv (nb057_alpha_dummy_125))).fv) 0

theorem nb057_fresh_131 : (nb057_alpha_dummy_131) ∉ (((Class.cv (nb057_alpha_dummy_124))).fv ∪ ((Class.cv (nb057_alpha_dummy_125))).fv) := by
  simpa only [nb057_alpha_dummy_131] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_124))).fv ∪ ((Class.cv (nb057_alpha_dummy_125))).fv) 1

theorem nb057_distinct_132 : (nb057_alpha_dummy_130) ≠ (nb057_alpha_dummy_131) := by
  simpa only [nb057_alpha_dummy_130, nb057_alpha_dummy_131] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_124))).fv ∪ ((Class.cv (nb057_alpha_dummy_125))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_133 : (nb057_alpha_dummy_166) ∉ (((Class.cv (nb057_alpha_dummy_125))).fv ∪ ((Class.cv (nb057_alpha_dummy_124))).fv) := by
  simpa only [nb057_alpha_dummy_166] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_125))).fv ∪ ((Class.cv (nb057_alpha_dummy_124))).fv) 0

theorem nb057_fresh_134 : (nb057_alpha_dummy_167) ∉ (((Class.cv (nb057_alpha_dummy_125))).fv ∪ ((Class.cv (nb057_alpha_dummy_124))).fv) := by
  simpa only [nb057_alpha_dummy_167] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_125))).fv ∪ ((Class.cv (nb057_alpha_dummy_124))).fv) 1

theorem nb057_distinct_135 : (nb057_alpha_dummy_166) ≠ (nb057_alpha_dummy_167) := by
  simpa only [nb057_alpha_dummy_166, nb057_alpha_dummy_167] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_125))).fv ∪ ((Class.cv (nb057_alpha_dummy_124))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_136 (f : Var) : (nb057_alpha_dummy_132 f) ∉ (((Class.cv (nb057_alpha_dummy_126 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_127 f))).fv) := by
  simpa only [nb057_alpha_dummy_132] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_126 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_127 f))).fv) 0

theorem nb057_fresh_137 (f : Var) : (nb057_alpha_dummy_133 f) ∉ (((Class.cv (nb057_alpha_dummy_126 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_127 f))).fv) := by
  simpa only [nb057_alpha_dummy_133] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_126 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_127 f))).fv) 1

theorem nb057_distinct_138 (f : Var) : (nb057_alpha_dummy_132 f) ≠ (nb057_alpha_dummy_133 f) := by
  simpa only [nb057_alpha_dummy_132, nb057_alpha_dummy_133] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_126 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_127 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_139 (f : Var) : (nb057_alpha_dummy_168 f) ∉ (((Class.cv (nb057_alpha_dummy_127 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_126 f))).fv) := by
  simpa only [nb057_alpha_dummy_168] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_127 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_126 f))).fv) 0

theorem nb057_fresh_140 (f : Var) : (nb057_alpha_dummy_169 f) ∉ (((Class.cv (nb057_alpha_dummy_127 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_126 f))).fv) := by
  simpa only [nb057_alpha_dummy_169] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_127 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_126 f))).fv) 1

theorem nb057_distinct_141 (f : Var) : (nb057_alpha_dummy_168 f) ≠ (nb057_alpha_dummy_169 f) := by
  simpa only [nb057_alpha_dummy_168, nb057_alpha_dummy_169] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_127 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_126 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_142 : (nb057_alpha_dummy_138) ∉ (((Class.cv (nb057_alpha_dummy_131))).fv) := by
  simpa only [nb057_alpha_dummy_138] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_131))).fv) 0

theorem nb057_fresh_143 : (nb057_alpha_dummy_139) ∉ (((Class.cv (nb057_alpha_dummy_131))).fv) := by
  simpa only [nb057_alpha_dummy_139] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_131))).fv) 1

theorem nb057_distinct_144 : (nb057_alpha_dummy_138) ≠ (nb057_alpha_dummy_139) := by
  simpa only [nb057_alpha_dummy_138, nb057_alpha_dummy_139] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_131))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_145 (f : Var) : (nb057_alpha_dummy_140 f) ∉ (((Class.cv (nb057_alpha_dummy_133 f))).fv) := by
  simpa only [nb057_alpha_dummy_140] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_133 f))).fv) 0

theorem nb057_fresh_146 (f : Var) : (nb057_alpha_dummy_141 f) ∉ (((Class.cv (nb057_alpha_dummy_133 f))).fv) := by
  simpa only [nb057_alpha_dummy_141] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_133 f))).fv) 1

theorem nb057_distinct_147 (f : Var) : (nb057_alpha_dummy_140 f) ≠ (nb057_alpha_dummy_141 f) := by
  simpa only [nb057_alpha_dummy_140, nb057_alpha_dummy_141] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_133 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_148 : (nb057_alpha_dummy_144) ∉ (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_144] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) 0

theorem nb057_fresh_149 : (nb057_alpha_dummy_145) ∉ (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_145] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) 1

theorem nb057_fresh_150 : (nb057_alpha_dummy_146) ∉ (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_146] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) 2

theorem nb057_distinct_151 : (nb057_alpha_dummy_144) ≠ (nb057_alpha_dummy_145) := by
  simpa only [nb057_alpha_dummy_144, nb057_alpha_dummy_145] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb057_distinct_152 : (nb057_alpha_dummy_144) ≠ (nb057_alpha_dummy_146) := by
  simpa only [nb057_alpha_dummy_144, nb057_alpha_dummy_146] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb057_distinct_153 : (nb057_alpha_dummy_145) ≠ (nb057_alpha_dummy_146) := by
  simpa only [nb057_alpha_dummy_145, nb057_alpha_dummy_146] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb057_fresh_154 (f : Var) : (nb057_alpha_dummy_147 f) ∉ (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_147] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb057_fresh_155 (f : Var) : (nb057_alpha_dummy_148 f) ∉ (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_148] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb057_fresh_156 (f : Var) : (nb057_alpha_dummy_149 f) ∉ (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb057_alpha_dummy_149] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb057_distinct_157 (f : Var) : (nb057_alpha_dummy_147 f) ≠ (nb057_alpha_dummy_148 f) := by
  simpa only [nb057_alpha_dummy_147, nb057_alpha_dummy_148] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb057_distinct_158 (f : Var) : (nb057_alpha_dummy_147 f) ≠ (nb057_alpha_dummy_149 f) := by
  simpa only [nb057_alpha_dummy_147, nb057_alpha_dummy_149] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb057_distinct_159 (f : Var) : (nb057_alpha_dummy_148 f) ≠ (nb057_alpha_dummy_149 f) := by
  simpa only [nb057_alpha_dummy_148, nb057_alpha_dummy_149] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb057_fresh_160 : (nb057_alpha_dummy_156) ∉ (((Class.cv (nb057_alpha_dummy_145))).fv ∪ ((Class.cv (nb057_alpha_dummy_145))).fv) := by
  simpa only [nb057_alpha_dummy_156] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_145))).fv ∪ ((Class.cv (nb057_alpha_dummy_145))).fv) 0

theorem nb057_fresh_161 : (nb057_alpha_dummy_152) ∉ (((Class.cv (nb057_alpha_dummy_145))).fv ∪ ((Class.cv (nb057_alpha_dummy_146))).fv) := by
  simpa only [nb057_alpha_dummy_152] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_145))).fv ∪ ((Class.cv (nb057_alpha_dummy_146))).fv) 0

theorem nb057_fresh_162 : (nb057_alpha_dummy_158) ∉ (((Class.cv (nb057_alpha_dummy_146))).fv ∪ ((Class.cv (nb057_alpha_dummy_146))).fv) := by
  simpa only [nb057_alpha_dummy_158] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_146))).fv ∪ ((Class.cv (nb057_alpha_dummy_146))).fv) 0

theorem nb057_fresh_163 (f : Var) : (nb057_alpha_dummy_157 f) ∉ (((Class.cv (nb057_alpha_dummy_148 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_148 f))).fv) := by
  simpa only [nb057_alpha_dummy_157] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_148 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_148 f))).fv) 0

theorem nb057_fresh_164 (f : Var) : (nb057_alpha_dummy_153 f) ∉ (((Class.cv (nb057_alpha_dummy_148 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_149 f))).fv) := by
  simpa only [nb057_alpha_dummy_153] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_148 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_149 f))).fv) 0

theorem nb057_fresh_165 (f : Var) : (nb057_alpha_dummy_159 f) ∉ (((Class.cv (nb057_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_149 f))).fv) := by
  simpa only [nb057_alpha_dummy_159] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_149 f))).fv) 0

theorem nb057_fresh_166 : (nb057_alpha_dummy_174) ∉ (((Class.cv (nb057_alpha_dummy_167))).fv) := by
  simpa only [nb057_alpha_dummy_174] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_167))).fv) 0

theorem nb057_fresh_167 : (nb057_alpha_dummy_175) ∉ (((Class.cv (nb057_alpha_dummy_167))).fv) := by
  simpa only [nb057_alpha_dummy_175] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_167))).fv) 1

theorem nb057_distinct_168 : (nb057_alpha_dummy_174) ≠ (nb057_alpha_dummy_175) := by
  simpa only [nb057_alpha_dummy_174, nb057_alpha_dummy_175] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_167))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_169 (f : Var) : (nb057_alpha_dummy_176 f) ∉ (((Class.cv (nb057_alpha_dummy_169 f))).fv) := by
  simpa only [nb057_alpha_dummy_176] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_169 f))).fv) 0

theorem nb057_fresh_170 (f : Var) : (nb057_alpha_dummy_177 f) ∉ (((Class.cv (nb057_alpha_dummy_169 f))).fv) := by
  simpa only [nb057_alpha_dummy_177] using freshVar_not_mem (((Class.cv (nb057_alpha_dummy_169 f))).fv) 1

theorem nb057_distinct_171 (f : Var) : (nb057_alpha_dummy_176 f) ≠ (nb057_alpha_dummy_177 f) := by
  simpa only [nb057_alpha_dummy_176, nb057_alpha_dummy_177] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_169 f))).fv) (i := 0) (j := 1) (by decide))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
