import NAR4C060C001Part001

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

noncomputable def nb060_alpha_dummy_150 (x : Var) (z : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))).fv ∪ ((syn_cphi (Class.cv (nb060_alpha_dummy_118 x z)))).fv) 0)

theorem nb060_fresh_000 : (nb060_alpha_dummy_037) ∉ (((Class.cab (nb060_alpha_dummy_007) (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_000)) (Wff.classEq (Class.cv (nb060_alpha_dummy_007)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_008))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_007) (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_000)) (Wff.classEq (Class.cv (nb060_alpha_dummy_007)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_008))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb060_alpha_dummy_037] using freshVar_not_mem (((Class.cab (nb060_alpha_dummy_007) (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_000)) (Wff.classEq (Class.cv (nb060_alpha_dummy_007)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_008))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_007) (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_000)) (Wff.classEq (Class.cv (nb060_alpha_dummy_007)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_008))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb060_fresh_001 : (nb060_alpha_dummy_013) ∉ (((Class.cab (nb060_alpha_dummy_007) (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_001)) (Wff.classEq (Class.cv (nb060_alpha_dummy_007)) (syn_cphi (Class.cv (nb060_alpha_dummy_008))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_007) (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_001)) (Wff.classEq (Class.cv (nb060_alpha_dummy_007)) (syn_cphi (Class.cv (nb060_alpha_dummy_008))))))).fv) := by
  simpa only [nb060_alpha_dummy_013] using freshVar_not_mem (((Class.cab (nb060_alpha_dummy_007) (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_001)) (Wff.classEq (Class.cv (nb060_alpha_dummy_007)) (syn_cphi (Class.cv (nb060_alpha_dummy_008))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_007) (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_001)) (Wff.classEq (Class.cv (nb060_alpha_dummy_007)) (syn_cphi (Class.cv (nb060_alpha_dummy_008))))))).fv) 0

theorem nb060_fresh_002 (r : Var) (a : Var) : (nb060_alpha_dummy_038 r a) ∉ (((Class.cab (nb060_alpha_dummy_009 r a) (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv a) (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_009 r a) (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv a) (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb060_alpha_dummy_038] using freshVar_not_mem (((Class.cab (nb060_alpha_dummy_009 r a) (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv a) (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_009 r a) (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv a) (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb060_fresh_003 (r : Var) (a : Var) : (nb060_alpha_dummy_014 r a) ∉ (((Class.cab (nb060_alpha_dummy_009 r a) (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv r) (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a)) (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_009 r a) (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv r) (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a)) (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))))))).fv) := by
  simpa only [nb060_alpha_dummy_014] using freshVar_not_mem (((Class.cab (nb060_alpha_dummy_009 r a) (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv r) (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a)) (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_009 r a) (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv r) (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a)) (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))))))).fv) 0

theorem nb060_fresh_004 : (nb060_alpha_dummy_049) ∉ (((Class.cab (nb060_alpha_dummy_043) (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_002)) (Wff.classEq (Class.cv (nb060_alpha_dummy_043)) (syn_cphi (Class.cv (nb060_alpha_dummy_044))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_043) (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_002)) (Wff.classEq (Class.cv (nb060_alpha_dummy_043)) (syn_cphi (Class.cv (nb060_alpha_dummy_044))))))).fv) := by
  simpa only [nb060_alpha_dummy_049] using freshVar_not_mem (((Class.cab (nb060_alpha_dummy_043) (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_002)) (Wff.classEq (Class.cv (nb060_alpha_dummy_043)) (syn_cphi (Class.cv (nb060_alpha_dummy_044))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_043) (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_002)) (Wff.classEq (Class.cv (nb060_alpha_dummy_043)) (syn_cphi (Class.cv (nb060_alpha_dummy_044))))))).fv) 0

theorem nb060_fresh_005 : (nb060_alpha_dummy_073) ∉ (((Class.cab (nb060_alpha_dummy_043) (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_003)) (Wff.classEq (Class.cv (nb060_alpha_dummy_043)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_044))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_043) (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_003)) (Wff.classEq (Class.cv (nb060_alpha_dummy_043)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_044))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb060_alpha_dummy_073] using freshVar_not_mem (((Class.cab (nb060_alpha_dummy_043) (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_003)) (Wff.classEq (Class.cv (nb060_alpha_dummy_043)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_044))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_043) (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_003)) (Wff.classEq (Class.cv (nb060_alpha_dummy_043)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_044))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb060_fresh_006 (x : Var) (y : Var) : (nb060_alpha_dummy_050 x y) ∉ (((Class.cab (nb060_alpha_dummy_045 x y) (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv x) (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y)) (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_045 x y) (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv x) (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y)) (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))))))).fv) := by
  simpa only [nb060_alpha_dummy_050] using freshVar_not_mem (((Class.cab (nb060_alpha_dummy_045 x y) (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv x) (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y)) (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_045 x y) (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv x) (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y)) (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))))))).fv) 0

theorem nb060_fresh_007 (x : Var) (y : Var) : (nb060_alpha_dummy_074 x y) ∉ (((Class.cab (nb060_alpha_dummy_045 x y) (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv y) (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_045 x y) (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv y) (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb060_alpha_dummy_074] using freshVar_not_mem (((Class.cab (nb060_alpha_dummy_045 x y) (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv y) (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_045 x y) (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv y) (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb060_fresh_008 : (nb060_alpha_dummy_085) ∉ (((Class.cab (nb060_alpha_dummy_079) (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_003)) (Wff.classEq (Class.cv (nb060_alpha_dummy_079)) (syn_cphi (Class.cv (nb060_alpha_dummy_080))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_079) (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_003)) (Wff.classEq (Class.cv (nb060_alpha_dummy_079)) (syn_cphi (Class.cv (nb060_alpha_dummy_080))))))).fv) := by
  simpa only [nb060_alpha_dummy_085] using freshVar_not_mem (((Class.cab (nb060_alpha_dummy_079) (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_003)) (Wff.classEq (Class.cv (nb060_alpha_dummy_079)) (syn_cphi (Class.cv (nb060_alpha_dummy_080))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_079) (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_003)) (Wff.classEq (Class.cv (nb060_alpha_dummy_079)) (syn_cphi (Class.cv (nb060_alpha_dummy_080))))))).fv) 0

theorem nb060_fresh_009 : (nb060_alpha_dummy_109) ∉ (((Class.cab (nb060_alpha_dummy_079) (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_004)) (Wff.classEq (Class.cv (nb060_alpha_dummy_079)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_080))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_079) (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_004)) (Wff.classEq (Class.cv (nb060_alpha_dummy_079)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_080))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb060_alpha_dummy_109] using freshVar_not_mem (((Class.cab (nb060_alpha_dummy_079) (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_004)) (Wff.classEq (Class.cv (nb060_alpha_dummy_079)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_080))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_079) (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_004)) (Wff.classEq (Class.cv (nb060_alpha_dummy_079)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_080))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb060_fresh_010 (y : Var) (z : Var) : (nb060_alpha_dummy_086 y z) ∉ (((Class.cab (nb060_alpha_dummy_081 y z) (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv y) (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z)) (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_081 y z) (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv y) (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z)) (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))))))).fv) := by
  simpa only [nb060_alpha_dummy_086] using freshVar_not_mem (((Class.cab (nb060_alpha_dummy_081 y z) (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv y) (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z)) (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_081 y z) (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv y) (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z)) (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))))))).fv) 0

theorem nb060_fresh_011 (y : Var) (z : Var) : (nb060_alpha_dummy_110 y z) ∉ (((Class.cab (nb060_alpha_dummy_081 y z) (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv z) (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_081 y z) (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv z) (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb060_alpha_dummy_110] using freshVar_not_mem (((Class.cab (nb060_alpha_dummy_081 y z) (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv z) (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_081 y z) (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv z) (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb060_fresh_012 : (nb060_alpha_dummy_121) ∉ (((Class.cab (nb060_alpha_dummy_115) (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_002)) (Wff.classEq (Class.cv (nb060_alpha_dummy_115)) (syn_cphi (Class.cv (nb060_alpha_dummy_116))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_115) (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_002)) (Wff.classEq (Class.cv (nb060_alpha_dummy_115)) (syn_cphi (Class.cv (nb060_alpha_dummy_116))))))).fv) := by
  simpa only [nb060_alpha_dummy_121] using freshVar_not_mem (((Class.cab (nb060_alpha_dummy_115) (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_002)) (Wff.classEq (Class.cv (nb060_alpha_dummy_115)) (syn_cphi (Class.cv (nb060_alpha_dummy_116))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_115) (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_002)) (Wff.classEq (Class.cv (nb060_alpha_dummy_115)) (syn_cphi (Class.cv (nb060_alpha_dummy_116))))))).fv) 0

theorem nb060_fresh_013 : (nb060_alpha_dummy_145) ∉ (((Class.cab (nb060_alpha_dummy_115) (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_004)) (Wff.classEq (Class.cv (nb060_alpha_dummy_115)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_116))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_115) (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_004)) (Wff.classEq (Class.cv (nb060_alpha_dummy_115)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_116))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb060_alpha_dummy_145] using freshVar_not_mem (((Class.cab (nb060_alpha_dummy_115) (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_004)) (Wff.classEq (Class.cv (nb060_alpha_dummy_115)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_116))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_115) (syn_wrex (nb060_alpha_dummy_116) (Class.cv (nb060_alpha_dummy_004)) (Wff.classEq (Class.cv (nb060_alpha_dummy_115)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_116))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb060_fresh_014 (x : Var) (z : Var) : (nb060_alpha_dummy_122 x z) ∉ (((Class.cab (nb060_alpha_dummy_117 x z) (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv x) (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z)) (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_117 x z) (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv x) (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z)) (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))))))).fv) := by
  simpa only [nb060_alpha_dummy_122] using freshVar_not_mem (((Class.cab (nb060_alpha_dummy_117 x z) (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv x) (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z)) (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_117 x z) (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv x) (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z)) (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))))))).fv) 0

theorem nb060_fresh_015 (x : Var) (z : Var) : (nb060_alpha_dummy_146 x z) ∉ (((Class.cab (nb060_alpha_dummy_117 x z) (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv z) (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_117 x z) (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv z) (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb060_alpha_dummy_146] using freshVar_not_mem (((Class.cab (nb060_alpha_dummy_117 x z) (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv z) (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb060_alpha_dummy_117 x z) (syn_wrex (nb060_alpha_dummy_118 x z) (Class.cv z) (Wff.classEq (Class.cv (nb060_alpha_dummy_117 x z)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_118 x z))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb060_fresh_016 : (nb060_alpha_dummy_007) ∉ (((Class.cv (nb060_alpha_dummy_001))).fv ∪ ((Class.cv (nb060_alpha_dummy_000))).fv) := by
  simpa only [nb060_alpha_dummy_007] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_001))).fv ∪ ((Class.cv (nb060_alpha_dummy_000))).fv) 0

theorem nb060_fresh_017 : (nb060_alpha_dummy_008) ∉ (((Class.cv (nb060_alpha_dummy_001))).fv ∪ ((Class.cv (nb060_alpha_dummy_000))).fv) := by
  simpa only [nb060_alpha_dummy_008] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_001))).fv ∪ ((Class.cv (nb060_alpha_dummy_000))).fv) 1

theorem nb060_distinct_018 : (nb060_alpha_dummy_007) ≠ (nb060_alpha_dummy_008) := by
  simpa only [nb060_alpha_dummy_007, nb060_alpha_dummy_008] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_001))).fv ∪ ((Class.cv (nb060_alpha_dummy_000))).fv) (i := 0) (j := 1) (by decide))

theorem nb060_fresh_019 : (nb060_alpha_dummy_043) ∉ (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_003))).fv) := by
  simpa only [nb060_alpha_dummy_043] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_003))).fv) 0

theorem nb060_fresh_020 : (nb060_alpha_dummy_044) ∉ (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_003))).fv) := by
  simpa only [nb060_alpha_dummy_044] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_003))).fv) 1

theorem nb060_distinct_021 : (nb060_alpha_dummy_043) ≠ (nb060_alpha_dummy_044) := by
  simpa only [nb060_alpha_dummy_043, nb060_alpha_dummy_044] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_003))).fv) (i := 0) (j := 1) (by decide))

theorem nb060_fresh_022 : (nb060_alpha_dummy_115) ∉ (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv) := by
  simpa only [nb060_alpha_dummy_115] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv) 0

theorem nb060_fresh_023 : (nb060_alpha_dummy_116) ∉ (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv) := by
  simpa only [nb060_alpha_dummy_116] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv) 1

theorem nb060_distinct_024 : (nb060_alpha_dummy_115) ≠ (nb060_alpha_dummy_116) := by
  simpa only [nb060_alpha_dummy_115, nb060_alpha_dummy_116] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_002))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv) (i := 0) (j := 1) (by decide))

theorem nb060_fresh_025 : (nb060_alpha_dummy_079) ∉ (((Class.cv (nb060_alpha_dummy_003))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv) := by
  simpa only [nb060_alpha_dummy_079] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_003))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv) 0

theorem nb060_fresh_026 : (nb060_alpha_dummy_080) ∉ (((Class.cv (nb060_alpha_dummy_003))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv) := by
  simpa only [nb060_alpha_dummy_080] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_003))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv) 1

theorem nb060_distinct_027 : (nb060_alpha_dummy_079) ≠ (nb060_alpha_dummy_080) := by
  simpa only [nb060_alpha_dummy_079, nb060_alpha_dummy_080] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_003))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv) (i := 0) (j := 1) (by decide))

theorem nb060_fresh_028 : (nb060_alpha_dummy_015) ∉ (((Class.cv (nb060_alpha_dummy_008))).fv) := by
  simpa only [nb060_alpha_dummy_015] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_008))).fv) 0

theorem nb060_fresh_029 : (nb060_alpha_dummy_016) ∉ (((Class.cv (nb060_alpha_dummy_008))).fv) := by
  simpa only [nb060_alpha_dummy_016] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_008))).fv) 1

theorem nb060_distinct_030 : (nb060_alpha_dummy_015) ≠ (nb060_alpha_dummy_016) := by
  simpa only [nb060_alpha_dummy_015, nb060_alpha_dummy_016] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_008))).fv) (i := 0) (j := 1) (by decide))

theorem nb060_fresh_031 (r : Var) (a : Var) : (nb060_alpha_dummy_017 r a) ∉ (((Class.cv (nb060_alpha_dummy_010 r a))).fv) := by
  simpa only [nb060_alpha_dummy_017] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_010 r a))).fv) 0

theorem nb060_fresh_032 (r : Var) (a : Var) : (nb060_alpha_dummy_018 r a) ∉ (((Class.cv (nb060_alpha_dummy_010 r a))).fv) := by
  simpa only [nb060_alpha_dummy_018] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_010 r a))).fv) 1

theorem nb060_distinct_033 (r : Var) (a : Var) : (nb060_alpha_dummy_017 r a) ≠ (nb060_alpha_dummy_018 r a) := by
  simpa only [nb060_alpha_dummy_017, nb060_alpha_dummy_018] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_010 r a))).fv) (i := 0) (j := 1) (by decide))

theorem nb060_fresh_034 : (nb060_alpha_dummy_021) ∉ (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb060_alpha_dummy_021] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) 0

theorem nb060_fresh_035 : (nb060_alpha_dummy_022) ∉ (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb060_alpha_dummy_022] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) 1

theorem nb060_fresh_036 : (nb060_alpha_dummy_023) ∉ (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb060_alpha_dummy_023] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) 2

theorem nb060_distinct_037 : (nb060_alpha_dummy_021) ≠ (nb060_alpha_dummy_022) := by
  simpa only [nb060_alpha_dummy_021, nb060_alpha_dummy_022] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb060_distinct_038 : (nb060_alpha_dummy_021) ≠ (nb060_alpha_dummy_023) := by
  simpa only [nb060_alpha_dummy_021, nb060_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb060_distinct_039 : (nb060_alpha_dummy_022) ≠ (nb060_alpha_dummy_023) := by
  simpa only [nb060_alpha_dummy_022, nb060_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_015))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb060_fresh_040 (r : Var) (a : Var) : (nb060_alpha_dummy_024 r a) ∉ (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb060_alpha_dummy_024] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) 0

theorem nb060_fresh_041 (r : Var) (a : Var) : (nb060_alpha_dummy_025 r a) ∉ (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb060_alpha_dummy_025] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) 1

theorem nb060_fresh_042 (r : Var) (a : Var) : (nb060_alpha_dummy_026 r a) ∉ (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb060_alpha_dummy_026] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) 2

theorem nb060_distinct_043 (r : Var) (a : Var) : (nb060_alpha_dummy_024 r a) ≠ (nb060_alpha_dummy_025 r a) := by
  simpa only [nb060_alpha_dummy_024, nb060_alpha_dummy_025] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb060_distinct_044 (r : Var) (a : Var) : (nb060_alpha_dummy_024 r a) ≠ (nb060_alpha_dummy_026 r a) := by
  simpa only [nb060_alpha_dummy_024, nb060_alpha_dummy_026] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb060_distinct_045 (r : Var) (a : Var) : (nb060_alpha_dummy_025 r a) ≠ (nb060_alpha_dummy_026 r a) := by
  simpa only [nb060_alpha_dummy_025, nb060_alpha_dummy_026] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_017 r a))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb060_fresh_046 : (nb060_alpha_dummy_033) ∉ (((Class.cv (nb060_alpha_dummy_022))).fv ∪ ((Class.cv (nb060_alpha_dummy_022))).fv) := by
  simpa only [nb060_alpha_dummy_033] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_022))).fv ∪ ((Class.cv (nb060_alpha_dummy_022))).fv) 0

theorem nb060_fresh_047 : (nb060_alpha_dummy_029) ∉ (((Class.cv (nb060_alpha_dummy_022))).fv ∪ ((Class.cv (nb060_alpha_dummy_023))).fv) := by
  simpa only [nb060_alpha_dummy_029] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_022))).fv ∪ ((Class.cv (nb060_alpha_dummy_023))).fv) 0

theorem nb060_fresh_048 : (nb060_alpha_dummy_035) ∉ (((Class.cv (nb060_alpha_dummy_023))).fv ∪ ((Class.cv (nb060_alpha_dummy_023))).fv) := by
  simpa only [nb060_alpha_dummy_035] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_023))).fv ∪ ((Class.cv (nb060_alpha_dummy_023))).fv) 0

theorem nb060_fresh_049 (r : Var) (a : Var) : (nb060_alpha_dummy_034 r a) ∉ (((Class.cv (nb060_alpha_dummy_025 r a))).fv ∪ ((Class.cv (nb060_alpha_dummy_025 r a))).fv) := by
  simpa only [nb060_alpha_dummy_034] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_025 r a))).fv ∪ ((Class.cv (nb060_alpha_dummy_025 r a))).fv) 0

theorem nb060_fresh_050 (r : Var) (a : Var) : (nb060_alpha_dummy_030 r a) ∉ (((Class.cv (nb060_alpha_dummy_025 r a))).fv ∪ ((Class.cv (nb060_alpha_dummy_026 r a))).fv) := by
  simpa only [nb060_alpha_dummy_030] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_025 r a))).fv ∪ ((Class.cv (nb060_alpha_dummy_026 r a))).fv) 0

theorem nb060_fresh_051 (r : Var) (a : Var) : (nb060_alpha_dummy_036 r a) ∉ (((Class.cv (nb060_alpha_dummy_026 r a))).fv ∪ ((Class.cv (nb060_alpha_dummy_026 r a))).fv) := by
  simpa only [nb060_alpha_dummy_036] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_026 r a))).fv ∪ ((Class.cv (nb060_alpha_dummy_026 r a))).fv) 0

theorem nb060_fresh_052 : (nb060_alpha_dummy_051) ∉ (((Class.cv (nb060_alpha_dummy_044))).fv) := by
  simpa only [nb060_alpha_dummy_051] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_044))).fv) 0

theorem nb060_fresh_053 : (nb060_alpha_dummy_052) ∉ (((Class.cv (nb060_alpha_dummy_044))).fv) := by
  simpa only [nb060_alpha_dummy_052] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_044))).fv) 1

theorem nb060_distinct_054 : (nb060_alpha_dummy_051) ≠ (nb060_alpha_dummy_052) := by
  simpa only [nb060_alpha_dummy_051, nb060_alpha_dummy_052] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_044))).fv) (i := 0) (j := 1) (by decide))

theorem nb060_fresh_055 (x : Var) (y : Var) : (nb060_alpha_dummy_053 x y) ∉ (((Class.cv (nb060_alpha_dummy_046 x y))).fv) := by
  simpa only [nb060_alpha_dummy_053] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_046 x y))).fv) 0

theorem nb060_fresh_056 (x : Var) (y : Var) : (nb060_alpha_dummy_054 x y) ∉ (((Class.cv (nb060_alpha_dummy_046 x y))).fv) := by
  simpa only [nb060_alpha_dummy_054] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_046 x y))).fv) 1

theorem nb060_distinct_057 (x : Var) (y : Var) : (nb060_alpha_dummy_053 x y) ≠ (nb060_alpha_dummy_054 x y) := by
  simpa only [nb060_alpha_dummy_053, nb060_alpha_dummy_054] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_046 x y))).fv) (i := 0) (j := 1) (by decide))

theorem nb060_fresh_058 : (nb060_alpha_dummy_057) ∉ (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb060_alpha_dummy_057] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) 0

theorem nb060_fresh_059 : (nb060_alpha_dummy_058) ∉ (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb060_alpha_dummy_058] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) 1

theorem nb060_fresh_060 : (nb060_alpha_dummy_059) ∉ (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb060_alpha_dummy_059] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) 2

theorem nb060_distinct_061 : (nb060_alpha_dummy_057) ≠ (nb060_alpha_dummy_058) := by
  simpa only [nb060_alpha_dummy_057, nb060_alpha_dummy_058] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb060_distinct_062 : (nb060_alpha_dummy_057) ≠ (nb060_alpha_dummy_059) := by
  simpa only [nb060_alpha_dummy_057, nb060_alpha_dummy_059] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb060_distinct_063 : (nb060_alpha_dummy_058) ≠ (nb060_alpha_dummy_059) := by
  simpa only [nb060_alpha_dummy_058, nb060_alpha_dummy_059] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_051))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb060_fresh_064 (x : Var) (y : Var) : (nb060_alpha_dummy_060 x y) ∉ (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb060_alpha_dummy_060] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) 0

theorem nb060_fresh_065 (x : Var) (y : Var) : (nb060_alpha_dummy_061 x y) ∉ (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb060_alpha_dummy_061] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) 1

theorem nb060_fresh_066 (x : Var) (y : Var) : (nb060_alpha_dummy_062 x y) ∉ (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb060_alpha_dummy_062] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) 2

theorem nb060_distinct_067 (x : Var) (y : Var) : (nb060_alpha_dummy_060 x y) ≠ (nb060_alpha_dummy_061 x y) := by
  simpa only [nb060_alpha_dummy_060, nb060_alpha_dummy_061] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb060_distinct_068 (x : Var) (y : Var) : (nb060_alpha_dummy_060 x y) ≠ (nb060_alpha_dummy_062 x y) := by
  simpa only [nb060_alpha_dummy_060, nb060_alpha_dummy_062] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb060_distinct_069 (x : Var) (y : Var) : (nb060_alpha_dummy_061 x y) ≠ (nb060_alpha_dummy_062 x y) := by
  simpa only [nb060_alpha_dummy_061, nb060_alpha_dummy_062] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_053 x y))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb060_fresh_070 : (nb060_alpha_dummy_069) ∉ (((Class.cv (nb060_alpha_dummy_058))).fv ∪ ((Class.cv (nb060_alpha_dummy_058))).fv) := by
  simpa only [nb060_alpha_dummy_069] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_058))).fv ∪ ((Class.cv (nb060_alpha_dummy_058))).fv) 0

theorem nb060_fresh_071 : (nb060_alpha_dummy_065) ∉ (((Class.cv (nb060_alpha_dummy_058))).fv ∪ ((Class.cv (nb060_alpha_dummy_059))).fv) := by
  simpa only [nb060_alpha_dummy_065] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_058))).fv ∪ ((Class.cv (nb060_alpha_dummy_059))).fv) 0

theorem nb060_fresh_072 : (nb060_alpha_dummy_071) ∉ (((Class.cv (nb060_alpha_dummy_059))).fv ∪ ((Class.cv (nb060_alpha_dummy_059))).fv) := by
  simpa only [nb060_alpha_dummy_071] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_059))).fv ∪ ((Class.cv (nb060_alpha_dummy_059))).fv) 0

theorem nb060_fresh_073 (x : Var) (y : Var) : (nb060_alpha_dummy_070 x y) ∉ (((Class.cv (nb060_alpha_dummy_061 x y))).fv ∪ ((Class.cv (nb060_alpha_dummy_061 x y))).fv) := by
  simpa only [nb060_alpha_dummy_070] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_061 x y))).fv ∪ ((Class.cv (nb060_alpha_dummy_061 x y))).fv) 0

theorem nb060_fresh_074 (x : Var) (y : Var) : (nb060_alpha_dummy_066 x y) ∉ (((Class.cv (nb060_alpha_dummy_061 x y))).fv ∪ ((Class.cv (nb060_alpha_dummy_062 x y))).fv) := by
  simpa only [nb060_alpha_dummy_066] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_061 x y))).fv ∪ ((Class.cv (nb060_alpha_dummy_062 x y))).fv) 0

theorem nb060_fresh_075 (x : Var) (y : Var) : (nb060_alpha_dummy_072 x y) ∉ (((Class.cv (nb060_alpha_dummy_062 x y))).fv ∪ ((Class.cv (nb060_alpha_dummy_062 x y))).fv) := by
  simpa only [nb060_alpha_dummy_072] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_062 x y))).fv ∪ ((Class.cv (nb060_alpha_dummy_062 x y))).fv) 0

theorem nb060_fresh_076 : (nb060_alpha_dummy_087) ∉ (((Class.cv (nb060_alpha_dummy_080))).fv) := by
  simpa only [nb060_alpha_dummy_087] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_080))).fv) 0

theorem nb060_fresh_077 : (nb060_alpha_dummy_088) ∉ (((Class.cv (nb060_alpha_dummy_080))).fv) := by
  simpa only [nb060_alpha_dummy_088] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_080))).fv) 1

theorem nb060_distinct_078 : (nb060_alpha_dummy_087) ≠ (nb060_alpha_dummy_088) := by
  simpa only [nb060_alpha_dummy_087, nb060_alpha_dummy_088] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_080))).fv) (i := 0) (j := 1) (by decide))

theorem nb060_fresh_079 (y : Var) (z : Var) : (nb060_alpha_dummy_089 y z) ∉ (((Class.cv (nb060_alpha_dummy_082 y z))).fv) := by
  simpa only [nb060_alpha_dummy_089] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_082 y z))).fv) 0

theorem nb060_fresh_080 (y : Var) (z : Var) : (nb060_alpha_dummy_090 y z) ∉ (((Class.cv (nb060_alpha_dummy_082 y z))).fv) := by
  simpa only [nb060_alpha_dummy_090] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_082 y z))).fv) 1

theorem nb060_distinct_081 (y : Var) (z : Var) : (nb060_alpha_dummy_089 y z) ≠ (nb060_alpha_dummy_090 y z) := by
  simpa only [nb060_alpha_dummy_089, nb060_alpha_dummy_090] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_082 y z))).fv) (i := 0) (j := 1) (by decide))

theorem nb060_fresh_082 : (nb060_alpha_dummy_093) ∉ (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb060_alpha_dummy_093] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) 0

theorem nb060_fresh_083 : (nb060_alpha_dummy_094) ∉ (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb060_alpha_dummy_094] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) 1

theorem nb060_fresh_084 : (nb060_alpha_dummy_095) ∉ (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb060_alpha_dummy_095] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) 2

theorem nb060_distinct_085 : (nb060_alpha_dummy_093) ≠ (nb060_alpha_dummy_094) := by
  simpa only [nb060_alpha_dummy_093, nb060_alpha_dummy_094] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb060_distinct_086 : (nb060_alpha_dummy_093) ≠ (nb060_alpha_dummy_095) := by
  simpa only [nb060_alpha_dummy_093, nb060_alpha_dummy_095] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb060_distinct_087 : (nb060_alpha_dummy_094) ≠ (nb060_alpha_dummy_095) := by
  simpa only [nb060_alpha_dummy_094, nb060_alpha_dummy_095] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb060_fresh_088 (y : Var) (z : Var) : (nb060_alpha_dummy_096 y z) ∉ (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb060_alpha_dummy_096] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) 0

theorem nb060_fresh_089 (y : Var) (z : Var) : (nb060_alpha_dummy_097 y z) ∉ (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb060_alpha_dummy_097] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) 1

theorem nb060_fresh_090 (y : Var) (z : Var) : (nb060_alpha_dummy_098 y z) ∉ (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb060_alpha_dummy_098] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) 2

theorem nb060_distinct_091 (y : Var) (z : Var) : (nb060_alpha_dummy_096 y z) ≠ (nb060_alpha_dummy_097 y z) := by
  simpa only [nb060_alpha_dummy_096, nb060_alpha_dummy_097] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb060_distinct_092 (y : Var) (z : Var) : (nb060_alpha_dummy_096 y z) ≠ (nb060_alpha_dummy_098 y z) := by
  simpa only [nb060_alpha_dummy_096, nb060_alpha_dummy_098] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb060_distinct_093 (y : Var) (z : Var) : (nb060_alpha_dummy_097 y z) ≠ (nb060_alpha_dummy_098 y z) := by
  simpa only [nb060_alpha_dummy_097, nb060_alpha_dummy_098] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb060_fresh_094 : (nb060_alpha_dummy_105) ∉ (((Class.cv (nb060_alpha_dummy_094))).fv ∪ ((Class.cv (nb060_alpha_dummy_094))).fv) := by
  simpa only [nb060_alpha_dummy_105] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_094))).fv ∪ ((Class.cv (nb060_alpha_dummy_094))).fv) 0

theorem nb060_fresh_095 : (nb060_alpha_dummy_101) ∉ (((Class.cv (nb060_alpha_dummy_094))).fv ∪ ((Class.cv (nb060_alpha_dummy_095))).fv) := by
  simpa only [nb060_alpha_dummy_101] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_094))).fv ∪ ((Class.cv (nb060_alpha_dummy_095))).fv) 0

theorem nb060_fresh_096 : (nb060_alpha_dummy_107) ∉ (((Class.cv (nb060_alpha_dummy_095))).fv ∪ ((Class.cv (nb060_alpha_dummy_095))).fv) := by
  simpa only [nb060_alpha_dummy_107] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_095))).fv ∪ ((Class.cv (nb060_alpha_dummy_095))).fv) 0

theorem nb060_fresh_097 (y : Var) (z : Var) : (nb060_alpha_dummy_106 y z) ∉ (((Class.cv (nb060_alpha_dummy_097 y z))).fv ∪ ((Class.cv (nb060_alpha_dummy_097 y z))).fv) := by
  simpa only [nb060_alpha_dummy_106] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_097 y z))).fv ∪ ((Class.cv (nb060_alpha_dummy_097 y z))).fv) 0

theorem nb060_fresh_098 (y : Var) (z : Var) : (nb060_alpha_dummy_102 y z) ∉ (((Class.cv (nb060_alpha_dummy_097 y z))).fv ∪ ((Class.cv (nb060_alpha_dummy_098 y z))).fv) := by
  simpa only [nb060_alpha_dummy_102] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_097 y z))).fv ∪ ((Class.cv (nb060_alpha_dummy_098 y z))).fv) 0

theorem nb060_fresh_099 (y : Var) (z : Var) : (nb060_alpha_dummy_108 y z) ∉ (((Class.cv (nb060_alpha_dummy_098 y z))).fv ∪ ((Class.cv (nb060_alpha_dummy_098 y z))).fv) := by
  simpa only [nb060_alpha_dummy_108] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_098 y z))).fv ∪ ((Class.cv (nb060_alpha_dummy_098 y z))).fv) 0

theorem nb060_fresh_100 : (nb060_alpha_dummy_123) ∉ (((Class.cv (nb060_alpha_dummy_116))).fv) := by
  simpa only [nb060_alpha_dummy_123] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_116))).fv) 0

theorem nb060_fresh_101 : (nb060_alpha_dummy_124) ∉ (((Class.cv (nb060_alpha_dummy_116))).fv) := by
  simpa only [nb060_alpha_dummy_124] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_116))).fv) 1

theorem nb060_distinct_102 : (nb060_alpha_dummy_123) ≠ (nb060_alpha_dummy_124) := by
  simpa only [nb060_alpha_dummy_123, nb060_alpha_dummy_124] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_116))).fv) (i := 0) (j := 1) (by decide))

theorem nb060_fresh_103 (x : Var) (z : Var) : (nb060_alpha_dummy_125 x z) ∉ (((Class.cv (nb060_alpha_dummy_118 x z))).fv) := by
  simpa only [nb060_alpha_dummy_125] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_118 x z))).fv) 0

theorem nb060_fresh_104 (x : Var) (z : Var) : (nb060_alpha_dummy_126 x z) ∉ (((Class.cv (nb060_alpha_dummy_118 x z))).fv) := by
  simpa only [nb060_alpha_dummy_126] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_118 x z))).fv) 1

theorem nb060_distinct_105 (x : Var) (z : Var) : (nb060_alpha_dummy_125 x z) ≠ (nb060_alpha_dummy_126 x z) := by
  simpa only [nb060_alpha_dummy_125, nb060_alpha_dummy_126] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_118 x z))).fv) (i := 0) (j := 1) (by decide))

theorem nb060_fresh_106 : (nb060_alpha_dummy_129) ∉ (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb060_alpha_dummy_129] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv) 0

theorem nb060_fresh_107 : (nb060_alpha_dummy_130) ∉ (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb060_alpha_dummy_130] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv) 1

theorem nb060_fresh_108 : (nb060_alpha_dummy_131) ∉ (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb060_alpha_dummy_131] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv) 2

theorem nb060_distinct_109 : (nb060_alpha_dummy_129) ≠ (nb060_alpha_dummy_130) := by
  simpa only [nb060_alpha_dummy_129, nb060_alpha_dummy_130] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb060_distinct_110 : (nb060_alpha_dummy_129) ≠ (nb060_alpha_dummy_131) := by
  simpa only [nb060_alpha_dummy_129, nb060_alpha_dummy_131] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb060_distinct_111 : (nb060_alpha_dummy_130) ≠ (nb060_alpha_dummy_131) := by
  simpa only [nb060_alpha_dummy_130, nb060_alpha_dummy_131] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_123))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb060_fresh_112 (x : Var) (z : Var) : (nb060_alpha_dummy_132 x z) ∉ (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb060_alpha_dummy_132] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv) 0

theorem nb060_fresh_113 (x : Var) (z : Var) : (nb060_alpha_dummy_133 x z) ∉ (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb060_alpha_dummy_133] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv) 1

theorem nb060_fresh_114 (x : Var) (z : Var) : (nb060_alpha_dummy_134 x z) ∉ (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb060_alpha_dummy_134] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv) 2

theorem nb060_distinct_115 (x : Var) (z : Var) : (nb060_alpha_dummy_132 x z) ≠ (nb060_alpha_dummy_133 x z) := by
  simpa only [nb060_alpha_dummy_132, nb060_alpha_dummy_133] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb060_distinct_116 (x : Var) (z : Var) : (nb060_alpha_dummy_132 x z) ≠ (nb060_alpha_dummy_134 x z) := by
  simpa only [nb060_alpha_dummy_132, nb060_alpha_dummy_134] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb060_distinct_117 (x : Var) (z : Var) : (nb060_alpha_dummy_133 x z) ≠ (nb060_alpha_dummy_134 x z) := by
  simpa only [nb060_alpha_dummy_133, nb060_alpha_dummy_134] using
    (freshVar_injective (((Class.cv (nb060_alpha_dummy_125 x z))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb060_fresh_118 : (nb060_alpha_dummy_141) ∉ (((Class.cv (nb060_alpha_dummy_130))).fv ∪ ((Class.cv (nb060_alpha_dummy_130))).fv) := by
  simpa only [nb060_alpha_dummy_141] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_130))).fv ∪ ((Class.cv (nb060_alpha_dummy_130))).fv) 0

theorem nb060_fresh_119 : (nb060_alpha_dummy_137) ∉ (((Class.cv (nb060_alpha_dummy_130))).fv ∪ ((Class.cv (nb060_alpha_dummy_131))).fv) := by
  simpa only [nb060_alpha_dummy_137] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_130))).fv ∪ ((Class.cv (nb060_alpha_dummy_131))).fv) 0

theorem nb060_fresh_120 : (nb060_alpha_dummy_143) ∉ (((Class.cv (nb060_alpha_dummy_131))).fv ∪ ((Class.cv (nb060_alpha_dummy_131))).fv) := by
  simpa only [nb060_alpha_dummy_143] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_131))).fv ∪ ((Class.cv (nb060_alpha_dummy_131))).fv) 0

theorem nb060_fresh_121 (x : Var) (z : Var) : (nb060_alpha_dummy_142 x z) ∉ (((Class.cv (nb060_alpha_dummy_133 x z))).fv ∪ ((Class.cv (nb060_alpha_dummy_133 x z))).fv) := by
  simpa only [nb060_alpha_dummy_142] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_133 x z))).fv ∪ ((Class.cv (nb060_alpha_dummy_133 x z))).fv) 0

theorem nb060_fresh_122 (x : Var) (z : Var) : (nb060_alpha_dummy_138 x z) ∉ (((Class.cv (nb060_alpha_dummy_133 x z))).fv ∪ ((Class.cv (nb060_alpha_dummy_134 x z))).fv) := by
  simpa only [nb060_alpha_dummy_138] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_133 x z))).fv ∪ ((Class.cv (nb060_alpha_dummy_134 x z))).fv) 0

theorem nb060_fresh_123 (x : Var) (z : Var) : (nb060_alpha_dummy_144 x z) ∉ (((Class.cv (nb060_alpha_dummy_134 x z))).fv ∪ ((Class.cv (nb060_alpha_dummy_134 x z))).fv) := by
  simpa only [nb060_alpha_dummy_144] using freshVar_not_mem (((Class.cv (nb060_alpha_dummy_134 x z))).fv ∪ ((Class.cv (nb060_alpha_dummy_134 x z))).fv) 0

theorem nb060_fresh_124 (r : Var) (a : Var) : (nb060_alpha_dummy_009 r a) ∉ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb060_alpha_dummy_009] using freshVar_not_mem (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 0

theorem nb060_fresh_125 (r : Var) (a : Var) : (nb060_alpha_dummy_010 r a) ∉ (((Class.cv r)).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb060_alpha_dummy_010] using freshVar_not_mem (((Class.cv r)).fv ∪ ((Class.cv a)).fv) 1

theorem nb060_distinct_126 (r : Var) (a : Var) : (nb060_alpha_dummy_009 r a) ≠ (nb060_alpha_dummy_010 r a) := by
  simpa only [nb060_alpha_dummy_009, nb060_alpha_dummy_010] using
    (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (i := 0) (j := 1) (by decide))

theorem nb060_fresh_127 (x : Var) (y : Var) : (nb060_alpha_dummy_045 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb060_alpha_dummy_045] using freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb060_fresh_128 (x : Var) (y : Var) : (nb060_alpha_dummy_046 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb060_alpha_dummy_046] using freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb060_distinct_129 (x : Var) (y : Var) : (nb060_alpha_dummy_045 x y) ≠ (nb060_alpha_dummy_046 x y) := by
  simpa only [nb060_alpha_dummy_045, nb060_alpha_dummy_046] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))

theorem nb060_fresh_130 (x : Var) (z : Var) : (nb060_alpha_dummy_117 x z) ∉ (((Class.cv x)).fv ∪ ((Class.cv z)).fv) := by
  simpa only [nb060_alpha_dummy_117] using freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv z)).fv) 0

theorem nb060_fresh_131 (x : Var) (z : Var) : (nb060_alpha_dummy_118 x z) ∉ (((Class.cv x)).fv ∪ ((Class.cv z)).fv) := by
  simpa only [nb060_alpha_dummy_118] using freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv z)).fv) 1

theorem nb060_distinct_132 (x : Var) (z : Var) : (nb060_alpha_dummy_117 x z) ≠ (nb060_alpha_dummy_118 x z) := by
  simpa only [nb060_alpha_dummy_117, nb060_alpha_dummy_118] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv z)).fv) (i := 0) (j := 1) (by decide))

theorem nb060_fresh_133 (y : Var) (z : Var) : (nb060_alpha_dummy_081 y z) ∉ (((Class.cv y)).fv ∪ ((Class.cv z)).fv) := by
  simpa only [nb060_alpha_dummy_081] using freshVar_not_mem (((Class.cv y)).fv ∪ ((Class.cv z)).fv) 0

theorem nb060_fresh_134 (y : Var) (z : Var) : (nb060_alpha_dummy_082 y z) ∉ (((Class.cv y)).fv ∪ ((Class.cv z)).fv) := by
  simpa only [nb060_alpha_dummy_082] using freshVar_not_mem (((Class.cv y)).fv ∪ ((Class.cv z)).fv) 1

theorem nb060_distinct_135 (y : Var) (z : Var) : (nb060_alpha_dummy_081 y z) ≠ (nb060_alpha_dummy_082 y z) := by
  simpa only [nb060_alpha_dummy_081, nb060_alpha_dummy_082] using
    (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv z)).fv) (i := 0) (j := 1) (by decide))

theorem nb060_fresh_136 : (nb060_alpha_dummy_019) ∉ (((Wff.classMem (Class.cv (nb060_alpha_dummy_015)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb060_alpha_dummy_015)) (syn_c1c))).fv ∪ ((Class.cv (nb060_alpha_dummy_015))).fv) := by
  simpa only [nb060_alpha_dummy_019] using freshVar_not_mem (((Wff.classMem (Class.cv (nb060_alpha_dummy_015)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb060_alpha_dummy_015)) (syn_c1c))).fv ∪ ((Class.cv (nb060_alpha_dummy_015))).fv) 0

theorem nb060_fresh_137 (r : Var) (a : Var) : (nb060_alpha_dummy_020 r a) ∉ (((Wff.classMem (Class.cv (nb060_alpha_dummy_017 r a)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb060_alpha_dummy_017 r a)) (syn_c1c))).fv ∪ ((Class.cv (nb060_alpha_dummy_017 r a))).fv) := by
  simpa only [nb060_alpha_dummy_020] using freshVar_not_mem (((Wff.classMem (Class.cv (nb060_alpha_dummy_017 r a)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb060_alpha_dummy_017 r a)) (syn_c1c))).fv ∪ ((Class.cv (nb060_alpha_dummy_017 r a))).fv) 0

theorem nb060_fresh_138 : (nb060_alpha_dummy_055) ∉ (((Wff.classMem (Class.cv (nb060_alpha_dummy_051)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb060_alpha_dummy_051)) (syn_c1c))).fv ∪ ((Class.cv (nb060_alpha_dummy_051))).fv) := by
  simpa only [nb060_alpha_dummy_055] using freshVar_not_mem (((Wff.classMem (Class.cv (nb060_alpha_dummy_051)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb060_alpha_dummy_051)) (syn_c1c))).fv ∪ ((Class.cv (nb060_alpha_dummy_051))).fv) 0

theorem nb060_fresh_139 (x : Var) (y : Var) : (nb060_alpha_dummy_056 x y) ∉ (((Wff.classMem (Class.cv (nb060_alpha_dummy_053 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb060_alpha_dummy_053 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb060_alpha_dummy_053 x y))).fv) := by
  simpa only [nb060_alpha_dummy_056] using freshVar_not_mem (((Wff.classMem (Class.cv (nb060_alpha_dummy_053 x y)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb060_alpha_dummy_053 x y)) (syn_c1c))).fv ∪ ((Class.cv (nb060_alpha_dummy_053 x y))).fv) 0

theorem nb060_fresh_140 : (nb060_alpha_dummy_091) ∉ (((Wff.classMem (Class.cv (nb060_alpha_dummy_087)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb060_alpha_dummy_087)) (syn_c1c))).fv ∪ ((Class.cv (nb060_alpha_dummy_087))).fv) := by
  simpa only [nb060_alpha_dummy_091] using freshVar_not_mem (((Wff.classMem (Class.cv (nb060_alpha_dummy_087)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb060_alpha_dummy_087)) (syn_c1c))).fv ∪ ((Class.cv (nb060_alpha_dummy_087))).fv) 0

theorem nb060_fresh_141 (y : Var) (z : Var) : (nb060_alpha_dummy_092 y z) ∉ (((Wff.classMem (Class.cv (nb060_alpha_dummy_089 y z)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb060_alpha_dummy_089 y z)) (syn_c1c))).fv ∪ ((Class.cv (nb060_alpha_dummy_089 y z))).fv) := by
  simpa only [nb060_alpha_dummy_092] using freshVar_not_mem (((Wff.classMem (Class.cv (nb060_alpha_dummy_089 y z)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb060_alpha_dummy_089 y z)) (syn_c1c))).fv ∪ ((Class.cv (nb060_alpha_dummy_089 y z))).fv) 0

theorem nb060_fresh_142 : (nb060_alpha_dummy_127) ∉ (((Wff.classMem (Class.cv (nb060_alpha_dummy_123)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb060_alpha_dummy_123)) (syn_c1c))).fv ∪ ((Class.cv (nb060_alpha_dummy_123))).fv) := by
  simpa only [nb060_alpha_dummy_127] using freshVar_not_mem (((Wff.classMem (Class.cv (nb060_alpha_dummy_123)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb060_alpha_dummy_123)) (syn_c1c))).fv ∪ ((Class.cv (nb060_alpha_dummy_123))).fv) 0

theorem nb060_fresh_143 (x : Var) (z : Var) : (nb060_alpha_dummy_128 x z) ∉ (((Wff.classMem (Class.cv (nb060_alpha_dummy_125 x z)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb060_alpha_dummy_125 x z)) (syn_c1c))).fv ∪ ((Class.cv (nb060_alpha_dummy_125 x z))).fv) := by
  simpa only [nb060_alpha_dummy_128] using freshVar_not_mem (((Wff.classMem (Class.cv (nb060_alpha_dummy_125 x z)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb060_alpha_dummy_125 x z)) (syn_c1c))).fv ∪ ((Class.cv (nb060_alpha_dummy_125 x z))).fv) 0

theorem nb060_fresh_144 : (nb060_alpha_dummy_011) ∉ (((syn_ccompl (Class.cab (nb060_alpha_dummy_007) (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_001)) (Wff.classEq (Class.cv (nb060_alpha_dummy_007)) (syn_cphi (Class.cv (nb060_alpha_dummy_008)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_007) (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_000)) (Wff.classEq (Class.cv (nb060_alpha_dummy_007)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_008))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb060_alpha_dummy_011] using freshVar_not_mem (((syn_ccompl (Class.cab (nb060_alpha_dummy_007) (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_001)) (Wff.classEq (Class.cv (nb060_alpha_dummy_007)) (syn_cphi (Class.cv (nb060_alpha_dummy_008)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_007) (syn_wrex (nb060_alpha_dummy_008) (Class.cv (nb060_alpha_dummy_000)) (Wff.classEq (Class.cv (nb060_alpha_dummy_007)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_008))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb060_fresh_145 (r : Var) (a : Var) : (nb060_alpha_dummy_012 r a) ∉ (((syn_ccompl (Class.cab (nb060_alpha_dummy_009 r a) (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv r) (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a)) (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_009 r a) (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv a) (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb060_alpha_dummy_012] using freshVar_not_mem (((syn_ccompl (Class.cab (nb060_alpha_dummy_009 r a) (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv r) (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a)) (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_009 r a) (syn_wrex (nb060_alpha_dummy_010 r a) (Class.cv a) (Wff.classEq (Class.cv (nb060_alpha_dummy_009 r a)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_010 r a))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb060_fresh_146 : (nb060_alpha_dummy_047) ∉ (((syn_ccompl (Class.cab (nb060_alpha_dummy_043) (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_002)) (Wff.classEq (Class.cv (nb060_alpha_dummy_043)) (syn_cphi (Class.cv (nb060_alpha_dummy_044)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_043) (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_003)) (Wff.classEq (Class.cv (nb060_alpha_dummy_043)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_044))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb060_alpha_dummy_047] using freshVar_not_mem (((syn_ccompl (Class.cab (nb060_alpha_dummy_043) (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_002)) (Wff.classEq (Class.cv (nb060_alpha_dummy_043)) (syn_cphi (Class.cv (nb060_alpha_dummy_044)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_043) (syn_wrex (nb060_alpha_dummy_044) (Class.cv (nb060_alpha_dummy_003)) (Wff.classEq (Class.cv (nb060_alpha_dummy_043)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_044))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb060_fresh_147 (x : Var) (y : Var) : (nb060_alpha_dummy_048 x y) ∉ (((syn_ccompl (Class.cab (nb060_alpha_dummy_045 x y) (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv x) (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y)) (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_045 x y) (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv y) (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb060_alpha_dummy_048] using freshVar_not_mem (((syn_ccompl (Class.cab (nb060_alpha_dummy_045 x y) (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv x) (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y)) (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_045 x y) (syn_wrex (nb060_alpha_dummy_046 x y) (Class.cv y) (Wff.classEq (Class.cv (nb060_alpha_dummy_045 x y)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_046 x y))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb060_fresh_148 : (nb060_alpha_dummy_083) ∉ (((syn_ccompl (Class.cab (nb060_alpha_dummy_079) (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_003)) (Wff.classEq (Class.cv (nb060_alpha_dummy_079)) (syn_cphi (Class.cv (nb060_alpha_dummy_080)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_079) (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_004)) (Wff.classEq (Class.cv (nb060_alpha_dummy_079)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_080))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb060_alpha_dummy_083] using freshVar_not_mem (((syn_ccompl (Class.cab (nb060_alpha_dummy_079) (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_003)) (Wff.classEq (Class.cv (nb060_alpha_dummy_079)) (syn_cphi (Class.cv (nb060_alpha_dummy_080)))))))).fv ∪ ((syn_ccompl (Class.cab (nb060_alpha_dummy_079) (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_004)) (Wff.classEq (Class.cv (nb060_alpha_dummy_079)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_080))) (syn_csn (syn_c0c)))))))).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
