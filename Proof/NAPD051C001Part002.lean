import NAPD051C001Part001

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

theorem nb051_fresh_000 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_033 x y A B C) ∉ (((Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C) (Class.cv (nb051_alpha_dummy_000 x y A B C)) (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C)) (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C) (Class.cv (nb051_alpha_dummy_000 x y A B C)) (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C)) (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb051_alpha_dummy_033] using freshVar_not_mem (((Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C) (Class.cv (nb051_alpha_dummy_000 x y A B C)) (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C)) (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C) (Class.cv (nb051_alpha_dummy_000 x y A B C)) (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C)) (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb051_fresh_001 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_009 x y A B C) ∉ (((Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C)) (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))))))).fv ∪ ((Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C)) (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))))))).fv) := by
  simpa only [nb051_alpha_dummy_009] using freshVar_not_mem (((Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C)) (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))))))).fv ∪ ((Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C)) (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))))))).fv) 0

theorem nb051_fresh_002 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_034 x y z) ∉ (((Class.cab (nb051_alpha_dummy_005 x y z) (syn_wrex (nb051_alpha_dummy_006 x y z) (Class.cv z) (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z)) (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb051_alpha_dummy_005 x y z) (syn_wrex (nb051_alpha_dummy_006 x y z) (Class.cv z) (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z)) (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb051_alpha_dummy_034] using freshVar_not_mem (((Class.cab (nb051_alpha_dummy_005 x y z) (syn_wrex (nb051_alpha_dummy_006 x y z) (Class.cv z) (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z)) (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb051_alpha_dummy_005 x y z) (syn_wrex (nb051_alpha_dummy_006 x y z) (Class.cv z) (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z)) (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb051_fresh_003 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_010 x y z) ∉ (((Class.cab (nb051_alpha_dummy_005 x y z) (syn_wrex (nb051_alpha_dummy_006 x y z) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z)) (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))))))).fv ∪ ((Class.cab (nb051_alpha_dummy_005 x y z) (syn_wrex (nb051_alpha_dummy_006 x y z) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z)) (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))))))).fv) := by
  simpa only [nb051_alpha_dummy_010] using freshVar_not_mem (((Class.cab (nb051_alpha_dummy_005 x y z) (syn_wrex (nb051_alpha_dummy_006 x y z) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z)) (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))))))).fv ∪ ((Class.cab (nb051_alpha_dummy_005 x y z) (syn_wrex (nb051_alpha_dummy_006 x y z) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z)) (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))))))).fv) 0

theorem nb051_fresh_004 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_011 x y A B C) ∉ (((Class.cv (nb051_alpha_dummy_004 x y A B C))).fv) := by
  simpa only [nb051_alpha_dummy_011] using freshVar_not_mem (((Class.cv (nb051_alpha_dummy_004 x y A B C))).fv) 0

theorem nb051_fresh_005 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_012 x y A B C) ∉ (((Class.cv (nb051_alpha_dummy_004 x y A B C))).fv) := by
  simpa only [nb051_alpha_dummy_012] using freshVar_not_mem (((Class.cv (nb051_alpha_dummy_004 x y A B C))).fv) 1

theorem nb051_distinct_006 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_011 x y A B C) ≠ (nb051_alpha_dummy_012 x y A B C) := by
  simpa only [nb051_alpha_dummy_011, nb051_alpha_dummy_012] using
    (freshVar_injective (((Class.cv (nb051_alpha_dummy_004 x y A B C))).fv) (i := 0) (j := 1) (by decide))

theorem nb051_fresh_007 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_013 x y z) ∉ (((Class.cv (nb051_alpha_dummy_006 x y z))).fv) := by
  simpa only [nb051_alpha_dummy_013] using freshVar_not_mem (((Class.cv (nb051_alpha_dummy_006 x y z))).fv) 0

theorem nb051_fresh_008 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_014 x y z) ∉ (((Class.cv (nb051_alpha_dummy_006 x y z))).fv) := by
  simpa only [nb051_alpha_dummy_014] using freshVar_not_mem (((Class.cv (nb051_alpha_dummy_006 x y z))).fv) 1

theorem nb051_distinct_009 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_013 x y z) ≠ (nb051_alpha_dummy_014 x y z) := by
  simpa only [nb051_alpha_dummy_013, nb051_alpha_dummy_014] using
    (freshVar_injective (((Class.cv (nb051_alpha_dummy_006 x y z))).fv) (i := 0) (j := 1) (by decide))

theorem nb051_fresh_010 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_017 x y A B C) ∉ (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb051_alpha_dummy_017] using freshVar_not_mem (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪ ((syn_c1c)).fv) 0

theorem nb051_fresh_011 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_018 x y A B C) ∉ (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb051_alpha_dummy_018] using freshVar_not_mem (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪ ((syn_c1c)).fv) 1

theorem nb051_fresh_012 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_019 x y A B C) ∉ (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb051_alpha_dummy_019] using freshVar_not_mem (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪ ((syn_c1c)).fv) 2

theorem nb051_distinct_013 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_017 x y A B C) ≠ (nb051_alpha_dummy_018 x y A B C) := by
  simpa only [nb051_alpha_dummy_017, nb051_alpha_dummy_018] using
    (freshVar_injective (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb051_distinct_014 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_017 x y A B C) ≠ (nb051_alpha_dummy_019 x y A B C) := by
  simpa only [nb051_alpha_dummy_017, nb051_alpha_dummy_019] using
    (freshVar_injective (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb051_distinct_015 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_018 x y A B C) ≠ (nb051_alpha_dummy_019 x y A B C) := by
  simpa only [nb051_alpha_dummy_018, nb051_alpha_dummy_019] using
    (freshVar_injective (((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb051_fresh_016 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_020 x y z) ∉ (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb051_alpha_dummy_020] using freshVar_not_mem (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪ ((syn_c1c)).fv) 0

theorem nb051_fresh_017 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_021 x y z) ∉ (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb051_alpha_dummy_021] using freshVar_not_mem (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪ ((syn_c1c)).fv) 1

theorem nb051_fresh_018 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_022 x y z) ∉ (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb051_alpha_dummy_022] using freshVar_not_mem (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪ ((syn_c1c)).fv) 2

theorem nb051_distinct_019 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_020 x y z) ≠ (nb051_alpha_dummy_021 x y z) := by
  simpa only [nb051_alpha_dummy_020, nb051_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb051_distinct_020 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_020 x y z) ≠ (nb051_alpha_dummy_022 x y z) := by
  simpa only [nb051_alpha_dummy_020, nb051_alpha_dummy_022] using
    (freshVar_injective (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb051_distinct_021 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_021 x y z) ≠ (nb051_alpha_dummy_022 x y z) := by
  simpa only [nb051_alpha_dummy_021, nb051_alpha_dummy_022] using
    (freshVar_injective (((Class.cv (nb051_alpha_dummy_013 x y z))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb051_fresh_022 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_029 x y A B C) ∉ (((Class.cv (nb051_alpha_dummy_018 x y A B C))).fv ∪ ((Class.cv (nb051_alpha_dummy_018 x y A B C))).fv) := by
  simpa only [nb051_alpha_dummy_029] using freshVar_not_mem (((Class.cv (nb051_alpha_dummy_018 x y A B C))).fv ∪ ((Class.cv (nb051_alpha_dummy_018 x y A B C))).fv) 0

theorem nb051_fresh_023 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_025 x y A B C) ∉ (((Class.cv (nb051_alpha_dummy_018 x y A B C))).fv ∪ ((Class.cv (nb051_alpha_dummy_019 x y A B C))).fv) := by
  simpa only [nb051_alpha_dummy_025] using freshVar_not_mem (((Class.cv (nb051_alpha_dummy_018 x y A B C))).fv ∪ ((Class.cv (nb051_alpha_dummy_019 x y A B C))).fv) 0

theorem nb051_fresh_024 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_031 x y A B C) ∉ (((Class.cv (nb051_alpha_dummy_019 x y A B C))).fv ∪ ((Class.cv (nb051_alpha_dummy_019 x y A B C))).fv) := by
  simpa only [nb051_alpha_dummy_031] using freshVar_not_mem (((Class.cv (nb051_alpha_dummy_019 x y A B C))).fv ∪ ((Class.cv (nb051_alpha_dummy_019 x y A B C))).fv) 0

theorem nb051_fresh_025 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_030 x y z) ∉ (((Class.cv (nb051_alpha_dummy_021 x y z))).fv ∪ ((Class.cv (nb051_alpha_dummy_021 x y z))).fv) := by
  simpa only [nb051_alpha_dummy_030] using freshVar_not_mem (((Class.cv (nb051_alpha_dummy_021 x y z))).fv ∪ ((Class.cv (nb051_alpha_dummy_021 x y z))).fv) 0

theorem nb051_fresh_026 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_026 x y z) ∉ (((Class.cv (nb051_alpha_dummy_021 x y z))).fv ∪ ((Class.cv (nb051_alpha_dummy_022 x y z))).fv) := by
  simpa only [nb051_alpha_dummy_026] using freshVar_not_mem (((Class.cv (nb051_alpha_dummy_021 x y z))).fv ∪ ((Class.cv (nb051_alpha_dummy_022 x y z))).fv) 0

theorem nb051_fresh_027 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_032 x y z) ∉ (((Class.cv (nb051_alpha_dummy_022 x y z))).fv ∪ ((Class.cv (nb051_alpha_dummy_022 x y z))).fv) := by
  simpa only [nb051_alpha_dummy_032] using freshVar_not_mem (((Class.cv (nb051_alpha_dummy_022 x y z))).fv ∪ ((Class.cv (nb051_alpha_dummy_022 x y z))).fv) 0

theorem nb051_fresh_028 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_015 x y A B C) ∉ (((Wff.classMem (Class.cv (nb051_alpha_dummy_011 x y A B C)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb051_alpha_dummy_011 x y A B C)) (syn_c1c))).fv ∪ ((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv) := by
  simpa only [nb051_alpha_dummy_015] using freshVar_not_mem (((Wff.classMem (Class.cv (nb051_alpha_dummy_011 x y A B C)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb051_alpha_dummy_011 x y A B C)) (syn_c1c))).fv ∪ ((Class.cv (nb051_alpha_dummy_011 x y A B C))).fv) 0

theorem nb051_fresh_029 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_016 x y z) ∉ (((Wff.classMem (Class.cv (nb051_alpha_dummy_013 x y z)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb051_alpha_dummy_013 x y z)) (syn_c1c))).fv ∪ ((Class.cv (nb051_alpha_dummy_013 x y z))).fv) := by
  simpa only [nb051_alpha_dummy_016] using freshVar_not_mem (((Wff.classMem (Class.cv (nb051_alpha_dummy_013 x y z)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb051_alpha_dummy_013 x y z)) (syn_c1c))).fv ∪ ((Class.cv (nb051_alpha_dummy_013 x y z))).fv) 0

theorem nb051_fresh_030 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_007 x y A B C) ∉ (((syn_ccompl (Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C)) (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))))))).fv ∪ ((syn_ccompl (Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C) (Class.cv (nb051_alpha_dummy_000 x y A B C)) (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C)) (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb051_alpha_dummy_007] using freshVar_not_mem (((syn_ccompl (Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C)) (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))))))).fv ∪ ((syn_ccompl (Class.cab (nb051_alpha_dummy_003 x y A B C) (syn_wrex (nb051_alpha_dummy_004 x y A B C) (Class.cv (nb051_alpha_dummy_000 x y A B C)) (Wff.classEq (Class.cv (nb051_alpha_dummy_003 x y A B C)) (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb051_fresh_031 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_008 x y z) ∉ (((syn_ccompl (Class.cab (nb051_alpha_dummy_005 x y z) (syn_wrex (nb051_alpha_dummy_006 x y z) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z)) (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))))))).fv ∪ ((syn_ccompl (Class.cab (nb051_alpha_dummy_005 x y z) (syn_wrex (nb051_alpha_dummy_006 x y z) (Class.cv z) (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z)) (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb051_alpha_dummy_008] using freshVar_not_mem (((syn_ccompl (Class.cab (nb051_alpha_dummy_005 x y z) (syn_wrex (nb051_alpha_dummy_006 x y z) (syn_cop (Class.cv x) (Class.cv y)) (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z)) (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))))))).fv ∪ ((syn_ccompl (Class.cab (nb051_alpha_dummy_005 x y z) (syn_wrex (nb051_alpha_dummy_006 x y z) (Class.cv z) (Wff.classEq (Class.cv (nb051_alpha_dummy_005 x y z)) (syn_cun (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb051_fresh_032 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_027 x y A B C) ∉ (((syn_ccompl (Class.cv (nb051_alpha_dummy_018 x y A B C)))).fv ∪ ((syn_ccompl (Class.cv (nb051_alpha_dummy_019 x y A B C)))).fv) := by
  simpa only [nb051_alpha_dummy_027] using freshVar_not_mem (((syn_ccompl (Class.cv (nb051_alpha_dummy_018 x y A B C)))).fv ∪ ((syn_ccompl (Class.cv (nb051_alpha_dummy_019 x y A B C)))).fv) 0

theorem nb051_fresh_033 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_028 x y z) ∉ (((syn_ccompl (Class.cv (nb051_alpha_dummy_021 x y z)))).fv ∪ ((syn_ccompl (Class.cv (nb051_alpha_dummy_022 x y z)))).fv) := by
  simpa only [nb051_alpha_dummy_028] using freshVar_not_mem (((syn_ccompl (Class.cv (nb051_alpha_dummy_021 x y z)))).fv ∪ ((syn_ccompl (Class.cv (nb051_alpha_dummy_022 x y z)))).fv) 0

theorem nb051_fresh_034 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_035 x y A B C) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb051_alpha_dummy_035] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb051_fresh_035 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_036 x y z) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb051_alpha_dummy_036] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb051_fresh_036 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_023 x y A B C) ∉ (((syn_cnin (Class.cv (nb051_alpha_dummy_018 x y A B C)) (Class.cv (nb051_alpha_dummy_019 x y A B C)))).fv ∪ ((syn_cnin (Class.cv (nb051_alpha_dummy_018 x y A B C)) (Class.cv (nb051_alpha_dummy_019 x y A B C)))).fv) := by
  simpa only [nb051_alpha_dummy_023] using freshVar_not_mem (((syn_cnin (Class.cv (nb051_alpha_dummy_018 x y A B C)) (Class.cv (nb051_alpha_dummy_019 x y A B C)))).fv ∪ ((syn_cnin (Class.cv (nb051_alpha_dummy_018 x y A B C)) (Class.cv (nb051_alpha_dummy_019 x y A B C)))).fv) 0

theorem nb051_fresh_037 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_024 x y z) ∉ (((syn_cnin (Class.cv (nb051_alpha_dummy_021 x y z)) (Class.cv (nb051_alpha_dummy_022 x y z)))).fv ∪ ((syn_cnin (Class.cv (nb051_alpha_dummy_021 x y z)) (Class.cv (nb051_alpha_dummy_022 x y z)))).fv) := by
  simpa only [nb051_alpha_dummy_024] using freshVar_not_mem (((syn_cnin (Class.cv (nb051_alpha_dummy_021 x y z)) (Class.cv (nb051_alpha_dummy_022 x y z)))).fv ∪ ((syn_cnin (Class.cv (nb051_alpha_dummy_021 x y z)) (Class.cv (nb051_alpha_dummy_022 x y z)))).fv) 0

theorem nb051_fresh_038 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_003 x y A B C) ∉ (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb051_alpha_dummy_000 x y A B C))).fv) := by
  simpa only [nb051_alpha_dummy_003] using freshVar_not_mem (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb051_alpha_dummy_000 x y A B C))).fv) 0

theorem nb051_fresh_039 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_004 x y A B C) ∉ (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb051_alpha_dummy_000 x y A B C))).fv) := by
  simpa only [nb051_alpha_dummy_004] using freshVar_not_mem (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb051_alpha_dummy_000 x y A B C))).fv) 1

theorem nb051_distinct_040 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_003 x y A B C) ≠ (nb051_alpha_dummy_004 x y A B C) := by
  simpa only [nb051_alpha_dummy_003, nb051_alpha_dummy_004] using
    (freshVar_injective (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb051_alpha_dummy_000 x y A B C))).fv) (i := 0) (j := 1) (by decide))

theorem nb051_fresh_041 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_005 x y z) ∉ (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv z)).fv) := by
  simpa only [nb051_alpha_dummy_005] using freshVar_not_mem (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv z)).fv) 0

theorem nb051_fresh_042 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_006 x y z) ∉ (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv z)).fv) := by
  simpa only [nb051_alpha_dummy_006] using freshVar_not_mem (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv z)).fv) 1

theorem nb051_distinct_043 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_005 x y z) ≠ (nb051_alpha_dummy_006 x y z) := by
  simpa only [nb051_alpha_dummy_005, nb051_alpha_dummy_006] using
    (freshVar_injective (((syn_cop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv z)).fv) (i := 0) (j := 1) (by decide))

theorem nb051_fresh_044 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_037 x y A B C) ∉ (((syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))).fv ∪ ((syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))).fv) := by
  simpa only [nb051_alpha_dummy_037] using freshVar_not_mem (((syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))).fv ∪ ((syn_cphi (Class.cv (nb051_alpha_dummy_004 x y A B C)))).fv) 0

theorem nb051_fresh_045 (x : Var) (y : Var) (z : Var) : (nb051_alpha_dummy_038 x y z) ∉ (((syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))).fv ∪ ((syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))).fv) := by
  simpa only [nb051_alpha_dummy_038] using freshVar_not_mem (((syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))).fv ∪ ((syn_cphi (Class.cv (nb051_alpha_dummy_006 x y z)))).fv) 0

theorem nb051_fresh_046 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_000 x y A B C) ∉ (({x} : Finset Var) ∪ (A).fv ∪ ({y} : Finset Var) ∪ (B).fv ∪ (C).fv) := by
  simpa only [nb051_alpha_dummy_000] using freshVar_not_mem (({x} : Finset Var) ∪ (A).fv ∪ ({y} : Finset Var) ∪ (B).fv ∪ (C).fv) 0

theorem nb051_fresh_047 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_001 x y A B C) ∉ (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({(nb051_alpha_dummy_000 x y A B C)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B)) (Wff.classEq (Class.cv (nb051_alpha_dummy_000 x y A B C)) C))).fv) := by
  simpa only [nb051_alpha_dummy_001] using freshVar_not_mem (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({(nb051_alpha_dummy_000 x y A B C)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B)) (Wff.classEq (Class.cv (nb051_alpha_dummy_000 x y A B C)) C))).fv) 0

theorem nb051_fresh_048 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) : (nb051_alpha_dummy_002 x y z A B C) ∉ (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B)) (Wff.classEq (Class.cv z) C))).fv) := by
  simpa only [nb051_alpha_dummy_002] using freshVar_not_mem (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({z} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B)) (Wff.classEq (Class.cv z) C))).fv) 0

theorem nb051_support_mem_0000 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class) : x ∈ (({x} : Finset Var) ∪ ({y} : Finset Var) ∪ ({(nb051_alpha_dummy_000 x y A B C)} : Finset Var) ∪ ((syn_wa (syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B)) (Wff.classEq (Class.cv (nb051_alpha_dummy_000 x y A B C)) C))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
