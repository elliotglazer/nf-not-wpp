import NAR5H088P001Part001

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

theorem nb088_fresh_069 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_010 u A B C R) ∉ (((syn_ccompl (Class.cab (nb088_alpha_dummy_007 u A B C R) (syn_wrex (nb088_alpha_dummy_008 u A B C R) (Class.cv u) (Wff.classEq (Class.cv (nb088_alpha_dummy_007 u A B C R)) (syn_cphi (Class.cv (nb088_alpha_dummy_008 u A B C R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb088_alpha_dummy_007 u A B C R) (syn_wrex (nb088_alpha_dummy_008 u A B C R) (Class.cv (nb088_alpha_dummy_002 u A B C R)) (Wff.classEq (Class.cv (nb088_alpha_dummy_007 u A B C R)) (syn_cun (syn_cphi (Class.cv (nb088_alpha_dummy_008 u A B C R))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb088_alpha_dummy_010] using freshVar_not_mem (((syn_ccompl (Class.cab (nb088_alpha_dummy_007 u A B C R) (syn_wrex (nb088_alpha_dummy_008 u A B C R) (Class.cv u) (Wff.classEq (Class.cv (nb088_alpha_dummy_007 u A B C R)) (syn_cphi (Class.cv (nb088_alpha_dummy_008 u A B C R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb088_alpha_dummy_007 u A B C R) (syn_wrex (nb088_alpha_dummy_008 u A B C R) (Class.cv (nb088_alpha_dummy_002 u A B C R)) (Wff.classEq (Class.cv (nb088_alpha_dummy_007 u A B C R)) (syn_cun (syn_cphi (Class.cv (nb088_alpha_dummy_008 u A B C R))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb088_fresh_070 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_047 A B C R) ∉ (((syn_ccompl (Class.cab (nb088_alpha_dummy_043 A B C R) (syn_wrex (nb088_alpha_dummy_044 A B C R) (syn_csn (Class.cv (nb088_alpha_dummy_041 A B C R))) (Wff.classEq (Class.cv (nb088_alpha_dummy_043 A B C R)) (syn_cphi (Class.cv (nb088_alpha_dummy_044 A B C R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb088_alpha_dummy_043 A B C R) (syn_wrex (nb088_alpha_dummy_044 A B C R) (Class.cv (nb088_alpha_dummy_000 A B C R)) (Wff.classEq (Class.cv (nb088_alpha_dummy_043 A B C R)) (syn_cun (syn_cphi (Class.cv (nb088_alpha_dummy_044 A B C R))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb088_alpha_dummy_047] using freshVar_not_mem (((syn_ccompl (Class.cab (nb088_alpha_dummy_043 A B C R) (syn_wrex (nb088_alpha_dummy_044 A B C R) (syn_csn (Class.cv (nb088_alpha_dummy_041 A B C R))) (Wff.classEq (Class.cv (nb088_alpha_dummy_043 A B C R)) (syn_cphi (Class.cv (nb088_alpha_dummy_044 A B C R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb088_alpha_dummy_043 A B C R) (syn_wrex (nb088_alpha_dummy_044 A B C R) (Class.cv (nb088_alpha_dummy_000 A B C R)) (Wff.classEq (Class.cv (nb088_alpha_dummy_043 A B C R)) (syn_cun (syn_cphi (Class.cv (nb088_alpha_dummy_044 A B C R))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb088_fresh_071 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_048 u A B R) ∉ (((syn_ccompl (Class.cab (nb088_alpha_dummy_045 u A B R) (syn_wrex (nb088_alpha_dummy_046 u A B R) (syn_csn (Class.cv (nb088_alpha_dummy_042 u A B R))) (Wff.classEq (Class.cv (nb088_alpha_dummy_045 u A B R)) (syn_cphi (Class.cv (nb088_alpha_dummy_046 u A B R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb088_alpha_dummy_045 u A B R) (syn_wrex (nb088_alpha_dummy_046 u A B R) (Class.cv u) (Wff.classEq (Class.cv (nb088_alpha_dummy_045 u A B R)) (syn_cun (syn_cphi (Class.cv (nb088_alpha_dummy_046 u A B R))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb088_alpha_dummy_048] using freshVar_not_mem (((syn_ccompl (Class.cab (nb088_alpha_dummy_045 u A B R) (syn_wrex (nb088_alpha_dummy_046 u A B R) (syn_csn (Class.cv (nb088_alpha_dummy_042 u A B R))) (Wff.classEq (Class.cv (nb088_alpha_dummy_045 u A B R)) (syn_cphi (Class.cv (nb088_alpha_dummy_046 u A B R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb088_alpha_dummy_045 u A B R) (syn_wrex (nb088_alpha_dummy_046 u A B R) (Class.cv u) (Wff.classEq (Class.cv (nb088_alpha_dummy_045 u A B R)) (syn_cun (syn_cphi (Class.cv (nb088_alpha_dummy_046 u A B R))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb088_fresh_072 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_029 A B C R) ∉ (((syn_ccompl (Class.cv (nb088_alpha_dummy_020 A B C R)))).fv ∪ ((syn_ccompl (Class.cv (nb088_alpha_dummy_021 A B C R)))).fv) := by
  simpa only [nb088_alpha_dummy_029] using freshVar_not_mem (((syn_ccompl (Class.cv (nb088_alpha_dummy_020 A B C R)))).fv ∪ ((syn_ccompl (Class.cv (nb088_alpha_dummy_021 A B C R)))).fv) 0

theorem nb088_fresh_073 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_030 u A B C R) ∉ (((syn_ccompl (Class.cv (nb088_alpha_dummy_023 u A B C R)))).fv ∪ ((syn_ccompl (Class.cv (nb088_alpha_dummy_024 u A B C R)))).fv) := by
  simpa only [nb088_alpha_dummy_030] using freshVar_not_mem (((syn_ccompl (Class.cv (nb088_alpha_dummy_023 u A B C R)))).fv ∪ ((syn_ccompl (Class.cv (nb088_alpha_dummy_024 u A B C R)))).fv) 0

theorem nb088_fresh_074 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_069 A B C R) ∉ (((syn_ccompl (Class.cv (nb088_alpha_dummy_060 A B C R)))).fv ∪ ((syn_ccompl (Class.cv (nb088_alpha_dummy_061 A B C R)))).fv) := by
  simpa only [nb088_alpha_dummy_069] using freshVar_not_mem (((syn_ccompl (Class.cv (nb088_alpha_dummy_060 A B C R)))).fv ∪ ((syn_ccompl (Class.cv (nb088_alpha_dummy_061 A B C R)))).fv) 0

theorem nb088_fresh_075 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_070 u A B R) ∉ (((syn_ccompl (Class.cv (nb088_alpha_dummy_063 u A B R)))).fv ∪ ((syn_ccompl (Class.cv (nb088_alpha_dummy_064 u A B R)))).fv) := by
  simpa only [nb088_alpha_dummy_070] using freshVar_not_mem (((syn_ccompl (Class.cv (nb088_alpha_dummy_063 u A B R)))).fv ∪ ((syn_ccompl (Class.cv (nb088_alpha_dummy_064 u A B R)))).fv) 0

theorem nb088_fresh_076 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_037 A B C R) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb088_alpha_dummy_006 A B C R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb088_alpha_dummy_037] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb088_alpha_dummy_006 A B C R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb088_fresh_077 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_038 u A B C R) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb088_alpha_dummy_008 u A B C R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb088_alpha_dummy_038] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb088_alpha_dummy_008 u A B C R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb088_fresh_078 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_077 A B C R) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb088_alpha_dummy_044 A B C R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb088_alpha_dummy_077] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb088_alpha_dummy_044 A B C R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb088_fresh_079 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_078 u A B R) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb088_alpha_dummy_046 u A B R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb088_alpha_dummy_078] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb088_alpha_dummy_046 u A B R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb088_fresh_080 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_025 A B C R) ∉ (((syn_cnin (Class.cv (nb088_alpha_dummy_020 A B C R)) (Class.cv (nb088_alpha_dummy_021 A B C R)))).fv ∪ ((syn_cnin (Class.cv (nb088_alpha_dummy_020 A B C R)) (Class.cv (nb088_alpha_dummy_021 A B C R)))).fv) := by
  simpa only [nb088_alpha_dummy_025] using freshVar_not_mem (((syn_cnin (Class.cv (nb088_alpha_dummy_020 A B C R)) (Class.cv (nb088_alpha_dummy_021 A B C R)))).fv ∪ ((syn_cnin (Class.cv (nb088_alpha_dummy_020 A B C R)) (Class.cv (nb088_alpha_dummy_021 A B C R)))).fv) 0

theorem nb088_fresh_081 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_026 u A B C R) ∉ (((syn_cnin (Class.cv (nb088_alpha_dummy_023 u A B C R)) (Class.cv (nb088_alpha_dummy_024 u A B C R)))).fv ∪ ((syn_cnin (Class.cv (nb088_alpha_dummy_023 u A B C R)) (Class.cv (nb088_alpha_dummy_024 u A B C R)))).fv) := by
  simpa only [nb088_alpha_dummy_026] using freshVar_not_mem (((syn_cnin (Class.cv (nb088_alpha_dummy_023 u A B C R)) (Class.cv (nb088_alpha_dummy_024 u A B C R)))).fv ∪ ((syn_cnin (Class.cv (nb088_alpha_dummy_023 u A B C R)) (Class.cv (nb088_alpha_dummy_024 u A B C R)))).fv) 0

theorem nb088_fresh_082 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_065 A B C R) ∉ (((syn_cnin (Class.cv (nb088_alpha_dummy_060 A B C R)) (Class.cv (nb088_alpha_dummy_061 A B C R)))).fv ∪ ((syn_cnin (Class.cv (nb088_alpha_dummy_060 A B C R)) (Class.cv (nb088_alpha_dummy_061 A B C R)))).fv) := by
  simpa only [nb088_alpha_dummy_065] using freshVar_not_mem (((syn_cnin (Class.cv (nb088_alpha_dummy_060 A B C R)) (Class.cv (nb088_alpha_dummy_061 A B C R)))).fv ∪ ((syn_cnin (Class.cv (nb088_alpha_dummy_060 A B C R)) (Class.cv (nb088_alpha_dummy_061 A B C R)))).fv) 0

theorem nb088_fresh_083 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_066 u A B R) ∉ (((syn_cnin (Class.cv (nb088_alpha_dummy_063 u A B R)) (Class.cv (nb088_alpha_dummy_064 u A B R)))).fv ∪ ((syn_cnin (Class.cv (nb088_alpha_dummy_063 u A B R)) (Class.cv (nb088_alpha_dummy_064 u A B R)))).fv) := by
  simpa only [nb088_alpha_dummy_066] using freshVar_not_mem (((syn_cnin (Class.cv (nb088_alpha_dummy_063 u A B R)) (Class.cv (nb088_alpha_dummy_064 u A B R)))).fv ∪ ((syn_cnin (Class.cv (nb088_alpha_dummy_063 u A B R)) (Class.cv (nb088_alpha_dummy_064 u A B R)))).fv) 0

theorem nb088_fresh_084 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_039 A B C R) ∉ (((syn_cphi (Class.cv (nb088_alpha_dummy_006 A B C R)))).fv ∪ ((syn_cphi (Class.cv (nb088_alpha_dummy_006 A B C R)))).fv) := by
  simpa only [nb088_alpha_dummy_039] using freshVar_not_mem (((syn_cphi (Class.cv (nb088_alpha_dummy_006 A B C R)))).fv ∪ ((syn_cphi (Class.cv (nb088_alpha_dummy_006 A B C R)))).fv) 0

theorem nb088_fresh_085 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_040 u A B C R) ∉ (((syn_cphi (Class.cv (nb088_alpha_dummy_008 u A B C R)))).fv ∪ ((syn_cphi (Class.cv (nb088_alpha_dummy_008 u A B C R)))).fv) := by
  simpa only [nb088_alpha_dummy_040] using freshVar_not_mem (((syn_cphi (Class.cv (nb088_alpha_dummy_008 u A B C R)))).fv ∪ ((syn_cphi (Class.cv (nb088_alpha_dummy_008 u A B C R)))).fv) 0

theorem nb088_fresh_086 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_079 A B C R) ∉ (((syn_cphi (Class.cv (nb088_alpha_dummy_044 A B C R)))).fv ∪ ((syn_cphi (Class.cv (nb088_alpha_dummy_044 A B C R)))).fv) := by
  simpa only [nb088_alpha_dummy_079] using freshVar_not_mem (((syn_cphi (Class.cv (nb088_alpha_dummy_044 A B C R)))).fv ∪ ((syn_cphi (Class.cv (nb088_alpha_dummy_044 A B C R)))).fv) 0

theorem nb088_fresh_087 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_080 u A B R) ∉ (((syn_cphi (Class.cv (nb088_alpha_dummy_046 u A B R)))).fv ∪ ((syn_cphi (Class.cv (nb088_alpha_dummy_046 u A B R)))).fv) := by
  simpa only [nb088_alpha_dummy_080] using freshVar_not_mem (((syn_cphi (Class.cv (nb088_alpha_dummy_046 u A B R)))).fv ∪ ((syn_cphi (Class.cv (nb088_alpha_dummy_046 u A B R)))).fv) 0

theorem nb088_fresh_088 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_043 A B C R) ∉ (((syn_csn (Class.cv (nb088_alpha_dummy_041 A B C R)))).fv ∪ ((Class.cv (nb088_alpha_dummy_000 A B C R))).fv) := by
  simpa only [nb088_alpha_dummy_043] using freshVar_not_mem (((syn_csn (Class.cv (nb088_alpha_dummy_041 A B C R)))).fv ∪ ((Class.cv (nb088_alpha_dummy_000 A B C R))).fv) 0

theorem nb088_fresh_089 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_044 A B C R) ∉ (((syn_csn (Class.cv (nb088_alpha_dummy_041 A B C R)))).fv ∪ ((Class.cv (nb088_alpha_dummy_000 A B C R))).fv) := by
  simpa only [nb088_alpha_dummy_044] using freshVar_not_mem (((syn_csn (Class.cv (nb088_alpha_dummy_041 A B C R)))).fv ∪ ((Class.cv (nb088_alpha_dummy_000 A B C R))).fv) 1

theorem nb088_distinct_090 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_043 A B C R) ≠ (nb088_alpha_dummy_044 A B C R) := by
  simpa only [nb088_alpha_dummy_043, nb088_alpha_dummy_044] using
    (freshVar_injective (((syn_csn (Class.cv (nb088_alpha_dummy_041 A B C R)))).fv ∪ ((Class.cv (nb088_alpha_dummy_000 A B C R))).fv) (i := 0) (j := 1) (by decide))

theorem nb088_fresh_091 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_045 u A B R) ∉ (((syn_csn (Class.cv (nb088_alpha_dummy_042 u A B R)))).fv ∪ ((Class.cv u)).fv) := by
  simpa only [nb088_alpha_dummy_045] using freshVar_not_mem (((syn_csn (Class.cv (nb088_alpha_dummy_042 u A B R)))).fv ∪ ((Class.cv u)).fv) 0

theorem nb088_fresh_092 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_046 u A B R) ∉ (((syn_csn (Class.cv (nb088_alpha_dummy_042 u A B R)))).fv ∪ ((Class.cv u)).fv) := by
  simpa only [nb088_alpha_dummy_046] using freshVar_not_mem (((syn_csn (Class.cv (nb088_alpha_dummy_042 u A B R)))).fv ∪ ((Class.cv u)).fv) 1

theorem nb088_distinct_093 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_045 u A B R) ≠ (nb088_alpha_dummy_046 u A B R) := by
  simpa only [nb088_alpha_dummy_045, nb088_alpha_dummy_046] using
    (freshVar_injective (((syn_csn (Class.cv (nb088_alpha_dummy_042 u A B R)))).fv ∪ ((Class.cv u)).fv) (i := 0) (j := 1) (by decide))

theorem nb088_fresh_094 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_041 A B C R) ∉ ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb088_alpha_dummy_000 A B C R))).fv) := by
  simpa only [nb088_alpha_dummy_041] using freshVar_not_mem ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb088_alpha_dummy_000 A B C R))).fv) 0

theorem nb088_fresh_095 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_042 u A B R) ∉ ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv u)).fv) := by
  simpa only [nb088_alpha_dummy_042] using freshVar_not_mem ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv u)).fv) 0

theorem nb088_fresh_096 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_000 A B C R) ∉ ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) := by
  simpa only [nb088_alpha_dummy_000] using freshVar_not_mem ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0

theorem nb088_fresh_097 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_001 A B C R) ∉ (({(nb088_alpha_dummy_000 A B C R)} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 C))).fv ∪ ((syn_cfdrowfib R A B (Class.cv (nb088_alpha_dummy_000 A B C R)))).fv) := by
  simpa only [nb088_alpha_dummy_001] using freshVar_not_mem (({(nb088_alpha_dummy_000 A B C R)} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 C))).fv ∪ ((syn_cfdrowfib R A B (Class.cv (nb088_alpha_dummy_000 A B C R)))).fv) 0

theorem nb088_fresh_098 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_003 A B C R) ∉ (({(nb088_alpha_dummy_000 A B C R)} : Finset Var) ∪ ({(nb088_alpha_dummy_001 A B C R)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb088_alpha_dummy_000 A B C R)) (syn_cpw1 (syn_cpw1 C))) (Wff.classEq (Class.cv (nb088_alpha_dummy_001 A B C R)) (syn_cfdrowfib R A B (Class.cv (nb088_alpha_dummy_000 A B C R)))))).fv) := by
  simpa only [nb088_alpha_dummy_003] using freshVar_not_mem (({(nb088_alpha_dummy_000 A B C R)} : Finset Var) ∪ ({(nb088_alpha_dummy_001 A B C R)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb088_alpha_dummy_000 A B C R)) (syn_cpw1 (syn_cpw1 C))) (Wff.classEq (Class.cv (nb088_alpha_dummy_001 A B C R)) (syn_cfdrowfib R A B (Class.cv (nb088_alpha_dummy_000 A B C R)))))).fv) 0

theorem nb088_fresh_099 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_002 u A B C R) ∉ (({u} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 C))).fv ∪ ((syn_cfdrowfib R A B (Class.cv u))).fv) := by
  simpa only [nb088_alpha_dummy_002] using freshVar_not_mem (({u} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 C))).fv ∪ ((syn_cfdrowfib R A B (Class.cv u))).fv) 0

theorem nb088_fresh_100 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_004 u A B C R) ∉ (({u} : Finset Var) ∪ ({(nb088_alpha_dummy_002 u A B C R)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv u) (syn_cpw1 (syn_cpw1 C))) (Wff.classEq (Class.cv (nb088_alpha_dummy_002 u A B C R)) (syn_cfdrowfib R A B (Class.cv u))))).fv) := by
  simpa only [nb088_alpha_dummy_004] using freshVar_not_mem (({u} : Finset Var) ∪ ({(nb088_alpha_dummy_002 u A B C R)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv u) (syn_cpw1 (syn_cpw1 C))) (Wff.classEq (Class.cv (nb088_alpha_dummy_002 u A B C R)) (syn_cfdrowfib R A B (Class.cv u))))).fv) 0

theorem nb088_support_mem_0000 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_000 A B C R) ∈ (({(nb088_alpha_dummy_000 A B C R)} : Finset Var) ∪ ({(nb088_alpha_dummy_001 A B C R)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb088_alpha_dummy_000 A B C R)) (syn_cpw1 (syn_cpw1 C))) (Wff.classEq (Class.cv (nb088_alpha_dummy_001 A B C R)) (syn_cfdrowfib R A B (Class.cv (nb088_alpha_dummy_000 A B C R)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0001 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : u ∈ (({u} : Finset Var) ∪ ({(nb088_alpha_dummy_002 u A B C R)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv u) (syn_cpw1 (syn_cpw1 C))) (Wff.classEq (Class.cv (nb088_alpha_dummy_002 u A B C R)) (syn_cfdrowfib R A B (Class.cv u))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0002 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_001 A B C R) ∈ (({(nb088_alpha_dummy_000 A B C R)} : Finset Var) ∪ ({(nb088_alpha_dummy_001 A B C R)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb088_alpha_dummy_000 A B C R)) (syn_cpw1 (syn_cpw1 C))) (Wff.classEq (Class.cv (nb088_alpha_dummy_001 A B C R)) (syn_cfdrowfib R A B (Class.cv (nb088_alpha_dummy_000 A B C R)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0003 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_002 u A B C R) ∈ (({u} : Finset Var) ∪ ({(nb088_alpha_dummy_002 u A B C R)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv u) (syn_cpw1 (syn_cpw1 C))) (Wff.classEq (Class.cv (nb088_alpha_dummy_002 u A B C R)) (syn_cfdrowfib R A B (Class.cv u))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0004 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_000 A B C R) ∈ (({(nb088_alpha_dummy_000 A B C R)} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 C))).fv ∪ ((syn_cfdrowfib R A B (Class.cv (nb088_alpha_dummy_000 A B C R)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0005 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : u ∈ (({u} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 C))).fv ∪ ((syn_cfdrowfib R A B (Class.cv u))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0006 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_000 A B C R) ∈ (((Class.cv (nb088_alpha_dummy_000 A B C R))).fv ∪ ((Class.cv (nb088_alpha_dummy_001 A B C R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0007 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_000 A B C R) ∈ (((syn_ccompl (Class.cab (nb088_alpha_dummy_005 A B C R) (syn_wrex (nb088_alpha_dummy_006 A B C R) (Class.cv (nb088_alpha_dummy_000 A B C R)) (Wff.classEq (Class.cv (nb088_alpha_dummy_005 A B C R)) (syn_cphi (Class.cv (nb088_alpha_dummy_006 A B C R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb088_alpha_dummy_005 A B C R) (syn_wrex (nb088_alpha_dummy_006 A B C R) (Class.cv (nb088_alpha_dummy_001 A B C R)) (Wff.classEq (Class.cv (nb088_alpha_dummy_005 A B C R)) (syn_cun (syn_cphi (Class.cv (nb088_alpha_dummy_006 A B C R))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0006 A B C R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0006 A B C R) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb088_support_mem_0008 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : u ∈ (((Class.cv u)).fv ∪ ((Class.cv (nb088_alpha_dummy_002 u A B C R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0009 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : u ∈ (((syn_ccompl (Class.cab (nb088_alpha_dummy_007 u A B C R) (syn_wrex (nb088_alpha_dummy_008 u A B C R) (Class.cv u) (Wff.classEq (Class.cv (nb088_alpha_dummy_007 u A B C R)) (syn_cphi (Class.cv (nb088_alpha_dummy_008 u A B C R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb088_alpha_dummy_007 u A B C R) (syn_wrex (nb088_alpha_dummy_008 u A B C R) (Class.cv (nb088_alpha_dummy_002 u A B C R)) (Wff.classEq (Class.cv (nb088_alpha_dummy_007 u A B C R)) (syn_cun (syn_cphi (Class.cv (nb088_alpha_dummy_008 u A B C R))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0008 u A B C R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0008 u A B C R) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb088_support_mem_0010 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_000 A B C R) ∈ (((Class.cab (nb088_alpha_dummy_005 A B C R) (syn_wrex (nb088_alpha_dummy_006 A B C R) (Class.cv (nb088_alpha_dummy_000 A B C R)) (Wff.classEq (Class.cv (nb088_alpha_dummy_005 A B C R)) (syn_cphi (Class.cv (nb088_alpha_dummy_006 A B C R))))))).fv ∪ ((Class.cab (nb088_alpha_dummy_005 A B C R) (syn_wrex (nb088_alpha_dummy_006 A B C R) (Class.cv (nb088_alpha_dummy_000 A B C R)) (Wff.classEq (Class.cv (nb088_alpha_dummy_005 A B C R)) (syn_cphi (Class.cv (nb088_alpha_dummy_006 A B C R))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0006 A B C R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0006 A B C R) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb088_support_mem_0011 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : u ∈ (((Class.cab (nb088_alpha_dummy_007 u A B C R) (syn_wrex (nb088_alpha_dummy_008 u A B C R) (Class.cv u) (Wff.classEq (Class.cv (nb088_alpha_dummy_007 u A B C R)) (syn_cphi (Class.cv (nb088_alpha_dummy_008 u A B C R))))))).fv ∪ ((Class.cab (nb088_alpha_dummy_007 u A B C R) (syn_wrex (nb088_alpha_dummy_008 u A B C R) (Class.cv u) (Wff.classEq (Class.cv (nb088_alpha_dummy_007 u A B C R)) (syn_cphi (Class.cv (nb088_alpha_dummy_008 u A B C R))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0008 u A B C R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0008 u A B C R) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb088_support_mem_0012 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_006 A B C R) ∈ (((Class.cv (nb088_alpha_dummy_006 A B C R))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0013 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_008 u A B C R) ∈ (((Class.cv (nb088_alpha_dummy_008 u A B C R))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0014 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_013 A B C R) ∈ (((Wff.classMem (Class.cv (nb088_alpha_dummy_013 A B C R)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb088_alpha_dummy_013 A B C R)) (syn_c1c))).fv ∪ ((Class.cv (nb088_alpha_dummy_013 A B C R))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0015 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_015 u A B C R) ∈ (((Wff.classMem (Class.cv (nb088_alpha_dummy_015 u A B C R)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb088_alpha_dummy_015 u A B C R)) (syn_c1c))).fv ∪ ((Class.cv (nb088_alpha_dummy_015 u A B C R))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0016 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_013 A B C R) ∈ (((Class.cv (nb088_alpha_dummy_013 A B C R))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0017 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_015 u A B C R) ∈ (((Class.cv (nb088_alpha_dummy_015 u A B C R))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0018 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_020 A B C R) ∈ (((syn_cnin (Class.cv (nb088_alpha_dummy_020 A B C R)) (Class.cv (nb088_alpha_dummy_021 A B C R)))).fv ∪ ((syn_cnin (Class.cv (nb088_alpha_dummy_020 A B C R)) (Class.cv (nb088_alpha_dummy_021 A B C R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0019 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_023 u A B C R) ∈ (((syn_cnin (Class.cv (nb088_alpha_dummy_023 u A B C R)) (Class.cv (nb088_alpha_dummy_024 u A B C R)))).fv ∪ ((syn_cnin (Class.cv (nb088_alpha_dummy_023 u A B C R)) (Class.cv (nb088_alpha_dummy_024 u A B C R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0020 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_020 A B C R) ∈ (((Class.cv (nb088_alpha_dummy_020 A B C R))).fv ∪ ((Class.cv (nb088_alpha_dummy_021 A B C R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0021 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_023 u A B C R) ∈ (((Class.cv (nb088_alpha_dummy_023 u A B C R))).fv ∪ ((Class.cv (nb088_alpha_dummy_024 u A B C R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0022 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_021 A B C R) ∈ (((syn_cnin (Class.cv (nb088_alpha_dummy_020 A B C R)) (Class.cv (nb088_alpha_dummy_021 A B C R)))).fv ∪ ((syn_cnin (Class.cv (nb088_alpha_dummy_020 A B C R)) (Class.cv (nb088_alpha_dummy_021 A B C R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0023 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_024 u A B C R) ∈ (((syn_cnin (Class.cv (nb088_alpha_dummy_023 u A B C R)) (Class.cv (nb088_alpha_dummy_024 u A B C R)))).fv ∪ ((syn_cnin (Class.cv (nb088_alpha_dummy_023 u A B C R)) (Class.cv (nb088_alpha_dummy_024 u A B C R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0024 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_021 A B C R) ∈ (((Class.cv (nb088_alpha_dummy_020 A B C R))).fv ∪ ((Class.cv (nb088_alpha_dummy_021 A B C R))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0025 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_024 u A B C R) ∈ (((Class.cv (nb088_alpha_dummy_023 u A B C R))).fv ∪ ((Class.cv (nb088_alpha_dummy_024 u A B C R))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0026 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_020 A B C R) ∈ (((syn_ccompl (Class.cv (nb088_alpha_dummy_020 A B C R)))).fv ∪ ((syn_ccompl (Class.cv (nb088_alpha_dummy_021 A B C R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0027 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_023 u A B C R) ∈ (((syn_ccompl (Class.cv (nb088_alpha_dummy_023 u A B C R)))).fv ∪ ((syn_ccompl (Class.cv (nb088_alpha_dummy_024 u A B C R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0028 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_020 A B C R) ∈ (((Class.cv (nb088_alpha_dummy_020 A B C R))).fv ∪ ((Class.cv (nb088_alpha_dummy_020 A B C R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0029 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_023 u A B C R) ∈ (((Class.cv (nb088_alpha_dummy_023 u A B C R))).fv ∪ ((Class.cv (nb088_alpha_dummy_023 u A B C R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0030 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_021 A B C R) ∈ (((syn_ccompl (Class.cv (nb088_alpha_dummy_020 A B C R)))).fv ∪ ((syn_ccompl (Class.cv (nb088_alpha_dummy_021 A B C R)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0031 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_024 u A B C R) ∈ (((syn_ccompl (Class.cv (nb088_alpha_dummy_023 u A B C R)))).fv ∪ ((syn_ccompl (Class.cv (nb088_alpha_dummy_024 u A B C R)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0032 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_021 A B C R) ∈ (((Class.cv (nb088_alpha_dummy_021 A B C R))).fv ∪ ((Class.cv (nb088_alpha_dummy_021 A B C R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0033 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_024 u A B C R) ∈ (((Class.cv (nb088_alpha_dummy_024 u A B C R))).fv ∪ ((Class.cv (nb088_alpha_dummy_024 u A B C R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0034 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_001 A B C R) ∈ (((Class.cv (nb088_alpha_dummy_000 A B C R))).fv ∪ ((Class.cv (nb088_alpha_dummy_001 A B C R))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0035 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_001 A B C R) ∈ (((syn_ccompl (Class.cab (nb088_alpha_dummy_005 A B C R) (syn_wrex (nb088_alpha_dummy_006 A B C R) (Class.cv (nb088_alpha_dummy_000 A B C R)) (Wff.classEq (Class.cv (nb088_alpha_dummy_005 A B C R)) (syn_cphi (Class.cv (nb088_alpha_dummy_006 A B C R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb088_alpha_dummy_005 A B C R) (syn_wrex (nb088_alpha_dummy_006 A B C R) (Class.cv (nb088_alpha_dummy_001 A B C R)) (Wff.classEq (Class.cv (nb088_alpha_dummy_005 A B C R)) (syn_cun (syn_cphi (Class.cv (nb088_alpha_dummy_006 A B C R))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0034 A B C R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0034 A B C R) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb088_support_mem_0036 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_002 u A B C R) ∈ (((Class.cv u)).fv ∪ ((Class.cv (nb088_alpha_dummy_002 u A B C R))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0037 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_002 u A B C R) ∈ (((syn_ccompl (Class.cab (nb088_alpha_dummy_007 u A B C R) (syn_wrex (nb088_alpha_dummy_008 u A B C R) (Class.cv u) (Wff.classEq (Class.cv (nb088_alpha_dummy_007 u A B C R)) (syn_cphi (Class.cv (nb088_alpha_dummy_008 u A B C R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb088_alpha_dummy_007 u A B C R) (syn_wrex (nb088_alpha_dummy_008 u A B C R) (Class.cv (nb088_alpha_dummy_002 u A B C R)) (Wff.classEq (Class.cv (nb088_alpha_dummy_007 u A B C R)) (syn_cun (syn_cphi (Class.cv (nb088_alpha_dummy_008 u A B C R))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0036 u A B C R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0036 u A B C R) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb088_support_mem_0038 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_001 A B C R) ∈ (((Class.cab (nb088_alpha_dummy_005 A B C R) (syn_wrex (nb088_alpha_dummy_006 A B C R) (Class.cv (nb088_alpha_dummy_001 A B C R)) (Wff.classEq (Class.cv (nb088_alpha_dummy_005 A B C R)) (syn_cun (syn_cphi (Class.cv (nb088_alpha_dummy_006 A B C R))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb088_alpha_dummy_005 A B C R) (syn_wrex (nb088_alpha_dummy_006 A B C R) (Class.cv (nb088_alpha_dummy_001 A B C R)) (Wff.classEq (Class.cv (nb088_alpha_dummy_005 A B C R)) (syn_cun (syn_cphi (Class.cv (nb088_alpha_dummy_006 A B C R))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0034 A B C R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0034 A B C R) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb088_support_mem_0039 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_002 u A B C R) ∈ (((Class.cab (nb088_alpha_dummy_007 u A B C R) (syn_wrex (nb088_alpha_dummy_008 u A B C R) (Class.cv (nb088_alpha_dummy_002 u A B C R)) (Wff.classEq (Class.cv (nb088_alpha_dummy_007 u A B C R)) (syn_cun (syn_cphi (Class.cv (nb088_alpha_dummy_008 u A B C R))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb088_alpha_dummy_007 u A B C R) (syn_wrex (nb088_alpha_dummy_008 u A B C R) (Class.cv (nb088_alpha_dummy_002 u A B C R)) (Wff.classEq (Class.cv (nb088_alpha_dummy_007 u A B C R)) (syn_cun (syn_cphi (Class.cv (nb088_alpha_dummy_008 u A B C R))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0036 u A B C R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0036 u A B C R) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb088_support_mem_0040 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_006 A B C R) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb088_alpha_dummy_006 A B C R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0041 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_008 u A B C R) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb088_alpha_dummy_008 u A B C R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0042 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_006 A B C R) ∈ (((syn_cphi (Class.cv (nb088_alpha_dummy_006 A B C R)))).fv ∪ ((syn_cphi (Class.cv (nb088_alpha_dummy_006 A B C R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0043 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_008 u A B C R) ∈ (((syn_cphi (Class.cv (nb088_alpha_dummy_008 u A B C R)))).fv ∪ ((syn_cphi (Class.cv (nb088_alpha_dummy_008 u A B C R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0044 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_041 A B C R) ∈ (((syn_csn (Class.cv (nb088_alpha_dummy_041 A B C R)))).fv ∪ ((Class.cv (nb088_alpha_dummy_000 A B C R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0045 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_041 A B C R) ∈ (((syn_ccompl (Class.cab (nb088_alpha_dummy_043 A B C R) (syn_wrex (nb088_alpha_dummy_044 A B C R) (syn_csn (Class.cv (nb088_alpha_dummy_041 A B C R))) (Wff.classEq (Class.cv (nb088_alpha_dummy_043 A B C R)) (syn_cphi (Class.cv (nb088_alpha_dummy_044 A B C R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb088_alpha_dummy_043 A B C R) (syn_wrex (nb088_alpha_dummy_044 A B C R) (Class.cv (nb088_alpha_dummy_000 A B C R)) (Wff.classEq (Class.cv (nb088_alpha_dummy_043 A B C R)) (syn_cun (syn_cphi (Class.cv (nb088_alpha_dummy_044 A B C R))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0044 A B C R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0044 A B C R) 1))
    ·
      rw [fv_syn_csn]
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb088_support_mem_0046 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_042 u A B R) ∈ (((syn_csn (Class.cv (nb088_alpha_dummy_042 u A B R)))).fv ∪ ((Class.cv u)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0047 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_042 u A B R) ∈ (((syn_ccompl (Class.cab (nb088_alpha_dummy_045 u A B R) (syn_wrex (nb088_alpha_dummy_046 u A B R) (syn_csn (Class.cv (nb088_alpha_dummy_042 u A B R))) (Wff.classEq (Class.cv (nb088_alpha_dummy_045 u A B R)) (syn_cphi (Class.cv (nb088_alpha_dummy_046 u A B R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb088_alpha_dummy_045 u A B R) (syn_wrex (nb088_alpha_dummy_046 u A B R) (Class.cv u) (Wff.classEq (Class.cv (nb088_alpha_dummy_045 u A B R)) (syn_cun (syn_cphi (Class.cv (nb088_alpha_dummy_046 u A B R))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0046 u A B R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0046 u A B R) 1))
    ·
      rw [fv_syn_csn]
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb088_support_mem_0048 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_041 A B C R) ∈ (((Class.cab (nb088_alpha_dummy_043 A B C R) (syn_wrex (nb088_alpha_dummy_044 A B C R) (syn_csn (Class.cv (nb088_alpha_dummy_041 A B C R))) (Wff.classEq (Class.cv (nb088_alpha_dummy_043 A B C R)) (syn_cphi (Class.cv (nb088_alpha_dummy_044 A B C R))))))).fv ∪ ((Class.cab (nb088_alpha_dummy_043 A B C R) (syn_wrex (nb088_alpha_dummy_044 A B C R) (syn_csn (Class.cv (nb088_alpha_dummy_041 A B C R))) (Wff.classEq (Class.cv (nb088_alpha_dummy_043 A B C R)) (syn_cphi (Class.cv (nb088_alpha_dummy_044 A B C R))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0044 A B C R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0044 A B C R) 1))
    ·
      rw [fv_syn_csn]
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb088_support_mem_0049 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_042 u A B R) ∈ (((Class.cab (nb088_alpha_dummy_045 u A B R) (syn_wrex (nb088_alpha_dummy_046 u A B R) (syn_csn (Class.cv (nb088_alpha_dummy_042 u A B R))) (Wff.classEq (Class.cv (nb088_alpha_dummy_045 u A B R)) (syn_cphi (Class.cv (nb088_alpha_dummy_046 u A B R))))))).fv ∪ ((Class.cab (nb088_alpha_dummy_045 u A B R) (syn_wrex (nb088_alpha_dummy_046 u A B R) (syn_csn (Class.cv (nb088_alpha_dummy_042 u A B R))) (Wff.classEq (Class.cv (nb088_alpha_dummy_045 u A B R)) (syn_cphi (Class.cv (nb088_alpha_dummy_046 u A B R))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0046 u A B R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0046 u A B R) 1))
    ·
      rw [fv_syn_csn]
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb088_support_mem_0050 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_041 A B C R) ∈ (((Class.cv (nb088_alpha_dummy_041 A B C R))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0051 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_042 u A B R) ∈ (((Class.cv (nb088_alpha_dummy_042 u A B R))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0052 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_044 A B C R) ∈ (((Class.cv (nb088_alpha_dummy_044 A B C R))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0053 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_046 u A B R) ∈ (((Class.cv (nb088_alpha_dummy_046 u A B R))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0054 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_053 A B C R) ∈ (((Wff.classMem (Class.cv (nb088_alpha_dummy_053 A B C R)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb088_alpha_dummy_053 A B C R)) (syn_c1c))).fv ∪ ((Class.cv (nb088_alpha_dummy_053 A B C R))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0055 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_055 u A B R) ∈ (((Wff.classMem (Class.cv (nb088_alpha_dummy_055 u A B R)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb088_alpha_dummy_055 u A B R)) (syn_c1c))).fv ∪ ((Class.cv (nb088_alpha_dummy_055 u A B R))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0056 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_053 A B C R) ∈ (((Class.cv (nb088_alpha_dummy_053 A B C R))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0057 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_055 u A B R) ∈ (((Class.cv (nb088_alpha_dummy_055 u A B R))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0058 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_060 A B C R) ∈ (((syn_cnin (Class.cv (nb088_alpha_dummy_060 A B C R)) (Class.cv (nb088_alpha_dummy_061 A B C R)))).fv ∪ ((syn_cnin (Class.cv (nb088_alpha_dummy_060 A B C R)) (Class.cv (nb088_alpha_dummy_061 A B C R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0059 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_063 u A B R) ∈ (((syn_cnin (Class.cv (nb088_alpha_dummy_063 u A B R)) (Class.cv (nb088_alpha_dummy_064 u A B R)))).fv ∪ ((syn_cnin (Class.cv (nb088_alpha_dummy_063 u A B R)) (Class.cv (nb088_alpha_dummy_064 u A B R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0060 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_060 A B C R) ∈ (((Class.cv (nb088_alpha_dummy_060 A B C R))).fv ∪ ((Class.cv (nb088_alpha_dummy_061 A B C R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0061 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_063 u A B R) ∈ (((Class.cv (nb088_alpha_dummy_063 u A B R))).fv ∪ ((Class.cv (nb088_alpha_dummy_064 u A B R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0062 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_061 A B C R) ∈ (((syn_cnin (Class.cv (nb088_alpha_dummy_060 A B C R)) (Class.cv (nb088_alpha_dummy_061 A B C R)))).fv ∪ ((syn_cnin (Class.cv (nb088_alpha_dummy_060 A B C R)) (Class.cv (nb088_alpha_dummy_061 A B C R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0063 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_064 u A B R) ∈ (((syn_cnin (Class.cv (nb088_alpha_dummy_063 u A B R)) (Class.cv (nb088_alpha_dummy_064 u A B R)))).fv ∪ ((syn_cnin (Class.cv (nb088_alpha_dummy_063 u A B R)) (Class.cv (nb088_alpha_dummy_064 u A B R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0064 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_061 A B C R) ∈ (((Class.cv (nb088_alpha_dummy_060 A B C R))).fv ∪ ((Class.cv (nb088_alpha_dummy_061 A B C R))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0065 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_064 u A B R) ∈ (((Class.cv (nb088_alpha_dummy_063 u A B R))).fv ∪ ((Class.cv (nb088_alpha_dummy_064 u A B R))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0066 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_060 A B C R) ∈ (((syn_ccompl (Class.cv (nb088_alpha_dummy_060 A B C R)))).fv ∪ ((syn_ccompl (Class.cv (nb088_alpha_dummy_061 A B C R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0067 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_063 u A B R) ∈ (((syn_ccompl (Class.cv (nb088_alpha_dummy_063 u A B R)))).fv ∪ ((syn_ccompl (Class.cv (nb088_alpha_dummy_064 u A B R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0068 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_060 A B C R) ∈ (((Class.cv (nb088_alpha_dummy_060 A B C R))).fv ∪ ((Class.cv (nb088_alpha_dummy_060 A B C R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0069 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_063 u A B R) ∈ (((Class.cv (nb088_alpha_dummy_063 u A B R))).fv ∪ ((Class.cv (nb088_alpha_dummy_063 u A B R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0070 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_061 A B C R) ∈ (((syn_ccompl (Class.cv (nb088_alpha_dummy_060 A B C R)))).fv ∪ ((syn_ccompl (Class.cv (nb088_alpha_dummy_061 A B C R)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0071 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_064 u A B R) ∈ (((syn_ccompl (Class.cv (nb088_alpha_dummy_063 u A B R)))).fv ∪ ((syn_ccompl (Class.cv (nb088_alpha_dummy_064 u A B R)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0072 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_061 A B C R) ∈ (((Class.cv (nb088_alpha_dummy_061 A B C R))).fv ∪ ((Class.cv (nb088_alpha_dummy_061 A B C R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0073 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_064 u A B R) ∈ (((Class.cv (nb088_alpha_dummy_064 u A B R))).fv ∪ ((Class.cv (nb088_alpha_dummy_064 u A B R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0074 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_000 A B C R) ∈ ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb088_alpha_dummy_000 A B C R))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0075 (u : Var) (A : Class) (B : Class) (R : Class) : u ∈ ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv u)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0076 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_000 A B C R) ∈ (((syn_csn (Class.cv (nb088_alpha_dummy_041 A B C R)))).fv ∪ ((Class.cv (nb088_alpha_dummy_000 A B C R))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0077 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_000 A B C R) ∈ (((syn_ccompl (Class.cab (nb088_alpha_dummy_043 A B C R) (syn_wrex (nb088_alpha_dummy_044 A B C R) (syn_csn (Class.cv (nb088_alpha_dummy_041 A B C R))) (Wff.classEq (Class.cv (nb088_alpha_dummy_043 A B C R)) (syn_cphi (Class.cv (nb088_alpha_dummy_044 A B C R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb088_alpha_dummy_043 A B C R) (syn_wrex (nb088_alpha_dummy_044 A B C R) (Class.cv (nb088_alpha_dummy_000 A B C R)) (Wff.classEq (Class.cv (nb088_alpha_dummy_043 A B C R)) (syn_cun (syn_cphi (Class.cv (nb088_alpha_dummy_044 A B C R))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0076 A B C R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0076 A B C R) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb088_support_mem_0078 (u : Var) (A : Class) (B : Class) (R : Class) : u ∈ (((syn_csn (Class.cv (nb088_alpha_dummy_042 u A B R)))).fv ∪ ((Class.cv u)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0079 (u : Var) (A : Class) (B : Class) (R : Class) : u ∈ (((syn_ccompl (Class.cab (nb088_alpha_dummy_045 u A B R) (syn_wrex (nb088_alpha_dummy_046 u A B R) (syn_csn (Class.cv (nb088_alpha_dummy_042 u A B R))) (Wff.classEq (Class.cv (nb088_alpha_dummy_045 u A B R)) (syn_cphi (Class.cv (nb088_alpha_dummy_046 u A B R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb088_alpha_dummy_045 u A B R) (syn_wrex (nb088_alpha_dummy_046 u A B R) (Class.cv u) (Wff.classEq (Class.cv (nb088_alpha_dummy_045 u A B R)) (syn_cun (syn_cphi (Class.cv (nb088_alpha_dummy_046 u A B R))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0078 u A B R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0078 u A B R) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb088_support_mem_0080 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_000 A B C R) ∈ (((Class.cab (nb088_alpha_dummy_043 A B C R) (syn_wrex (nb088_alpha_dummy_044 A B C R) (Class.cv (nb088_alpha_dummy_000 A B C R)) (Wff.classEq (Class.cv (nb088_alpha_dummy_043 A B C R)) (syn_cun (syn_cphi (Class.cv (nb088_alpha_dummy_044 A B C R))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb088_alpha_dummy_043 A B C R) (syn_wrex (nb088_alpha_dummy_044 A B C R) (Class.cv (nb088_alpha_dummy_000 A B C R)) (Wff.classEq (Class.cv (nb088_alpha_dummy_043 A B C R)) (syn_cun (syn_cphi (Class.cv (nb088_alpha_dummy_044 A B C R))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0076 A B C R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0076 A B C R) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb088_support_mem_0081 (u : Var) (A : Class) (B : Class) (R : Class) : u ∈ (((Class.cab (nb088_alpha_dummy_045 u A B R) (syn_wrex (nb088_alpha_dummy_046 u A B R) (Class.cv u) (Wff.classEq (Class.cv (nb088_alpha_dummy_045 u A B R)) (syn_cun (syn_cphi (Class.cv (nb088_alpha_dummy_046 u A B R))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb088_alpha_dummy_045 u A B R) (syn_wrex (nb088_alpha_dummy_046 u A B R) (Class.cv u) (Wff.classEq (Class.cv (nb088_alpha_dummy_045 u A B R)) (syn_cun (syn_cphi (Class.cv (nb088_alpha_dummy_046 u A B R))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0078 u A B R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb088_support_mem_0078 u A B R) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb088_support_mem_0082 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_044 A B C R) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb088_alpha_dummy_044 A B C R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0083 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_046 u A B R) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb088_alpha_dummy_046 u A B R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0084 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_044 A B C R) ∈ (((syn_cphi (Class.cv (nb088_alpha_dummy_044 A B C R)))).fv ∪ ((syn_cphi (Class.cv (nb088_alpha_dummy_044 A B C R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_support_mem_0085 (u : Var) (A : Class) (B : Class) (R : Class) : (nb088_alpha_dummy_046 u A B R) ∈ (((syn_cphi (Class.cv (nb088_alpha_dummy_046 u A B R)))).fv ∪ ((syn_cphi (Class.cv (nb088_alpha_dummy_046 u A B R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb088_compact_fv_empty_0000 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_021 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb088_wpp_notmem_0000 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_021 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb088_alpha_dummy_021, fv_syn_c1c] using (nb088_compact_fv_empty_0000 A B C R)

theorem nb088_compact_fv_empty_0001 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_024 u A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb088_wpp_notmem_0001 (u : Var) (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_024 u A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb088_alpha_dummy_024, fv_syn_c1c] using (nb088_compact_fv_empty_0001 u A B C R)

theorem nb088_compact_fv_empty_0002 (A : Class) (B : Class) (C : Class) (R : Class) : (nb088_alpha_dummy_020 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
