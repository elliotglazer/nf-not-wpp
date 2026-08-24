import NAR4C089C001Part001

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

theorem nb089_fresh_067 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_060 u A B R) ∉ (((Wff.classMem (Class.cv (nb089_alpha_dummy_057 u A B R)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb089_alpha_dummy_057 u A B R)) (syn_c1c))).fv ∪ ((Class.cv (nb089_alpha_dummy_057 u A B R))).fv) := by
  simpa only [nb089_alpha_dummy_060] using freshVar_not_mem (((Wff.classMem (Class.cv (nb089_alpha_dummy_057 u A B R)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb089_alpha_dummy_057 u A B R)) (syn_c1c))).fv ∪ ((Class.cv (nb089_alpha_dummy_057 u A B R))).fv) 0

theorem nb089_fresh_068 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_011 A B R) ∉ (((syn_ccompl (Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_003 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb089_alpha_dummy_011] using freshVar_not_mem (((syn_ccompl (Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_003 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb089_fresh_069 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_012 u A B R) ∉ (((syn_ccompl (Class.cab (nb089_alpha_dummy_009 u A B R) (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv u) (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb089_alpha_dummy_009 u A B R) (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv (nb089_alpha_dummy_004 u A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb089_alpha_dummy_012] using freshVar_not_mem (((syn_ccompl (Class.cab (nb089_alpha_dummy_009 u A B R) (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv u) (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb089_alpha_dummy_009 u A B R) (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv (nb089_alpha_dummy_004 u A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb089_fresh_070 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_049 A B R) ∉ (((syn_ccompl (Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R) (syn_csn (Class.cv (nb089_alpha_dummy_043 A B R))) (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R) (Class.cv (nb089_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb089_alpha_dummy_049] using freshVar_not_mem (((syn_ccompl (Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R) (syn_csn (Class.cv (nb089_alpha_dummy_043 A B R))) (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R) (Class.cv (nb089_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb089_fresh_071 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_050 u A B R) ∉ (((syn_ccompl (Class.cab (nb089_alpha_dummy_047 u A B R) (syn_wrex (nb089_alpha_dummy_048 u A B R) (syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R))) (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb089_alpha_dummy_047 u A B R) (syn_wrex (nb089_alpha_dummy_048 u A B R) (Class.cv u) (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb089_alpha_dummy_050] using freshVar_not_mem (((syn_ccompl (Class.cab (nb089_alpha_dummy_047 u A B R) (syn_wrex (nb089_alpha_dummy_048 u A B R) (syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R))) (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb089_alpha_dummy_047 u A B R) (syn_wrex (nb089_alpha_dummy_048 u A B R) (Class.cv u) (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb089_fresh_072 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_031 A B R) ∉ (((syn_ccompl (Class.cv (nb089_alpha_dummy_022 A B R)))).fv ∪ ((syn_ccompl (Class.cv (nb089_alpha_dummy_023 A B R)))).fv) := by
  simpa only [nb089_alpha_dummy_031] using freshVar_not_mem (((syn_ccompl (Class.cv (nb089_alpha_dummy_022 A B R)))).fv ∪ ((syn_ccompl (Class.cv (nb089_alpha_dummy_023 A B R)))).fv) 0

theorem nb089_fresh_073 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_032 u A B R) ∉ (((syn_ccompl (Class.cv (nb089_alpha_dummy_025 u A B R)))).fv ∪ ((syn_ccompl (Class.cv (nb089_alpha_dummy_026 u A B R)))).fv) := by
  simpa only [nb089_alpha_dummy_032] using freshVar_not_mem (((syn_ccompl (Class.cv (nb089_alpha_dummy_025 u A B R)))).fv ∪ ((syn_ccompl (Class.cv (nb089_alpha_dummy_026 u A B R)))).fv) 0

theorem nb089_fresh_074 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_071 A B R) ∉ (((syn_ccompl (Class.cv (nb089_alpha_dummy_062 A B R)))).fv ∪ ((syn_ccompl (Class.cv (nb089_alpha_dummy_063 A B R)))).fv) := by
  simpa only [nb089_alpha_dummy_071] using freshVar_not_mem (((syn_ccompl (Class.cv (nb089_alpha_dummy_062 A B R)))).fv ∪ ((syn_ccompl (Class.cv (nb089_alpha_dummy_063 A B R)))).fv) 0

theorem nb089_fresh_075 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_072 u A B R) ∉ (((syn_ccompl (Class.cv (nb089_alpha_dummy_065 u A B R)))).fv ∪ ((syn_ccompl (Class.cv (nb089_alpha_dummy_066 u A B R)))).fv) := by
  simpa only [nb089_alpha_dummy_072] using freshVar_not_mem (((syn_ccompl (Class.cv (nb089_alpha_dummy_065 u A B R)))).fv ∪ ((syn_ccompl (Class.cv (nb089_alpha_dummy_066 u A B R)))).fv) 0

theorem nb089_fresh_076 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_039 A B R) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb089_alpha_dummy_039] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb089_fresh_077 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_040 u A B R) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb089_alpha_dummy_040] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb089_fresh_078 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_079 A B R) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb089_alpha_dummy_079] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb089_fresh_079 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_080 u A B R) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb089_alpha_dummy_080] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb089_fresh_080 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_027 A B R) ∉ (((syn_cnin (Class.cv (nb089_alpha_dummy_022 A B R)) (Class.cv (nb089_alpha_dummy_023 A B R)))).fv ∪ ((syn_cnin (Class.cv (nb089_alpha_dummy_022 A B R)) (Class.cv (nb089_alpha_dummy_023 A B R)))).fv) := by
  simpa only [nb089_alpha_dummy_027] using freshVar_not_mem (((syn_cnin (Class.cv (nb089_alpha_dummy_022 A B R)) (Class.cv (nb089_alpha_dummy_023 A B R)))).fv ∪ ((syn_cnin (Class.cv (nb089_alpha_dummy_022 A B R)) (Class.cv (nb089_alpha_dummy_023 A B R)))).fv) 0

theorem nb089_fresh_081 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_028 u A B R) ∉ (((syn_cnin (Class.cv (nb089_alpha_dummy_025 u A B R)) (Class.cv (nb089_alpha_dummy_026 u A B R)))).fv ∪ ((syn_cnin (Class.cv (nb089_alpha_dummy_025 u A B R)) (Class.cv (nb089_alpha_dummy_026 u A B R)))).fv) := by
  simpa only [nb089_alpha_dummy_028] using freshVar_not_mem (((syn_cnin (Class.cv (nb089_alpha_dummy_025 u A B R)) (Class.cv (nb089_alpha_dummy_026 u A B R)))).fv ∪ ((syn_cnin (Class.cv (nb089_alpha_dummy_025 u A B R)) (Class.cv (nb089_alpha_dummy_026 u A B R)))).fv) 0

theorem nb089_fresh_082 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_067 A B R) ∉ (((syn_cnin (Class.cv (nb089_alpha_dummy_062 A B R)) (Class.cv (nb089_alpha_dummy_063 A B R)))).fv ∪ ((syn_cnin (Class.cv (nb089_alpha_dummy_062 A B R)) (Class.cv (nb089_alpha_dummy_063 A B R)))).fv) := by
  simpa only [nb089_alpha_dummy_067] using freshVar_not_mem (((syn_cnin (Class.cv (nb089_alpha_dummy_062 A B R)) (Class.cv (nb089_alpha_dummy_063 A B R)))).fv ∪ ((syn_cnin (Class.cv (nb089_alpha_dummy_062 A B R)) (Class.cv (nb089_alpha_dummy_063 A B R)))).fv) 0

theorem nb089_fresh_083 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_068 u A B R) ∉ (((syn_cnin (Class.cv (nb089_alpha_dummy_065 u A B R)) (Class.cv (nb089_alpha_dummy_066 u A B R)))).fv ∪ ((syn_cnin (Class.cv (nb089_alpha_dummy_065 u A B R)) (Class.cv (nb089_alpha_dummy_066 u A B R)))).fv) := by
  simpa only [nb089_alpha_dummy_068] using freshVar_not_mem (((syn_cnin (Class.cv (nb089_alpha_dummy_065 u A B R)) (Class.cv (nb089_alpha_dummy_066 u A B R)))).fv ∪ ((syn_cnin (Class.cv (nb089_alpha_dummy_065 u A B R)) (Class.cv (nb089_alpha_dummy_066 u A B R)))).fv) 0

theorem nb089_fresh_084 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_041 A B R) ∉ (((syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))).fv ∪ ((syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))).fv) := by
  simpa only [nb089_alpha_dummy_041] using freshVar_not_mem (((syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))).fv ∪ ((syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))).fv) 0

theorem nb089_fresh_085 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_042 u A B R) ∉ (((syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))).fv ∪ ((syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))).fv) := by
  simpa only [nb089_alpha_dummy_042] using freshVar_not_mem (((syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))).fv ∪ ((syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))).fv) 0

theorem nb089_fresh_086 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_081 A B R) ∉ (((syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))).fv ∪ ((syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))).fv) := by
  simpa only [nb089_alpha_dummy_081] using freshVar_not_mem (((syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))).fv ∪ ((syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))).fv) 0

theorem nb089_fresh_087 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_082 u A B R) ∉ (((syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))).fv ∪ ((syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))).fv) := by
  simpa only [nb089_alpha_dummy_082] using freshVar_not_mem (((syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))).fv ∪ ((syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))).fv) 0

theorem nb089_fresh_088 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_045 A B R) ∉ (((syn_csn (Class.cv (nb089_alpha_dummy_043 A B R)))).fv ∪ ((Class.cv (nb089_alpha_dummy_000 A B R))).fv) := by
  simpa only [nb089_alpha_dummy_045] using freshVar_not_mem (((syn_csn (Class.cv (nb089_alpha_dummy_043 A B R)))).fv ∪ ((Class.cv (nb089_alpha_dummy_000 A B R))).fv) 0

theorem nb089_fresh_089 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_046 A B R) ∉ (((syn_csn (Class.cv (nb089_alpha_dummy_043 A B R)))).fv ∪ ((Class.cv (nb089_alpha_dummy_000 A B R))).fv) := by
  simpa only [nb089_alpha_dummy_046] using freshVar_not_mem (((syn_csn (Class.cv (nb089_alpha_dummy_043 A B R)))).fv ∪ ((Class.cv (nb089_alpha_dummy_000 A B R))).fv) 1

theorem nb089_distinct_090 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_045 A B R) ≠ (nb089_alpha_dummy_046 A B R) := by
  simpa only [nb089_alpha_dummy_045, nb089_alpha_dummy_046] using
    (freshVar_injective (((syn_csn (Class.cv (nb089_alpha_dummy_043 A B R)))).fv ∪ ((Class.cv (nb089_alpha_dummy_000 A B R))).fv) (i := 0) (j := 1) (by decide))

theorem nb089_fresh_091 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_047 u A B R) ∉ (((syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R)))).fv ∪ ((Class.cv u)).fv) := by
  simpa only [nb089_alpha_dummy_047] using freshVar_not_mem (((syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R)))).fv ∪ ((Class.cv u)).fv) 0

theorem nb089_fresh_092 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_048 u A B R) ∉ (((syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R)))).fv ∪ ((Class.cv u)).fv) := by
  simpa only [nb089_alpha_dummy_048] using freshVar_not_mem (((syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R)))).fv ∪ ((Class.cv u)).fv) 1

theorem nb089_distinct_093 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_047 u A B R) ≠ (nb089_alpha_dummy_048 u A B R) := by
  simpa only [nb089_alpha_dummy_047, nb089_alpha_dummy_048] using
    (freshVar_injective (((syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R)))).fv ∪ ((Class.cv u)).fv) (i := 0) (j := 1) (by decide))

theorem nb089_fresh_094 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_001 A B R) ∉ (((syn_wbr R (syn_cwe) A)).fv ∪ ((syn_cmpt (nb089_alpha_dummy_000 A B R) (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R))))).fv ∪ ((syn_c0)).fv) := by
  simpa only [nb089_alpha_dummy_001] using freshVar_not_mem (((syn_wbr R (syn_cwe) A)).fv ∪ ((syn_cmpt (nb089_alpha_dummy_000 A B R) (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R))))).fv ∪ ((syn_c0)).fv) 0

theorem nb089_fresh_095 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_002 u A B R) ∉ (((syn_wbr R (syn_cwe) A)).fv ∪ ((syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (Class.cv u)))).fv ∪ ((syn_c0)).fv) := by
  simpa only [nb089_alpha_dummy_002] using freshVar_not_mem (((syn_wbr R (syn_cwe) A)).fv ∪ ((syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A))) (syn_cfdrowfib R A B (Class.cv u)))).fv ∪ ((syn_c0)).fv) 0

theorem nb089_fresh_096 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_000 A B R) ∉ ((R).fv ∪ (A).fv ∪ (B).fv) := by
  simpa only [nb089_alpha_dummy_000] using freshVar_not_mem ((R).fv ∪ (A).fv ∪ (B).fv) 0

theorem nb089_fresh_097 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_043 A B R) ∉ ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb089_alpha_dummy_000 A B R))).fv) := by
  simpa only [nb089_alpha_dummy_043] using freshVar_not_mem ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb089_alpha_dummy_000 A B R))).fv) 0

theorem nb089_fresh_098 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_044 u A B R) ∉ ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv u)).fv) := by
  simpa only [nb089_alpha_dummy_044] using freshVar_not_mem ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv u)).fv) 0

theorem nb089_fresh_099 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_003 A B R) ∉ (({(nb089_alpha_dummy_000 A B R)} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv ∪ ((syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R)))).fv) := by
  simpa only [nb089_alpha_dummy_003] using freshVar_not_mem (({(nb089_alpha_dummy_000 A B R)} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv ∪ ((syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R)))).fv) 0

theorem nb089_fresh_100 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_005 A B R) ∉ (({(nb089_alpha_dummy_000 A B R)} : Finset Var) ∪ ({(nb089_alpha_dummy_003 A B R)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb089_alpha_dummy_000 A B R)) (syn_cpw1 (syn_cpw1 (syn_cuni A)))) (Wff.classEq (Class.cv (nb089_alpha_dummy_003 A B R)) (syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R)))))).fv) := by
  simpa only [nb089_alpha_dummy_005] using freshVar_not_mem (({(nb089_alpha_dummy_000 A B R)} : Finset Var) ∪ ({(nb089_alpha_dummy_003 A B R)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb089_alpha_dummy_000 A B R)) (syn_cpw1 (syn_cpw1 (syn_cuni A)))) (Wff.classEq (Class.cv (nb089_alpha_dummy_003 A B R)) (syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R)))))).fv) 0

theorem nb089_fresh_101 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_004 u A B R) ∉ (({u} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv ∪ ((syn_cfdrowfib R A B (Class.cv u))).fv) := by
  simpa only [nb089_alpha_dummy_004] using freshVar_not_mem (({u} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv ∪ ((syn_cfdrowfib R A B (Class.cv u))).fv) 0

theorem nb089_fresh_102 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_006 u A B R) ∉ (({u} : Finset Var) ∪ ({(nb089_alpha_dummy_004 u A B R)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv u) (syn_cpw1 (syn_cpw1 (syn_cuni A)))) (Wff.classEq (Class.cv (nb089_alpha_dummy_004 u A B R)) (syn_cfdrowfib R A B (Class.cv u))))).fv) := by
  simpa only [nb089_alpha_dummy_006] using freshVar_not_mem (({u} : Finset Var) ∪ ({(nb089_alpha_dummy_004 u A B R)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv u) (syn_cpw1 (syn_cpw1 (syn_cuni A)))) (Wff.classEq (Class.cv (nb089_alpha_dummy_004 u A B R)) (syn_cfdrowfib R A B (Class.cv u))))).fv) 0

theorem nb089_support_mem_0000 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_000 A B R) ∈ (({(nb089_alpha_dummy_000 A B R)} : Finset Var) ∪ ({(nb089_alpha_dummy_003 A B R)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb089_alpha_dummy_000 A B R)) (syn_cpw1 (syn_cpw1 (syn_cuni A)))) (Wff.classEq (Class.cv (nb089_alpha_dummy_003 A B R)) (syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0001 (u : Var) (A : Class) (B : Class) (R : Class) : u ∈ (({u} : Finset Var) ∪ ({(nb089_alpha_dummy_004 u A B R)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv u) (syn_cpw1 (syn_cpw1 (syn_cuni A)))) (Wff.classEq (Class.cv (nb089_alpha_dummy_004 u A B R)) (syn_cfdrowfib R A B (Class.cv u))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0002 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_003 A B R) ∈ (({(nb089_alpha_dummy_000 A B R)} : Finset Var) ∪ ({(nb089_alpha_dummy_003 A B R)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv (nb089_alpha_dummy_000 A B R)) (syn_cpw1 (syn_cpw1 (syn_cuni A)))) (Wff.classEq (Class.cv (nb089_alpha_dummy_003 A B R)) (syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R)))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0003 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_004 u A B R) ∈ (({u} : Finset Var) ∪ ({(nb089_alpha_dummy_004 u A B R)} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv u) (syn_cpw1 (syn_cpw1 (syn_cuni A)))) (Wff.classEq (Class.cv (nb089_alpha_dummy_004 u A B R)) (syn_cfdrowfib R A B (Class.cv u))))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0004 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_000 A B R) ∈ (({(nb089_alpha_dummy_000 A B R)} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv ∪ ((syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R)))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0005 (u : Var) (A : Class) (B : Class) (R : Class) : u ∈ (({u} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv ∪ ((syn_cfdrowfib R A B (Class.cv u))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0006 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_000 A B R) ∈ (((Class.cv (nb089_alpha_dummy_000 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_003 A B R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0007 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_000 A B R) ∈ (((syn_ccompl (Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_003 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0006 A B R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0006 A B R) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0008 (u : Var) (A : Class) (B : Class) (R : Class) : u ∈ (((Class.cv u)).fv ∪ ((Class.cv (nb089_alpha_dummy_004 u A B R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0009 (u : Var) (A : Class) (B : Class) (R : Class) : u ∈ (((syn_ccompl (Class.cab (nb089_alpha_dummy_009 u A B R) (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv u) (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb089_alpha_dummy_009 u A B R) (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv (nb089_alpha_dummy_004 u A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0008 u A B R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0008 u A B R) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0010 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_000 A B R) ∈ (((Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0006 A B R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0006 A B R) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0011 (u : Var) (A : Class) (B : Class) (R : Class) : u ∈ (((Class.cab (nb089_alpha_dummy_009 u A B R) (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv u) (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_009 u A B R) (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv u) (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0008 u A B R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0008 u A B R) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0012 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_008 A B R) ∈ (((Class.cv (nb089_alpha_dummy_008 A B R))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0013 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_010 u A B R) ∈ (((Class.cv (nb089_alpha_dummy_010 u A B R))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0014 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_015 A B R) ∈ (((Wff.classMem (Class.cv (nb089_alpha_dummy_015 A B R)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb089_alpha_dummy_015 A B R)) (syn_c1c))).fv ∪ ((Class.cv (nb089_alpha_dummy_015 A B R))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0015 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_017 u A B R) ∈ (((Wff.classMem (Class.cv (nb089_alpha_dummy_017 u A B R)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb089_alpha_dummy_017 u A B R)) (syn_c1c))).fv ∪ ((Class.cv (nb089_alpha_dummy_017 u A B R))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0016 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_015 A B R) ∈ (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0017 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_017 u A B R) ∈ (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0018 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_022 A B R) ∈ (((syn_cnin (Class.cv (nb089_alpha_dummy_022 A B R)) (Class.cv (nb089_alpha_dummy_023 A B R)))).fv ∪ ((syn_cnin (Class.cv (nb089_alpha_dummy_022 A B R)) (Class.cv (nb089_alpha_dummy_023 A B R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0019 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_025 u A B R) ∈ (((syn_cnin (Class.cv (nb089_alpha_dummy_025 u A B R)) (Class.cv (nb089_alpha_dummy_026 u A B R)))).fv ∪ ((syn_cnin (Class.cv (nb089_alpha_dummy_025 u A B R)) (Class.cv (nb089_alpha_dummy_026 u A B R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0020 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_022 A B R) ∈ (((Class.cv (nb089_alpha_dummy_022 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_023 A B R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0021 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_025 u A B R) ∈ (((Class.cv (nb089_alpha_dummy_025 u A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_026 u A B R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0022 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_023 A B R) ∈ (((syn_cnin (Class.cv (nb089_alpha_dummy_022 A B R)) (Class.cv (nb089_alpha_dummy_023 A B R)))).fv ∪ ((syn_cnin (Class.cv (nb089_alpha_dummy_022 A B R)) (Class.cv (nb089_alpha_dummy_023 A B R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0023 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_026 u A B R) ∈ (((syn_cnin (Class.cv (nb089_alpha_dummy_025 u A B R)) (Class.cv (nb089_alpha_dummy_026 u A B R)))).fv ∪ ((syn_cnin (Class.cv (nb089_alpha_dummy_025 u A B R)) (Class.cv (nb089_alpha_dummy_026 u A B R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0024 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_023 A B R) ∈ (((Class.cv (nb089_alpha_dummy_022 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_023 A B R))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0025 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_026 u A B R) ∈ (((Class.cv (nb089_alpha_dummy_025 u A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_026 u A B R))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0026 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_022 A B R) ∈ (((syn_ccompl (Class.cv (nb089_alpha_dummy_022 A B R)))).fv ∪ ((syn_ccompl (Class.cv (nb089_alpha_dummy_023 A B R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0027 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_025 u A B R) ∈ (((syn_ccompl (Class.cv (nb089_alpha_dummy_025 u A B R)))).fv ∪ ((syn_ccompl (Class.cv (nb089_alpha_dummy_026 u A B R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0028 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_022 A B R) ∈ (((Class.cv (nb089_alpha_dummy_022 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_022 A B R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0029 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_025 u A B R) ∈ (((Class.cv (nb089_alpha_dummy_025 u A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_025 u A B R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0030 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_023 A B R) ∈ (((syn_ccompl (Class.cv (nb089_alpha_dummy_022 A B R)))).fv ∪ ((syn_ccompl (Class.cv (nb089_alpha_dummy_023 A B R)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0031 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_026 u A B R) ∈ (((syn_ccompl (Class.cv (nb089_alpha_dummy_025 u A B R)))).fv ∪ ((syn_ccompl (Class.cv (nb089_alpha_dummy_026 u A B R)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0032 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_023 A B R) ∈ (((Class.cv (nb089_alpha_dummy_023 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_023 A B R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0033 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_026 u A B R) ∈ (((Class.cv (nb089_alpha_dummy_026 u A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_026 u A B R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0034 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_003 A B R) ∈ (((Class.cv (nb089_alpha_dummy_000 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_003 A B R))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0035 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_003 A B R) ∈ (((syn_ccompl (Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_003 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0034 A B R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0034 A B R) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0036 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_004 u A B R) ∈ (((Class.cv u)).fv ∪ ((Class.cv (nb089_alpha_dummy_004 u A B R))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0037 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_004 u A B R) ∈ (((syn_ccompl (Class.cab (nb089_alpha_dummy_009 u A B R) (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv u) (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb089_alpha_dummy_009 u A B R) (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv (nb089_alpha_dummy_004 u A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0036 u A B R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0036 u A B R) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0038 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_003 A B R) ∈ (((Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_003 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_003 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0034 A B R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0034 A B R) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0039 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_004 u A B R) ∈ (((Class.cab (nb089_alpha_dummy_009 u A B R) (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv (nb089_alpha_dummy_004 u A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_009 u A B R) (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv (nb089_alpha_dummy_004 u A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0036 u A B R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0036 u A B R) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0040 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_008 A B R) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0041 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_010 u A B R) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0042 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_008 A B R) ∈ (((syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))).fv ∪ ((syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0043 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_010 u A B R) ∈ (((syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))).fv ∪ ((syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0044 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_043 A B R) ∈ (((syn_csn (Class.cv (nb089_alpha_dummy_043 A B R)))).fv ∪ ((Class.cv (nb089_alpha_dummy_000 A B R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0045 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_043 A B R) ∈ (((syn_ccompl (Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R) (syn_csn (Class.cv (nb089_alpha_dummy_043 A B R))) (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R) (Class.cv (nb089_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0044 A B R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0044 A B R) 1))
    ·
      rw [fv_syn_csn]
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0046 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_044 u A B R) ∈ (((syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R)))).fv ∪ ((Class.cv u)).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0047 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_044 u A B R) ∈ (((syn_ccompl (Class.cab (nb089_alpha_dummy_047 u A B R) (syn_wrex (nb089_alpha_dummy_048 u A B R) (syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R))) (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb089_alpha_dummy_047 u A B R) (syn_wrex (nb089_alpha_dummy_048 u A B R) (Class.cv u) (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0046 u A B R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0046 u A B R) 1))
    ·
      rw [fv_syn_csn]
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0048 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_043 A B R) ∈ (((Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R) (syn_csn (Class.cv (nb089_alpha_dummy_043 A B R))) (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R) (syn_csn (Class.cv (nb089_alpha_dummy_043 A B R))) (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0044 A B R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0044 A B R) 1))
    ·
      rw [fv_syn_csn]
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0049 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_044 u A B R) ∈ (((Class.cab (nb089_alpha_dummy_047 u A B R) (syn_wrex (nb089_alpha_dummy_048 u A B R) (syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R))) (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_047 u A B R) (syn_wrex (nb089_alpha_dummy_048 u A B R) (syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R))) (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0046 u A B R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0046 u A B R) 1))
    ·
      rw [fv_syn_csn]
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0050 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_043 A B R) ∈ (((Class.cv (nb089_alpha_dummy_043 A B R))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0051 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_044 u A B R) ∈ (((Class.cv (nb089_alpha_dummy_044 u A B R))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0052 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_046 A B R) ∈ (((Class.cv (nb089_alpha_dummy_046 A B R))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0053 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_048 u A B R) ∈ (((Class.cv (nb089_alpha_dummy_048 u A B R))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0054 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_055 A B R) ∈ (((Wff.classMem (Class.cv (nb089_alpha_dummy_055 A B R)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb089_alpha_dummy_055 A B R)) (syn_c1c))).fv ∪ ((Class.cv (nb089_alpha_dummy_055 A B R))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0055 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_057 u A B R) ∈ (((Wff.classMem (Class.cv (nb089_alpha_dummy_057 u A B R)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb089_alpha_dummy_057 u A B R)) (syn_c1c))).fv ∪ ((Class.cv (nb089_alpha_dummy_057 u A B R))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0056 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_055 A B R) ∈ (((Class.cv (nb089_alpha_dummy_055 A B R))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0057 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_057 u A B R) ∈ (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0058 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_062 A B R) ∈ (((syn_cnin (Class.cv (nb089_alpha_dummy_062 A B R)) (Class.cv (nb089_alpha_dummy_063 A B R)))).fv ∪ ((syn_cnin (Class.cv (nb089_alpha_dummy_062 A B R)) (Class.cv (nb089_alpha_dummy_063 A B R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0059 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_065 u A B R) ∈ (((syn_cnin (Class.cv (nb089_alpha_dummy_065 u A B R)) (Class.cv (nb089_alpha_dummy_066 u A B R)))).fv ∪ ((syn_cnin (Class.cv (nb089_alpha_dummy_065 u A B R)) (Class.cv (nb089_alpha_dummy_066 u A B R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0060 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_062 A B R) ∈ (((Class.cv (nb089_alpha_dummy_062 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_063 A B R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0061 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_065 u A B R) ∈ (((Class.cv (nb089_alpha_dummy_065 u A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_066 u A B R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0062 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_063 A B R) ∈ (((syn_cnin (Class.cv (nb089_alpha_dummy_062 A B R)) (Class.cv (nb089_alpha_dummy_063 A B R)))).fv ∪ ((syn_cnin (Class.cv (nb089_alpha_dummy_062 A B R)) (Class.cv (nb089_alpha_dummy_063 A B R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0063 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_066 u A B R) ∈ (((syn_cnin (Class.cv (nb089_alpha_dummy_065 u A B R)) (Class.cv (nb089_alpha_dummy_066 u A B R)))).fv ∪ ((syn_cnin (Class.cv (nb089_alpha_dummy_065 u A B R)) (Class.cv (nb089_alpha_dummy_066 u A B R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0064 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_063 A B R) ∈ (((Class.cv (nb089_alpha_dummy_062 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_063 A B R))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0065 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_066 u A B R) ∈ (((Class.cv (nb089_alpha_dummy_065 u A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_066 u A B R))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0066 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_062 A B R) ∈ (((syn_ccompl (Class.cv (nb089_alpha_dummy_062 A B R)))).fv ∪ ((syn_ccompl (Class.cv (nb089_alpha_dummy_063 A B R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0067 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_065 u A B R) ∈ (((syn_ccompl (Class.cv (nb089_alpha_dummy_065 u A B R)))).fv ∪ ((syn_ccompl (Class.cv (nb089_alpha_dummy_066 u A B R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0068 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_062 A B R) ∈ (((Class.cv (nb089_alpha_dummy_062 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_062 A B R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0069 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_065 u A B R) ∈ (((Class.cv (nb089_alpha_dummy_065 u A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_065 u A B R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0070 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_063 A B R) ∈ (((syn_ccompl (Class.cv (nb089_alpha_dummy_062 A B R)))).fv ∪ ((syn_ccompl (Class.cv (nb089_alpha_dummy_063 A B R)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0071 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_066 u A B R) ∈ (((syn_ccompl (Class.cv (nb089_alpha_dummy_065 u A B R)))).fv ∪ ((syn_ccompl (Class.cv (nb089_alpha_dummy_066 u A B R)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0072 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_063 A B R) ∈ (((Class.cv (nb089_alpha_dummy_063 A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_063 A B R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0073 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_066 u A B R) ∈ (((Class.cv (nb089_alpha_dummy_066 u A B R))).fv ∪ ((Class.cv (nb089_alpha_dummy_066 u A B R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0074 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_000 A B R) ∈ ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb089_alpha_dummy_000 A B R))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0075 (u : Var) (A : Class) (B : Class) (R : Class) : u ∈ ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv u)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0076 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_000 A B R) ∈ (((syn_csn (Class.cv (nb089_alpha_dummy_043 A B R)))).fv ∪ ((Class.cv (nb089_alpha_dummy_000 A B R))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0077 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_000 A B R) ∈ (((syn_ccompl (Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R) (syn_csn (Class.cv (nb089_alpha_dummy_043 A B R))) (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R) (Class.cv (nb089_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0076 A B R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0076 A B R) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0078 (u : Var) (A : Class) (B : Class) (R : Class) : u ∈ (((syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R)))).fv ∪ ((Class.cv u)).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0079 (u : Var) (A : Class) (B : Class) (R : Class) : u ∈ (((syn_ccompl (Class.cab (nb089_alpha_dummy_047 u A B R) (syn_wrex (nb089_alpha_dummy_048 u A B R) (syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R))) (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R)) (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb089_alpha_dummy_047 u A B R) (syn_wrex (nb089_alpha_dummy_048 u A B R) (Class.cv u) (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0078 u A B R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0078 u A B R) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0080 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_000 A B R) ∈ (((Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R) (Class.cv (nb089_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R) (Class.cv (nb089_alpha_dummy_000 A B R)) (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0076 A B R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0076 A B R) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0081 (u : Var) (A : Class) (B : Class) (R : Class) : u ∈ (((Class.cab (nb089_alpha_dummy_047 u A B R) (syn_wrex (nb089_alpha_dummy_048 u A B R) (Class.cv u) (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_047 u A B R) (syn_wrex (nb089_alpha_dummy_048 u A B R) (Class.cv u) (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R)) (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))) (syn_csn (syn_c0c))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0078 u A B R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0078 u A B R) 1))
    ·
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0082 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_046 A B R) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0083 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_048 u A B R) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0084 (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_046 A B R) ∈ (((syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))).fv ∪ ((syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0085 (u : Var) (A : Class) (B : Class) (R : Class) : (nb089_alpha_dummy_048 u A B R) ∈ (((syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))).fv ∪ ((syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
