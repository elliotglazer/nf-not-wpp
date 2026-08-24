import NominalAlphaCompactEnvFreshSupport002
import NominalAlphaTransport
import WPPCompactSourceSyntax
import WPPCompactSyntaxFVExplicit
import CoreFVSimp
import CompactSyntaxFVDisable
import ReplaySupport.Basic
import AlphaFocusedSupport
import FocusedFVPaths

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

noncomputable def nb087_alpha_dummy_000 (A : Class) (B : Class) (C : Class) (R : Class) : Var := (freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0)

noncomputable def nb087_alpha_dummy_001 (A : Class) (B : Class) (C : Class) (R : Class) : Var := (freshVar (((syn_csn (Class.cv (nb087_alpha_dummy_000 A B C R)))).fv ∪ (C).fv) 0)

noncomputable def nb087_alpha_dummy_002 (A : Class) (B : Class) (C : Class) (R : Class) : Var := (freshVar (((syn_csn (Class.cv (nb087_alpha_dummy_000 A B C R)))).fv ∪ (C).fv) 1)

noncomputable def nb087_alpha_dummy_003 (C : Class) (d : Var) : Var := (freshVar (((syn_csn (Class.cv d))).fv ∪ (C).fv) 0)

noncomputable def nb087_alpha_dummy_004 (C : Class) (d : Var) : Var := (freshVar (((syn_csn (Class.cv d))).fv ∪ (C).fv) 1)

noncomputable def nb087_alpha_dummy_005 (A : Class) (B : Class) (C : Class) (R : Class) : Var := (freshVar (((syn_ccompl (Class.cab (nb087_alpha_dummy_001 A B C R) (syn_wrex (nb087_alpha_dummy_002 A B C R) (syn_csn (Class.cv (nb087_alpha_dummy_000 A B C R))) (Wff.classEq (Class.cv (nb087_alpha_dummy_001 A B C R)) (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb087_alpha_dummy_001 A B C R) (syn_wrex (nb087_alpha_dummy_002 A B C R) C (Wff.classEq (Class.cv (nb087_alpha_dummy_001 A B C R)) (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb087_alpha_dummy_006 (C : Class) (d : Var) : Var := (freshVar (((syn_ccompl (Class.cab (nb087_alpha_dummy_003 C d) (syn_wrex (nb087_alpha_dummy_004 C d) (syn_csn (Class.cv d)) (Wff.classEq (Class.cv (nb087_alpha_dummy_003 C d)) (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d)))))))).fv ∪ ((syn_ccompl (Class.cab (nb087_alpha_dummy_003 C d) (syn_wrex (nb087_alpha_dummy_004 C d) C (Wff.classEq (Class.cv (nb087_alpha_dummy_003 C d)) (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d))) (syn_csn (syn_c0c)))))))).fv) 0)

noncomputable def nb087_alpha_dummy_007 (A : Class) (B : Class) (C : Class) (R : Class) : Var := (freshVar (((Class.cab (nb087_alpha_dummy_001 A B C R) (syn_wrex (nb087_alpha_dummy_002 A B C R) (syn_csn (Class.cv (nb087_alpha_dummy_000 A B C R))) (Wff.classEq (Class.cv (nb087_alpha_dummy_001 A B C R)) (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R))))))).fv ∪ ((Class.cab (nb087_alpha_dummy_001 A B C R) (syn_wrex (nb087_alpha_dummy_002 A B C R) (syn_csn (Class.cv (nb087_alpha_dummy_000 A B C R))) (Wff.classEq (Class.cv (nb087_alpha_dummy_001 A B C R)) (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R))))))).fv) 0)

noncomputable def nb087_alpha_dummy_008 (C : Class) (d : Var) : Var := (freshVar (((Class.cab (nb087_alpha_dummy_003 C d) (syn_wrex (nb087_alpha_dummy_004 C d) (syn_csn (Class.cv d)) (Wff.classEq (Class.cv (nb087_alpha_dummy_003 C d)) (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d))))))).fv ∪ ((Class.cab (nb087_alpha_dummy_003 C d) (syn_wrex (nb087_alpha_dummy_004 C d) (syn_csn (Class.cv d)) (Wff.classEq (Class.cv (nb087_alpha_dummy_003 C d)) (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d))))))).fv) 0)

noncomputable def nb087_alpha_dummy_009 (A : Class) (B : Class) (C : Class) (R : Class) : Var := (freshVar (((Class.cv (nb087_alpha_dummy_000 A B C R))).fv) 0)

noncomputable def nb087_alpha_dummy_010 (d : Var) : Var := (freshVar (((Class.cv d)).fv) 0)

noncomputable def nb087_alpha_dummy_011 (A : Class) (B : Class) (C : Class) (R : Class) : Var := (freshVar (((Class.cv (nb087_alpha_dummy_002 A B C R))).fv) 0)

noncomputable def nb087_alpha_dummy_012 (A : Class) (B : Class) (C : Class) (R : Class) : Var := (freshVar (((Class.cv (nb087_alpha_dummy_002 A B C R))).fv) 1)

noncomputable def nb087_alpha_dummy_013 (C : Class) (d : Var) : Var := (freshVar (((Class.cv (nb087_alpha_dummy_004 C d))).fv) 0)

noncomputable def nb087_alpha_dummy_014 (C : Class) (d : Var) : Var := (freshVar (((Class.cv (nb087_alpha_dummy_004 C d))).fv) 1)

noncomputable def nb087_alpha_dummy_015 (A : Class) (B : Class) (C : Class) (R : Class) : Var := (freshVar (((Wff.classMem (Class.cv (nb087_alpha_dummy_011 A B C R)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb087_alpha_dummy_011 A B C R)) (syn_c1c))).fv ∪ ((Class.cv (nb087_alpha_dummy_011 A B C R))).fv) 0)

noncomputable def nb087_alpha_dummy_016 (C : Class) (d : Var) : Var := (freshVar (((Wff.classMem (Class.cv (nb087_alpha_dummy_013 C d)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb087_alpha_dummy_013 C d)) (syn_c1c))).fv ∪ ((Class.cv (nb087_alpha_dummy_013 C d))).fv) 0)

noncomputable def nb087_alpha_dummy_017 (A : Class) (B : Class) (C : Class) (R : Class) : Var := (freshVar (((Class.cv (nb087_alpha_dummy_011 A B C R))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb087_alpha_dummy_018 (A : Class) (B : Class) (C : Class) (R : Class) : Var := (freshVar (((Class.cv (nb087_alpha_dummy_011 A B C R))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb087_alpha_dummy_019 (A : Class) (B : Class) (C : Class) (R : Class) : Var := (freshVar (((Class.cv (nb087_alpha_dummy_011 A B C R))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb087_alpha_dummy_020 (C : Class) (d : Var) : Var := (freshVar (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪ ((syn_c1c)).fv) 0)

noncomputable def nb087_alpha_dummy_021 (C : Class) (d : Var) : Var := (freshVar (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪ ((syn_c1c)).fv) 1)

noncomputable def nb087_alpha_dummy_022 (C : Class) (d : Var) : Var := (freshVar (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪ ((syn_c1c)).fv) 2)

noncomputable def nb087_alpha_dummy_023 (A : Class) (B : Class) (C : Class) (R : Class) : Var := (freshVar (((syn_cnin (Class.cv (nb087_alpha_dummy_018 A B C R)) (Class.cv (nb087_alpha_dummy_019 A B C R)))).fv ∪ ((syn_cnin (Class.cv (nb087_alpha_dummy_018 A B C R)) (Class.cv (nb087_alpha_dummy_019 A B C R)))).fv) 0)

noncomputable def nb087_alpha_dummy_024 (C : Class) (d : Var) : Var := (freshVar (((syn_cnin (Class.cv (nb087_alpha_dummy_021 C d)) (Class.cv (nb087_alpha_dummy_022 C d)))).fv ∪ ((syn_cnin (Class.cv (nb087_alpha_dummy_021 C d)) (Class.cv (nb087_alpha_dummy_022 C d)))).fv) 0)

noncomputable def nb087_alpha_dummy_025 (A : Class) (B : Class) (C : Class) (R : Class) : Var := (freshVar (((Class.cv (nb087_alpha_dummy_018 A B C R))).fv ∪ ((Class.cv (nb087_alpha_dummy_019 A B C R))).fv) 0)

noncomputable def nb087_alpha_dummy_026 (C : Class) (d : Var) : Var := (freshVar (((Class.cv (nb087_alpha_dummy_021 C d))).fv ∪ ((Class.cv (nb087_alpha_dummy_022 C d))).fv) 0)

noncomputable def nb087_alpha_dummy_027 (A : Class) (B : Class) (C : Class) (R : Class) : Var := (freshVar (((syn_ccompl (Class.cv (nb087_alpha_dummy_018 A B C R)))).fv ∪ ((syn_ccompl (Class.cv (nb087_alpha_dummy_019 A B C R)))).fv) 0)

noncomputable def nb087_alpha_dummy_028 (C : Class) (d : Var) : Var := (freshVar (((syn_ccompl (Class.cv (nb087_alpha_dummy_021 C d)))).fv ∪ ((syn_ccompl (Class.cv (nb087_alpha_dummy_022 C d)))).fv) 0)

noncomputable def nb087_alpha_dummy_029 (A : Class) (B : Class) (C : Class) (R : Class) : Var := (freshVar (((Class.cv (nb087_alpha_dummy_018 A B C R))).fv ∪ ((Class.cv (nb087_alpha_dummy_018 A B C R))).fv) 0)

noncomputable def nb087_alpha_dummy_030 (C : Class) (d : Var) : Var := (freshVar (((Class.cv (nb087_alpha_dummy_021 C d))).fv ∪ ((Class.cv (nb087_alpha_dummy_021 C d))).fv) 0)

noncomputable def nb087_alpha_dummy_031 (A : Class) (B : Class) (C : Class) (R : Class) : Var := (freshVar (((Class.cv (nb087_alpha_dummy_019 A B C R))).fv ∪ ((Class.cv (nb087_alpha_dummy_019 A B C R))).fv) 0)

noncomputable def nb087_alpha_dummy_032 (C : Class) (d : Var) : Var := (freshVar (((Class.cv (nb087_alpha_dummy_022 C d))).fv ∪ ((Class.cv (nb087_alpha_dummy_022 C d))).fv) 0)

noncomputable def nb087_alpha_dummy_033 (A : Class) (B : Class) (C : Class) (R : Class) : Var := (freshVar (((Class.cab (nb087_alpha_dummy_001 A B C R) (syn_wrex (nb087_alpha_dummy_002 A B C R) C (Wff.classEq (Class.cv (nb087_alpha_dummy_001 A B C R)) (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb087_alpha_dummy_001 A B C R) (syn_wrex (nb087_alpha_dummy_002 A B C R) C (Wff.classEq (Class.cv (nb087_alpha_dummy_001 A B C R)) (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb087_alpha_dummy_034 (C : Class) (d : Var) : Var := (freshVar (((Class.cab (nb087_alpha_dummy_003 C d) (syn_wrex (nb087_alpha_dummy_004 C d) C (Wff.classEq (Class.cv (nb087_alpha_dummy_003 C d)) (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb087_alpha_dummy_003 C d) (syn_wrex (nb087_alpha_dummy_004 C d) C (Wff.classEq (Class.cv (nb087_alpha_dummy_003 C d)) (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d))) (syn_csn (syn_c0c))))))).fv) 0)

noncomputable def nb087_alpha_dummy_035 (A : Class) (B : Class) (C : Class) (R : Class) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb087_alpha_dummy_036 (C : Class) (d : Var) : Var := (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

noncomputable def nb087_alpha_dummy_037 (A : Class) (B : Class) (C : Class) (R : Class) : Var := (freshVar (((syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R)))).fv ∪ ((syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R)))).fv) 0)

noncomputable def nb087_alpha_dummy_038 (C : Class) (d : Var) : Var := (freshVar (((syn_cphi (Class.cv (nb087_alpha_dummy_004 C d)))).fv ∪ ((syn_cphi (Class.cv (nb087_alpha_dummy_004 C d)))).fv) 0)

theorem nb087_fresh_000 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_007 A B C R) ∉ (((Class.cab (nb087_alpha_dummy_001 A B C R) (syn_wrex (nb087_alpha_dummy_002 A B C R) (syn_csn (Class.cv (nb087_alpha_dummy_000 A B C R))) (Wff.classEq (Class.cv (nb087_alpha_dummy_001 A B C R)) (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R))))))).fv ∪ ((Class.cab (nb087_alpha_dummy_001 A B C R) (syn_wrex (nb087_alpha_dummy_002 A B C R) (syn_csn (Class.cv (nb087_alpha_dummy_000 A B C R))) (Wff.classEq (Class.cv (nb087_alpha_dummy_001 A B C R)) (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R))))))).fv) := by
  simpa only [nb087_alpha_dummy_007] using freshVar_not_mem (((Class.cab (nb087_alpha_dummy_001 A B C R) (syn_wrex (nb087_alpha_dummy_002 A B C R) (syn_csn (Class.cv (nb087_alpha_dummy_000 A B C R))) (Wff.classEq (Class.cv (nb087_alpha_dummy_001 A B C R)) (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R))))))).fv ∪ ((Class.cab (nb087_alpha_dummy_001 A B C R) (syn_wrex (nb087_alpha_dummy_002 A B C R) (syn_csn (Class.cv (nb087_alpha_dummy_000 A B C R))) (Wff.classEq (Class.cv (nb087_alpha_dummy_001 A B C R)) (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R))))))).fv) 0

theorem nb087_fresh_001 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_033 A B C R) ∉ (((Class.cab (nb087_alpha_dummy_001 A B C R) (syn_wrex (nb087_alpha_dummy_002 A B C R) C (Wff.classEq (Class.cv (nb087_alpha_dummy_001 A B C R)) (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb087_alpha_dummy_001 A B C R) (syn_wrex (nb087_alpha_dummy_002 A B C R) C (Wff.classEq (Class.cv (nb087_alpha_dummy_001 A B C R)) (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb087_alpha_dummy_033] using freshVar_not_mem (((Class.cab (nb087_alpha_dummy_001 A B C R) (syn_wrex (nb087_alpha_dummy_002 A B C R) C (Wff.classEq (Class.cv (nb087_alpha_dummy_001 A B C R)) (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb087_alpha_dummy_001 A B C R) (syn_wrex (nb087_alpha_dummy_002 A B C R) C (Wff.classEq (Class.cv (nb087_alpha_dummy_001 A B C R)) (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb087_fresh_002 (C : Class) (d : Var) : (nb087_alpha_dummy_008 C d) ∉ (((Class.cab (nb087_alpha_dummy_003 C d) (syn_wrex (nb087_alpha_dummy_004 C d) (syn_csn (Class.cv d)) (Wff.classEq (Class.cv (nb087_alpha_dummy_003 C d)) (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d))))))).fv ∪ ((Class.cab (nb087_alpha_dummy_003 C d) (syn_wrex (nb087_alpha_dummy_004 C d) (syn_csn (Class.cv d)) (Wff.classEq (Class.cv (nb087_alpha_dummy_003 C d)) (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d))))))).fv) := by
  simpa only [nb087_alpha_dummy_008] using freshVar_not_mem (((Class.cab (nb087_alpha_dummy_003 C d) (syn_wrex (nb087_alpha_dummy_004 C d) (syn_csn (Class.cv d)) (Wff.classEq (Class.cv (nb087_alpha_dummy_003 C d)) (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d))))))).fv ∪ ((Class.cab (nb087_alpha_dummy_003 C d) (syn_wrex (nb087_alpha_dummy_004 C d) (syn_csn (Class.cv d)) (Wff.classEq (Class.cv (nb087_alpha_dummy_003 C d)) (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d))))))).fv) 0

theorem nb087_fresh_003 (C : Class) (d : Var) : (nb087_alpha_dummy_034 C d) ∉ (((Class.cab (nb087_alpha_dummy_003 C d) (syn_wrex (nb087_alpha_dummy_004 C d) C (Wff.classEq (Class.cv (nb087_alpha_dummy_003 C d)) (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb087_alpha_dummy_003 C d) (syn_wrex (nb087_alpha_dummy_004 C d) C (Wff.classEq (Class.cv (nb087_alpha_dummy_003 C d)) (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d))) (syn_csn (syn_c0c))))))).fv) := by
  simpa only [nb087_alpha_dummy_034] using freshVar_not_mem (((Class.cab (nb087_alpha_dummy_003 C d) (syn_wrex (nb087_alpha_dummy_004 C d) C (Wff.classEq (Class.cv (nb087_alpha_dummy_003 C d)) (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d))) (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb087_alpha_dummy_003 C d) (syn_wrex (nb087_alpha_dummy_004 C d) C (Wff.classEq (Class.cv (nb087_alpha_dummy_003 C d)) (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d))) (syn_csn (syn_c0c))))))).fv) 0

theorem nb087_fresh_004 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_009 A B C R) ∉ (((Class.cv (nb087_alpha_dummy_000 A B C R))).fv) := by
  simpa only [nb087_alpha_dummy_009] using freshVar_not_mem (((Class.cv (nb087_alpha_dummy_000 A B C R))).fv) 0

theorem nb087_fresh_005 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_011 A B C R) ∉ (((Class.cv (nb087_alpha_dummy_002 A B C R))).fv) := by
  simpa only [nb087_alpha_dummy_011] using freshVar_not_mem (((Class.cv (nb087_alpha_dummy_002 A B C R))).fv) 0

theorem nb087_fresh_006 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_012 A B C R) ∉ (((Class.cv (nb087_alpha_dummy_002 A B C R))).fv) := by
  simpa only [nb087_alpha_dummy_012] using freshVar_not_mem (((Class.cv (nb087_alpha_dummy_002 A B C R))).fv) 1

theorem nb087_distinct_007 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_011 A B C R) ≠ (nb087_alpha_dummy_012 A B C R) := by
  simpa only [nb087_alpha_dummy_011, nb087_alpha_dummy_012] using
    (freshVar_injective (((Class.cv (nb087_alpha_dummy_002 A B C R))).fv) (i := 0) (j := 1) (by decide))

theorem nb087_fresh_008 (C : Class) (d : Var) : (nb087_alpha_dummy_013 C d) ∉ (((Class.cv (nb087_alpha_dummy_004 C d))).fv) := by
  simpa only [nb087_alpha_dummy_013] using freshVar_not_mem (((Class.cv (nb087_alpha_dummy_004 C d))).fv) 0

theorem nb087_fresh_009 (C : Class) (d : Var) : (nb087_alpha_dummy_014 C d) ∉ (((Class.cv (nb087_alpha_dummy_004 C d))).fv) := by
  simpa only [nb087_alpha_dummy_014] using freshVar_not_mem (((Class.cv (nb087_alpha_dummy_004 C d))).fv) 1

theorem nb087_distinct_010 (C : Class) (d : Var) : (nb087_alpha_dummy_013 C d) ≠ (nb087_alpha_dummy_014 C d) := by
  simpa only [nb087_alpha_dummy_013, nb087_alpha_dummy_014] using
    (freshVar_injective (((Class.cv (nb087_alpha_dummy_004 C d))).fv) (i := 0) (j := 1) (by decide))

theorem nb087_fresh_011 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_017 A B C R) ∉ (((Class.cv (nb087_alpha_dummy_011 A B C R))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb087_alpha_dummy_017] using freshVar_not_mem (((Class.cv (nb087_alpha_dummy_011 A B C R))).fv ∪ ((syn_c1c)).fv) 0

theorem nb087_fresh_012 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_018 A B C R) ∉ (((Class.cv (nb087_alpha_dummy_011 A B C R))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb087_alpha_dummy_018] using freshVar_not_mem (((Class.cv (nb087_alpha_dummy_011 A B C R))).fv ∪ ((syn_c1c)).fv) 1

theorem nb087_fresh_013 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_019 A B C R) ∉ (((Class.cv (nb087_alpha_dummy_011 A B C R))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb087_alpha_dummy_019] using freshVar_not_mem (((Class.cv (nb087_alpha_dummy_011 A B C R))).fv ∪ ((syn_c1c)).fv) 2

theorem nb087_distinct_014 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_017 A B C R) ≠ (nb087_alpha_dummy_018 A B C R) := by
  simpa only [nb087_alpha_dummy_017, nb087_alpha_dummy_018] using
    (freshVar_injective (((Class.cv (nb087_alpha_dummy_011 A B C R))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb087_distinct_015 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_017 A B C R) ≠ (nb087_alpha_dummy_019 A B C R) := by
  simpa only [nb087_alpha_dummy_017, nb087_alpha_dummy_019] using
    (freshVar_injective (((Class.cv (nb087_alpha_dummy_011 A B C R))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb087_distinct_016 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_018 A B C R) ≠ (nb087_alpha_dummy_019 A B C R) := by
  simpa only [nb087_alpha_dummy_018, nb087_alpha_dummy_019] using
    (freshVar_injective (((Class.cv (nb087_alpha_dummy_011 A B C R))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb087_fresh_017 (C : Class) (d : Var) : (nb087_alpha_dummy_020 C d) ∉ (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb087_alpha_dummy_020] using freshVar_not_mem (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪ ((syn_c1c)).fv) 0

theorem nb087_fresh_018 (C : Class) (d : Var) : (nb087_alpha_dummy_021 C d) ∉ (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb087_alpha_dummy_021] using freshVar_not_mem (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪ ((syn_c1c)).fv) 1

theorem nb087_fresh_019 (C : Class) (d : Var) : (nb087_alpha_dummy_022 C d) ∉ (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb087_alpha_dummy_022] using freshVar_not_mem (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪ ((syn_c1c)).fv) 2

theorem nb087_distinct_020 (C : Class) (d : Var) : (nb087_alpha_dummy_020 C d) ≠ (nb087_alpha_dummy_021 C d) := by
  simpa only [nb087_alpha_dummy_020, nb087_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))

theorem nb087_distinct_021 (C : Class) (d : Var) : (nb087_alpha_dummy_020 C d) ≠ (nb087_alpha_dummy_022 C d) := by
  simpa only [nb087_alpha_dummy_020, nb087_alpha_dummy_022] using
    (freshVar_injective (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))

theorem nb087_distinct_022 (C : Class) (d : Var) : (nb087_alpha_dummy_021 C d) ≠ (nb087_alpha_dummy_022 C d) := by
  simpa only [nb087_alpha_dummy_021, nb087_alpha_dummy_022] using
    (freshVar_injective (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))

theorem nb087_fresh_023 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_029 A B C R) ∉ (((Class.cv (nb087_alpha_dummy_018 A B C R))).fv ∪ ((Class.cv (nb087_alpha_dummy_018 A B C R))).fv) := by
  simpa only [nb087_alpha_dummy_029] using freshVar_not_mem (((Class.cv (nb087_alpha_dummy_018 A B C R))).fv ∪ ((Class.cv (nb087_alpha_dummy_018 A B C R))).fv) 0

theorem nb087_fresh_024 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_025 A B C R) ∉ (((Class.cv (nb087_alpha_dummy_018 A B C R))).fv ∪ ((Class.cv (nb087_alpha_dummy_019 A B C R))).fv) := by
  simpa only [nb087_alpha_dummy_025] using freshVar_not_mem (((Class.cv (nb087_alpha_dummy_018 A B C R))).fv ∪ ((Class.cv (nb087_alpha_dummy_019 A B C R))).fv) 0

theorem nb087_fresh_025 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_031 A B C R) ∉ (((Class.cv (nb087_alpha_dummy_019 A B C R))).fv ∪ ((Class.cv (nb087_alpha_dummy_019 A B C R))).fv) := by
  simpa only [nb087_alpha_dummy_031] using freshVar_not_mem (((Class.cv (nb087_alpha_dummy_019 A B C R))).fv ∪ ((Class.cv (nb087_alpha_dummy_019 A B C R))).fv) 0

theorem nb087_fresh_026 (C : Class) (d : Var) : (nb087_alpha_dummy_030 C d) ∉ (((Class.cv (nb087_alpha_dummy_021 C d))).fv ∪ ((Class.cv (nb087_alpha_dummy_021 C d))).fv) := by
  simpa only [nb087_alpha_dummy_030] using freshVar_not_mem (((Class.cv (nb087_alpha_dummy_021 C d))).fv ∪ ((Class.cv (nb087_alpha_dummy_021 C d))).fv) 0

theorem nb087_fresh_027 (C : Class) (d : Var) : (nb087_alpha_dummy_026 C d) ∉ (((Class.cv (nb087_alpha_dummy_021 C d))).fv ∪ ((Class.cv (nb087_alpha_dummy_022 C d))).fv) := by
  simpa only [nb087_alpha_dummy_026] using freshVar_not_mem (((Class.cv (nb087_alpha_dummy_021 C d))).fv ∪ ((Class.cv (nb087_alpha_dummy_022 C d))).fv) 0

theorem nb087_fresh_028 (C : Class) (d : Var) : (nb087_alpha_dummy_032 C d) ∉ (((Class.cv (nb087_alpha_dummy_022 C d))).fv ∪ ((Class.cv (nb087_alpha_dummy_022 C d))).fv) := by
  simpa only [nb087_alpha_dummy_032] using freshVar_not_mem (((Class.cv (nb087_alpha_dummy_022 C d))).fv ∪ ((Class.cv (nb087_alpha_dummy_022 C d))).fv) 0

theorem nb087_fresh_029 (d : Var) : (nb087_alpha_dummy_010 d) ∉ (((Class.cv d)).fv) := by
  simpa only [nb087_alpha_dummy_010] using freshVar_not_mem (((Class.cv d)).fv) 0

theorem nb087_fresh_030 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_015 A B C R) ∉ (((Wff.classMem (Class.cv (nb087_alpha_dummy_011 A B C R)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb087_alpha_dummy_011 A B C R)) (syn_c1c))).fv ∪ ((Class.cv (nb087_alpha_dummy_011 A B C R))).fv) := by
  simpa only [nb087_alpha_dummy_015] using freshVar_not_mem (((Wff.classMem (Class.cv (nb087_alpha_dummy_011 A B C R)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb087_alpha_dummy_011 A B C R)) (syn_c1c))).fv ∪ ((Class.cv (nb087_alpha_dummy_011 A B C R))).fv) 0

theorem nb087_fresh_031 (C : Class) (d : Var) : (nb087_alpha_dummy_016 C d) ∉ (((Wff.classMem (Class.cv (nb087_alpha_dummy_013 C d)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb087_alpha_dummy_013 C d)) (syn_c1c))).fv ∪ ((Class.cv (nb087_alpha_dummy_013 C d))).fv) := by
  simpa only [nb087_alpha_dummy_016] using freshVar_not_mem (((Wff.classMem (Class.cv (nb087_alpha_dummy_013 C d)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb087_alpha_dummy_013 C d)) (syn_c1c))).fv ∪ ((Class.cv (nb087_alpha_dummy_013 C d))).fv) 0

theorem nb087_fresh_032 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_005 A B C R) ∉ (((syn_ccompl (Class.cab (nb087_alpha_dummy_001 A B C R) (syn_wrex (nb087_alpha_dummy_002 A B C R) (syn_csn (Class.cv (nb087_alpha_dummy_000 A B C R))) (Wff.classEq (Class.cv (nb087_alpha_dummy_001 A B C R)) (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb087_alpha_dummy_001 A B C R) (syn_wrex (nb087_alpha_dummy_002 A B C R) C (Wff.classEq (Class.cv (nb087_alpha_dummy_001 A B C R)) (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb087_alpha_dummy_005] using freshVar_not_mem (((syn_ccompl (Class.cab (nb087_alpha_dummy_001 A B C R) (syn_wrex (nb087_alpha_dummy_002 A B C R) (syn_csn (Class.cv (nb087_alpha_dummy_000 A B C R))) (Wff.classEq (Class.cv (nb087_alpha_dummy_001 A B C R)) (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb087_alpha_dummy_001 A B C R) (syn_wrex (nb087_alpha_dummy_002 A B C R) C (Wff.classEq (Class.cv (nb087_alpha_dummy_001 A B C R)) (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb087_fresh_033 (C : Class) (d : Var) : (nb087_alpha_dummy_006 C d) ∉ (((syn_ccompl (Class.cab (nb087_alpha_dummy_003 C d) (syn_wrex (nb087_alpha_dummy_004 C d) (syn_csn (Class.cv d)) (Wff.classEq (Class.cv (nb087_alpha_dummy_003 C d)) (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d)))))))).fv ∪ ((syn_ccompl (Class.cab (nb087_alpha_dummy_003 C d) (syn_wrex (nb087_alpha_dummy_004 C d) C (Wff.classEq (Class.cv (nb087_alpha_dummy_003 C d)) (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d))) (syn_csn (syn_c0c)))))))).fv) := by
  simpa only [nb087_alpha_dummy_006] using freshVar_not_mem (((syn_ccompl (Class.cab (nb087_alpha_dummy_003 C d) (syn_wrex (nb087_alpha_dummy_004 C d) (syn_csn (Class.cv d)) (Wff.classEq (Class.cv (nb087_alpha_dummy_003 C d)) (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d)))))))).fv ∪ ((syn_ccompl (Class.cab (nb087_alpha_dummy_003 C d) (syn_wrex (nb087_alpha_dummy_004 C d) C (Wff.classEq (Class.cv (nb087_alpha_dummy_003 C d)) (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d))) (syn_csn (syn_c0c)))))))).fv) 0

theorem nb087_fresh_034 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_027 A B C R) ∉ (((syn_ccompl (Class.cv (nb087_alpha_dummy_018 A B C R)))).fv ∪ ((syn_ccompl (Class.cv (nb087_alpha_dummy_019 A B C R)))).fv) := by
  simpa only [nb087_alpha_dummy_027] using freshVar_not_mem (((syn_ccompl (Class.cv (nb087_alpha_dummy_018 A B C R)))).fv ∪ ((syn_ccompl (Class.cv (nb087_alpha_dummy_019 A B C R)))).fv) 0

theorem nb087_fresh_035 (C : Class) (d : Var) : (nb087_alpha_dummy_028 C d) ∉ (((syn_ccompl (Class.cv (nb087_alpha_dummy_021 C d)))).fv ∪ ((syn_ccompl (Class.cv (nb087_alpha_dummy_022 C d)))).fv) := by
  simpa only [nb087_alpha_dummy_028] using freshVar_not_mem (((syn_ccompl (Class.cv (nb087_alpha_dummy_021 C d)))).fv ∪ ((syn_ccompl (Class.cv (nb087_alpha_dummy_022 C d)))).fv) 0

theorem nb087_fresh_036 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_035 A B C R) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb087_alpha_dummy_035] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb087_fresh_037 (C : Class) (d : Var) : (nb087_alpha_dummy_036 C d) ∉ (((syn_ccompl (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  simpa only [nb087_alpha_dummy_036] using freshVar_not_mem (((syn_ccompl (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0

theorem nb087_fresh_038 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_023 A B C R) ∉ (((syn_cnin (Class.cv (nb087_alpha_dummy_018 A B C R)) (Class.cv (nb087_alpha_dummy_019 A B C R)))).fv ∪ ((syn_cnin (Class.cv (nb087_alpha_dummy_018 A B C R)) (Class.cv (nb087_alpha_dummy_019 A B C R)))).fv) := by
  simpa only [nb087_alpha_dummy_023] using freshVar_not_mem (((syn_cnin (Class.cv (nb087_alpha_dummy_018 A B C R)) (Class.cv (nb087_alpha_dummy_019 A B C R)))).fv ∪ ((syn_cnin (Class.cv (nb087_alpha_dummy_018 A B C R)) (Class.cv (nb087_alpha_dummy_019 A B C R)))).fv) 0

theorem nb087_fresh_039 (C : Class) (d : Var) : (nb087_alpha_dummy_024 C d) ∉ (((syn_cnin (Class.cv (nb087_alpha_dummy_021 C d)) (Class.cv (nb087_alpha_dummy_022 C d)))).fv ∪ ((syn_cnin (Class.cv (nb087_alpha_dummy_021 C d)) (Class.cv (nb087_alpha_dummy_022 C d)))).fv) := by
  simpa only [nb087_alpha_dummy_024] using freshVar_not_mem (((syn_cnin (Class.cv (nb087_alpha_dummy_021 C d)) (Class.cv (nb087_alpha_dummy_022 C d)))).fv ∪ ((syn_cnin (Class.cv (nb087_alpha_dummy_021 C d)) (Class.cv (nb087_alpha_dummy_022 C d)))).fv) 0

theorem nb087_fresh_040 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_037 A B C R) ∉ (((syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R)))).fv ∪ ((syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R)))).fv) := by
  simpa only [nb087_alpha_dummy_037] using freshVar_not_mem (((syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R)))).fv ∪ ((syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R)))).fv) 0

theorem nb087_fresh_041 (C : Class) (d : Var) : (nb087_alpha_dummy_038 C d) ∉ (((syn_cphi (Class.cv (nb087_alpha_dummy_004 C d)))).fv ∪ ((syn_cphi (Class.cv (nb087_alpha_dummy_004 C d)))).fv) := by
  simpa only [nb087_alpha_dummy_038] using freshVar_not_mem (((syn_cphi (Class.cv (nb087_alpha_dummy_004 C d)))).fv ∪ ((syn_cphi (Class.cv (nb087_alpha_dummy_004 C d)))).fv) 0

theorem nb087_fresh_042 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_001 A B C R) ∉ (((syn_csn (Class.cv (nb087_alpha_dummy_000 A B C R)))).fv ∪ (C).fv) := by
  simpa only [nb087_alpha_dummy_001] using freshVar_not_mem (((syn_csn (Class.cv (nb087_alpha_dummy_000 A B C R)))).fv ∪ (C).fv) 0

theorem nb087_fresh_043 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_002 A B C R) ∉ (((syn_csn (Class.cv (nb087_alpha_dummy_000 A B C R)))).fv ∪ (C).fv) := by
  simpa only [nb087_alpha_dummy_002] using freshVar_not_mem (((syn_csn (Class.cv (nb087_alpha_dummy_000 A B C R)))).fv ∪ (C).fv) 1

theorem nb087_distinct_044 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_001 A B C R) ≠ (nb087_alpha_dummy_002 A B C R) := by
  simpa only [nb087_alpha_dummy_001, nb087_alpha_dummy_002] using
    (freshVar_injective (((syn_csn (Class.cv (nb087_alpha_dummy_000 A B C R)))).fv ∪ (C).fv) (i := 0) (j := 1) (by decide))

theorem nb087_fresh_045 (C : Class) (d : Var) : (nb087_alpha_dummy_003 C d) ∉ (((syn_csn (Class.cv d))).fv ∪ (C).fv) := by
  simpa only [nb087_alpha_dummy_003] using freshVar_not_mem (((syn_csn (Class.cv d))).fv ∪ (C).fv) 0

theorem nb087_fresh_046 (C : Class) (d : Var) : (nb087_alpha_dummy_004 C d) ∉ (((syn_csn (Class.cv d))).fv ∪ (C).fv) := by
  simpa only [nb087_alpha_dummy_004] using freshVar_not_mem (((syn_csn (Class.cv d))).fv ∪ (C).fv) 1

theorem nb087_distinct_047 (C : Class) (d : Var) : (nb087_alpha_dummy_003 C d) ≠ (nb087_alpha_dummy_004 C d) := by
  simpa only [nb087_alpha_dummy_003, nb087_alpha_dummy_004] using
    (freshVar_injective (((syn_csn (Class.cv d))).fv ∪ (C).fv) (i := 0) (j := 1) (by decide))

theorem nb087_fresh_048 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_000 A B C R) ∉ ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) := by
  simpa only [nb087_alpha_dummy_000] using freshVar_not_mem ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0

theorem nb087_support_mem_0000 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_000 A B C R) ∈ (((syn_csn (Class.cv (nb087_alpha_dummy_000 A B C R)))).fv ∪ (C).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0001 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_000 A B C R) ∈ (((syn_ccompl (Class.cab (nb087_alpha_dummy_001 A B C R) (syn_wrex (nb087_alpha_dummy_002 A B C R) (syn_csn (Class.cv (nb087_alpha_dummy_000 A B C R))) (Wff.classEq (Class.cv (nb087_alpha_dummy_001 A B C R)) (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R)))))))).fv ∪ ((syn_ccompl (Class.cab (nb087_alpha_dummy_001 A B C R) (syn_wrex (nb087_alpha_dummy_002 A B C R) C (Wff.classEq (Class.cv (nb087_alpha_dummy_001 A B C R)) (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb087_support_mem_0000 A B C R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb087_support_mem_0000 A B C R) 1))
    ·
      rw [fv_syn_csn]
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb087_support_mem_0002 (C : Class) (d : Var) : d ∈ (((syn_csn (Class.cv d))).fv ∪ (C).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0003 (C : Class) (d : Var) : d ∈ (((syn_ccompl (Class.cab (nb087_alpha_dummy_003 C d) (syn_wrex (nb087_alpha_dummy_004 C d) (syn_csn (Class.cv d)) (Wff.classEq (Class.cv (nb087_alpha_dummy_003 C d)) (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d)))))))).fv ∪ ((syn_ccompl (Class.cab (nb087_alpha_dummy_003 C d) (syn_wrex (nb087_alpha_dummy_004 C d) C (Wff.classEq (Class.cv (nb087_alpha_dummy_003 C d)) (syn_cun (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d))) (syn_csn (syn_c0c)))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb087_support_mem_0002 C d) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb087_support_mem_0002 C d) 1))
    ·
      rw [fv_syn_csn]
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb087_support_mem_0004 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_000 A B C R) ∈ (((Class.cab (nb087_alpha_dummy_001 A B C R) (syn_wrex (nb087_alpha_dummy_002 A B C R) (syn_csn (Class.cv (nb087_alpha_dummy_000 A B C R))) (Wff.classEq (Class.cv (nb087_alpha_dummy_001 A B C R)) (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R))))))).fv ∪ ((Class.cab (nb087_alpha_dummy_001 A B C R) (syn_wrex (nb087_alpha_dummy_002 A B C R) (syn_csn (Class.cv (nb087_alpha_dummy_000 A B C R))) (Wff.classEq (Class.cv (nb087_alpha_dummy_001 A B C R)) (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb087_support_mem_0000 A B C R) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb087_support_mem_0000 A B C R) 1))
    ·
      rw [fv_syn_csn]
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb087_support_mem_0005 (C : Class) (d : Var) : d ∈ (((Class.cab (nb087_alpha_dummy_003 C d) (syn_wrex (nb087_alpha_dummy_004 C d) (syn_csn (Class.cv d)) (Wff.classEq (Class.cv (nb087_alpha_dummy_003 C d)) (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d))))))).fv ∪ ((Class.cab (nb087_alpha_dummy_003 C d) (syn_wrex (nb087_alpha_dummy_004 C d) (syn_csn (Class.cv d)) (Wff.classEq (Class.cv (nb087_alpha_dummy_003 C d)) (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d))))))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cab]
  apply Finset.mem_erase.mpr
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb087_support_mem_0002 C d) 0))
  ·
    rw [fv_syn_wrex]
    apply Finset.mem_union_left
    apply Finset.mem_erase.mpr
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb087_support_mem_0002 C d) 1))
    ·
      rw [fv_syn_csn]
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb087_support_mem_0006 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_000 A B C R) ∈ (((Class.cv (nb087_alpha_dummy_000 A B C R))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0007 (d : Var) : d ∈ (((Class.cv d)).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0008 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_002 A B C R) ∈ (((Class.cv (nb087_alpha_dummy_002 A B C R))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0009 (C : Class) (d : Var) : (nb087_alpha_dummy_004 C d) ∈ (((Class.cv (nb087_alpha_dummy_004 C d))).fv) := by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0010 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_011 A B C R) ∈ (((Wff.classMem (Class.cv (nb087_alpha_dummy_011 A B C R)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb087_alpha_dummy_011 A B C R)) (syn_c1c))).fv ∪ ((Class.cv (nb087_alpha_dummy_011 A B C R))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0011 (C : Class) (d : Var) : (nb087_alpha_dummy_013 C d) ∈ (((Wff.classMem (Class.cv (nb087_alpha_dummy_013 C d)) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv (nb087_alpha_dummy_013 C d)) (syn_c1c))).fv ∪ ((Class.cv (nb087_alpha_dummy_013 C d))).fv) := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [fv_wff_classMem]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0012 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_011 A B C R) ∈ (((Class.cv (nb087_alpha_dummy_011 A B C R))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0013 (C : Class) (d : Var) : (nb087_alpha_dummy_013 C d) ∈ (((Class.cv (nb087_alpha_dummy_013 C d))).fv ∪ ((syn_c1c)).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0014 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_018 A B C R) ∈ (((syn_cnin (Class.cv (nb087_alpha_dummy_018 A B C R)) (Class.cv (nb087_alpha_dummy_019 A B C R)))).fv ∪ ((syn_cnin (Class.cv (nb087_alpha_dummy_018 A B C R)) (Class.cv (nb087_alpha_dummy_019 A B C R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0015 (C : Class) (d : Var) : (nb087_alpha_dummy_021 C d) ∈ (((syn_cnin (Class.cv (nb087_alpha_dummy_021 C d)) (Class.cv (nb087_alpha_dummy_022 C d)))).fv ∪ ((syn_cnin (Class.cv (nb087_alpha_dummy_021 C d)) (Class.cv (nb087_alpha_dummy_022 C d)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0016 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_018 A B C R) ∈ (((Class.cv (nb087_alpha_dummy_018 A B C R))).fv ∪ ((Class.cv (nb087_alpha_dummy_019 A B C R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0017 (C : Class) (d : Var) : (nb087_alpha_dummy_021 C d) ∈ (((Class.cv (nb087_alpha_dummy_021 C d))).fv ∪ ((Class.cv (nb087_alpha_dummy_022 C d))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0018 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_019 A B C R) ∈ (((syn_cnin (Class.cv (nb087_alpha_dummy_018 A B C R)) (Class.cv (nb087_alpha_dummy_019 A B C R)))).fv ∪ ((syn_cnin (Class.cv (nb087_alpha_dummy_018 A B C R)) (Class.cv (nb087_alpha_dummy_019 A B C R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0019 (C : Class) (d : Var) : (nb087_alpha_dummy_022 C d) ∈ (((syn_cnin (Class.cv (nb087_alpha_dummy_021 C d)) (Class.cv (nb087_alpha_dummy_022 C d)))).fv ∪ ((syn_cnin (Class.cv (nb087_alpha_dummy_021 C d)) (Class.cv (nb087_alpha_dummy_022 C d)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cnin]
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0020 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_019 A B C R) ∈ (((Class.cv (nb087_alpha_dummy_018 A B C R))).fv ∪ ((Class.cv (nb087_alpha_dummy_019 A B C R))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0021 (C : Class) (d : Var) : (nb087_alpha_dummy_022 C d) ∈ (((Class.cv (nb087_alpha_dummy_021 C d))).fv ∪ ((Class.cv (nb087_alpha_dummy_022 C d))).fv) := by
  apply Finset.mem_union_right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0022 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_018 A B C R) ∈ (((syn_ccompl (Class.cv (nb087_alpha_dummy_018 A B C R)))).fv ∪ ((syn_ccompl (Class.cv (nb087_alpha_dummy_019 A B C R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0023 (C : Class) (d : Var) : (nb087_alpha_dummy_021 C d) ∈ (((syn_ccompl (Class.cv (nb087_alpha_dummy_021 C d)))).fv ∪ ((syn_ccompl (Class.cv (nb087_alpha_dummy_022 C d)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0024 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_018 A B C R) ∈ (((Class.cv (nb087_alpha_dummy_018 A B C R))).fv ∪ ((Class.cv (nb087_alpha_dummy_018 A B C R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0025 (C : Class) (d : Var) : (nb087_alpha_dummy_021 C d) ∈ (((Class.cv (nb087_alpha_dummy_021 C d))).fv ∪ ((Class.cv (nb087_alpha_dummy_021 C d))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0026 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_019 A B C R) ∈ (((syn_ccompl (Class.cv (nb087_alpha_dummy_018 A B C R)))).fv ∪ ((syn_ccompl (Class.cv (nb087_alpha_dummy_019 A B C R)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0027 (C : Class) (d : Var) : (nb087_alpha_dummy_022 C d) ∈ (((syn_ccompl (Class.cv (nb087_alpha_dummy_021 C d)))).fv ∪ ((syn_ccompl (Class.cv (nb087_alpha_dummy_022 C d)))).fv) := by
  apply Finset.mem_union_right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0028 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_019 A B C R) ∈ (((Class.cv (nb087_alpha_dummy_019 A B C R))).fv ∪ ((Class.cv (nb087_alpha_dummy_019 A B C R))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0029 (C : Class) (d : Var) : (nb087_alpha_dummy_022 C d) ∈ (((Class.cv (nb087_alpha_dummy_022 C d))).fv ∪ ((Class.cv (nb087_alpha_dummy_022 C d))).fv) := by
  apply Finset.mem_union_left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0030 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_002 A B C R) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0031 (C : Class) (d : Var) : (nb087_alpha_dummy_004 C d) ∈ (((syn_ccompl (syn_cphi (Class.cv (nb087_alpha_dummy_004 C d))))).fv ∪ ((syn_ccompl (syn_csn (syn_c0c)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0032 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_002 A B C R) ∈ (((syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R)))).fv ∪ ((syn_cphi (Class.cv (nb087_alpha_dummy_002 A B C R)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_support_mem_0033 (C : Class) (d : Var) : (nb087_alpha_dummy_004 C d) ∈ (((syn_cphi (Class.cv (nb087_alpha_dummy_004 C d)))).fv ∪ ((syn_cphi (Class.cv (nb087_alpha_dummy_004 C d)))).fv) := by
  apply Finset.mem_union_left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb087_compact_fv_empty_0000 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_019 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb087_wpp_notmem_0000 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_019 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb087_alpha_dummy_019, fv_syn_c1c] using (nb087_compact_fv_empty_0000 A B C R)

theorem nb087_compact_fv_empty_0001 (C : Class) (d : Var) : (nb087_alpha_dummy_022 C d) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb087_wpp_notmem_0001 (C : Class) (d : Var) : (nb087_alpha_dummy_022 C d) ∉ ((syn_c1c)).fv := by
  simpa only [nb087_alpha_dummy_022, fv_syn_c1c] using (nb087_compact_fv_empty_0001 C d)

theorem nb087_compact_fv_empty_0002 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_018 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb087_wpp_notmem_0002 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_018 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb087_alpha_dummy_018, fv_syn_c1c] using (nb087_compact_fv_empty_0002 A B C R)

theorem nb087_compact_fv_empty_0003 (C : Class) (d : Var) : (nb087_alpha_dummy_021 C d) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb087_wpp_notmem_0003 (C : Class) (d : Var) : (nb087_alpha_dummy_021 C d) ∉ ((syn_c1c)).fv := by
  simpa only [nb087_alpha_dummy_021, fv_syn_c1c] using (nb087_compact_fv_empty_0003 C d)

theorem nb087_compact_fv_empty_0004 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_017 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb087_wpp_notmem_0004 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_017 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb087_alpha_dummy_017, fv_syn_c1c] using (nb087_compact_fv_empty_0004 A B C R)

theorem nb087_compact_fv_empty_0005 (C : Class) (d : Var) : (nb087_alpha_dummy_020 C d) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb087_wpp_notmem_0005 (C : Class) (d : Var) : (nb087_alpha_dummy_020 C d) ∉ ((syn_c1c)).fv := by
  simpa only [nb087_alpha_dummy_020, fv_syn_c1c] using (nb087_compact_fv_empty_0005 C d)

theorem nb087_compact_fv_empty_0006 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_015 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb087_wpp_notmem_0006 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_015 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb087_alpha_dummy_015, fv_syn_c1c] using (nb087_compact_fv_empty_0006 A B C R)

theorem nb087_compact_fv_empty_0007 (C : Class) (d : Var) : (nb087_alpha_dummy_016 C d) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb087_wpp_notmem_0007 (C : Class) (d : Var) : (nb087_alpha_dummy_016 C d) ∉ ((syn_c1c)).fv := by
  simpa only [nb087_alpha_dummy_016, fv_syn_c1c] using (nb087_compact_fv_empty_0007 C d)

theorem nb087_compact_fv_empty_0008 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_011 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb087_wpp_notmem_0008 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_011 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb087_alpha_dummy_011, fv_syn_c1c] using (nb087_compact_fv_empty_0008 A B C R)

theorem nb087_compact_fv_empty_0009 (C : Class) (d : Var) : (nb087_alpha_dummy_013 C d) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb087_wpp_notmem_0009 (C : Class) (d : Var) : (nb087_alpha_dummy_013 C d) ∉ ((syn_c1c)).fv := by
  simpa only [nb087_alpha_dummy_013, fv_syn_c1c] using (nb087_compact_fv_empty_0009 C d)

theorem nb087_compact_fv_empty_0010 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_012 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb087_wpp_notmem_0010 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_012 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb087_alpha_dummy_012, fv_syn_c1c] using (nb087_compact_fv_empty_0010 A B C R)

theorem nb087_compact_fv_empty_0011 (C : Class) (d : Var) : (nb087_alpha_dummy_014 C d) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb087_wpp_notmem_0011 (C : Class) (d : Var) : (nb087_alpha_dummy_014 C d) ∉ ((syn_c1c)).fv := by
  simpa only [nb087_alpha_dummy_014, fv_syn_c1c] using (nb087_compact_fv_empty_0011 C d)

theorem nb087_compact_fv_empty_0012 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_002 A B C R) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb087_wpp_notmem_0012 (A : Class) (B : Class) (C : Class) (R : Class) : (nb087_alpha_dummy_002 A B C R) ∉ ((syn_c1c)).fv := by
  simpa only [nb087_alpha_dummy_002, fv_syn_c1c] using (nb087_compact_fv_empty_0012 A B C R)

theorem nb087_compact_fv_empty_0013 (C : Class) (d : Var) : (nb087_alpha_dummy_004 C d) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb087_wpp_notmem_0013 (C : Class) (d : Var) : (nb087_alpha_dummy_004 C d) ∉ ((syn_c1c)).fv := by
  simpa only [nb087_alpha_dummy_004, fv_syn_c1c] using (nb087_compact_fv_empty_0013 C d)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
