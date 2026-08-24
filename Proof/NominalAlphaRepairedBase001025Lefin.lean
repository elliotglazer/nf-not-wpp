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

noncomputable def nominal_df_lefin
    (x : Var) (y : Var) (z : Var) (w : Var) (dv_w_x : w ≠ x) (dv_w_y : w ≠ y) (dv_w_z : w ≠ z) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf (.classEq (syn_clefin) (.cab x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (syn_wrex w (syn_cnnc) (.classEq (.cv z) (syn_cplc (.cv y) (.cv w))))))))) := by
  let alpha_dummy_000 : Var := (freshVar ((∅ : Finset Var)) 0)
  let alpha_dummy_001 : Var := (freshVar ((∅ : Finset Var)) 1)
  let alpha_dummy_002 : Var := (freshVar ((∅ : Finset Var)) 2)
  let alpha_dummy_003 : Var := (freshVar ((∅ : Finset Var)) 3)
  let alpha_dummy_004 : Var := (freshVar (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_002))))).fv ∪ ((syn_ccompl (syn_csn (syn_cpr (Class.cv alpha_dummy_002) (Class.cv alpha_dummy_003))))).fv) 0)
  let alpha_dummy_005 : Var := (freshVar (((syn_ccompl (syn_csn (syn_csn (Class.cv y))))).fv ∪ ((syn_ccompl (syn_csn (syn_cpr (Class.cv y) (Class.cv z))))).fv) 0)
  let alpha_dummy_006 : Var := (freshVar (((syn_csn (syn_csn (Class.cv alpha_dummy_002)))).fv ∪ ((syn_csn (syn_csn (Class.cv alpha_dummy_002)))).fv) 0)
  let alpha_dummy_007 : Var := (freshVar (((syn_csn (syn_csn (Class.cv y)))).fv ∪ ((syn_csn (syn_csn (Class.cv y)))).fv) 0)
  let alpha_dummy_008 : Var := (freshVar (((syn_csn (Class.cv alpha_dummy_002))).fv) 0)
  let alpha_dummy_009 : Var := (freshVar (((syn_csn (Class.cv y))).fv) 0)
  let alpha_dummy_010 : Var := (freshVar (((Class.cv alpha_dummy_002)).fv) 0)
  let alpha_dummy_011 : Var := (freshVar (((Class.cv y)).fv) 0)
  let alpha_dummy_012 : Var := (freshVar (((syn_csn (syn_cpr (Class.cv alpha_dummy_002) (Class.cv alpha_dummy_003)))).fv ∪ ((syn_csn (syn_cpr (Class.cv alpha_dummy_002) (Class.cv alpha_dummy_003)))).fv) 0)
  let alpha_dummy_013 : Var := (freshVar (((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv ∪ ((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv) 0)
  let alpha_dummy_014 : Var := (freshVar (((syn_cpr (Class.cv alpha_dummy_002) (Class.cv alpha_dummy_003))).fv) 0)
  let alpha_dummy_015 : Var := (freshVar (((syn_cpr (Class.cv y) (Class.cv z))).fv) 0)
  let alpha_dummy_016 : Var := (freshVar (((syn_ccompl (syn_csn (Class.cv alpha_dummy_002)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv alpha_dummy_003)))).fv) 0)
  let alpha_dummy_017 : Var := (freshVar (((syn_ccompl (syn_csn (Class.cv y)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv z)))).fv) 0)
  let alpha_dummy_018 : Var := (freshVar (((syn_csn (Class.cv alpha_dummy_002))).fv ∪ ((syn_csn (Class.cv alpha_dummy_002))).fv) 0)
  let alpha_dummy_019 : Var := (freshVar (((syn_csn (Class.cv y))).fv ∪ ((syn_csn (Class.cv y))).fv) 0)
  let alpha_dummy_020 : Var := (freshVar (((syn_csn (Class.cv alpha_dummy_003))).fv ∪ ((syn_csn (Class.cv alpha_dummy_003))).fv) 0)
  let alpha_dummy_021 : Var := (freshVar (((syn_csn (Class.cv z))).fv ∪ ((syn_csn (Class.cv z))).fv) 0)
  let alpha_dummy_022 : Var := (freshVar (((Class.cv alpha_dummy_003)).fv) 0)
  let alpha_dummy_023 : Var := (freshVar (((Class.cv z)).fv) 0)
  let alpha_dummy_024 : Var := (freshVar (((Class.cab alpha_dummy_000 (syn_wa (Wff.classMem (syn_c0c) (Class.cv alpha_dummy_000)) (syn_wral alpha_dummy_001 (Class.cv alpha_dummy_000) (Wff.classMem (syn_cplc (Class.cv alpha_dummy_001) (syn_c1c)) (Class.cv alpha_dummy_000)))))).fv) 0)
  let alpha_dummy_025 : Var := (freshVar (((Class.cab alpha_dummy_000 (syn_wa (Wff.classMem (syn_c0c) (Class.cv alpha_dummy_000)) (syn_wral alpha_dummy_001 (Class.cv alpha_dummy_000) (Wff.classMem (syn_cplc (Class.cv alpha_dummy_001) (syn_c1c)) (Class.cv alpha_dummy_000)))))).fv) 1)
  let alpha_dummy_026 : Var := (freshVar (((syn_c0)).fv) 0)
  let alpha_dummy_027 : Var := (freshVar (((syn_cnin (syn_cvv) (syn_ccompl (syn_cvv)))).fv ∪ ((syn_cnin (syn_cvv) (syn_ccompl (syn_cvv)))).fv) 0)
  let alpha_dummy_028 : Var := (freshVar (((syn_cvv)).fv ∪ ((syn_ccompl (syn_cvv))).fv) 0)
  let alpha_dummy_029 : Var := (freshVar (((syn_cvv)).fv ∪ ((syn_cvv)).fv) 0)
  let alpha_dummy_030 : Var := (freshVar (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv) 0)
  let alpha_dummy_031 : Var := (freshVar (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv) 1)
  let alpha_dummy_032 : Var := (freshVar (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv) 2)
  let alpha_dummy_033 : Var := (freshVar (((Class.cv alpha_dummy_001)).fv) 0)
  let alpha_dummy_034 : Var := (freshVar (((syn_cnin (Class.cv alpha_dummy_031) (Class.cv alpha_dummy_032))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_031) (Class.cv alpha_dummy_032))).fv) 0)
  let alpha_dummy_035 : Var := (freshVar (((Class.cv alpha_dummy_031)).fv ∪ ((Class.cv alpha_dummy_032)).fv) 0)
  let alpha_dummy_036 : Var := (freshVar (((syn_ccompl (Class.cv alpha_dummy_031))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_032))).fv) 0)
  let alpha_dummy_037 : Var := (freshVar (((Class.cv alpha_dummy_031)).fv ∪ ((Class.cv alpha_dummy_031)).fv) 0)
  let alpha_dummy_038 : Var := (freshVar (((Class.cv alpha_dummy_032)).fv ∪ ((Class.cv alpha_dummy_032)).fv) 0)
  let alpha_dummy_039 : Var := (freshVar (((Class.cv alpha_dummy_002)).fv ∪ ((Class.cv alpha_dummy_000)).fv) 0)
  let alpha_dummy_040 : Var := (freshVar (((Class.cv alpha_dummy_002)).fv ∪ ((Class.cv alpha_dummy_000)).fv) 1)
  let alpha_dummy_041 : Var := (freshVar (((Class.cv alpha_dummy_002)).fv ∪ ((Class.cv alpha_dummy_000)).fv) 2)
  let alpha_dummy_042 : Var := (freshVar (((Class.cv y)).fv ∪ ((Class.cv w)).fv) 0)
  let alpha_dummy_043 : Var := (freshVar (((Class.cv y)).fv ∪ ((Class.cv w)).fv) 1)
  let alpha_dummy_044 : Var := (freshVar (((Class.cv y)).fv ∪ ((Class.cv w)).fv) 2)
  let alpha_dummy_045 : Var := (freshVar (((syn_cnin (Class.cv alpha_dummy_040) (Class.cv alpha_dummy_041))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_040) (Class.cv alpha_dummy_041))).fv) 0)
  let alpha_dummy_046 : Var := (freshVar (((syn_cnin (Class.cv alpha_dummy_043) (Class.cv alpha_dummy_044))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_043) (Class.cv alpha_dummy_044))).fv) 0)
  let alpha_dummy_047 : Var := (freshVar (((Class.cv alpha_dummy_040)).fv ∪ ((Class.cv alpha_dummy_041)).fv) 0)
  let alpha_dummy_048 : Var := (freshVar (((Class.cv alpha_dummy_043)).fv ∪ ((Class.cv alpha_dummy_044)).fv) 0)
  let alpha_dummy_049 : Var := (freshVar (((syn_ccompl (Class.cv alpha_dummy_040))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_041))).fv) 0)
  let alpha_dummy_050 : Var := (freshVar (((syn_ccompl (Class.cv alpha_dummy_043))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_044))).fv) 0)
  let alpha_dummy_051 : Var := (freshVar (((Class.cv alpha_dummy_040)).fv ∪ ((Class.cv alpha_dummy_040)).fv) 0)
  let alpha_dummy_052 : Var := (freshVar (((Class.cv alpha_dummy_043)).fv ∪ ((Class.cv alpha_dummy_043)).fv) 0)
  let alpha_dummy_053 : Var := (freshVar (((Class.cv alpha_dummy_041)).fv ∪ ((Class.cv alpha_dummy_041)).fv) 0)
  let alpha_dummy_054 : Var := (freshVar (((Class.cv alpha_dummy_044)).fv ∪ ((Class.cv alpha_dummy_044)).fv) 0)
  have fresh_000 : alpha_dummy_024 ∉ (((Class.cab alpha_dummy_000 (syn_wa (Wff.classMem (syn_c0c) (Class.cv alpha_dummy_000)) (syn_wral alpha_dummy_001 (Class.cv alpha_dummy_000) (Wff.classMem (syn_cplc (Class.cv alpha_dummy_001) (syn_c1c)) (Class.cv alpha_dummy_000)))))).fv) := by
    simpa [alpha_dummy_024] using freshVar_not_mem (((Class.cab alpha_dummy_000 (syn_wa (Wff.classMem (syn_c0c) (Class.cv alpha_dummy_000)) (syn_wral alpha_dummy_001 (Class.cv alpha_dummy_000) (Wff.classMem (syn_cplc (Class.cv alpha_dummy_001) (syn_c1c)) (Class.cv alpha_dummy_000)))))).fv) 0
  have fresh_001 : alpha_dummy_025 ∉ (((Class.cab alpha_dummy_000 (syn_wa (Wff.classMem (syn_c0c) (Class.cv alpha_dummy_000)) (syn_wral alpha_dummy_001 (Class.cv alpha_dummy_000) (Wff.classMem (syn_cplc (Class.cv alpha_dummy_001) (syn_c1c)) (Class.cv alpha_dummy_000)))))).fv) := by
    simpa [alpha_dummy_025] using freshVar_not_mem (((Class.cab alpha_dummy_000 (syn_wa (Wff.classMem (syn_c0c) (Class.cv alpha_dummy_000)) (syn_wral alpha_dummy_001 (Class.cv alpha_dummy_000) (Wff.classMem (syn_cplc (Class.cv alpha_dummy_001) (syn_c1c)) (Class.cv alpha_dummy_000)))))).fv) 1
  have distinct_002 : alpha_dummy_024 ≠ alpha_dummy_025 := by
    simpa [alpha_dummy_024, alpha_dummy_025] using
      (freshVar_injective (((Class.cab alpha_dummy_000 (syn_wa (Wff.classMem (syn_c0c) (Class.cv alpha_dummy_000)) (syn_wral alpha_dummy_001 (Class.cv alpha_dummy_000) (Wff.classMem (syn_cplc (Class.cv alpha_dummy_001) (syn_c1c)) (Class.cv alpha_dummy_000)))))).fv) (i := 0) (j := 1) (by decide))
  have fresh_003 : alpha_dummy_033 ∉ (((Class.cv alpha_dummy_001)).fv) := by
    simpa [alpha_dummy_033] using freshVar_not_mem (((Class.cv alpha_dummy_001)).fv) 0
  have fresh_004 : alpha_dummy_030 ∉ (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv) := by
    simpa [alpha_dummy_030] using freshVar_not_mem (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv) 0
  have fresh_005 : alpha_dummy_031 ∉ (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv) := by
    simpa [alpha_dummy_031] using freshVar_not_mem (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv) 1
  have fresh_006 : alpha_dummy_032 ∉ (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv) := by
    simpa [alpha_dummy_032] using freshVar_not_mem (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv) 2
  have distinct_007 : alpha_dummy_030 ≠ alpha_dummy_031 := by
    simpa [alpha_dummy_030, alpha_dummy_031] using
      (freshVar_injective (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))
  have distinct_008 : alpha_dummy_030 ≠ alpha_dummy_032 := by
    simpa [alpha_dummy_030, alpha_dummy_032] using
      (freshVar_injective (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))
  have distinct_009 : alpha_dummy_031 ≠ alpha_dummy_032 := by
    simpa [alpha_dummy_031, alpha_dummy_032] using
      (freshVar_injective (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))
  have fresh_010 : alpha_dummy_010 ∉ (((Class.cv alpha_dummy_002)).fv) := by
    simpa [alpha_dummy_010] using freshVar_not_mem (((Class.cv alpha_dummy_002)).fv) 0
  have fresh_011 : alpha_dummy_039 ∉ (((Class.cv alpha_dummy_002)).fv ∪ ((Class.cv alpha_dummy_000)).fv) := by
    simpa [alpha_dummy_039] using freshVar_not_mem (((Class.cv alpha_dummy_002)).fv ∪ ((Class.cv alpha_dummy_000)).fv) 0
  have fresh_012 : alpha_dummy_040 ∉ (((Class.cv alpha_dummy_002)).fv ∪ ((Class.cv alpha_dummy_000)).fv) := by
    simpa [alpha_dummy_040] using freshVar_not_mem (((Class.cv alpha_dummy_002)).fv ∪ ((Class.cv alpha_dummy_000)).fv) 1
  have fresh_013 : alpha_dummy_041 ∉ (((Class.cv alpha_dummy_002)).fv ∪ ((Class.cv alpha_dummy_000)).fv) := by
    simpa [alpha_dummy_041] using freshVar_not_mem (((Class.cv alpha_dummy_002)).fv ∪ ((Class.cv alpha_dummy_000)).fv) 2
  have distinct_014 : alpha_dummy_039 ≠ alpha_dummy_040 := by
    simpa [alpha_dummy_039, alpha_dummy_040] using
      (freshVar_injective (((Class.cv alpha_dummy_002)).fv ∪ ((Class.cv alpha_dummy_000)).fv) (i := 0) (j := 1) (by decide))
  have distinct_015 : alpha_dummy_039 ≠ alpha_dummy_041 := by
    simpa [alpha_dummy_039, alpha_dummy_041] using
      (freshVar_injective (((Class.cv alpha_dummy_002)).fv ∪ ((Class.cv alpha_dummy_000)).fv) (i := 0) (j := 2) (by decide))
  have distinct_016 : alpha_dummy_040 ≠ alpha_dummy_041 := by
    simpa [alpha_dummy_040, alpha_dummy_041] using
      (freshVar_injective (((Class.cv alpha_dummy_002)).fv ∪ ((Class.cv alpha_dummy_000)).fv) (i := 1) (j := 2) (by decide))
  have fresh_017 : alpha_dummy_022 ∉ (((Class.cv alpha_dummy_003)).fv) := by
    simpa [alpha_dummy_022] using freshVar_not_mem (((Class.cv alpha_dummy_003)).fv) 0
  have fresh_018 : alpha_dummy_037 ∉ (((Class.cv alpha_dummy_031)).fv ∪ ((Class.cv alpha_dummy_031)).fv) := by
    simpa [alpha_dummy_037] using freshVar_not_mem (((Class.cv alpha_dummy_031)).fv ∪ ((Class.cv alpha_dummy_031)).fv) 0
  have fresh_019 : alpha_dummy_035 ∉ (((Class.cv alpha_dummy_031)).fv ∪ ((Class.cv alpha_dummy_032)).fv) := by
    simpa [alpha_dummy_035] using freshVar_not_mem (((Class.cv alpha_dummy_031)).fv ∪ ((Class.cv alpha_dummy_032)).fv) 0
  have fresh_020 : alpha_dummy_038 ∉ (((Class.cv alpha_dummy_032)).fv ∪ ((Class.cv alpha_dummy_032)).fv) := by
    simpa [alpha_dummy_038] using freshVar_not_mem (((Class.cv alpha_dummy_032)).fv ∪ ((Class.cv alpha_dummy_032)).fv) 0
  have fresh_021 : alpha_dummy_051 ∉ (((Class.cv alpha_dummy_040)).fv ∪ ((Class.cv alpha_dummy_040)).fv) := by
    simpa [alpha_dummy_051] using freshVar_not_mem (((Class.cv alpha_dummy_040)).fv ∪ ((Class.cv alpha_dummy_040)).fv) 0
  have fresh_022 : alpha_dummy_047 ∉ (((Class.cv alpha_dummy_040)).fv ∪ ((Class.cv alpha_dummy_041)).fv) := by
    simpa [alpha_dummy_047] using freshVar_not_mem (((Class.cv alpha_dummy_040)).fv ∪ ((Class.cv alpha_dummy_041)).fv) 0
  have fresh_023 : alpha_dummy_053 ∉ (((Class.cv alpha_dummy_041)).fv ∪ ((Class.cv alpha_dummy_041)).fv) := by
    simpa [alpha_dummy_053] using freshVar_not_mem (((Class.cv alpha_dummy_041)).fv ∪ ((Class.cv alpha_dummy_041)).fv) 0
  have fresh_024 : alpha_dummy_052 ∉ (((Class.cv alpha_dummy_043)).fv ∪ ((Class.cv alpha_dummy_043)).fv) := by
    simpa [alpha_dummy_052] using freshVar_not_mem (((Class.cv alpha_dummy_043)).fv ∪ ((Class.cv alpha_dummy_043)).fv) 0
  have fresh_025 : alpha_dummy_048 ∉ (((Class.cv alpha_dummy_043)).fv ∪ ((Class.cv alpha_dummy_044)).fv) := by
    simpa [alpha_dummy_048] using freshVar_not_mem (((Class.cv alpha_dummy_043)).fv ∪ ((Class.cv alpha_dummy_044)).fv) 0
  have fresh_026 : alpha_dummy_054 ∉ (((Class.cv alpha_dummy_044)).fv ∪ ((Class.cv alpha_dummy_044)).fv) := by
    simpa [alpha_dummy_054] using freshVar_not_mem (((Class.cv alpha_dummy_044)).fv ∪ ((Class.cv alpha_dummy_044)).fv) 0
  have fresh_027 : alpha_dummy_011 ∉ (((Class.cv y)).fv) := by
    simpa [alpha_dummy_011] using freshVar_not_mem (((Class.cv y)).fv) 0
  have fresh_028 : alpha_dummy_042 ∉ (((Class.cv y)).fv ∪ ((Class.cv w)).fv) := by
    simpa [alpha_dummy_042] using freshVar_not_mem (((Class.cv y)).fv ∪ ((Class.cv w)).fv) 0
  have fresh_029 : alpha_dummy_043 ∉ (((Class.cv y)).fv ∪ ((Class.cv w)).fv) := by
    simpa [alpha_dummy_043] using freshVar_not_mem (((Class.cv y)).fv ∪ ((Class.cv w)).fv) 1
  have fresh_030 : alpha_dummy_044 ∉ (((Class.cv y)).fv ∪ ((Class.cv w)).fv) := by
    simpa [alpha_dummy_044] using freshVar_not_mem (((Class.cv y)).fv ∪ ((Class.cv w)).fv) 2
  have distinct_031 : alpha_dummy_042 ≠ alpha_dummy_043 := by
    simpa [alpha_dummy_042, alpha_dummy_043] using
      (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv w)).fv) (i := 0) (j := 1) (by decide))
  have distinct_032 : alpha_dummy_042 ≠ alpha_dummy_044 := by
    simpa [alpha_dummy_042, alpha_dummy_044] using
      (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv w)).fv) (i := 0) (j := 2) (by decide))
  have distinct_033 : alpha_dummy_043 ≠ alpha_dummy_044 := by
    simpa [alpha_dummy_043, alpha_dummy_044] using
      (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv w)).fv) (i := 1) (j := 2) (by decide))
  have fresh_034 : alpha_dummy_023 ∉ (((Class.cv z)).fv) := by
    simpa [alpha_dummy_023] using freshVar_not_mem (((Class.cv z)).fv) 0
  have fresh_035 : alpha_dummy_026 ∉ (((syn_c0)).fv) := by
    simpa [alpha_dummy_026] using freshVar_not_mem (((syn_c0)).fv) 0
  have fresh_036 : alpha_dummy_036 ∉ (((syn_ccompl (Class.cv alpha_dummy_031))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_032))).fv) := by
    simpa [alpha_dummy_036] using freshVar_not_mem (((syn_ccompl (Class.cv alpha_dummy_031))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_032))).fv) 0
  have fresh_037 : alpha_dummy_049 ∉ (((syn_ccompl (Class.cv alpha_dummy_040))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_041))).fv) := by
    simpa [alpha_dummy_049] using freshVar_not_mem (((syn_ccompl (Class.cv alpha_dummy_040))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_041))).fv) 0
  have fresh_038 : alpha_dummy_050 ∉ (((syn_ccompl (Class.cv alpha_dummy_043))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_044))).fv) := by
    simpa [alpha_dummy_050] using freshVar_not_mem (((syn_ccompl (Class.cv alpha_dummy_043))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_044))).fv) 0
  have fresh_039 : alpha_dummy_016 ∉ (((syn_ccompl (syn_csn (Class.cv alpha_dummy_002)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv alpha_dummy_003)))).fv) := by
    simpa [alpha_dummy_016] using freshVar_not_mem (((syn_ccompl (syn_csn (Class.cv alpha_dummy_002)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv alpha_dummy_003)))).fv) 0
  have fresh_040 : alpha_dummy_017 ∉ (((syn_ccompl (syn_csn (Class.cv y)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv z)))).fv) := by
    simpa [alpha_dummy_017] using freshVar_not_mem (((syn_ccompl (syn_csn (Class.cv y)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv z)))).fv) 0
  have fresh_041 : alpha_dummy_004 ∉ (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_002))))).fv ∪ ((syn_ccompl (syn_csn (syn_cpr (Class.cv alpha_dummy_002) (Class.cv alpha_dummy_003))))).fv) := by
    simpa [alpha_dummy_004] using freshVar_not_mem (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_002))))).fv ∪ ((syn_ccompl (syn_csn (syn_cpr (Class.cv alpha_dummy_002) (Class.cv alpha_dummy_003))))).fv) 0
  have fresh_042 : alpha_dummy_005 ∉ (((syn_ccompl (syn_csn (syn_csn (Class.cv y))))).fv ∪ ((syn_ccompl (syn_csn (syn_cpr (Class.cv y) (Class.cv z))))).fv) := by
    simpa [alpha_dummy_005] using freshVar_not_mem (((syn_ccompl (syn_csn (syn_csn (Class.cv y))))).fv ∪ ((syn_ccompl (syn_csn (syn_cpr (Class.cv y) (Class.cv z))))).fv) 0
  have fresh_043 : alpha_dummy_034 ∉ (((syn_cnin (Class.cv alpha_dummy_031) (Class.cv alpha_dummy_032))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_031) (Class.cv alpha_dummy_032))).fv) := by
    simpa [alpha_dummy_034] using freshVar_not_mem (((syn_cnin (Class.cv alpha_dummy_031) (Class.cv alpha_dummy_032))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_031) (Class.cv alpha_dummy_032))).fv) 0
  have fresh_044 : alpha_dummy_045 ∉ (((syn_cnin (Class.cv alpha_dummy_040) (Class.cv alpha_dummy_041))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_040) (Class.cv alpha_dummy_041))).fv) := by
    simpa [alpha_dummy_045] using freshVar_not_mem (((syn_cnin (Class.cv alpha_dummy_040) (Class.cv alpha_dummy_041))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_040) (Class.cv alpha_dummy_041))).fv) 0
  have fresh_045 : alpha_dummy_046 ∉ (((syn_cnin (Class.cv alpha_dummy_043) (Class.cv alpha_dummy_044))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_043) (Class.cv alpha_dummy_044))).fv) := by
    simpa [alpha_dummy_046] using freshVar_not_mem (((syn_cnin (Class.cv alpha_dummy_043) (Class.cv alpha_dummy_044))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_043) (Class.cv alpha_dummy_044))).fv) 0
  have fresh_046 : alpha_dummy_027 ∉ (((syn_cnin (syn_cvv) (syn_ccompl (syn_cvv)))).fv ∪ ((syn_cnin (syn_cvv) (syn_ccompl (syn_cvv)))).fv) := by
    simpa [alpha_dummy_027] using freshVar_not_mem (((syn_cnin (syn_cvv) (syn_ccompl (syn_cvv)))).fv ∪ ((syn_cnin (syn_cvv) (syn_ccompl (syn_cvv)))).fv) 0
  have fresh_047 : alpha_dummy_014 ∉ (((syn_cpr (Class.cv alpha_dummy_002) (Class.cv alpha_dummy_003))).fv) := by
    simpa [alpha_dummy_014] using freshVar_not_mem (((syn_cpr (Class.cv alpha_dummy_002) (Class.cv alpha_dummy_003))).fv) 0
  have fresh_048 : alpha_dummy_015 ∉ (((syn_cpr (Class.cv y) (Class.cv z))).fv) := by
    simpa [alpha_dummy_015] using freshVar_not_mem (((syn_cpr (Class.cv y) (Class.cv z))).fv) 0
  have fresh_049 : alpha_dummy_008 ∉ (((syn_csn (Class.cv alpha_dummy_002))).fv) := by
    simpa [alpha_dummy_008] using freshVar_not_mem (((syn_csn (Class.cv alpha_dummy_002))).fv) 0
  have fresh_050 : alpha_dummy_018 ∉ (((syn_csn (Class.cv alpha_dummy_002))).fv ∪ ((syn_csn (Class.cv alpha_dummy_002))).fv) := by
    simpa [alpha_dummy_018] using freshVar_not_mem (((syn_csn (Class.cv alpha_dummy_002))).fv ∪ ((syn_csn (Class.cv alpha_dummy_002))).fv) 0
  have fresh_051 : alpha_dummy_020 ∉ (((syn_csn (Class.cv alpha_dummy_003))).fv ∪ ((syn_csn (Class.cv alpha_dummy_003))).fv) := by
    simpa [alpha_dummy_020] using freshVar_not_mem (((syn_csn (Class.cv alpha_dummy_003))).fv ∪ ((syn_csn (Class.cv alpha_dummy_003))).fv) 0
  have fresh_052 : alpha_dummy_009 ∉ (((syn_csn (Class.cv y))).fv) := by
    simpa [alpha_dummy_009] using freshVar_not_mem (((syn_csn (Class.cv y))).fv) 0
  have fresh_053 : alpha_dummy_019 ∉ (((syn_csn (Class.cv y))).fv ∪ ((syn_csn (Class.cv y))).fv) := by
    simpa [alpha_dummy_019] using freshVar_not_mem (((syn_csn (Class.cv y))).fv ∪ ((syn_csn (Class.cv y))).fv) 0
  have fresh_054 : alpha_dummy_021 ∉ (((syn_csn (Class.cv z))).fv ∪ ((syn_csn (Class.cv z))).fv) := by
    simpa [alpha_dummy_021] using freshVar_not_mem (((syn_csn (Class.cv z))).fv ∪ ((syn_csn (Class.cv z))).fv) 0
  have fresh_055 : alpha_dummy_012 ∉ (((syn_csn (syn_cpr (Class.cv alpha_dummy_002) (Class.cv alpha_dummy_003)))).fv ∪ ((syn_csn (syn_cpr (Class.cv alpha_dummy_002) (Class.cv alpha_dummy_003)))).fv) := by
    simpa [alpha_dummy_012] using freshVar_not_mem (((syn_csn (syn_cpr (Class.cv alpha_dummy_002) (Class.cv alpha_dummy_003)))).fv ∪ ((syn_csn (syn_cpr (Class.cv alpha_dummy_002) (Class.cv alpha_dummy_003)))).fv) 0
  have fresh_056 : alpha_dummy_013 ∉ (((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv ∪ ((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv) := by
    simpa [alpha_dummy_013] using freshVar_not_mem (((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv ∪ ((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv) 0
  have fresh_057 : alpha_dummy_006 ∉ (((syn_csn (syn_csn (Class.cv alpha_dummy_002)))).fv ∪ ((syn_csn (syn_csn (Class.cv alpha_dummy_002)))).fv) := by
    simpa [alpha_dummy_006] using freshVar_not_mem (((syn_csn (syn_csn (Class.cv alpha_dummy_002)))).fv ∪ ((syn_csn (syn_csn (Class.cv alpha_dummy_002)))).fv) 0
  have fresh_058 : alpha_dummy_007 ∉ (((syn_csn (syn_csn (Class.cv y)))).fv ∪ ((syn_csn (syn_csn (Class.cv y)))).fv) := by
    simpa [alpha_dummy_007] using freshVar_not_mem (((syn_csn (syn_csn (Class.cv y)))).fv ∪ ((syn_csn (syn_csn (Class.cv y)))).fv) 0
  have fresh_059 : alpha_dummy_028 ∉ (((syn_cvv)).fv ∪ ((syn_ccompl (syn_cvv))).fv) := by
    simpa [alpha_dummy_028] using freshVar_not_mem (((syn_cvv)).fv ∪ ((syn_ccompl (syn_cvv))).fv) 0
  have fresh_060 : alpha_dummy_029 ∉ (((syn_cvv)).fv ∪ ((syn_cvv)).fv) := by
    simpa [alpha_dummy_029] using freshVar_not_mem (((syn_cvv)).fv ∪ ((syn_cvv)).fv) 0
  have fresh_061 : alpha_dummy_000 ∉ ((∅ : Finset Var)) := by
    simpa [alpha_dummy_000] using freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_062 : alpha_dummy_001 ∉ ((∅ : Finset Var)) := by
    simpa [alpha_dummy_001] using freshVar_not_mem ((∅ : Finset Var)) 1
  have fresh_063 : alpha_dummy_002 ∉ ((∅ : Finset Var)) := by
    simpa [alpha_dummy_002] using freshVar_not_mem ((∅ : Finset Var)) 2
  have fresh_064 : alpha_dummy_003 ∉ ((∅ : Finset Var)) := by
    simpa [alpha_dummy_003] using freshVar_not_mem ((∅ : Finset Var)) 3
  have distinct_065 : alpha_dummy_000 ≠ alpha_dummy_001 := by
    simpa [alpha_dummy_000, alpha_dummy_001] using
      (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))
  have distinct_066 : alpha_dummy_000 ≠ alpha_dummy_002 := by
    simpa [alpha_dummy_000, alpha_dummy_002] using
      (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 2) (by decide))
  have distinct_067 : alpha_dummy_000 ≠ alpha_dummy_003 := by
    simpa [alpha_dummy_000, alpha_dummy_003] using
      (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 3) (by decide))
  have distinct_068 : alpha_dummy_001 ≠ alpha_dummy_002 := by
    simpa [alpha_dummy_001, alpha_dummy_002] using
      (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 2) (by decide))
  have distinct_069 : alpha_dummy_001 ≠ alpha_dummy_003 := by
    simpa [alpha_dummy_001, alpha_dummy_003] using
      (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 3) (by decide))
  have distinct_070 : alpha_dummy_002 ≠ alpha_dummy_003 := by
    simpa [alpha_dummy_002, alpha_dummy_003] using
      (freshVar_injective ((∅ : Finset Var)) (i := 2) (j := 3) (by decide))
  have support_part_0000 : alpha_dummy_002 ∈ (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_002))))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl, fv_syn_csn] <;> aesop
  have support_mem_0000 : alpha_dummy_002 ∈ (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_002))))).fv ∪ ((syn_ccompl (syn_csn (syn_cpr (Class.cv alpha_dummy_002) (Class.cv alpha_dummy_003))))).fv) := by
    exact (Finset.mem_union_left (((syn_ccompl (syn_csn (syn_cpr (Class.cv alpha_dummy_002) (Class.cv alpha_dummy_003))))).fv) support_part_0000)
  have support_part_0001 : y ∈ (((syn_ccompl (syn_csn (syn_csn (Class.cv y))))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl, fv_syn_csn] <;> aesop
  have support_mem_0001 : y ∈ (((syn_ccompl (syn_csn (syn_csn (Class.cv y))))).fv ∪ ((syn_ccompl (syn_csn (syn_cpr (Class.cv y) (Class.cv z))))).fv) := by
    exact (Finset.mem_union_left (((syn_ccompl (syn_csn (syn_cpr (Class.cv y) (Class.cv z))))).fv) support_part_0001)
  have support_part_0002 : alpha_dummy_002 ∈ (((syn_csn (syn_csn (Class.cv alpha_dummy_002)))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_csn] <;> aesop
  have support_mem_0002 : alpha_dummy_002 ∈ (((syn_csn (syn_csn (Class.cv alpha_dummy_002)))).fv ∪ ((syn_csn (syn_csn (Class.cv alpha_dummy_002)))).fv) := by
    exact (Finset.mem_union_left (((syn_csn (syn_csn (Class.cv alpha_dummy_002)))).fv) support_part_0002)
  have support_part_0003 : y ∈ (((syn_csn (syn_csn (Class.cv y)))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_csn] <;> aesop
  have support_mem_0003 : y ∈ (((syn_csn (syn_csn (Class.cv y)))).fv ∪ ((syn_csn (syn_csn (Class.cv y)))).fv) := by
    exact (Finset.mem_union_left (((syn_csn (syn_csn (Class.cv y)))).fv) support_part_0003)
  have support_part_0004 : alpha_dummy_002 ∈ (((syn_csn (Class.cv alpha_dummy_002))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_csn] <;> aesop
  have support_mem_0004 : alpha_dummy_002 ∈ (((syn_csn (Class.cv alpha_dummy_002))).fv) := by
    exact support_part_0004
  have support_part_0005 : y ∈ (((syn_csn (Class.cv y))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_csn] <;> aesop
  have support_mem_0005 : y ∈ (((syn_csn (Class.cv y))).fv) := by
    exact support_part_0005
  have support_part_0006 : alpha_dummy_002 ∈ (((Class.cv alpha_dummy_002)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0006 : alpha_dummy_002 ∈ (((Class.cv alpha_dummy_002)).fv) := by
    exact support_part_0006
  have support_part_0007 : y ∈ (((Class.cv y)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0007 : y ∈ (((Class.cv y)).fv) := by
    exact support_part_0007
  have support_part_0008 : alpha_dummy_002 ∈ (((syn_csn (syn_cpr (Class.cv alpha_dummy_002) (Class.cv alpha_dummy_003)))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, fv_syn_csn] <;> aesop
  have support_mem_0008 : alpha_dummy_002 ∈ (((syn_csn (syn_cpr (Class.cv alpha_dummy_002) (Class.cv alpha_dummy_003)))).fv ∪ ((syn_csn (syn_cpr (Class.cv alpha_dummy_002) (Class.cv alpha_dummy_003)))).fv) := by
    exact (Finset.mem_union_left (((syn_csn (syn_cpr (Class.cv alpha_dummy_002) (Class.cv alpha_dummy_003)))).fv) support_part_0008)
  have support_part_0009 : y ∈ (((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, fv_syn_csn] <;> aesop
  have support_mem_0009 : y ∈ (((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv ∪ ((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv) := by
    exact (Finset.mem_union_left (((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv) support_part_0009)
  have support_part_0010 : alpha_dummy_002 ∈ (((syn_cpr (Class.cv alpha_dummy_002) (Class.cv alpha_dummy_003))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr] <;> aesop
  have support_mem_0010 : alpha_dummy_002 ∈ (((syn_cpr (Class.cv alpha_dummy_002) (Class.cv alpha_dummy_003))).fv) := by
    exact support_part_0010
  have support_part_0011 : y ∈ (((syn_cpr (Class.cv y) (Class.cv z))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr] <;> aesop
  have support_mem_0011 : y ∈ (((syn_cpr (Class.cv y) (Class.cv z))).fv) := by
    exact support_part_0011
  have support_part_0012 : alpha_dummy_002 ∈ (((syn_ccompl (syn_csn (Class.cv alpha_dummy_002)))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl, fv_syn_csn] <;> aesop
  have support_mem_0012 : alpha_dummy_002 ∈ (((syn_ccompl (syn_csn (Class.cv alpha_dummy_002)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv alpha_dummy_003)))).fv) := by
    exact (Finset.mem_union_left (((syn_ccompl (syn_csn (Class.cv alpha_dummy_003)))).fv) support_part_0012)
  have support_part_0013 : y ∈ (((syn_ccompl (syn_csn (Class.cv y)))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl, fv_syn_csn] <;> aesop
  have support_mem_0013 : y ∈ (((syn_ccompl (syn_csn (Class.cv y)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv z)))).fv) := by
    exact (Finset.mem_union_left (((syn_ccompl (syn_csn (Class.cv z)))).fv) support_part_0013)
  have support_part_0014 : alpha_dummy_002 ∈ (((syn_csn (Class.cv alpha_dummy_002))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_csn] <;> aesop
  have support_mem_0014 : alpha_dummy_002 ∈ (((syn_csn (Class.cv alpha_dummy_002))).fv ∪ ((syn_csn (Class.cv alpha_dummy_002))).fv) := by
    exact (Finset.mem_union_left (((syn_csn (Class.cv alpha_dummy_002))).fv) support_part_0014)
  have support_part_0015 : y ∈ (((syn_csn (Class.cv y))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_csn] <;> aesop
  have support_mem_0015 : y ∈ (((syn_csn (Class.cv y))).fv ∪ ((syn_csn (Class.cv y))).fv) := by
    exact (Finset.mem_union_left (((syn_csn (Class.cv y))).fv) support_part_0015)
  have support_part_0016 : alpha_dummy_003 ∈ (((syn_ccompl (syn_csn (syn_cpr (Class.cv alpha_dummy_002) (Class.cv alpha_dummy_003))))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl, fv_syn_cpr, fv_syn_csn] <;> aesop
  have support_mem_0016 : alpha_dummy_003 ∈ (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_002))))).fv ∪ ((syn_ccompl (syn_csn (syn_cpr (Class.cv alpha_dummy_002) (Class.cv alpha_dummy_003))))).fv) := by
    exact (Finset.mem_union_right (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_002))))).fv) support_part_0016)
  have support_part_0017 : z ∈ (((syn_ccompl (syn_csn (syn_cpr (Class.cv y) (Class.cv z))))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl, fv_syn_cpr, fv_syn_csn] <;> aesop
  have support_mem_0017 : z ∈ (((syn_ccompl (syn_csn (syn_csn (Class.cv y))))).fv ∪ ((syn_ccompl (syn_csn (syn_cpr (Class.cv y) (Class.cv z))))).fv) := by
    exact (Finset.mem_union_right (((syn_ccompl (syn_csn (syn_csn (Class.cv y))))).fv) support_part_0017)
  have support_part_0018 : alpha_dummy_003 ∈ (((syn_csn (syn_cpr (Class.cv alpha_dummy_002) (Class.cv alpha_dummy_003)))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, fv_syn_csn] <;> aesop
  have support_mem_0018 : alpha_dummy_003 ∈ (((syn_csn (syn_cpr (Class.cv alpha_dummy_002) (Class.cv alpha_dummy_003)))).fv ∪ ((syn_csn (syn_cpr (Class.cv alpha_dummy_002) (Class.cv alpha_dummy_003)))).fv) := by
    exact (Finset.mem_union_left (((syn_csn (syn_cpr (Class.cv alpha_dummy_002) (Class.cv alpha_dummy_003)))).fv) support_part_0018)
  have support_part_0019 : z ∈ (((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, fv_syn_csn] <;> aesop
  have support_mem_0019 : z ∈ (((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv ∪ ((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv) := by
    exact (Finset.mem_union_left (((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv) support_part_0019)
  have support_part_0020 : alpha_dummy_003 ∈ (((syn_cpr (Class.cv alpha_dummy_002) (Class.cv alpha_dummy_003))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr] <;> aesop
  have support_mem_0020 : alpha_dummy_003 ∈ (((syn_cpr (Class.cv alpha_dummy_002) (Class.cv alpha_dummy_003))).fv) := by
    exact support_part_0020
  have support_part_0021 : z ∈ (((syn_cpr (Class.cv y) (Class.cv z))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr] <;> aesop
  have support_mem_0021 : z ∈ (((syn_cpr (Class.cv y) (Class.cv z))).fv) := by
    exact support_part_0021
  have support_part_0022 : alpha_dummy_003 ∈ (((syn_ccompl (syn_csn (Class.cv alpha_dummy_003)))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl, fv_syn_csn] <;> aesop
  have support_mem_0022 : alpha_dummy_003 ∈ (((syn_ccompl (syn_csn (Class.cv alpha_dummy_002)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv alpha_dummy_003)))).fv) := by
    exact (Finset.mem_union_right (((syn_ccompl (syn_csn (Class.cv alpha_dummy_002)))).fv) support_part_0022)
  have support_part_0023 : z ∈ (((syn_ccompl (syn_csn (Class.cv z)))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl, fv_syn_csn] <;> aesop
  have support_mem_0023 : z ∈ (((syn_ccompl (syn_csn (Class.cv y)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv z)))).fv) := by
    exact (Finset.mem_union_right (((syn_ccompl (syn_csn (Class.cv y)))).fv) support_part_0023)
  have support_part_0024 : alpha_dummy_003 ∈ (((syn_csn (Class.cv alpha_dummy_003))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_csn] <;> aesop
  have support_mem_0024 : alpha_dummy_003 ∈ (((syn_csn (Class.cv alpha_dummy_003))).fv ∪ ((syn_csn (Class.cv alpha_dummy_003))).fv) := by
    exact (Finset.mem_union_left (((syn_csn (Class.cv alpha_dummy_003))).fv) support_part_0024)
  have support_part_0025 : z ∈ (((syn_csn (Class.cv z))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_csn] <;> aesop
  have support_mem_0025 : z ∈ (((syn_csn (Class.cv z))).fv ∪ ((syn_csn (Class.cv z))).fv) := by
    exact (Finset.mem_union_left (((syn_csn (Class.cv z))).fv) support_part_0025)
  have support_part_0026 : alpha_dummy_003 ∈ (((Class.cv alpha_dummy_003)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0026 : alpha_dummy_003 ∈ (((Class.cv alpha_dummy_003)).fv) := by
    exact support_part_0026
  have support_part_0027 : z ∈ (((Class.cv z)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0027 : z ∈ (((Class.cv z)).fv) := by
    exact support_part_0027
  have support_part_0028 : alpha_dummy_001 ∈ (((Class.cv alpha_dummy_001)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0028 : alpha_dummy_001 ∈ (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv) := by
    exact (Finset.mem_union_left (((syn_c1c)).fv) support_part_0028)
  have support_part_0029 : alpha_dummy_001 ∈ (((Class.cv alpha_dummy_001)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0029 : alpha_dummy_001 ∈ (((Class.cv alpha_dummy_001)).fv) := by
    exact support_part_0029
  have support_part_0030 : alpha_dummy_031 ∈ (((syn_cnin (Class.cv alpha_dummy_031) (Class.cv alpha_dummy_032))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin] <;> aesop
  have support_mem_0030 : alpha_dummy_031 ∈ (((syn_cnin (Class.cv alpha_dummy_031) (Class.cv alpha_dummy_032))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_031) (Class.cv alpha_dummy_032))).fv) := by
    exact (Finset.mem_union_left (((syn_cnin (Class.cv alpha_dummy_031) (Class.cv alpha_dummy_032))).fv) support_part_0030)
  have support_part_0031 : alpha_dummy_031 ∈ (((Class.cv alpha_dummy_031)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0031 : alpha_dummy_031 ∈ (((Class.cv alpha_dummy_031)).fv ∪ ((Class.cv alpha_dummy_032)).fv) := by
    exact (Finset.mem_union_left (((Class.cv alpha_dummy_032)).fv) support_part_0031)
  have support_part_0032 : alpha_dummy_032 ∈ (((syn_cnin (Class.cv alpha_dummy_031) (Class.cv alpha_dummy_032))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin] <;> aesop
  have support_mem_0032 : alpha_dummy_032 ∈ (((syn_cnin (Class.cv alpha_dummy_031) (Class.cv alpha_dummy_032))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_031) (Class.cv alpha_dummy_032))).fv) := by
    exact (Finset.mem_union_left (((syn_cnin (Class.cv alpha_dummy_031) (Class.cv alpha_dummy_032))).fv) support_part_0032)
  have support_part_0033 : alpha_dummy_032 ∈ (((Class.cv alpha_dummy_032)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0033 : alpha_dummy_032 ∈ (((Class.cv alpha_dummy_031)).fv ∪ ((Class.cv alpha_dummy_032)).fv) := by
    exact (Finset.mem_union_right (((Class.cv alpha_dummy_031)).fv) support_part_0033)
  have support_part_0034 : alpha_dummy_031 ∈ (((syn_ccompl (Class.cv alpha_dummy_031))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl] <;> aesop
  have support_mem_0034 : alpha_dummy_031 ∈ (((syn_ccompl (Class.cv alpha_dummy_031))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_032))).fv) := by
    exact (Finset.mem_union_left (((syn_ccompl (Class.cv alpha_dummy_032))).fv) support_part_0034)
  have support_part_0035 : alpha_dummy_031 ∈ (((Class.cv alpha_dummy_031)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0035 : alpha_dummy_031 ∈ (((Class.cv alpha_dummy_031)).fv ∪ ((Class.cv alpha_dummy_031)).fv) := by
    exact (Finset.mem_union_left (((Class.cv alpha_dummy_031)).fv) support_part_0035)
  have support_part_0036 : alpha_dummy_032 ∈ (((syn_ccompl (Class.cv alpha_dummy_032))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl] <;> aesop
  have support_mem_0036 : alpha_dummy_032 ∈ (((syn_ccompl (Class.cv alpha_dummy_031))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_032))).fv) := by
    exact (Finset.mem_union_right (((syn_ccompl (Class.cv alpha_dummy_031))).fv) support_part_0036)
  have support_part_0037 : alpha_dummy_032 ∈ (((Class.cv alpha_dummy_032)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0037 : alpha_dummy_032 ∈ (((Class.cv alpha_dummy_032)).fv ∪ ((Class.cv alpha_dummy_032)).fv) := by
    exact (Finset.mem_union_left (((Class.cv alpha_dummy_032)).fv) support_part_0037)
  have support_part_0038 : alpha_dummy_002 ∈ (((Class.cv alpha_dummy_002)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0038 : alpha_dummy_002 ∈ (((Class.cv alpha_dummy_002)).fv ∪ ((Class.cv alpha_dummy_000)).fv) := by
    exact (Finset.mem_union_left (((Class.cv alpha_dummy_000)).fv) support_part_0038)
  have support_part_0039 : y ∈ (((Class.cv y)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0039 : y ∈ (((Class.cv y)).fv ∪ ((Class.cv w)).fv) := by
    exact (Finset.mem_union_left (((Class.cv w)).fv) support_part_0039)
  have support_part_0040 : alpha_dummy_000 ∈ (((Class.cv alpha_dummy_000)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0040 : alpha_dummy_000 ∈ (((Class.cv alpha_dummy_002)).fv ∪ ((Class.cv alpha_dummy_000)).fv) := by
    exact (Finset.mem_union_right (((Class.cv alpha_dummy_002)).fv) support_part_0040)
  have support_part_0041 : w ∈ (((Class.cv w)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0041 : w ∈ (((Class.cv y)).fv ∪ ((Class.cv w)).fv) := by
    exact (Finset.mem_union_right (((Class.cv y)).fv) support_part_0041)
  have support_part_0042 : alpha_dummy_040 ∈ (((syn_cnin (Class.cv alpha_dummy_040) (Class.cv alpha_dummy_041))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin] <;> aesop
  have support_mem_0042 : alpha_dummy_040 ∈ (((syn_cnin (Class.cv alpha_dummy_040) (Class.cv alpha_dummy_041))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_040) (Class.cv alpha_dummy_041))).fv) := by
    exact (Finset.mem_union_left (((syn_cnin (Class.cv alpha_dummy_040) (Class.cv alpha_dummy_041))).fv) support_part_0042)
  have support_part_0043 : alpha_dummy_043 ∈ (((syn_cnin (Class.cv alpha_dummy_043) (Class.cv alpha_dummy_044))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin] <;> aesop
  have support_mem_0043 : alpha_dummy_043 ∈ (((syn_cnin (Class.cv alpha_dummy_043) (Class.cv alpha_dummy_044))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_043) (Class.cv alpha_dummy_044))).fv) := by
    exact (Finset.mem_union_left (((syn_cnin (Class.cv alpha_dummy_043) (Class.cv alpha_dummy_044))).fv) support_part_0043)
  have support_part_0044 : alpha_dummy_040 ∈ (((Class.cv alpha_dummy_040)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0044 : alpha_dummy_040 ∈ (((Class.cv alpha_dummy_040)).fv ∪ ((Class.cv alpha_dummy_041)).fv) := by
    exact (Finset.mem_union_left (((Class.cv alpha_dummy_041)).fv) support_part_0044)
  have support_part_0045 : alpha_dummy_043 ∈ (((Class.cv alpha_dummy_043)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0045 : alpha_dummy_043 ∈ (((Class.cv alpha_dummy_043)).fv ∪ ((Class.cv alpha_dummy_044)).fv) := by
    exact (Finset.mem_union_left (((Class.cv alpha_dummy_044)).fv) support_part_0045)
  have support_part_0046 : alpha_dummy_041 ∈ (((syn_cnin (Class.cv alpha_dummy_040) (Class.cv alpha_dummy_041))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin] <;> aesop
  have support_mem_0046 : alpha_dummy_041 ∈ (((syn_cnin (Class.cv alpha_dummy_040) (Class.cv alpha_dummy_041))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_040) (Class.cv alpha_dummy_041))).fv) := by
    exact (Finset.mem_union_left (((syn_cnin (Class.cv alpha_dummy_040) (Class.cv alpha_dummy_041))).fv) support_part_0046)
  have support_part_0047 : alpha_dummy_044 ∈ (((syn_cnin (Class.cv alpha_dummy_043) (Class.cv alpha_dummy_044))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin] <;> aesop
  have support_mem_0047 : alpha_dummy_044 ∈ (((syn_cnin (Class.cv alpha_dummy_043) (Class.cv alpha_dummy_044))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_043) (Class.cv alpha_dummy_044))).fv) := by
    exact (Finset.mem_union_left (((syn_cnin (Class.cv alpha_dummy_043) (Class.cv alpha_dummy_044))).fv) support_part_0047)
  have support_part_0048 : alpha_dummy_041 ∈ (((Class.cv alpha_dummy_041)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0048 : alpha_dummy_041 ∈ (((Class.cv alpha_dummy_040)).fv ∪ ((Class.cv alpha_dummy_041)).fv) := by
    exact (Finset.mem_union_right (((Class.cv alpha_dummy_040)).fv) support_part_0048)
  have support_part_0049 : alpha_dummy_044 ∈ (((Class.cv alpha_dummy_044)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0049 : alpha_dummy_044 ∈ (((Class.cv alpha_dummy_043)).fv ∪ ((Class.cv alpha_dummy_044)).fv) := by
    exact (Finset.mem_union_right (((Class.cv alpha_dummy_043)).fv) support_part_0049)
  have support_part_0050 : alpha_dummy_040 ∈ (((syn_ccompl (Class.cv alpha_dummy_040))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl] <;> aesop
  have support_mem_0050 : alpha_dummy_040 ∈ (((syn_ccompl (Class.cv alpha_dummy_040))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_041))).fv) := by
    exact (Finset.mem_union_left (((syn_ccompl (Class.cv alpha_dummy_041))).fv) support_part_0050)
  have support_part_0051 : alpha_dummy_043 ∈ (((syn_ccompl (Class.cv alpha_dummy_043))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl] <;> aesop
  have support_mem_0051 : alpha_dummy_043 ∈ (((syn_ccompl (Class.cv alpha_dummy_043))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_044))).fv) := by
    exact (Finset.mem_union_left (((syn_ccompl (Class.cv alpha_dummy_044))).fv) support_part_0051)
  have support_part_0052 : alpha_dummy_040 ∈ (((Class.cv alpha_dummy_040)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0052 : alpha_dummy_040 ∈ (((Class.cv alpha_dummy_040)).fv ∪ ((Class.cv alpha_dummy_040)).fv) := by
    exact (Finset.mem_union_left (((Class.cv alpha_dummy_040)).fv) support_part_0052)
  have support_part_0053 : alpha_dummy_043 ∈ (((Class.cv alpha_dummy_043)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0053 : alpha_dummy_043 ∈ (((Class.cv alpha_dummy_043)).fv ∪ ((Class.cv alpha_dummy_043)).fv) := by
    exact (Finset.mem_union_left (((Class.cv alpha_dummy_043)).fv) support_part_0053)
  have support_part_0054 : alpha_dummy_041 ∈ (((syn_ccompl (Class.cv alpha_dummy_041))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl] <;> aesop
  have support_mem_0054 : alpha_dummy_041 ∈ (((syn_ccompl (Class.cv alpha_dummy_040))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_041))).fv) := by
    exact (Finset.mem_union_right (((syn_ccompl (Class.cv alpha_dummy_040))).fv) support_part_0054)
  have support_part_0055 : alpha_dummy_044 ∈ (((syn_ccompl (Class.cv alpha_dummy_044))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl] <;> aesop
  have support_mem_0055 : alpha_dummy_044 ∈ (((syn_ccompl (Class.cv alpha_dummy_043))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_044))).fv) := by
    exact (Finset.mem_union_right (((syn_ccompl (Class.cv alpha_dummy_043))).fv) support_part_0055)
  have support_part_0056 : alpha_dummy_041 ∈ (((Class.cv alpha_dummy_041)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0056 : alpha_dummy_041 ∈ (((Class.cv alpha_dummy_041)).fv ∪ ((Class.cv alpha_dummy_041)).fv) := by
    exact (Finset.mem_union_left (((Class.cv alpha_dummy_041)).fv) support_part_0056)
  have support_part_0057 : alpha_dummy_044 ∈ (((Class.cv alpha_dummy_044)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0057 : alpha_dummy_044 ∈ (((Class.cv alpha_dummy_044)).fv ∪ ((Class.cv alpha_dummy_044)).fv) := by
    exact (Finset.mem_union_left (((Class.cv alpha_dummy_044)).fv) support_part_0057)
  have split_alpha_0000 : TAlphaWff [(alpha_dummy_016, alpha_dummy_017), (alpha_dummy_014, alpha_dummy_015), (alpha_dummy_012, alpha_dummy_013), (alpha_dummy_004, alpha_dummy_005), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x)] (Wff.imp (Wff.classMem (Class.cv alpha_dummy_016) (syn_ccompl (syn_csn (Class.cv alpha_dummy_002)))) (Wff.neg (Wff.classMem (Class.cv alpha_dummy_016) (syn_ccompl (syn_csn (Class.cv alpha_dummy_003)))))) (Wff.imp (Wff.classMem (Class.cv alpha_dummy_017) (syn_ccompl (syn_csn (Class.cv y)))) (Wff.neg (Wff.classMem (Class.cv alpha_dummy_017) (syn_ccompl (syn_csn (Class.cv z)))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_y_z (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_y_z (TAlphaVar.here _ _ _)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0)) (TAlphaVar.here _ _ _)))))))))))))))))))
  have split_alpha_0001 : TAlphaWff [(alpha_dummy_032, alpha_dummy_032), (alpha_dummy_031, alpha_dummy_031), (alpha_dummy_030, alpha_dummy_030), (alpha_dummy_001, alpha_dummy_001), (alpha_dummy_000, alpha_dummy_000), (alpha_dummy_025, alpha_dummy_025), (alpha_dummy_024, alpha_dummy_024), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x)] (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_031) (Class.cv alpha_dummy_032)) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_030) (syn_cun (Class.cv alpha_dummy_031) (Class.cv alpha_dummy_032))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_031) (Class.cv alpha_dummy_032)) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_030) (syn_cun (Class.cv alpha_dummy_031) (Class.cv alpha_dummy_032))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0033 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0033 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0033 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0033 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0035 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0035 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 0)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0035 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0035 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 0)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0037 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0037 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0036 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0036 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0037 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0037 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0036 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0036 0)) (TAlphaVar.here _ _ _)))))))))))))))))))
  have split_alpha_0002 : TAlphaWff [(alpha_dummy_041, alpha_dummy_044), (alpha_dummy_040, alpha_dummy_043), (alpha_dummy_039, alpha_dummy_042), (alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x)] (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_040) (Class.cv alpha_dummy_041)) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_039) (syn_cun (Class.cv alpha_dummy_040) (Class.cv alpha_dummy_041))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_043) (Class.cv alpha_dummy_044)) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_042) (syn_cun (Class.cv alpha_dummy_043) (Class.cv alpha_dummy_044))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0044 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0045 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0042 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0043 0)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_002)).fv ∪ ((Class.cv alpha_dummy_000)).fv) (by decide)) (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv w)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0048 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0049 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0046 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0047 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0044 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0045 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0042 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0043 0)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_002)).fv ∪ ((Class.cv alpha_dummy_000)).fv) (by decide)) (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv w)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0048 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0049 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0046 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0047 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_002)).fv ∪ ((Class.cv alpha_dummy_000)).fv) (by decide)) (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv w)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_002)).fv ∪ ((Class.cv alpha_dummy_000)).fv) (by decide)) (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv w)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0052 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0053 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0051 0)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_002)).fv ∪ ((Class.cv alpha_dummy_000)).fv) (by decide)) (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv w)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0052 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0053 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0051 0)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_002)).fv ∪ ((Class.cv alpha_dummy_000)).fv) (by decide)) (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv w)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0056 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0057 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0054 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0055 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0056 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0057 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0054 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0055 0)) (TAlphaVar.here _ _ _)))))))))))))))))))
  have split_alpha_0003 : TAlphaWff [(alpha_dummy_000, w), (alpha_dummy_003, z), (alpha_dummy_002, y), (alpha_dummy_001, x)] (Wff.imp (Wff.classMem (Class.cv alpha_dummy_000) (syn_cnnc)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_003) (syn_cplc (Class.cv alpha_dummy_002) (Class.cv alpha_dummy_000))))) (Wff.imp (Wff.classMem (Class.cv w) (syn_cnnc)) (Wff.neg (Wff.classEq (Class.cv z) (syn_cplc (Class.cv y) (Class.cv w))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.all (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _))))))))))))))))))))))) (TAlphaClass.cv (TAlphaVar.here _ _ _))) (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) (freshVar_injective ((∅ : Finset Var)) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 1)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) (freshVar_injective ((∅ : Finset Var)) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0029 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0029 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.neg split_alpha_0001)))))))))))))) (TAlphaClass.cv (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) (freshVar_injective ((∅ : Finset Var)) (by decide)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.objMem (TAlphaVar.there (freshVar_injective (((Class.cab alpha_dummy_000 (syn_wa (Wff.classMem (syn_c0c) (Class.cv alpha_dummy_000)) (syn_wral alpha_dummy_001 (Class.cv alpha_dummy_000) (Wff.classMem (syn_cplc (Class.cv alpha_dummy_001) (syn_c1c)) (Class.cv alpha_dummy_000)))))).fv) (by decide)) (freshVar_injective (((Class.cab alpha_dummy_000 (syn_wa (Wff.classMem (syn_c0c) (Class.cv alpha_dummy_000)) (syn_wral alpha_dummy_001 (Class.cv alpha_dummy_000) (Wff.classMem (syn_cplc (Class.cv alpha_dummy_001) (syn_c1c)) (Class.cv alpha_dummy_000)))))).fv) (by decide)) (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) (Ne.symm dv_w_z) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0038 1)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0039 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0038 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0039 0)) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) (Ne.symm dv_w_y) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_y_z (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0040 2)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0041 2)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0040 1)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0041 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0040 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0041 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg split_alpha_0002)))))))))))))))))
  exact Nominal.alphaClassEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_z (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_y_z (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_y_z (TAlphaVar.here _ _ _)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg split_alpha_0000)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg split_alpha_0000)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg split_alpha_0003))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
