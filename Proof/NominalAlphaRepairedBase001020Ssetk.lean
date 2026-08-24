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

noncomputable def nominal_df_ssetk
    (x : Var) (y : Var) (z : Var) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf (.classEq (syn_cssetk) (.cab x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (syn_wss (.cv y) (.cv z))))))) := by
  let alpha_dummy_000 : Var := (freshVar ((∅ : Finset Var)) 0)
  let alpha_dummy_001 : Var := (freshVar ((∅ : Finset Var)) 1)
  let alpha_dummy_002 : Var := (freshVar ((∅ : Finset Var)) 2)
  let alpha_dummy_003 : Var := (freshVar (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_001))))).fv ∪ ((syn_ccompl (syn_csn (syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))))).fv) 0)
  let alpha_dummy_004 : Var := (freshVar (((syn_ccompl (syn_csn (syn_csn (Class.cv y))))).fv ∪ ((syn_ccompl (syn_csn (syn_cpr (Class.cv y) (Class.cv z))))).fv) 0)
  let alpha_dummy_005 : Var := (freshVar (((syn_csn (syn_csn (Class.cv alpha_dummy_001)))).fv ∪ ((syn_csn (syn_csn (Class.cv alpha_dummy_001)))).fv) 0)
  let alpha_dummy_006 : Var := (freshVar (((syn_csn (syn_csn (Class.cv y)))).fv ∪ ((syn_csn (syn_csn (Class.cv y)))).fv) 0)
  let alpha_dummy_007 : Var := (freshVar (((syn_csn (Class.cv alpha_dummy_001))).fv) 0)
  let alpha_dummy_008 : Var := (freshVar (((syn_csn (Class.cv y))).fv) 0)
  let alpha_dummy_009 : Var := (freshVar (((Class.cv alpha_dummy_001)).fv) 0)
  let alpha_dummy_010 : Var := (freshVar (((Class.cv y)).fv) 0)
  let alpha_dummy_011 : Var := (freshVar (((syn_csn (syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002)))).fv ∪ ((syn_csn (syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002)))).fv) 0)
  let alpha_dummy_012 : Var := (freshVar (((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv ∪ ((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv) 0)
  let alpha_dummy_013 : Var := (freshVar (((syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv) 0)
  let alpha_dummy_014 : Var := (freshVar (((syn_cpr (Class.cv y) (Class.cv z))).fv) 0)
  let alpha_dummy_015 : Var := (freshVar (((syn_ccompl (syn_csn (Class.cv alpha_dummy_001)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv alpha_dummy_002)))).fv) 0)
  let alpha_dummy_016 : Var := (freshVar (((syn_ccompl (syn_csn (Class.cv y)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv z)))).fv) 0)
  let alpha_dummy_017 : Var := (freshVar (((syn_csn (Class.cv alpha_dummy_001))).fv ∪ ((syn_csn (Class.cv alpha_dummy_001))).fv) 0)
  let alpha_dummy_018 : Var := (freshVar (((syn_csn (Class.cv y))).fv ∪ ((syn_csn (Class.cv y))).fv) 0)
  let alpha_dummy_019 : Var := (freshVar (((syn_csn (Class.cv alpha_dummy_002))).fv ∪ ((syn_csn (Class.cv alpha_dummy_002))).fv) 0)
  let alpha_dummy_020 : Var := (freshVar (((syn_csn (Class.cv z))).fv ∪ ((syn_csn (Class.cv z))).fv) 0)
  let alpha_dummy_021 : Var := (freshVar (((Class.cv alpha_dummy_002)).fv) 0)
  let alpha_dummy_022 : Var := (freshVar (((Class.cv z)).fv) 0)
  let alpha_dummy_023 : Var := (freshVar (((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv) 0)
  let alpha_dummy_024 : Var := (freshVar (((syn_cnin (Class.cv y) (Class.cv z))).fv ∪ ((syn_cnin (Class.cv y) (Class.cv z))).fv) 0)
  let alpha_dummy_025 : Var := (freshVar (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_002)).fv) 0)
  let alpha_dummy_026 : Var := (freshVar (((Class.cv y)).fv ∪ ((Class.cv z)).fv) 0)
  have fresh_000 : alpha_dummy_009 ∉ (((Class.cv alpha_dummy_001)).fv) := by
    simpa [alpha_dummy_009] using freshVar_not_mem (((Class.cv alpha_dummy_001)).fv) 0
  have fresh_001 : alpha_dummy_025 ∉ (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_002)).fv) := by
    simpa [alpha_dummy_025] using freshVar_not_mem (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_002)).fv) 0
  have fresh_002 : alpha_dummy_021 ∉ (((Class.cv alpha_dummy_002)).fv) := by
    simpa [alpha_dummy_021] using freshVar_not_mem (((Class.cv alpha_dummy_002)).fv) 0
  have fresh_003 : alpha_dummy_010 ∉ (((Class.cv y)).fv) := by
    simpa [alpha_dummy_010] using freshVar_not_mem (((Class.cv y)).fv) 0
  have fresh_004 : alpha_dummy_026 ∉ (((Class.cv y)).fv ∪ ((Class.cv z)).fv) := by
    simpa [alpha_dummy_026] using freshVar_not_mem (((Class.cv y)).fv ∪ ((Class.cv z)).fv) 0
  have fresh_005 : alpha_dummy_022 ∉ (((Class.cv z)).fv) := by
    simpa [alpha_dummy_022] using freshVar_not_mem (((Class.cv z)).fv) 0
  have fresh_006 : alpha_dummy_015 ∉ (((syn_ccompl (syn_csn (Class.cv alpha_dummy_001)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv alpha_dummy_002)))).fv) := by
    simpa [alpha_dummy_015] using freshVar_not_mem (((syn_ccompl (syn_csn (Class.cv alpha_dummy_001)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv alpha_dummy_002)))).fv) 0
  have fresh_007 : alpha_dummy_016 ∉ (((syn_ccompl (syn_csn (Class.cv y)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv z)))).fv) := by
    simpa [alpha_dummy_016] using freshVar_not_mem (((syn_ccompl (syn_csn (Class.cv y)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv z)))).fv) 0
  have fresh_008 : alpha_dummy_003 ∉ (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_001))))).fv ∪ ((syn_ccompl (syn_csn (syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))))).fv) := by
    simpa [alpha_dummy_003] using freshVar_not_mem (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_001))))).fv ∪ ((syn_ccompl (syn_csn (syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))))).fv) 0
  have fresh_009 : alpha_dummy_004 ∉ (((syn_ccompl (syn_csn (syn_csn (Class.cv y))))).fv ∪ ((syn_ccompl (syn_csn (syn_cpr (Class.cv y) (Class.cv z))))).fv) := by
    simpa [alpha_dummy_004] using freshVar_not_mem (((syn_ccompl (syn_csn (syn_csn (Class.cv y))))).fv ∪ ((syn_ccompl (syn_csn (syn_cpr (Class.cv y) (Class.cv z))))).fv) 0
  have fresh_010 : alpha_dummy_023 ∉ (((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv) := by
    simpa [alpha_dummy_023] using freshVar_not_mem (((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv) 0
  have fresh_011 : alpha_dummy_024 ∉ (((syn_cnin (Class.cv y) (Class.cv z))).fv ∪ ((syn_cnin (Class.cv y) (Class.cv z))).fv) := by
    simpa [alpha_dummy_024] using freshVar_not_mem (((syn_cnin (Class.cv y) (Class.cv z))).fv ∪ ((syn_cnin (Class.cv y) (Class.cv z))).fv) 0
  have fresh_012 : alpha_dummy_013 ∉ (((syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv) := by
    simpa [alpha_dummy_013] using freshVar_not_mem (((syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv) 0
  have fresh_013 : alpha_dummy_014 ∉ (((syn_cpr (Class.cv y) (Class.cv z))).fv) := by
    simpa [alpha_dummy_014] using freshVar_not_mem (((syn_cpr (Class.cv y) (Class.cv z))).fv) 0
  have fresh_014 : alpha_dummy_007 ∉ (((syn_csn (Class.cv alpha_dummy_001))).fv) := by
    simpa [alpha_dummy_007] using freshVar_not_mem (((syn_csn (Class.cv alpha_dummy_001))).fv) 0
  have fresh_015 : alpha_dummy_017 ∉ (((syn_csn (Class.cv alpha_dummy_001))).fv ∪ ((syn_csn (Class.cv alpha_dummy_001))).fv) := by
    simpa [alpha_dummy_017] using freshVar_not_mem (((syn_csn (Class.cv alpha_dummy_001))).fv ∪ ((syn_csn (Class.cv alpha_dummy_001))).fv) 0
  have fresh_016 : alpha_dummy_019 ∉ (((syn_csn (Class.cv alpha_dummy_002))).fv ∪ ((syn_csn (Class.cv alpha_dummy_002))).fv) := by
    simpa [alpha_dummy_019] using freshVar_not_mem (((syn_csn (Class.cv alpha_dummy_002))).fv ∪ ((syn_csn (Class.cv alpha_dummy_002))).fv) 0
  have fresh_017 : alpha_dummy_008 ∉ (((syn_csn (Class.cv y))).fv) := by
    simpa [alpha_dummy_008] using freshVar_not_mem (((syn_csn (Class.cv y))).fv) 0
  have fresh_018 : alpha_dummy_018 ∉ (((syn_csn (Class.cv y))).fv ∪ ((syn_csn (Class.cv y))).fv) := by
    simpa [alpha_dummy_018] using freshVar_not_mem (((syn_csn (Class.cv y))).fv ∪ ((syn_csn (Class.cv y))).fv) 0
  have fresh_019 : alpha_dummy_020 ∉ (((syn_csn (Class.cv z))).fv ∪ ((syn_csn (Class.cv z))).fv) := by
    simpa [alpha_dummy_020] using freshVar_not_mem (((syn_csn (Class.cv z))).fv ∪ ((syn_csn (Class.cv z))).fv) 0
  have fresh_020 : alpha_dummy_011 ∉ (((syn_csn (syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002)))).fv ∪ ((syn_csn (syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002)))).fv) := by
    simpa [alpha_dummy_011] using freshVar_not_mem (((syn_csn (syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002)))).fv ∪ ((syn_csn (syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002)))).fv) 0
  have fresh_021 : alpha_dummy_012 ∉ (((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv ∪ ((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv) := by
    simpa [alpha_dummy_012] using freshVar_not_mem (((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv ∪ ((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv) 0
  have fresh_022 : alpha_dummy_005 ∉ (((syn_csn (syn_csn (Class.cv alpha_dummy_001)))).fv ∪ ((syn_csn (syn_csn (Class.cv alpha_dummy_001)))).fv) := by
    simpa [alpha_dummy_005] using freshVar_not_mem (((syn_csn (syn_csn (Class.cv alpha_dummy_001)))).fv ∪ ((syn_csn (syn_csn (Class.cv alpha_dummy_001)))).fv) 0
  have fresh_023 : alpha_dummy_006 ∉ (((syn_csn (syn_csn (Class.cv y)))).fv ∪ ((syn_csn (syn_csn (Class.cv y)))).fv) := by
    simpa [alpha_dummy_006] using freshVar_not_mem (((syn_csn (syn_csn (Class.cv y)))).fv ∪ ((syn_csn (syn_csn (Class.cv y)))).fv) 0
  have fresh_024 : alpha_dummy_000 ∉ ((∅ : Finset Var)) := by
    simpa [alpha_dummy_000] using freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_025 : alpha_dummy_001 ∉ ((∅ : Finset Var)) := by
    simpa [alpha_dummy_001] using freshVar_not_mem ((∅ : Finset Var)) 1
  have fresh_026 : alpha_dummy_002 ∉ ((∅ : Finset Var)) := by
    simpa [alpha_dummy_002] using freshVar_not_mem ((∅ : Finset Var)) 2
  have distinct_027 : alpha_dummy_000 ≠ alpha_dummy_001 := by
    simpa [alpha_dummy_000, alpha_dummy_001] using
      (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))
  have distinct_028 : alpha_dummy_000 ≠ alpha_dummy_002 := by
    simpa [alpha_dummy_000, alpha_dummy_002] using
      (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 2) (by decide))
  have distinct_029 : alpha_dummy_001 ≠ alpha_dummy_002 := by
    simpa [alpha_dummy_001, alpha_dummy_002] using
      (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 2) (by decide))
  have support_part_0000 : alpha_dummy_001 ∈ (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_001))))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl, fv_syn_csn] <;> aesop
  have support_mem_0000 : alpha_dummy_001 ∈ (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_001))))).fv ∪ ((syn_ccompl (syn_csn (syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))))).fv) := by
    exact (Finset.mem_union_left (((syn_ccompl (syn_csn (syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))))).fv) support_part_0000)
  have support_part_0001 : y ∈ (((syn_ccompl (syn_csn (syn_csn (Class.cv y))))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl, fv_syn_csn] <;> aesop
  have support_mem_0001 : y ∈ (((syn_ccompl (syn_csn (syn_csn (Class.cv y))))).fv ∪ ((syn_ccompl (syn_csn (syn_cpr (Class.cv y) (Class.cv z))))).fv) := by
    exact (Finset.mem_union_left (((syn_ccompl (syn_csn (syn_cpr (Class.cv y) (Class.cv z))))).fv) support_part_0001)
  have support_part_0002 : alpha_dummy_001 ∈ (((syn_csn (syn_csn (Class.cv alpha_dummy_001)))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_csn] <;> aesop
  have support_mem_0002 : alpha_dummy_001 ∈ (((syn_csn (syn_csn (Class.cv alpha_dummy_001)))).fv ∪ ((syn_csn (syn_csn (Class.cv alpha_dummy_001)))).fv) := by
    exact (Finset.mem_union_left (((syn_csn (syn_csn (Class.cv alpha_dummy_001)))).fv) support_part_0002)
  have support_part_0003 : y ∈ (((syn_csn (syn_csn (Class.cv y)))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_csn] <;> aesop
  have support_mem_0003 : y ∈ (((syn_csn (syn_csn (Class.cv y)))).fv ∪ ((syn_csn (syn_csn (Class.cv y)))).fv) := by
    exact (Finset.mem_union_left (((syn_csn (syn_csn (Class.cv y)))).fv) support_part_0003)
  have support_part_0004 : alpha_dummy_001 ∈ (((syn_csn (Class.cv alpha_dummy_001))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_csn] <;> aesop
  have support_mem_0004 : alpha_dummy_001 ∈ (((syn_csn (Class.cv alpha_dummy_001))).fv) := by
    exact support_part_0004
  have support_part_0005 : y ∈ (((syn_csn (Class.cv y))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_csn] <;> aesop
  have support_mem_0005 : y ∈ (((syn_csn (Class.cv y))).fv) := by
    exact support_part_0005
  have support_part_0006 : alpha_dummy_001 ∈ (((Class.cv alpha_dummy_001)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0006 : alpha_dummy_001 ∈ (((Class.cv alpha_dummy_001)).fv) := by
    exact support_part_0006
  have support_part_0007 : y ∈ (((Class.cv y)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0007 : y ∈ (((Class.cv y)).fv) := by
    exact support_part_0007
  have support_part_0008 : alpha_dummy_001 ∈ (((syn_csn (syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002)))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, fv_syn_csn] <;> aesop
  have support_mem_0008 : alpha_dummy_001 ∈ (((syn_csn (syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002)))).fv ∪ ((syn_csn (syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002)))).fv) := by
    exact (Finset.mem_union_left (((syn_csn (syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002)))).fv) support_part_0008)
  have support_part_0009 : y ∈ (((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, fv_syn_csn] <;> aesop
  have support_mem_0009 : y ∈ (((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv ∪ ((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv) := by
    exact (Finset.mem_union_left (((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv) support_part_0009)
  have support_part_0010 : alpha_dummy_001 ∈ (((syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr] <;> aesop
  have support_mem_0010 : alpha_dummy_001 ∈ (((syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv) := by
    exact support_part_0010
  have support_part_0011 : y ∈ (((syn_cpr (Class.cv y) (Class.cv z))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr] <;> aesop
  have support_mem_0011 : y ∈ (((syn_cpr (Class.cv y) (Class.cv z))).fv) := by
    exact support_part_0011
  have support_part_0012 : alpha_dummy_001 ∈ (((syn_ccompl (syn_csn (Class.cv alpha_dummy_001)))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl, fv_syn_csn] <;> aesop
  have support_mem_0012 : alpha_dummy_001 ∈ (((syn_ccompl (syn_csn (Class.cv alpha_dummy_001)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv alpha_dummy_002)))).fv) := by
    exact (Finset.mem_union_left (((syn_ccompl (syn_csn (Class.cv alpha_dummy_002)))).fv) support_part_0012)
  have support_part_0013 : y ∈ (((syn_ccompl (syn_csn (Class.cv y)))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl, fv_syn_csn] <;> aesop
  have support_mem_0013 : y ∈ (((syn_ccompl (syn_csn (Class.cv y)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv z)))).fv) := by
    exact (Finset.mem_union_left (((syn_ccompl (syn_csn (Class.cv z)))).fv) support_part_0013)
  have support_part_0014 : alpha_dummy_001 ∈ (((syn_csn (Class.cv alpha_dummy_001))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_csn] <;> aesop
  have support_mem_0014 : alpha_dummy_001 ∈ (((syn_csn (Class.cv alpha_dummy_001))).fv ∪ ((syn_csn (Class.cv alpha_dummy_001))).fv) := by
    exact (Finset.mem_union_left (((syn_csn (Class.cv alpha_dummy_001))).fv) support_part_0014)
  have support_part_0015 : y ∈ (((syn_csn (Class.cv y))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_csn] <;> aesop
  have support_mem_0015 : y ∈ (((syn_csn (Class.cv y))).fv ∪ ((syn_csn (Class.cv y))).fv) := by
    exact (Finset.mem_union_left (((syn_csn (Class.cv y))).fv) support_part_0015)
  have support_part_0016 : alpha_dummy_002 ∈ (((syn_ccompl (syn_csn (syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl, fv_syn_cpr, fv_syn_csn] <;> aesop
  have support_mem_0016 : alpha_dummy_002 ∈ (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_001))))).fv ∪ ((syn_ccompl (syn_csn (syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))))).fv) := by
    exact (Finset.mem_union_right (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_001))))).fv) support_part_0016)
  have support_part_0017 : z ∈ (((syn_ccompl (syn_csn (syn_cpr (Class.cv y) (Class.cv z))))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl, fv_syn_cpr, fv_syn_csn] <;> aesop
  have support_mem_0017 : z ∈ (((syn_ccompl (syn_csn (syn_csn (Class.cv y))))).fv ∪ ((syn_ccompl (syn_csn (syn_cpr (Class.cv y) (Class.cv z))))).fv) := by
    exact (Finset.mem_union_right (((syn_ccompl (syn_csn (syn_csn (Class.cv y))))).fv) support_part_0017)
  have support_part_0018 : alpha_dummy_002 ∈ (((syn_csn (syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002)))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, fv_syn_csn] <;> aesop
  have support_mem_0018 : alpha_dummy_002 ∈ (((syn_csn (syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002)))).fv ∪ ((syn_csn (syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002)))).fv) := by
    exact (Finset.mem_union_left (((syn_csn (syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002)))).fv) support_part_0018)
  have support_part_0019 : z ∈ (((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, fv_syn_csn] <;> aesop
  have support_mem_0019 : z ∈ (((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv ∪ ((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv) := by
    exact (Finset.mem_union_left (((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv) support_part_0019)
  have support_part_0020 : alpha_dummy_002 ∈ (((syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr] <;> aesop
  have support_mem_0020 : alpha_dummy_002 ∈ (((syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv) := by
    exact support_part_0020
  have support_part_0021 : z ∈ (((syn_cpr (Class.cv y) (Class.cv z))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr] <;> aesop
  have support_mem_0021 : z ∈ (((syn_cpr (Class.cv y) (Class.cv z))).fv) := by
    exact support_part_0021
  have support_part_0022 : alpha_dummy_002 ∈ (((syn_ccompl (syn_csn (Class.cv alpha_dummy_002)))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl, fv_syn_csn] <;> aesop
  have support_mem_0022 : alpha_dummy_002 ∈ (((syn_ccompl (syn_csn (Class.cv alpha_dummy_001)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv alpha_dummy_002)))).fv) := by
    exact (Finset.mem_union_right (((syn_ccompl (syn_csn (Class.cv alpha_dummy_001)))).fv) support_part_0022)
  have support_part_0023 : z ∈ (((syn_ccompl (syn_csn (Class.cv z)))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl, fv_syn_csn] <;> aesop
  have support_mem_0023 : z ∈ (((syn_ccompl (syn_csn (Class.cv y)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv z)))).fv) := by
    exact (Finset.mem_union_right (((syn_ccompl (syn_csn (Class.cv y)))).fv) support_part_0023)
  have support_part_0024 : alpha_dummy_002 ∈ (((syn_csn (Class.cv alpha_dummy_002))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_csn] <;> aesop
  have support_mem_0024 : alpha_dummy_002 ∈ (((syn_csn (Class.cv alpha_dummy_002))).fv ∪ ((syn_csn (Class.cv alpha_dummy_002))).fv) := by
    exact (Finset.mem_union_left (((syn_csn (Class.cv alpha_dummy_002))).fv) support_part_0024)
  have support_part_0025 : z ∈ (((syn_csn (Class.cv z))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_csn] <;> aesop
  have support_mem_0025 : z ∈ (((syn_csn (Class.cv z))).fv ∪ ((syn_csn (Class.cv z))).fv) := by
    exact (Finset.mem_union_left (((syn_csn (Class.cv z))).fv) support_part_0025)
  have support_part_0026 : alpha_dummy_002 ∈ (((Class.cv alpha_dummy_002)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0026 : alpha_dummy_002 ∈ (((Class.cv alpha_dummy_002)).fv) := by
    exact support_part_0026
  have support_part_0027 : z ∈ (((Class.cv z)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0027 : z ∈ (((Class.cv z)).fv) := by
    exact support_part_0027
  have support_part_0028 : alpha_dummy_001 ∈ (((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin] <;> aesop
  have support_mem_0028 : alpha_dummy_001 ∈ (((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv) := by
    exact (Finset.mem_union_left (((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv) support_part_0028)
  have support_part_0029 : y ∈ (((syn_cnin (Class.cv y) (Class.cv z))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin] <;> aesop
  have support_mem_0029 : y ∈ (((syn_cnin (Class.cv y) (Class.cv z))).fv ∪ ((syn_cnin (Class.cv y) (Class.cv z))).fv) := by
    exact (Finset.mem_union_left (((syn_cnin (Class.cv y) (Class.cv z))).fv) support_part_0029)
  have support_part_0030 : alpha_dummy_001 ∈ (((Class.cv alpha_dummy_001)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0030 : alpha_dummy_001 ∈ (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_002)).fv) := by
    exact (Finset.mem_union_left (((Class.cv alpha_dummy_002)).fv) support_part_0030)
  have support_part_0031 : y ∈ (((Class.cv y)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0031 : y ∈ (((Class.cv y)).fv ∪ ((Class.cv z)).fv) := by
    exact (Finset.mem_union_left (((Class.cv z)).fv) support_part_0031)
  have support_part_0032 : alpha_dummy_002 ∈ (((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin] <;> aesop
  have support_mem_0032 : alpha_dummy_002 ∈ (((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv) := by
    exact (Finset.mem_union_left (((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv) support_part_0032)
  have support_part_0033 : z ∈ (((syn_cnin (Class.cv y) (Class.cv z))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin] <;> aesop
  have support_mem_0033 : z ∈ (((syn_cnin (Class.cv y) (Class.cv z))).fv ∪ ((syn_cnin (Class.cv y) (Class.cv z))).fv) := by
    exact (Finset.mem_union_left (((syn_cnin (Class.cv y) (Class.cv z))).fv) support_part_0033)
  have support_part_0034 : alpha_dummy_002 ∈ (((Class.cv alpha_dummy_002)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0034 : alpha_dummy_002 ∈ (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_002)).fv) := by
    exact (Finset.mem_union_right (((Class.cv alpha_dummy_001)).fv) support_part_0034)
  have support_part_0035 : z ∈ (((Class.cv z)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0035 : z ∈ (((Class.cv y)).fv ∪ ((Class.cv z)).fv) := by
    exact (Finset.mem_union_right (((Class.cv y)).fv) support_part_0035)
  have split_alpha_0000 : TAlphaWff [(alpha_dummy_015, alpha_dummy_016), (alpha_dummy_013, alpha_dummy_014), (alpha_dummy_011, alpha_dummy_012), (alpha_dummy_003, alpha_dummy_004), (alpha_dummy_002, z), (alpha_dummy_001, y), (alpha_dummy_000, x)] (Wff.imp (Wff.classMem (Class.cv alpha_dummy_015) (syn_ccompl (syn_csn (Class.cv alpha_dummy_001)))) (Wff.neg (Wff.classMem (Class.cv alpha_dummy_015) (syn_ccompl (syn_csn (Class.cv alpha_dummy_002)))))) (Wff.imp (Wff.classMem (Class.cv alpha_dummy_016) (syn_ccompl (syn_csn (Class.cv y)))) (Wff.neg (Wff.classMem (Class.cv alpha_dummy_016) (syn_ccompl (syn_csn (Class.cv z)))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_y_z (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_y_z (TAlphaVar.here _ _ _)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0)) (TAlphaVar.here _ _ _)))))))))))))))))))
  have split_alpha_0001 : TAlphaWff [(alpha_dummy_002, z), (alpha_dummy_001, y), (alpha_dummy_000, x)] (Wff.imp (Wff.classEq (Class.cv alpha_dummy_000) (syn_copk (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))) (Wff.neg (syn_wss (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002)))) (Wff.imp (Wff.classEq (Class.cv x) (syn_copk (Class.cv y) (Class.cv z))) (Wff.neg (syn_wss (Class.cv y) (Class.cv z)))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_z (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_y (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_y_z (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_y_z (TAlphaVar.here _ _ _)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg split_alpha_0000)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg split_alpha_0000)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0029 0)) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_y_z (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0035 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0033 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0029 0)) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_y_z (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0035 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0033 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_y_z (TAlphaVar.here _ _ _))))))
  exact Nominal.alphaClassEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg split_alpha_0001))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
