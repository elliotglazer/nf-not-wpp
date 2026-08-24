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

noncomputable def nominal_df_ncfin
    (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.classEq (syn_cncfin A) (syn_cio x (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem A (.cv x))))) := by
  let alpha_dummy_000 : Var := (freshVar ((A).fv) 0)
  let alpha_dummy_001 : Var := (freshVar (({alpha_dummy_000} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv alpha_dummy_000) (syn_cnnc)) (Wff.classMem A (Class.cv alpha_dummy_000)))).fv) 0)
  let alpha_dummy_002 : Var := (freshVar (({x} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv x) (syn_cnnc)) (Wff.classMem A (Class.cv x)))).fv) 0)
  let alpha_dummy_003 : Var := (freshVar (((Class.cab alpha_dummy_001 (Wff.classEq (Class.cab alpha_dummy_000 (syn_wa (Wff.classMem (Class.cv alpha_dummy_000) (syn_cnnc)) (Wff.classMem A (Class.cv alpha_dummy_000)))) (syn_csn (Class.cv alpha_dummy_001))))).fv) 0)
  let alpha_dummy_004 : Var := (freshVar (((Class.cab alpha_dummy_001 (Wff.classEq (Class.cab alpha_dummy_000 (syn_wa (Wff.classMem (Class.cv alpha_dummy_000) (syn_cnnc)) (Wff.classMem A (Class.cv alpha_dummy_000)))) (syn_csn (Class.cv alpha_dummy_001))))).fv) 1)
  let alpha_dummy_005 : Var := (freshVar (((Class.cab alpha_dummy_002 (Wff.classEq (Class.cab x (syn_wa (Wff.classMem (Class.cv x) (syn_cnnc)) (Wff.classMem A (Class.cv x)))) (syn_csn (Class.cv alpha_dummy_002))))).fv) 0)
  let alpha_dummy_006 : Var := (freshVar (((Class.cab alpha_dummy_002 (Wff.classEq (Class.cab x (syn_wa (Wff.classMem (Class.cv x) (syn_cnnc)) (Wff.classMem A (Class.cv x)))) (syn_csn (Class.cv alpha_dummy_002))))).fv) 1)
  let alpha_dummy_007 : Var := (freshVar ((∅ : Finset Var)) 0)
  let alpha_dummy_008 : Var := (freshVar ((∅ : Finset Var)) 1)
  let alpha_dummy_009 : Var := (freshVar (((Class.cab alpha_dummy_007 (syn_wa (Wff.classMem (syn_c0c) (Class.cv alpha_dummy_007)) (syn_wral alpha_dummy_008 (Class.cv alpha_dummy_007) (Wff.classMem (syn_cplc (Class.cv alpha_dummy_008) (syn_c1c)) (Class.cv alpha_dummy_007)))))).fv) 0)
  let alpha_dummy_010 : Var := (freshVar (((Class.cab alpha_dummy_007 (syn_wa (Wff.classMem (syn_c0c) (Class.cv alpha_dummy_007)) (syn_wral alpha_dummy_008 (Class.cv alpha_dummy_007) (Wff.classMem (syn_cplc (Class.cv alpha_dummy_008) (syn_c1c)) (Class.cv alpha_dummy_007)))))).fv) 1)
  let alpha_dummy_011 : Var := (freshVar (((syn_c0)).fv) 0)
  let alpha_dummy_012 : Var := (freshVar (((syn_cnin (syn_cvv) (syn_ccompl (syn_cvv)))).fv ∪ ((syn_cnin (syn_cvv) (syn_ccompl (syn_cvv)))).fv) 0)
  let alpha_dummy_013 : Var := (freshVar (((syn_cvv)).fv ∪ ((syn_ccompl (syn_cvv))).fv) 0)
  let alpha_dummy_014 : Var := (freshVar (((syn_cvv)).fv ∪ ((syn_cvv)).fv) 0)
  let alpha_dummy_015 : Var := (freshVar (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv) 0)
  let alpha_dummy_016 : Var := (freshVar (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv) 1)
  let alpha_dummy_017 : Var := (freshVar (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv) 2)
  let alpha_dummy_018 : Var := (freshVar (((Class.cv alpha_dummy_008)).fv) 0)
  let alpha_dummy_019 : Var := (freshVar (((syn_cnin (Class.cv alpha_dummy_016) (Class.cv alpha_dummy_017))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_016) (Class.cv alpha_dummy_017))).fv) 0)
  let alpha_dummy_020 : Var := (freshVar (((Class.cv alpha_dummy_016)).fv ∪ ((Class.cv alpha_dummy_017)).fv) 0)
  let alpha_dummy_021 : Var := (freshVar (((syn_ccompl (Class.cv alpha_dummy_016))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_017))).fv) 0)
  let alpha_dummy_022 : Var := (freshVar (((Class.cv alpha_dummy_016)).fv ∪ ((Class.cv alpha_dummy_016)).fv) 0)
  let alpha_dummy_023 : Var := (freshVar (((Class.cv alpha_dummy_017)).fv ∪ ((Class.cv alpha_dummy_017)).fv) 0)
  let alpha_dummy_024 : Var := (freshVar (((Class.cv alpha_dummy_001)).fv) 0)
  let alpha_dummy_025 : Var := (freshVar (((Class.cv alpha_dummy_002)).fv) 0)
  have fresh_000 : alpha_dummy_003 ∉ (((Class.cab alpha_dummy_001 (Wff.classEq (Class.cab alpha_dummy_000 (syn_wa (Wff.classMem (Class.cv alpha_dummy_000) (syn_cnnc)) (Wff.classMem A (Class.cv alpha_dummy_000)))) (syn_csn (Class.cv alpha_dummy_001))))).fv) := by
    simpa [alpha_dummy_003] using freshVar_not_mem (((Class.cab alpha_dummy_001 (Wff.classEq (Class.cab alpha_dummy_000 (syn_wa (Wff.classMem (Class.cv alpha_dummy_000) (syn_cnnc)) (Wff.classMem A (Class.cv alpha_dummy_000)))) (syn_csn (Class.cv alpha_dummy_001))))).fv) 0
  have fresh_001 : alpha_dummy_004 ∉ (((Class.cab alpha_dummy_001 (Wff.classEq (Class.cab alpha_dummy_000 (syn_wa (Wff.classMem (Class.cv alpha_dummy_000) (syn_cnnc)) (Wff.classMem A (Class.cv alpha_dummy_000)))) (syn_csn (Class.cv alpha_dummy_001))))).fv) := by
    simpa [alpha_dummy_004] using freshVar_not_mem (((Class.cab alpha_dummy_001 (Wff.classEq (Class.cab alpha_dummy_000 (syn_wa (Wff.classMem (Class.cv alpha_dummy_000) (syn_cnnc)) (Wff.classMem A (Class.cv alpha_dummy_000)))) (syn_csn (Class.cv alpha_dummy_001))))).fv) 1
  have distinct_002 : alpha_dummy_003 ≠ alpha_dummy_004 := by
    simpa [alpha_dummy_003, alpha_dummy_004] using
      (freshVar_injective (((Class.cab alpha_dummy_001 (Wff.classEq (Class.cab alpha_dummy_000 (syn_wa (Wff.classMem (Class.cv alpha_dummy_000) (syn_cnnc)) (Wff.classMem A (Class.cv alpha_dummy_000)))) (syn_csn (Class.cv alpha_dummy_001))))).fv) (i := 0) (j := 1) (by decide))
  have fresh_003 : alpha_dummy_005 ∉ (((Class.cab alpha_dummy_002 (Wff.classEq (Class.cab x (syn_wa (Wff.classMem (Class.cv x) (syn_cnnc)) (Wff.classMem A (Class.cv x)))) (syn_csn (Class.cv alpha_dummy_002))))).fv) := by
    simpa [alpha_dummy_005] using freshVar_not_mem (((Class.cab alpha_dummy_002 (Wff.classEq (Class.cab x (syn_wa (Wff.classMem (Class.cv x) (syn_cnnc)) (Wff.classMem A (Class.cv x)))) (syn_csn (Class.cv alpha_dummy_002))))).fv) 0
  have fresh_004 : alpha_dummy_006 ∉ (((Class.cab alpha_dummy_002 (Wff.classEq (Class.cab x (syn_wa (Wff.classMem (Class.cv x) (syn_cnnc)) (Wff.classMem A (Class.cv x)))) (syn_csn (Class.cv alpha_dummy_002))))).fv) := by
    simpa [alpha_dummy_006] using freshVar_not_mem (((Class.cab alpha_dummy_002 (Wff.classEq (Class.cab x (syn_wa (Wff.classMem (Class.cv x) (syn_cnnc)) (Wff.classMem A (Class.cv x)))) (syn_csn (Class.cv alpha_dummy_002))))).fv) 1
  have distinct_005 : alpha_dummy_005 ≠ alpha_dummy_006 := by
    simpa [alpha_dummy_005, alpha_dummy_006] using
      (freshVar_injective (((Class.cab alpha_dummy_002 (Wff.classEq (Class.cab x (syn_wa (Wff.classMem (Class.cv x) (syn_cnnc)) (Wff.classMem A (Class.cv x)))) (syn_csn (Class.cv alpha_dummy_002))))).fv) (i := 0) (j := 1) (by decide))
  have fresh_006 : alpha_dummy_009 ∉ (((Class.cab alpha_dummy_007 (syn_wa (Wff.classMem (syn_c0c) (Class.cv alpha_dummy_007)) (syn_wral alpha_dummy_008 (Class.cv alpha_dummy_007) (Wff.classMem (syn_cplc (Class.cv alpha_dummy_008) (syn_c1c)) (Class.cv alpha_dummy_007)))))).fv) := by
    simpa [alpha_dummy_009] using freshVar_not_mem (((Class.cab alpha_dummy_007 (syn_wa (Wff.classMem (syn_c0c) (Class.cv alpha_dummy_007)) (syn_wral alpha_dummy_008 (Class.cv alpha_dummy_007) (Wff.classMem (syn_cplc (Class.cv alpha_dummy_008) (syn_c1c)) (Class.cv alpha_dummy_007)))))).fv) 0
  have fresh_007 : alpha_dummy_010 ∉ (((Class.cab alpha_dummy_007 (syn_wa (Wff.classMem (syn_c0c) (Class.cv alpha_dummy_007)) (syn_wral alpha_dummy_008 (Class.cv alpha_dummy_007) (Wff.classMem (syn_cplc (Class.cv alpha_dummy_008) (syn_c1c)) (Class.cv alpha_dummy_007)))))).fv) := by
    simpa [alpha_dummy_010] using freshVar_not_mem (((Class.cab alpha_dummy_007 (syn_wa (Wff.classMem (syn_c0c) (Class.cv alpha_dummy_007)) (syn_wral alpha_dummy_008 (Class.cv alpha_dummy_007) (Wff.classMem (syn_cplc (Class.cv alpha_dummy_008) (syn_c1c)) (Class.cv alpha_dummy_007)))))).fv) 1
  have distinct_008 : alpha_dummy_009 ≠ alpha_dummy_010 := by
    simpa [alpha_dummy_009, alpha_dummy_010] using
      (freshVar_injective (((Class.cab alpha_dummy_007 (syn_wa (Wff.classMem (syn_c0c) (Class.cv alpha_dummy_007)) (syn_wral alpha_dummy_008 (Class.cv alpha_dummy_007) (Wff.classMem (syn_cplc (Class.cv alpha_dummy_008) (syn_c1c)) (Class.cv alpha_dummy_007)))))).fv) (i := 0) (j := 1) (by decide))
  have fresh_009 : alpha_dummy_024 ∉ (((Class.cv alpha_dummy_001)).fv) := by
    simpa [alpha_dummy_024] using freshVar_not_mem (((Class.cv alpha_dummy_001)).fv) 0
  have fresh_010 : alpha_dummy_025 ∉ (((Class.cv alpha_dummy_002)).fv) := by
    simpa [alpha_dummy_025] using freshVar_not_mem (((Class.cv alpha_dummy_002)).fv) 0
  have fresh_011 : alpha_dummy_018 ∉ (((Class.cv alpha_dummy_008)).fv) := by
    simpa [alpha_dummy_018] using freshVar_not_mem (((Class.cv alpha_dummy_008)).fv) 0
  have fresh_012 : alpha_dummy_015 ∉ (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv) := by
    simpa [alpha_dummy_015] using freshVar_not_mem (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv) 0
  have fresh_013 : alpha_dummy_016 ∉ (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv) := by
    simpa [alpha_dummy_016] using freshVar_not_mem (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv) 1
  have fresh_014 : alpha_dummy_017 ∉ (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv) := by
    simpa [alpha_dummy_017] using freshVar_not_mem (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv) 2
  have distinct_015 : alpha_dummy_015 ≠ alpha_dummy_016 := by
    simpa [alpha_dummy_015, alpha_dummy_016] using
      (freshVar_injective (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 1) (by decide))
  have distinct_016 : alpha_dummy_015 ≠ alpha_dummy_017 := by
    simpa [alpha_dummy_015, alpha_dummy_017] using
      (freshVar_injective (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv) (i := 0) (j := 2) (by decide))
  have distinct_017 : alpha_dummy_016 ≠ alpha_dummy_017 := by
    simpa [alpha_dummy_016, alpha_dummy_017] using
      (freshVar_injective (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv) (i := 1) (j := 2) (by decide))
  have fresh_018 : alpha_dummy_022 ∉ (((Class.cv alpha_dummy_016)).fv ∪ ((Class.cv alpha_dummy_016)).fv) := by
    simpa [alpha_dummy_022] using freshVar_not_mem (((Class.cv alpha_dummy_016)).fv ∪ ((Class.cv alpha_dummy_016)).fv) 0
  have fresh_019 : alpha_dummy_020 ∉ (((Class.cv alpha_dummy_016)).fv ∪ ((Class.cv alpha_dummy_017)).fv) := by
    simpa [alpha_dummy_020] using freshVar_not_mem (((Class.cv alpha_dummy_016)).fv ∪ ((Class.cv alpha_dummy_017)).fv) 0
  have fresh_020 : alpha_dummy_023 ∉ (((Class.cv alpha_dummy_017)).fv ∪ ((Class.cv alpha_dummy_017)).fv) := by
    simpa [alpha_dummy_023] using freshVar_not_mem (((Class.cv alpha_dummy_017)).fv ∪ ((Class.cv alpha_dummy_017)).fv) 0
  have fresh_021 : alpha_dummy_011 ∉ (((syn_c0)).fv) := by
    simpa [alpha_dummy_011] using freshVar_not_mem (((syn_c0)).fv) 0
  have fresh_022 : alpha_dummy_021 ∉ (((syn_ccompl (Class.cv alpha_dummy_016))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_017))).fv) := by
    simpa [alpha_dummy_021] using freshVar_not_mem (((syn_ccompl (Class.cv alpha_dummy_016))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_017))).fv) 0
  have fresh_023 : alpha_dummy_019 ∉ (((syn_cnin (Class.cv alpha_dummy_016) (Class.cv alpha_dummy_017))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_016) (Class.cv alpha_dummy_017))).fv) := by
    simpa [alpha_dummy_019] using freshVar_not_mem (((syn_cnin (Class.cv alpha_dummy_016) (Class.cv alpha_dummy_017))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_016) (Class.cv alpha_dummy_017))).fv) 0
  have fresh_024 : alpha_dummy_012 ∉ (((syn_cnin (syn_cvv) (syn_ccompl (syn_cvv)))).fv ∪ ((syn_cnin (syn_cvv) (syn_ccompl (syn_cvv)))).fv) := by
    simpa [alpha_dummy_012] using freshVar_not_mem (((syn_cnin (syn_cvv) (syn_ccompl (syn_cvv)))).fv ∪ ((syn_cnin (syn_cvv) (syn_ccompl (syn_cvv)))).fv) 0
  have fresh_025 : alpha_dummy_013 ∉ (((syn_cvv)).fv ∪ ((syn_ccompl (syn_cvv))).fv) := by
    simpa [alpha_dummy_013] using freshVar_not_mem (((syn_cvv)).fv ∪ ((syn_ccompl (syn_cvv))).fv) 0
  have fresh_026 : alpha_dummy_014 ∉ (((syn_cvv)).fv ∪ ((syn_cvv)).fv) := by
    simpa [alpha_dummy_014] using freshVar_not_mem (((syn_cvv)).fv ∪ ((syn_cvv)).fv) 0
  have fresh_027 : alpha_dummy_000 ∉ ((A).fv) := by
    simpa [alpha_dummy_000] using freshVar_not_mem ((A).fv) 0
  have fresh_028 : alpha_dummy_001 ∉ (({alpha_dummy_000} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv alpha_dummy_000) (syn_cnnc)) (Wff.classMem A (Class.cv alpha_dummy_000)))).fv) := by
    simpa [alpha_dummy_001] using freshVar_not_mem (({alpha_dummy_000} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv alpha_dummy_000) (syn_cnnc)) (Wff.classMem A (Class.cv alpha_dummy_000)))).fv) 0
  have fresh_029 : alpha_dummy_002 ∉ (({x} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv x) (syn_cnnc)) (Wff.classMem A (Class.cv x)))).fv) := by
    simpa [alpha_dummy_002] using freshVar_not_mem (({x} : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv x) (syn_cnnc)) (Wff.classMem A (Class.cv x)))).fv) 0
  have fresh_030 : alpha_dummy_007 ∉ ((∅ : Finset Var)) := by
    simpa [alpha_dummy_007] using freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_031 : alpha_dummy_008 ∉ ((∅ : Finset Var)) := by
    simpa [alpha_dummy_008] using freshVar_not_mem ((∅ : Finset Var)) 1
  have distinct_032 : alpha_dummy_007 ≠ alpha_dummy_008 := by
    simpa [alpha_dummy_007, alpha_dummy_008] using
      (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))
  have support_part_0000 : alpha_dummy_008 ∈ (((Class.cv alpha_dummy_008)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0000 : alpha_dummy_008 ∈ (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv) := by
    exact (Finset.mem_union_left (((syn_c1c)).fv) support_part_0000)
  have support_part_0001 : alpha_dummy_008 ∈ (((Class.cv alpha_dummy_008)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0001 : alpha_dummy_008 ∈ (((Class.cv alpha_dummy_008)).fv) := by
    exact support_part_0001
  have support_part_0002 : alpha_dummy_016 ∈ (((syn_cnin (Class.cv alpha_dummy_016) (Class.cv alpha_dummy_017))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin] <;> aesop
  have support_mem_0002 : alpha_dummy_016 ∈ (((syn_cnin (Class.cv alpha_dummy_016) (Class.cv alpha_dummy_017))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_016) (Class.cv alpha_dummy_017))).fv) := by
    exact (Finset.mem_union_left (((syn_cnin (Class.cv alpha_dummy_016) (Class.cv alpha_dummy_017))).fv) support_part_0002)
  have support_part_0003 : alpha_dummy_016 ∈ (((Class.cv alpha_dummy_016)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0003 : alpha_dummy_016 ∈ (((Class.cv alpha_dummy_016)).fv ∪ ((Class.cv alpha_dummy_017)).fv) := by
    exact (Finset.mem_union_left (((Class.cv alpha_dummy_017)).fv) support_part_0003)
  have support_part_0004 : alpha_dummy_017 ∈ (((syn_cnin (Class.cv alpha_dummy_016) (Class.cv alpha_dummy_017))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin] <;> aesop
  have support_mem_0004 : alpha_dummy_017 ∈ (((syn_cnin (Class.cv alpha_dummy_016) (Class.cv alpha_dummy_017))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_016) (Class.cv alpha_dummy_017))).fv) := by
    exact (Finset.mem_union_left (((syn_cnin (Class.cv alpha_dummy_016) (Class.cv alpha_dummy_017))).fv) support_part_0004)
  have support_part_0005 : alpha_dummy_017 ∈ (((Class.cv alpha_dummy_017)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0005 : alpha_dummy_017 ∈ (((Class.cv alpha_dummy_016)).fv ∪ ((Class.cv alpha_dummy_017)).fv) := by
    exact (Finset.mem_union_right (((Class.cv alpha_dummy_016)).fv) support_part_0005)
  have support_part_0006 : alpha_dummy_016 ∈ (((syn_ccompl (Class.cv alpha_dummy_016))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl] <;> aesop
  have support_mem_0006 : alpha_dummy_016 ∈ (((syn_ccompl (Class.cv alpha_dummy_016))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_017))).fv) := by
    exact (Finset.mem_union_left (((syn_ccompl (Class.cv alpha_dummy_017))).fv) support_part_0006)
  have support_part_0007 : alpha_dummy_016 ∈ (((Class.cv alpha_dummy_016)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0007 : alpha_dummy_016 ∈ (((Class.cv alpha_dummy_016)).fv ∪ ((Class.cv alpha_dummy_016)).fv) := by
    exact (Finset.mem_union_left (((Class.cv alpha_dummy_016)).fv) support_part_0007)
  have support_part_0008 : alpha_dummy_017 ∈ (((syn_ccompl (Class.cv alpha_dummy_017))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl] <;> aesop
  have support_mem_0008 : alpha_dummy_017 ∈ (((syn_ccompl (Class.cv alpha_dummy_016))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_017))).fv) := by
    exact (Finset.mem_union_right (((syn_ccompl (Class.cv alpha_dummy_016))).fv) support_part_0008)
  have support_part_0009 : alpha_dummy_017 ∈ (((Class.cv alpha_dummy_017)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0009 : alpha_dummy_017 ∈ (((Class.cv alpha_dummy_017)).fv ∪ ((Class.cv alpha_dummy_017)).fv) := by
    exact (Finset.mem_union_left (((Class.cv alpha_dummy_017)).fv) support_part_0009)
  have support_part_0010 : alpha_dummy_001 ∈ (((Class.cv alpha_dummy_001)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0010 : alpha_dummy_001 ∈ (((Class.cv alpha_dummy_001)).fv) := by
    exact support_part_0010
  have support_part_0011 : alpha_dummy_002 ∈ (((Class.cv alpha_dummy_002)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0011 : alpha_dummy_002 ∈ (((Class.cv alpha_dummy_002)).fv) := by
    exact support_part_0011
  have split_alpha_0000 : TAlphaWff [(alpha_dummy_017, alpha_dummy_017), (alpha_dummy_016, alpha_dummy_016), (alpha_dummy_015, alpha_dummy_015), (alpha_dummy_008, alpha_dummy_008), (alpha_dummy_007, alpha_dummy_007), (alpha_dummy_010, alpha_dummy_010), (alpha_dummy_009, alpha_dummy_009), (alpha_dummy_000, x), (alpha_dummy_001, alpha_dummy_002), (alpha_dummy_004, alpha_dummy_006), (alpha_dummy_003, alpha_dummy_005)] (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_016) (Class.cv alpha_dummy_017)) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_015) (syn_cun (Class.cv alpha_dummy_016) (Class.cv alpha_dummy_017))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_016) (Class.cv alpha_dummy_017)) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_015) (syn_cun (Class.cv alpha_dummy_016) (Class.cv alpha_dummy_017))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0)) (TAlphaVar.there (freshVar_injective (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv alpha_dummy_008)).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0)) (TAlphaVar.here _ _ _)))))))))))))))))))
  have split_alpha_0001 : TAlphaWff [(alpha_dummy_000, x), (alpha_dummy_001, alpha_dummy_002), (alpha_dummy_004, alpha_dummy_006), (alpha_dummy_003, alpha_dummy_005)] (Wff.imp (Wff.classMem (Class.cv alpha_dummy_000) (syn_cnnc)) (Wff.neg (Wff.classMem A (Class.cv alpha_dummy_000)))) (Wff.imp (Wff.classMem (Class.cv x) (syn_cnnc)) (Wff.neg (Wff.classMem A (Class.cv x)))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.all (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _))))))))))))))))))))))) (TAlphaClass.cv (TAlphaVar.here _ _ _))) (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) (freshVar_injective ((∅ : Finset Var)) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) (freshVar_injective ((∅ : Finset Var)) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.neg split_alpha_0000)))))))))))))) (TAlphaClass.cv (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) (freshVar_injective ((∅ : Finset Var)) (by decide)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.objMem (TAlphaVar.there (freshVar_injective (((Class.cab alpha_dummy_007 (syn_wa (Wff.classMem (syn_c0c) (Class.cv alpha_dummy_007)) (syn_wral alpha_dummy_008 (Class.cv alpha_dummy_007) (Wff.classMem (syn_cplc (Class.cv alpha_dummy_008) (syn_c1c)) (Class.cv alpha_dummy_007)))))).fv) (by decide)) (freshVar_injective (((Class.cab alpha_dummy_007 (syn_wa (Wff.classMem (syn_c0c) (Class.cv alpha_dummy_007)) (syn_wral alpha_dummy_008 (Class.cv alpha_dummy_007) (Wff.classMem (syn_cplc (Class.cv alpha_dummy_008) (syn_c1c)) (Class.cv alpha_dummy_007)))))).fv) (by decide)) (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.refl_of_fv_fresh _ _ (by simp_all [TEnvFresh] <;> aesop (config := { maxRuleApplications := 2000 }))) (TAlphaClass.cv (TAlphaVar.here _ _ _)))))
  exact Nominal.alphaClassEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.objMem (TAlphaVar.there (freshVar_injective (((Class.cab alpha_dummy_001 (Wff.classEq (Class.cab alpha_dummy_000 (syn_wa (Wff.classMem (Class.cv alpha_dummy_000) (syn_cnnc)) (Wff.classMem A (Class.cv alpha_dummy_000)))) (syn_csn (Class.cv alpha_dummy_001))))).fv) (by decide)) (freshVar_injective (((Class.cab alpha_dummy_002 (Wff.classEq (Class.cab x (syn_wa (Wff.classMem (Class.cv x) (syn_cnnc)) (Wff.classMem A (Class.cv x)))) (syn_csn (Class.cv alpha_dummy_002))))).fv) (by decide)) (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _)) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg split_alpha_0001)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0)) (TAlphaVar.here _ _ _)))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
