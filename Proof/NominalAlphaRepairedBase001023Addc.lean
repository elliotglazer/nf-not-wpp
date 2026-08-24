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

noncomputable def nominal_df_addc
    (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf (.classEq (syn_cplc A B) (.cab x (syn_wrex y A (syn_wrex z B (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0)) (.classEq (.cv x) (syn_cun (.cv y) (.cv z)))))))) := by
  let alpha_dummy_000 : Var := (freshVar ((A).fv ∪ (B).fv) 0)
  let alpha_dummy_001 : Var := (freshVar ((A).fv ∪ (B).fv) 1)
  let alpha_dummy_002 : Var := (freshVar ((A).fv ∪ (B).fv) 2)
  let alpha_dummy_003 : Var := (freshVar (((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv) 0)
  let alpha_dummy_004 : Var := (freshVar (((syn_cnin (Class.cv y) (Class.cv z))).fv ∪ ((syn_cnin (Class.cv y) (Class.cv z))).fv) 0)
  let alpha_dummy_005 : Var := (freshVar (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_002)).fv) 0)
  let alpha_dummy_006 : Var := (freshVar (((Class.cv y)).fv ∪ ((Class.cv z)).fv) 0)
  let alpha_dummy_007 : Var := (freshVar (((syn_cnin (syn_cvv) (syn_ccompl (syn_cvv)))).fv ∪ ((syn_cnin (syn_cvv) (syn_ccompl (syn_cvv)))).fv) 0)
  let alpha_dummy_008 : Var := (freshVar (((syn_cvv)).fv ∪ ((syn_ccompl (syn_cvv))).fv) 0)
  let alpha_dummy_009 : Var := (freshVar ((∅ : Finset Var)) 0)
  let alpha_dummy_010 : Var := (freshVar (((syn_cvv)).fv ∪ ((syn_cvv)).fv) 0)
  let alpha_dummy_011 : Var := (freshVar (((syn_ccompl (Class.cv alpha_dummy_001))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_002))).fv) 0)
  let alpha_dummy_012 : Var := (freshVar (((syn_ccompl (Class.cv y))).fv ∪ ((syn_ccompl (Class.cv z))).fv) 0)
  let alpha_dummy_013 : Var := (freshVar (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_001)).fv) 0)
  let alpha_dummy_014 : Var := (freshVar (((Class.cv y)).fv ∪ ((Class.cv y)).fv) 0)
  let alpha_dummy_015 : Var := (freshVar (((Class.cv alpha_dummy_002)).fv ∪ ((Class.cv alpha_dummy_002)).fv) 0)
  let alpha_dummy_016 : Var := (freshVar (((Class.cv z)).fv ∪ ((Class.cv z)).fv) 0)
  have fresh_000 : alpha_dummy_013 ∉ (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_001)).fv) := by
    simpa [alpha_dummy_013] using freshVar_not_mem (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_001)).fv) 0
  have fresh_001 : alpha_dummy_005 ∉ (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_002)).fv) := by
    simpa [alpha_dummy_005] using freshVar_not_mem (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_002)).fv) 0
  have fresh_002 : alpha_dummy_015 ∉ (((Class.cv alpha_dummy_002)).fv ∪ ((Class.cv alpha_dummy_002)).fv) := by
    simpa [alpha_dummy_015] using freshVar_not_mem (((Class.cv alpha_dummy_002)).fv ∪ ((Class.cv alpha_dummy_002)).fv) 0
  have fresh_003 : alpha_dummy_014 ∉ (((Class.cv y)).fv ∪ ((Class.cv y)).fv) := by
    simpa [alpha_dummy_014] using freshVar_not_mem (((Class.cv y)).fv ∪ ((Class.cv y)).fv) 0
  have fresh_004 : alpha_dummy_006 ∉ (((Class.cv y)).fv ∪ ((Class.cv z)).fv) := by
    simpa [alpha_dummy_006] using freshVar_not_mem (((Class.cv y)).fv ∪ ((Class.cv z)).fv) 0
  have fresh_005 : alpha_dummy_016 ∉ (((Class.cv z)).fv ∪ ((Class.cv z)).fv) := by
    simpa [alpha_dummy_016] using freshVar_not_mem (((Class.cv z)).fv ∪ ((Class.cv z)).fv) 0
  have fresh_006 : alpha_dummy_011 ∉ (((syn_ccompl (Class.cv alpha_dummy_001))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_002))).fv) := by
    simpa [alpha_dummy_011] using freshVar_not_mem (((syn_ccompl (Class.cv alpha_dummy_001))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_002))).fv) 0
  have fresh_007 : alpha_dummy_012 ∉ (((syn_ccompl (Class.cv y))).fv ∪ ((syn_ccompl (Class.cv z))).fv) := by
    simpa [alpha_dummy_012] using freshVar_not_mem (((syn_ccompl (Class.cv y))).fv ∪ ((syn_ccompl (Class.cv z))).fv) 0
  have fresh_008 : alpha_dummy_003 ∉ (((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv) := by
    simpa [alpha_dummy_003] using freshVar_not_mem (((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv) 0
  have fresh_009 : alpha_dummy_004 ∉ (((syn_cnin (Class.cv y) (Class.cv z))).fv ∪ ((syn_cnin (Class.cv y) (Class.cv z))).fv) := by
    simpa [alpha_dummy_004] using freshVar_not_mem (((syn_cnin (Class.cv y) (Class.cv z))).fv ∪ ((syn_cnin (Class.cv y) (Class.cv z))).fv) 0
  have fresh_010 : alpha_dummy_007 ∉ (((syn_cnin (syn_cvv) (syn_ccompl (syn_cvv)))).fv ∪ ((syn_cnin (syn_cvv) (syn_ccompl (syn_cvv)))).fv) := by
    simpa [alpha_dummy_007] using freshVar_not_mem (((syn_cnin (syn_cvv) (syn_ccompl (syn_cvv)))).fv ∪ ((syn_cnin (syn_cvv) (syn_ccompl (syn_cvv)))).fv) 0
  have fresh_011 : alpha_dummy_008 ∉ (((syn_cvv)).fv ∪ ((syn_ccompl (syn_cvv))).fv) := by
    simpa [alpha_dummy_008] using freshVar_not_mem (((syn_cvv)).fv ∪ ((syn_ccompl (syn_cvv))).fv) 0
  have fresh_012 : alpha_dummy_010 ∉ (((syn_cvv)).fv ∪ ((syn_cvv)).fv) := by
    simpa [alpha_dummy_010] using freshVar_not_mem (((syn_cvv)).fv ∪ ((syn_cvv)).fv) 0
  have fresh_013 : alpha_dummy_000 ∉ ((A).fv ∪ (B).fv) := by
    simpa [alpha_dummy_000] using freshVar_not_mem ((A).fv ∪ (B).fv) 0
  have fresh_014 : alpha_dummy_001 ∉ ((A).fv ∪ (B).fv) := by
    simpa [alpha_dummy_001] using freshVar_not_mem ((A).fv ∪ (B).fv) 1
  have fresh_015 : alpha_dummy_002 ∉ ((A).fv ∪ (B).fv) := by
    simpa [alpha_dummy_002] using freshVar_not_mem ((A).fv ∪ (B).fv) 2
  have distinct_016 : alpha_dummy_000 ≠ alpha_dummy_001 := by
    simpa [alpha_dummy_000, alpha_dummy_001] using
      (freshVar_injective ((A).fv ∪ (B).fv) (i := 0) (j := 1) (by decide))
  have distinct_017 : alpha_dummy_000 ≠ alpha_dummy_002 := by
    simpa [alpha_dummy_000, alpha_dummy_002] using
      (freshVar_injective ((A).fv ∪ (B).fv) (i := 0) (j := 2) (by decide))
  have distinct_018 : alpha_dummy_001 ≠ alpha_dummy_002 := by
    simpa [alpha_dummy_001, alpha_dummy_002] using
      (freshVar_injective ((A).fv ∪ (B).fv) (i := 1) (j := 2) (by decide))
  have fresh_019 : alpha_dummy_009 ∉ ((∅ : Finset Var)) := by
    simpa [alpha_dummy_009] using freshVar_not_mem ((∅ : Finset Var)) 0
  have support_part_0000 : alpha_dummy_001 ∈ (((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin] <;> aesop
  have support_mem_0000 : alpha_dummy_001 ∈ (((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv) := by
    exact (Finset.mem_union_left (((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv) support_part_0000)
  have support_part_0001 : y ∈ (((syn_cnin (Class.cv y) (Class.cv z))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin] <;> aesop
  have support_mem_0001 : y ∈ (((syn_cnin (Class.cv y) (Class.cv z))).fv ∪ ((syn_cnin (Class.cv y) (Class.cv z))).fv) := by
    exact (Finset.mem_union_left (((syn_cnin (Class.cv y) (Class.cv z))).fv) support_part_0001)
  have support_part_0002 : alpha_dummy_001 ∈ (((Class.cv alpha_dummy_001)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0002 : alpha_dummy_001 ∈ (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_002)).fv) := by
    exact (Finset.mem_union_left (((Class.cv alpha_dummy_002)).fv) support_part_0002)
  have support_part_0003 : y ∈ (((Class.cv y)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0003 : y ∈ (((Class.cv y)).fv ∪ ((Class.cv z)).fv) := by
    exact (Finset.mem_union_left (((Class.cv z)).fv) support_part_0003)
  have support_part_0004 : alpha_dummy_002 ∈ (((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin] <;> aesop
  have support_mem_0004 : alpha_dummy_002 ∈ (((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv ∪ ((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv) := by
    exact (Finset.mem_union_left (((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv) support_part_0004)
  have support_part_0005 : z ∈ (((syn_cnin (Class.cv y) (Class.cv z))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin] <;> aesop
  have support_mem_0005 : z ∈ (((syn_cnin (Class.cv y) (Class.cv z))).fv ∪ ((syn_cnin (Class.cv y) (Class.cv z))).fv) := by
    exact (Finset.mem_union_left (((syn_cnin (Class.cv y) (Class.cv z))).fv) support_part_0005)
  have support_part_0006 : alpha_dummy_002 ∈ (((Class.cv alpha_dummy_002)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0006 : alpha_dummy_002 ∈ (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_002)).fv) := by
    exact (Finset.mem_union_right (((Class.cv alpha_dummy_001)).fv) support_part_0006)
  have support_part_0007 : z ∈ (((Class.cv z)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0007 : z ∈ (((Class.cv y)).fv ∪ ((Class.cv z)).fv) := by
    exact (Finset.mem_union_right (((Class.cv y)).fv) support_part_0007)
  have support_part_0008 : alpha_dummy_001 ∈ (((syn_ccompl (Class.cv alpha_dummy_001))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl] <;> aesop
  have support_mem_0008 : alpha_dummy_001 ∈ (((syn_ccompl (Class.cv alpha_dummy_001))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_002))).fv) := by
    exact (Finset.mem_union_left (((syn_ccompl (Class.cv alpha_dummy_002))).fv) support_part_0008)
  have support_part_0009 : y ∈ (((syn_ccompl (Class.cv y))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl] <;> aesop
  have support_mem_0009 : y ∈ (((syn_ccompl (Class.cv y))).fv ∪ ((syn_ccompl (Class.cv z))).fv) := by
    exact (Finset.mem_union_left (((syn_ccompl (Class.cv z))).fv) support_part_0009)
  have support_part_0010 : alpha_dummy_001 ∈ (((Class.cv alpha_dummy_001)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0010 : alpha_dummy_001 ∈ (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_001)).fv) := by
    exact (Finset.mem_union_left (((Class.cv alpha_dummy_001)).fv) support_part_0010)
  have support_part_0011 : y ∈ (((Class.cv y)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0011 : y ∈ (((Class.cv y)).fv ∪ ((Class.cv y)).fv) := by
    exact (Finset.mem_union_left (((Class.cv y)).fv) support_part_0011)
  have support_part_0012 : alpha_dummy_002 ∈ (((syn_ccompl (Class.cv alpha_dummy_002))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl] <;> aesop
  have support_mem_0012 : alpha_dummy_002 ∈ (((syn_ccompl (Class.cv alpha_dummy_001))).fv ∪ ((syn_ccompl (Class.cv alpha_dummy_002))).fv) := by
    exact (Finset.mem_union_right (((syn_ccompl (Class.cv alpha_dummy_001))).fv) support_part_0012)
  have support_part_0013 : z ∈ (((syn_ccompl (Class.cv z))).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl] <;> aesop
  have support_mem_0013 : z ∈ (((syn_ccompl (Class.cv y))).fv ∪ ((syn_ccompl (Class.cv z))).fv) := by
    exact (Finset.mem_union_right (((syn_ccompl (Class.cv y))).fv) support_part_0013)
  have support_part_0014 : alpha_dummy_002 ∈ (((Class.cv alpha_dummy_002)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0014 : alpha_dummy_002 ∈ (((Class.cv alpha_dummy_002)).fv ∪ ((Class.cv alpha_dummy_002)).fv) := by
    exact (Finset.mem_union_left (((Class.cv alpha_dummy_002)).fv) support_part_0014)
  have support_part_0015 : z ∈ (((Class.cv z)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0015 : z ∈ (((Class.cv z)).fv ∪ ((Class.cv z)).fv) := by
    exact (Finset.mem_union_left (((Class.cv z)).fv) support_part_0015)
  have split_alpha_0000 : TAlphaWff [(alpha_dummy_002, z), (alpha_dummy_001, y), (alpha_dummy_000, x)] (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002)) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_000) (syn_cun (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv y) (Class.cv z)) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv x) (syn_cun (Class.cv y) (Class.cv z))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.there (freshVar_injective ((A).fv ∪ (B).fv) (by decide)) dv_y_z (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.there (freshVar_injective ((A).fv ∪ (B).fv) (by decide)) dv_y_z (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective ((A).fv ∪ (B).fv) (by decide)) dv_x_z (TAlphaVar.there (freshVar_injective ((A).fv ∪ (B).fv) (by decide)) dv_x_y (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0)) (TAlphaVar.there (freshVar_injective ((A).fv ∪ (B).fv) (by decide)) dv_y_z (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0)) (TAlphaVar.there (freshVar_injective ((A).fv ∪ (B).fv) (by decide)) dv_y_z (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.here _ _ _)))))))))))))))))))
  exact Nominal.alphaClassEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_fv_fresh _ _ (by simp_all [TEnvFresh] <;> aesop (config := { maxRuleApplications := 2000 })))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_fv_fresh _ _ (by simp_all [TEnvFresh] <;> aesop (config := { maxRuleApplications := 2000 })))) (TAlphaWff.neg (TAlphaWff.neg split_alpha_0000))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
