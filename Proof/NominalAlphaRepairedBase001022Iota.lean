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

noncomputable def nominal_df_iota
    (ph : Wff) (x : Var) (y : Var) (dv_ph_y : y ∉ ph.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classEq (syn_cio x ph) (syn_cuni (.cab y (.classEq (.cab x ph) (syn_csn (.cv y)))))) := by
  let alpha_dummy_000 : Var := (freshVar (({x} : Finset Var) ∪ (ph).fv) 0)
  let alpha_dummy_001 : Var := (freshVar (((Class.cab alpha_dummy_000 (Wff.classEq (Class.cab x ph) (syn_csn (Class.cv alpha_dummy_000))))).fv) 0)
  let alpha_dummy_002 : Var := (freshVar (((Class.cab alpha_dummy_000 (Wff.classEq (Class.cab x ph) (syn_csn (Class.cv alpha_dummy_000))))).fv) 1)
  let alpha_dummy_003 : Var := (freshVar (((Class.cab y (Wff.classEq (Class.cab x ph) (syn_csn (Class.cv y))))).fv) 0)
  let alpha_dummy_004 : Var := (freshVar (((Class.cab y (Wff.classEq (Class.cab x ph) (syn_csn (Class.cv y))))).fv) 1)
  let alpha_dummy_005 : Var := (freshVar (((Class.cv alpha_dummy_000)).fv) 0)
  let alpha_dummy_006 : Var := (freshVar (((Class.cv y)).fv) 0)
  have fresh_000 : alpha_dummy_001 ∉ (((Class.cab alpha_dummy_000 (Wff.classEq (Class.cab x ph) (syn_csn (Class.cv alpha_dummy_000))))).fv) := by
    simpa [alpha_dummy_001] using freshVar_not_mem (((Class.cab alpha_dummy_000 (Wff.classEq (Class.cab x ph) (syn_csn (Class.cv alpha_dummy_000))))).fv) 0
  have fresh_001 : alpha_dummy_002 ∉ (((Class.cab alpha_dummy_000 (Wff.classEq (Class.cab x ph) (syn_csn (Class.cv alpha_dummy_000))))).fv) := by
    simpa [alpha_dummy_002] using freshVar_not_mem (((Class.cab alpha_dummy_000 (Wff.classEq (Class.cab x ph) (syn_csn (Class.cv alpha_dummy_000))))).fv) 1
  have distinct_002 : alpha_dummy_001 ≠ alpha_dummy_002 := by
    simpa [alpha_dummy_001, alpha_dummy_002] using
      (freshVar_injective (((Class.cab alpha_dummy_000 (Wff.classEq (Class.cab x ph) (syn_csn (Class.cv alpha_dummy_000))))).fv) (i := 0) (j := 1) (by decide))
  have fresh_003 : alpha_dummy_003 ∉ (((Class.cab y (Wff.classEq (Class.cab x ph) (syn_csn (Class.cv y))))).fv) := by
    simpa [alpha_dummy_003] using freshVar_not_mem (((Class.cab y (Wff.classEq (Class.cab x ph) (syn_csn (Class.cv y))))).fv) 0
  have fresh_004 : alpha_dummy_004 ∉ (((Class.cab y (Wff.classEq (Class.cab x ph) (syn_csn (Class.cv y))))).fv) := by
    simpa [alpha_dummy_004] using freshVar_not_mem (((Class.cab y (Wff.classEq (Class.cab x ph) (syn_csn (Class.cv y))))).fv) 1
  have distinct_005 : alpha_dummy_003 ≠ alpha_dummy_004 := by
    simpa [alpha_dummy_003, alpha_dummy_004] using
      (freshVar_injective (((Class.cab y (Wff.classEq (Class.cab x ph) (syn_csn (Class.cv y))))).fv) (i := 0) (j := 1) (by decide))
  have fresh_006 : alpha_dummy_005 ∉ (((Class.cv alpha_dummy_000)).fv) := by
    simpa [alpha_dummy_005] using freshVar_not_mem (((Class.cv alpha_dummy_000)).fv) 0
  have fresh_007 : alpha_dummy_006 ∉ (((Class.cv y)).fv) := by
    simpa [alpha_dummy_006] using freshVar_not_mem (((Class.cv y)).fv) 0
  have fresh_008 : alpha_dummy_000 ∉ (({x} : Finset Var) ∪ (ph).fv) := by
    simpa [alpha_dummy_000] using freshVar_not_mem (({x} : Finset Var) ∪ (ph).fv) 0
  have support_part_0000 : alpha_dummy_000 ∈ (((Class.cv alpha_dummy_000)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0000 : alpha_dummy_000 ∈ (((Class.cv alpha_dummy_000)).fv) := by
    exact support_part_0000
  have support_part_0001 : y ∈ (((Class.cv y)).fv) := by
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, fv_class_cv] <;> aesop
  have support_mem_0001 : y ∈ (((Class.cv y)).fv) := by
    exact support_part_0001
  exact Nominal.alphaClassEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.objMem (TAlphaVar.there (freshVar_injective (((Class.cab alpha_dummy_000 (Wff.classEq (Class.cab x ph) (syn_csn (Class.cv alpha_dummy_000))))).fv) (by decide)) (freshVar_injective (((Class.cab y (Wff.classEq (Class.cab x ph) (syn_csn (Class.cv y))))).fv) (by decide)) (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _)) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.refl_of_fv_fresh _ _ (by simp_all [TEnvFresh] <;> aesop (config := { maxRuleApplications := 2000 })))) (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.here _ _ _)))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
