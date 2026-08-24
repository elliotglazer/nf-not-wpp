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

noncomputable def nominal_df_nfc
    (x : Var) (y : Var) (A : Class) (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (syn_wb (syn_wnfc x A) (.all y (syn_wnf x (.classMem (.cv y) A)))) := by
  let alpha_dummy_000 : Var := (freshVar (({x} : Finset Var) ∪ (A).fv) 0)
  have fresh_000 : alpha_dummy_000 ∉ (({x} : Finset Var) ∪ (A).fv) := by
    simpa [alpha_dummy_000] using freshVar_not_mem (({x} : Finset Var) ∪ (A).fv) 0
  have support_part_0000 : x ∈ (({x} : Finset Var)) := by
    exact Finset.mem_singleton_self _
  have support_mem_0000 : x ∈ (({x} : Finset Var) ∪ (A).fv) := by
    exact (Finset.mem_union_left ((A).fv) support_part_0000)
  change Nominal.NPrf (Wff.biimp (syn_wnfc x A) (Wff.all y (syn_wnf x (Wff.classMem (Class.cv y) A))))
  exact Nominal.alphaBiimp (TAlphaWff.all (TAlphaWff.all (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))) (Ne.symm dv_x_y) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_fv_fresh _ _ (by simp_all [TEnvFresh] <;> aesop (config := { maxRuleApplications := 2000 })))) (TAlphaWff.all (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))) (Ne.symm dv_x_y) (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))) (Ne.symm dv_x_y) (TAlphaVar.here _ _ _)))) (TAlphaClass.refl_of_fv_fresh _ _ (by simp_all [TEnvFresh] <;> aesop (config := { maxRuleApplications := 2000 }))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
