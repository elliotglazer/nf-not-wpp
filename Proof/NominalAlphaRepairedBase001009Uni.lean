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

noncomputable def nominal_df_uni
    (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classEq (syn_cuni A) (.cab x (syn_wex y (syn_wa (.objMem x y) (.classMem (.cv y) A))))) := by
  let alpha_dummy_000 : Var := (freshVar ((A).fv) 0)
  let alpha_dummy_001 : Var := (freshVar ((A).fv) 1)
  have fresh_000 : alpha_dummy_000 ∉ ((A).fv) := by
    simpa [alpha_dummy_000] using freshVar_not_mem ((A).fv) 0
  have fresh_001 : alpha_dummy_001 ∉ ((A).fv) := by
    simpa [alpha_dummy_001] using freshVar_not_mem ((A).fv) 1
  have distinct_002 : alpha_dummy_000 ≠ alpha_dummy_001 := by
    simpa [alpha_dummy_000, alpha_dummy_001] using
      (freshVar_injective ((A).fv) (i := 0) (j := 1) (by decide))
  exact Nominal.alphaClassEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.objMem (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) dv_x_y (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _)) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_fv_fresh _ _ (by simp_all [TEnvFresh] <;> aesop (config := { maxRuleApplications := 2000 })))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
