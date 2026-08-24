import NominalAlphaRepairedBase001037OpabOpaqueCertificate004

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

noncomputable def nominal_df_opab
    (ph : Wff) (x : Var) (y : Var) (z : Var) (dv_ph_z : z ∉ ph.fv) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf (.classEq (syn_copab x y ph) (.cab z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph))))) := by
  exact Nominal.alphaClassEq (nb037_opab_alpha_certificate_opaque004 ph x y z dv_ph_z dv_x_z dv_y_z)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
