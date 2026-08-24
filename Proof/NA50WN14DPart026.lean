import NA50WN14DPart025

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

theorem nb050_compact_envfresh_0008 (x : Var) (y : Var) (A : Class) (B : Class) (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) : TEnvFresh [((nb050_alpha_dummy_000 x A B), y), (x, x), ((nb050_alpha_dummy_001 x A B), (nb050_alpha_dummy_002 x y A B))] ((Wff.classMem (Class.cv x) A)).fv := by
  exact (TEnvFresh.consFresh (nb050_alpha_dummy_000 x A B) y (nb050_wpp_notmem_0110 x A B) (nb050_wpp_notmem_0111 x y A dv_A_y dv_x_y) (TEnvFresh.consSame x (TEnvFresh.consFresh (nb050_alpha_dummy_001 x A B) (nb050_alpha_dummy_002 x y A B) (nb050_wpp_notmem_0112 x A B) (nb050_wpp_notmem_0113 x y A B) (TEnvFresh.nil ((Wff.classMem (Class.cv x) A)).fv))))

noncomputable def nb050_wpp_refl_0008 (x : Var) (y : Var) (A : Class) (B : Class) (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) : TReflOn [((nb050_alpha_dummy_000 x A B), y), (x, x), ((nb050_alpha_dummy_001 x A B), (nb050_alpha_dummy_002 x y A B))] ((Wff.classMem (Class.cv x) A)).fv :=
  TEnvFresh.reflOn (nb050_compact_envfresh_0008 x y A B dv_A_y dv_x_y)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
