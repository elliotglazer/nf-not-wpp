import NA50WN14DPart004

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

theorem nb050_compact_envfresh_0000 (x : Var) (y : Var) (A : Class) (B : Class) (dv_x_y : x ≠ y) : TEnvFresh [((nb050_alpha_dummy_004 x A B), (nb050_alpha_dummy_006 x y)), ((nb050_alpha_dummy_003 x A B), (nb050_alpha_dummy_005 x y)), ((nb050_alpha_dummy_009 x A B), (nb050_alpha_dummy_010 x y)), ((nb050_alpha_dummy_007 x A B), (nb050_alpha_dummy_008 x y)), ((nb050_alpha_dummy_000 x A B), y), (x, x), ((nb050_alpha_dummy_001 x A B), (nb050_alpha_dummy_002 x y A B))] ((Class.cv x)).fv := by
  exact (TEnvFresh.consFresh (nb050_alpha_dummy_004 x A B) (nb050_alpha_dummy_006 x y) (nb050_wpp_notmem_0000 x A B) (nb050_wpp_notmem_0001 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_003 x A B) (nb050_alpha_dummy_005 x y) (nb050_wpp_notmem_0002 x A B) (nb050_wpp_notmem_0003 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_009 x A B) (nb050_alpha_dummy_010 x y) (nb050_wpp_notmem_0004 x A B) (nb050_wpp_notmem_0005 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_007 x A B) (nb050_alpha_dummy_008 x y) (nb050_wpp_notmem_0006 x A B) (nb050_wpp_notmem_0007 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_000 x A B) y (nb050_wpp_notmem_0008 x A B) (nb050_wpp_notmem_0009 x y dv_x_y) (TEnvFresh.consSame x (TEnvFresh.consFresh (nb050_alpha_dummy_001 x A B) (nb050_alpha_dummy_002 x y A B) (nb050_wpp_notmem_0010 x A B) (nb050_wpp_notmem_0011 x y A B) (TEnvFresh.nil ((Class.cv x)).fv))))))))

noncomputable def nb050_wpp_refl_0000 (x : Var) (y : Var) (A : Class) (B : Class) (dv_x_y : x ≠ y) : TReflOn [((nb050_alpha_dummy_004 x A B), (nb050_alpha_dummy_006 x y)), ((nb050_alpha_dummy_003 x A B), (nb050_alpha_dummy_005 x y)), ((nb050_alpha_dummy_009 x A B), (nb050_alpha_dummy_010 x y)), ((nb050_alpha_dummy_007 x A B), (nb050_alpha_dummy_008 x y)), ((nb050_alpha_dummy_000 x A B), y), (x, x), ((nb050_alpha_dummy_001 x A B), (nb050_alpha_dummy_002 x y A B))] ((Class.cv x)).fv :=
  TEnvFresh.reflOn (nb050_compact_envfresh_0000 x y A B dv_x_y)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
