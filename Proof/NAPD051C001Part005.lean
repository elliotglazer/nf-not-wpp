import NAPD051C001Part004

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

theorem nb051_compact_envfresh_0000 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) : TEnvFresh [((nb051_alpha_dummy_004 x y A B C), (nb051_alpha_dummy_006 x y z)), ((nb051_alpha_dummy_003 x y A B C), (nb051_alpha_dummy_005 x y z)), ((nb051_alpha_dummy_009 x y A B C), (nb051_alpha_dummy_010 x y z)), ((nb051_alpha_dummy_007 x y A B C), (nb051_alpha_dummy_008 x y z)), ((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x), ((nb051_alpha_dummy_001 x y A B C), (nb051_alpha_dummy_002 x y z A B C))] ((syn_cop (Class.cv x) (Class.cv y))).fv := by
  exact (TEnvFresh.consFresh (nb051_alpha_dummy_004 x y A B C) (nb051_alpha_dummy_006 x y z) (nb051_wpp_notmem_0000 x y A B C) (nb051_wpp_notmem_0001 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_003 x y A B C) (nb051_alpha_dummy_005 x y z) (nb051_wpp_notmem_0002 x y A B C) (nb051_wpp_notmem_0003 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_009 x y A B C) (nb051_alpha_dummy_010 x y z) (nb051_wpp_notmem_0004 x y A B C) (nb051_wpp_notmem_0005 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_007 x y A B C) (nb051_alpha_dummy_008 x y z) (nb051_wpp_notmem_0006 x y A B C) (nb051_wpp_notmem_0007 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_000 x y A B C) z (nb051_wpp_notmem_0008 x y A B C) (nb051_wpp_notmem_0009 x y z dv_x_z dv_y_z) (TEnvFresh.consSame y (TEnvFresh.consSame x (TEnvFresh.consFresh (nb051_alpha_dummy_001 x y A B C) (nb051_alpha_dummy_002 x y z A B C) (nb051_wpp_notmem_0010 x y A B C) (nb051_wpp_notmem_0011 x y z A B C) (TEnvFresh.nil ((syn_cop (Class.cv x) (Class.cv y))).fv)))))))))

noncomputable def nb051_wpp_refl_0000 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) : TReflOn [((nb051_alpha_dummy_004 x y A B C), (nb051_alpha_dummy_006 x y z)), ((nb051_alpha_dummy_003 x y A B C), (nb051_alpha_dummy_005 x y z)), ((nb051_alpha_dummy_009 x y A B C), (nb051_alpha_dummy_010 x y z)), ((nb051_alpha_dummy_007 x y A B C), (nb051_alpha_dummy_008 x y z)), ((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x), ((nb051_alpha_dummy_001 x y A B C), (nb051_alpha_dummy_002 x y z A B C))] ((syn_cop (Class.cv x) (Class.cv y))).fv :=
  TEnvFresh.reflOn (nb051_compact_envfresh_0000 x y z A B C dv_x_z dv_y_z)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
