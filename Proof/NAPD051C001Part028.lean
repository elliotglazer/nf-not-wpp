import NAPD051C001Part027

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

theorem nb051_compact_envfresh_0009 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) (dv_C_z : z ∉ C.fv) : TEnvFresh [((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x), ((nb051_alpha_dummy_001 x y A B C), (nb051_alpha_dummy_002 x y z A B C))] (C).fv := by
  exact (TEnvFresh.consFresh (nb051_alpha_dummy_000 x y A B C) z (nb051_wpp_notmem_0114 x y A B C) (nb051_wpp_notmem_0115 z C dv_C_z) (TEnvFresh.consSame y (TEnvFresh.consSame x (TEnvFresh.consFresh (nb051_alpha_dummy_001 x y A B C) (nb051_alpha_dummy_002 x y z A B C) (nb051_wpp_notmem_0116 x y A B C) (nb051_wpp_notmem_0117 x y z A B C) (TEnvFresh.nil (C).fv)))))

noncomputable def nb051_wpp_refl_0009 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) (dv_C_z : z ∉ C.fv) : TReflOn [((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x), ((nb051_alpha_dummy_001 x y A B C), (nb051_alpha_dummy_002 x y z A B C))] (C).fv :=
  TEnvFresh.reflOn (nb051_compact_envfresh_0009 x y z A B C dv_C_z)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
