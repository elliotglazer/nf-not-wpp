import NAPD051C001Part025

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

theorem nb051_compact_envfresh_0008 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) (dv_A_z : z ∉ A.fv) (dv_B_z : z ∉ B.fv) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) : TEnvFresh [((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x), ((nb051_alpha_dummy_001 x y A B C), (nb051_alpha_dummy_002 x y z A B C))] ((syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))).fv := by
  exact (TEnvFresh.consFresh (nb051_alpha_dummy_000 x y A B C) z (nb051_wpp_notmem_0110 x y A B C) (nb051_wpp_notmem_0111 x y z A B dv_A_z dv_B_z dv_x_z dv_y_z) (TEnvFresh.consSame y (TEnvFresh.consSame x (TEnvFresh.consFresh (nb051_alpha_dummy_001 x y A B C) (nb051_alpha_dummy_002 x y z A B C) (nb051_wpp_notmem_0112 x y A B C) (nb051_wpp_notmem_0113 x y z A B C) (TEnvFresh.nil ((syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))).fv)))))

noncomputable def nb051_wpp_refl_0008 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) (dv_A_z : z ∉ A.fv) (dv_B_z : z ∉ B.fv) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) : TReflOn [((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x), ((nb051_alpha_dummy_001 x y A B C), (nb051_alpha_dummy_002 x y z A B C))] ((syn_wa (Wff.classMem (Class.cv x) A) (Wff.classMem (Class.cv y) B))).fv :=
  TEnvFresh.reflOn (nb051_compact_envfresh_0008 x y z A B C dv_A_z dv_B_z dv_x_z dv_y_z)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
