import NAPD051C001Part011

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

theorem nb051_compact_envfresh_0003 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) : TEnvFresh [((nb051_alpha_dummy_015 x y A B C), (nb051_alpha_dummy_016 x y z)), ((nb051_alpha_dummy_011 x y A B C), (nb051_alpha_dummy_013 x y z)), ((nb051_alpha_dummy_012 x y A B C), (nb051_alpha_dummy_014 x y z)), ((nb051_alpha_dummy_004 x y A B C), (nb051_alpha_dummy_006 x y z)), ((nb051_alpha_dummy_003 x y A B C), (nb051_alpha_dummy_005 x y z)), ((nb051_alpha_dummy_009 x y A B C), (nb051_alpha_dummy_010 x y z)), ((nb051_alpha_dummy_007 x y A B C), (nb051_alpha_dummy_008 x y z)), ((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x), ((nb051_alpha_dummy_001 x y A B C), (nb051_alpha_dummy_002 x y z A B C))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb051_alpha_dummy_015 x y A B C) (nb051_alpha_dummy_016 x y z) (nb051_wpp_notmem_0060 x y A B C) (nb051_wpp_notmem_0061 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_011 x y A B C) (nb051_alpha_dummy_013 x y z) (nb051_wpp_notmem_0062 x y A B C) (nb051_wpp_notmem_0063 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_012 x y A B C) (nb051_alpha_dummy_014 x y z) (nb051_wpp_notmem_0064 x y A B C) (nb051_wpp_notmem_0065 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_004 x y A B C) (nb051_alpha_dummy_006 x y z) (nb051_wpp_notmem_0066 x y A B C) (nb051_wpp_notmem_0067 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_003 x y A B C) (nb051_alpha_dummy_005 x y z) (nb051_wpp_notmem_0068 x y A B C) (nb051_wpp_notmem_0069 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_009 x y A B C) (nb051_alpha_dummy_010 x y z) (nb051_wpp_notmem_0070 x y A B C) (nb051_wpp_notmem_0071 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_007 x y A B C) (nb051_alpha_dummy_008 x y z) (nb051_wpp_notmem_0072 x y A B C) (nb051_wpp_notmem_0073 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_000 x y A B C) z (nb051_wpp_notmem_0074 x y A B C) (nb051_wpp_notmem_0075 z) (TEnvFresh.consSame y (TEnvFresh.consSame x (TEnvFresh.consFresh (nb051_alpha_dummy_001 x y A B C) (nb051_alpha_dummy_002 x y z A B C) (nb051_wpp_notmem_0076 x y A B C) (nb051_wpp_notmem_0077 x y z A B C) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))

noncomputable def nb051_wpp_refl_0003 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) : TReflOn [((nb051_alpha_dummy_015 x y A B C), (nb051_alpha_dummy_016 x y z)), ((nb051_alpha_dummy_011 x y A B C), (nb051_alpha_dummy_013 x y z)), ((nb051_alpha_dummy_012 x y A B C), (nb051_alpha_dummy_014 x y z)), ((nb051_alpha_dummy_004 x y A B C), (nb051_alpha_dummy_006 x y z)), ((nb051_alpha_dummy_003 x y A B C), (nb051_alpha_dummy_005 x y z)), ((nb051_alpha_dummy_009 x y A B C), (nb051_alpha_dummy_010 x y z)), ((nb051_alpha_dummy_007 x y A B C), (nb051_alpha_dummy_008 x y z)), ((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x), ((nb051_alpha_dummy_001 x y A B C), (nb051_alpha_dummy_002 x y z A B C))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb051_compact_envfresh_0003 x y z A B C)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
