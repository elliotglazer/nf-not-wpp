import NAPD051C001Part016

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

theorem nb051_compact_envfresh_0005 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) : TEnvFresh [((nb051_alpha_dummy_019 x y A B C), (nb051_alpha_dummy_022 x y z)), ((nb051_alpha_dummy_018 x y A B C), (nb051_alpha_dummy_021 x y z)), ((nb051_alpha_dummy_017 x y A B C), (nb051_alpha_dummy_020 x y z)), ((nb051_alpha_dummy_015 x y A B C), (nb051_alpha_dummy_016 x y z)), ((nb051_alpha_dummy_011 x y A B C), (nb051_alpha_dummy_013 x y z)), ((nb051_alpha_dummy_012 x y A B C), (nb051_alpha_dummy_014 x y z)), ((nb051_alpha_dummy_037 x y A B C), (nb051_alpha_dummy_038 x y z)), ((nb051_alpha_dummy_035 x y A B C), (nb051_alpha_dummy_036 x y z)), ((nb051_alpha_dummy_004 x y A B C), (nb051_alpha_dummy_006 x y z)), ((nb051_alpha_dummy_003 x y A B C), (nb051_alpha_dummy_005 x y z)), ((nb051_alpha_dummy_033 x y A B C), (nb051_alpha_dummy_034 x y z)), ((nb051_alpha_dummy_007 x y A B C), (nb051_alpha_dummy_008 x y z)), ((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x), ((nb051_alpha_dummy_001 x y A B C), (nb051_alpha_dummy_002 x y z A B C))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb051_alpha_dummy_019 x y A B C) (nb051_alpha_dummy_022 x y z) (nb051_wpp_notmem_0036 x y A B C) (nb051_wpp_notmem_0037 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_018 x y A B C) (nb051_alpha_dummy_021 x y z) (nb051_wpp_notmem_0038 x y A B C) (nb051_wpp_notmem_0039 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_017 x y A B C) (nb051_alpha_dummy_020 x y z) (nb051_wpp_notmem_0040 x y A B C) (nb051_wpp_notmem_0041 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_015 x y A B C) (nb051_alpha_dummy_016 x y z) (nb051_wpp_notmem_0042 x y A B C) (nb051_wpp_notmem_0043 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_011 x y A B C) (nb051_alpha_dummy_013 x y z) (nb051_wpp_notmem_0044 x y A B C) (nb051_wpp_notmem_0045 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_012 x y A B C) (nb051_alpha_dummy_014 x y z) (nb051_wpp_notmem_0046 x y A B C) (nb051_wpp_notmem_0047 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_037 x y A B C) (nb051_alpha_dummy_038 x y z) (nb051_wpp_notmem_0084 x y A B C) (nb051_wpp_notmem_0085 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_035 x y A B C) (nb051_alpha_dummy_036 x y z) (nb051_wpp_notmem_0086 x y A B C) (nb051_wpp_notmem_0087 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_004 x y A B C) (nb051_alpha_dummy_006 x y z) (nb051_wpp_notmem_0048 x y A B C) (nb051_wpp_notmem_0049 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_003 x y A B C) (nb051_alpha_dummy_005 x y z) (nb051_wpp_notmem_0050 x y A B C) (nb051_wpp_notmem_0051 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_033 x y A B C) (nb051_alpha_dummy_034 x y z) (nb051_wpp_notmem_0088 x y A B C) (nb051_wpp_notmem_0089 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_007 x y A B C) (nb051_alpha_dummy_008 x y z) (nb051_wpp_notmem_0054 x y A B C) (nb051_wpp_notmem_0055 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_000 x y A B C) z (nb051_wpp_notmem_0056 x y A B C) (nb051_wpp_notmem_0057 z) (TEnvFresh.consSame y (TEnvFresh.consSame x (TEnvFresh.consFresh (nb051_alpha_dummy_001 x y A B C) (nb051_alpha_dummy_002 x y z A B C) (nb051_wpp_notmem_0058 x y A B C) (nb051_wpp_notmem_0059 x y z A B C) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))

noncomputable def nb051_wpp_refl_0005 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) : TReflOn [((nb051_alpha_dummy_019 x y A B C), (nb051_alpha_dummy_022 x y z)), ((nb051_alpha_dummy_018 x y A B C), (nb051_alpha_dummy_021 x y z)), ((nb051_alpha_dummy_017 x y A B C), (nb051_alpha_dummy_020 x y z)), ((nb051_alpha_dummy_015 x y A B C), (nb051_alpha_dummy_016 x y z)), ((nb051_alpha_dummy_011 x y A B C), (nb051_alpha_dummy_013 x y z)), ((nb051_alpha_dummy_012 x y A B C), (nb051_alpha_dummy_014 x y z)), ((nb051_alpha_dummy_037 x y A B C), (nb051_alpha_dummy_038 x y z)), ((nb051_alpha_dummy_035 x y A B C), (nb051_alpha_dummy_036 x y z)), ((nb051_alpha_dummy_004 x y A B C), (nb051_alpha_dummy_006 x y z)), ((nb051_alpha_dummy_003 x y A B C), (nb051_alpha_dummy_005 x y z)), ((nb051_alpha_dummy_033 x y A B C), (nb051_alpha_dummy_034 x y z)), ((nb051_alpha_dummy_007 x y A B C), (nb051_alpha_dummy_008 x y z)), ((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x), ((nb051_alpha_dummy_001 x y A B C), (nb051_alpha_dummy_002 x y z A B C))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb051_compact_envfresh_0005 x y z A B C)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
