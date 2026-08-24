import NAPD051C001Part014

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

theorem nb051_compact_envfresh_0004 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) : TEnvFresh [((nb051_alpha_dummy_019 x y A B C), (nb051_alpha_dummy_022 x y z)), ((nb051_alpha_dummy_018 x y A B C), (nb051_alpha_dummy_021 x y z)), ((nb051_alpha_dummy_017 x y A B C), (nb051_alpha_dummy_020 x y z)), ((nb051_alpha_dummy_015 x y A B C), (nb051_alpha_dummy_016 x y z)), ((nb051_alpha_dummy_011 x y A B C), (nb051_alpha_dummy_013 x y z)), ((nb051_alpha_dummy_012 x y A B C), (nb051_alpha_dummy_014 x y z)), ((nb051_alpha_dummy_037 x y A B C), (nb051_alpha_dummy_038 x y z)), ((nb051_alpha_dummy_035 x y A B C), (nb051_alpha_dummy_036 x y z)), ((nb051_alpha_dummy_004 x y A B C), (nb051_alpha_dummy_006 x y z)), ((nb051_alpha_dummy_003 x y A B C), (nb051_alpha_dummy_005 x y z)), ((nb051_alpha_dummy_033 x y A B C), (nb051_alpha_dummy_034 x y z)), ((nb051_alpha_dummy_007 x y A B C), (nb051_alpha_dummy_008 x y z)), ((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x), ((nb051_alpha_dummy_001 x y A B C), (nb051_alpha_dummy_002 x y z A B C))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb051_alpha_dummy_019 x y A B C) (nb051_alpha_dummy_022 x y z) (nb051_wpp_notmem_0012 x y A B C) (nb051_wpp_notmem_0013 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_018 x y A B C) (nb051_alpha_dummy_021 x y z) (nb051_wpp_notmem_0014 x y A B C) (nb051_wpp_notmem_0015 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_017 x y A B C) (nb051_alpha_dummy_020 x y z) (nb051_wpp_notmem_0016 x y A B C) (nb051_wpp_notmem_0017 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_015 x y A B C) (nb051_alpha_dummy_016 x y z) (nb051_wpp_notmem_0018 x y A B C) (nb051_wpp_notmem_0019 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_011 x y A B C) (nb051_alpha_dummy_013 x y z) (nb051_wpp_notmem_0020 x y A B C) (nb051_wpp_notmem_0021 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_012 x y A B C) (nb051_alpha_dummy_014 x y z) (nb051_wpp_notmem_0022 x y A B C) (nb051_wpp_notmem_0023 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_037 x y A B C) (nb051_alpha_dummy_038 x y z) (nb051_wpp_notmem_0078 x y A B C) (nb051_wpp_notmem_0079 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_035 x y A B C) (nb051_alpha_dummy_036 x y z) (nb051_wpp_notmem_0080 x y A B C) (nb051_wpp_notmem_0081 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_004 x y A B C) (nb051_alpha_dummy_006 x y z) (nb051_wpp_notmem_0024 x y A B C) (nb051_wpp_notmem_0025 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_003 x y A B C) (nb051_alpha_dummy_005 x y z) (nb051_wpp_notmem_0026 x y A B C) (nb051_wpp_notmem_0027 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_033 x y A B C) (nb051_alpha_dummy_034 x y z) (nb051_wpp_notmem_0082 x y A B C) (nb051_wpp_notmem_0083 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_007 x y A B C) (nb051_alpha_dummy_008 x y z) (nb051_wpp_notmem_0030 x y A B C) (nb051_wpp_notmem_0031 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_000 x y A B C) z (nb051_wpp_notmem_0032 x y A B C) (nb051_wpp_notmem_0033 z) (TEnvFresh.consSame y (TEnvFresh.consSame x (TEnvFresh.consFresh (nb051_alpha_dummy_001 x y A B C) (nb051_alpha_dummy_002 x y z A B C) (nb051_wpp_notmem_0034 x y A B C) (nb051_wpp_notmem_0035 x y z A B C) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))

noncomputable def nb051_wpp_refl_0004 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) : TReflOn [((nb051_alpha_dummy_019 x y A B C), (nb051_alpha_dummy_022 x y z)), ((nb051_alpha_dummy_018 x y A B C), (nb051_alpha_dummy_021 x y z)), ((nb051_alpha_dummy_017 x y A B C), (nb051_alpha_dummy_020 x y z)), ((nb051_alpha_dummy_015 x y A B C), (nb051_alpha_dummy_016 x y z)), ((nb051_alpha_dummy_011 x y A B C), (nb051_alpha_dummy_013 x y z)), ((nb051_alpha_dummy_012 x y A B C), (nb051_alpha_dummy_014 x y z)), ((nb051_alpha_dummy_037 x y A B C), (nb051_alpha_dummy_038 x y z)), ((nb051_alpha_dummy_035 x y A B C), (nb051_alpha_dummy_036 x y z)), ((nb051_alpha_dummy_004 x y A B C), (nb051_alpha_dummy_006 x y z)), ((nb051_alpha_dummy_003 x y A B C), (nb051_alpha_dummy_005 x y z)), ((nb051_alpha_dummy_033 x y A B C), (nb051_alpha_dummy_034 x y z)), ((nb051_alpha_dummy_007 x y A B C), (nb051_alpha_dummy_008 x y z)), ((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x), ((nb051_alpha_dummy_001 x y A B C), (nb051_alpha_dummy_002 x y z A B C))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb051_compact_envfresh_0004 x y z A B C)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
