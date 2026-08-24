import NA50WN14DPart014

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

theorem nb050_compact_envfresh_0004 (x : Var) (y : Var) (A : Class) (B : Class) : TEnvFresh [((nb050_alpha_dummy_019 x A B), (nb050_alpha_dummy_022 x y)), ((nb050_alpha_dummy_018 x A B), (nb050_alpha_dummy_021 x y)), ((nb050_alpha_dummy_017 x A B), (nb050_alpha_dummy_020 x y)), ((nb050_alpha_dummy_015 x A B), (nb050_alpha_dummy_016 x y)), ((nb050_alpha_dummy_011 x A B), (nb050_alpha_dummy_013 x y)), ((nb050_alpha_dummy_012 x A B), (nb050_alpha_dummy_014 x y)), ((nb050_alpha_dummy_037 x A B), (nb050_alpha_dummy_038 x y)), ((nb050_alpha_dummy_035 x A B), (nb050_alpha_dummy_036 x y)), ((nb050_alpha_dummy_004 x A B), (nb050_alpha_dummy_006 x y)), ((nb050_alpha_dummy_003 x A B), (nb050_alpha_dummy_005 x y)), ((nb050_alpha_dummy_033 x A B), (nb050_alpha_dummy_034 x y)), ((nb050_alpha_dummy_007 x A B), (nb050_alpha_dummy_008 x y)), ((nb050_alpha_dummy_000 x A B), y), (x, x), ((nb050_alpha_dummy_001 x A B), (nb050_alpha_dummy_002 x y A B))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb050_alpha_dummy_019 x A B) (nb050_alpha_dummy_022 x y) (nb050_wpp_notmem_0012 x A B) (nb050_wpp_notmem_0013 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_018 x A B) (nb050_alpha_dummy_021 x y) (nb050_wpp_notmem_0014 x A B) (nb050_wpp_notmem_0015 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_017 x A B) (nb050_alpha_dummy_020 x y) (nb050_wpp_notmem_0016 x A B) (nb050_wpp_notmem_0017 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_015 x A B) (nb050_alpha_dummy_016 x y) (nb050_wpp_notmem_0018 x A B) (nb050_wpp_notmem_0019 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_011 x A B) (nb050_alpha_dummy_013 x y) (nb050_wpp_notmem_0020 x A B) (nb050_wpp_notmem_0021 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_012 x A B) (nb050_alpha_dummy_014 x y) (nb050_wpp_notmem_0022 x A B) (nb050_wpp_notmem_0023 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_037 x A B) (nb050_alpha_dummy_038 x y) (nb050_wpp_notmem_0078 x A B) (nb050_wpp_notmem_0079 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_035 x A B) (nb050_alpha_dummy_036 x y) (nb050_wpp_notmem_0080 x A B) (nb050_wpp_notmem_0081 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_004 x A B) (nb050_alpha_dummy_006 x y) (nb050_wpp_notmem_0024 x A B) (nb050_wpp_notmem_0025 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_003 x A B) (nb050_alpha_dummy_005 x y) (nb050_wpp_notmem_0026 x A B) (nb050_wpp_notmem_0027 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_033 x A B) (nb050_alpha_dummy_034 x y) (nb050_wpp_notmem_0082 x A B) (nb050_wpp_notmem_0083 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_007 x A B) (nb050_alpha_dummy_008 x y) (nb050_wpp_notmem_0030 x A B) (nb050_wpp_notmem_0031 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_000 x A B) y (nb050_wpp_notmem_0032 x A B) (nb050_wpp_notmem_0033 y) (TEnvFresh.consSame x (TEnvFresh.consFresh (nb050_alpha_dummy_001 x A B) (nb050_alpha_dummy_002 x y A B) (nb050_wpp_notmem_0034 x A B) (nb050_wpp_notmem_0035 x y A B) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))

noncomputable def nb050_wpp_refl_0004 (x : Var) (y : Var) (A : Class) (B : Class) : TReflOn [((nb050_alpha_dummy_019 x A B), (nb050_alpha_dummy_022 x y)), ((nb050_alpha_dummy_018 x A B), (nb050_alpha_dummy_021 x y)), ((nb050_alpha_dummy_017 x A B), (nb050_alpha_dummy_020 x y)), ((nb050_alpha_dummy_015 x A B), (nb050_alpha_dummy_016 x y)), ((nb050_alpha_dummy_011 x A B), (nb050_alpha_dummy_013 x y)), ((nb050_alpha_dummy_012 x A B), (nb050_alpha_dummy_014 x y)), ((nb050_alpha_dummy_037 x A B), (nb050_alpha_dummy_038 x y)), ((nb050_alpha_dummy_035 x A B), (nb050_alpha_dummy_036 x y)), ((nb050_alpha_dummy_004 x A B), (nb050_alpha_dummy_006 x y)), ((nb050_alpha_dummy_003 x A B), (nb050_alpha_dummy_005 x y)), ((nb050_alpha_dummy_033 x A B), (nb050_alpha_dummy_034 x y)), ((nb050_alpha_dummy_007 x A B), (nb050_alpha_dummy_008 x y)), ((nb050_alpha_dummy_000 x A B), y), (x, x), ((nb050_alpha_dummy_001 x A B), (nb050_alpha_dummy_002 x y A B))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb050_compact_envfresh_0004 x y A B)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
