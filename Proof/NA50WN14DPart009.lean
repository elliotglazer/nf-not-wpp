import NA50WN14DPart008

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

theorem nb050_compact_envfresh_0002 (x : Var) (y : Var) (A : Class) (B : Class) : TEnvFresh [((nb050_alpha_dummy_019 x A B), (nb050_alpha_dummy_022 x y)), ((nb050_alpha_dummy_018 x A B), (nb050_alpha_dummy_021 x y)), ((nb050_alpha_dummy_017 x A B), (nb050_alpha_dummy_020 x y)), ((nb050_alpha_dummy_015 x A B), (nb050_alpha_dummy_016 x y)), ((nb050_alpha_dummy_011 x A B), (nb050_alpha_dummy_013 x y)), ((nb050_alpha_dummy_012 x A B), (nb050_alpha_dummy_014 x y)), ((nb050_alpha_dummy_004 x A B), (nb050_alpha_dummy_006 x y)), ((nb050_alpha_dummy_003 x A B), (nb050_alpha_dummy_005 x y)), ((nb050_alpha_dummy_009 x A B), (nb050_alpha_dummy_010 x y)), ((nb050_alpha_dummy_007 x A B), (nb050_alpha_dummy_008 x y)), ((nb050_alpha_dummy_000 x A B), y), (x, x), ((nb050_alpha_dummy_001 x A B), (nb050_alpha_dummy_002 x y A B))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb050_alpha_dummy_019 x A B) (nb050_alpha_dummy_022 x y) (nb050_wpp_notmem_0036 x A B) (nb050_wpp_notmem_0037 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_018 x A B) (nb050_alpha_dummy_021 x y) (nb050_wpp_notmem_0038 x A B) (nb050_wpp_notmem_0039 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_017 x A B) (nb050_alpha_dummy_020 x y) (nb050_wpp_notmem_0040 x A B) (nb050_wpp_notmem_0041 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_015 x A B) (nb050_alpha_dummy_016 x y) (nb050_wpp_notmem_0042 x A B) (nb050_wpp_notmem_0043 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_011 x A B) (nb050_alpha_dummy_013 x y) (nb050_wpp_notmem_0044 x A B) (nb050_wpp_notmem_0045 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_012 x A B) (nb050_alpha_dummy_014 x y) (nb050_wpp_notmem_0046 x A B) (nb050_wpp_notmem_0047 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_004 x A B) (nb050_alpha_dummy_006 x y) (nb050_wpp_notmem_0048 x A B) (nb050_wpp_notmem_0049 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_003 x A B) (nb050_alpha_dummy_005 x y) (nb050_wpp_notmem_0050 x A B) (nb050_wpp_notmem_0051 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_009 x A B) (nb050_alpha_dummy_010 x y) (nb050_wpp_notmem_0052 x A B) (nb050_wpp_notmem_0053 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_007 x A B) (nb050_alpha_dummy_008 x y) (nb050_wpp_notmem_0054 x A B) (nb050_wpp_notmem_0055 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_000 x A B) y (nb050_wpp_notmem_0056 x A B) (nb050_wpp_notmem_0057 y) (TEnvFresh.consSame x (TEnvFresh.consFresh (nb050_alpha_dummy_001 x A B) (nb050_alpha_dummy_002 x y A B) (nb050_wpp_notmem_0058 x A B) (nb050_wpp_notmem_0059 x y A B) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))

noncomputable def nb050_wpp_refl_0002 (x : Var) (y : Var) (A : Class) (B : Class) : TReflOn [((nb050_alpha_dummy_019 x A B), (nb050_alpha_dummy_022 x y)), ((nb050_alpha_dummy_018 x A B), (nb050_alpha_dummy_021 x y)), ((nb050_alpha_dummy_017 x A B), (nb050_alpha_dummy_020 x y)), ((nb050_alpha_dummy_015 x A B), (nb050_alpha_dummy_016 x y)), ((nb050_alpha_dummy_011 x A B), (nb050_alpha_dummy_013 x y)), ((nb050_alpha_dummy_012 x A B), (nb050_alpha_dummy_014 x y)), ((nb050_alpha_dummy_004 x A B), (nb050_alpha_dummy_006 x y)), ((nb050_alpha_dummy_003 x A B), (nb050_alpha_dummy_005 x y)), ((nb050_alpha_dummy_009 x A B), (nb050_alpha_dummy_010 x y)), ((nb050_alpha_dummy_007 x A B), (nb050_alpha_dummy_008 x y)), ((nb050_alpha_dummy_000 x A B), y), (x, x), ((nb050_alpha_dummy_001 x A B), (nb050_alpha_dummy_002 x y A B))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb050_compact_envfresh_0002 x y A B)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
