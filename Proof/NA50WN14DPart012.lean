import NA50WN14DPart011

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

theorem nb050_compact_envfresh_0003 (x : Var) (y : Var) (A : Class) (B : Class) : TEnvFresh [((nb050_alpha_dummy_015 x A B), (nb050_alpha_dummy_016 x y)), ((nb050_alpha_dummy_011 x A B), (nb050_alpha_dummy_013 x y)), ((nb050_alpha_dummy_012 x A B), (nb050_alpha_dummy_014 x y)), ((nb050_alpha_dummy_004 x A B), (nb050_alpha_dummy_006 x y)), ((nb050_alpha_dummy_003 x A B), (nb050_alpha_dummy_005 x y)), ((nb050_alpha_dummy_009 x A B), (nb050_alpha_dummy_010 x y)), ((nb050_alpha_dummy_007 x A B), (nb050_alpha_dummy_008 x y)), ((nb050_alpha_dummy_000 x A B), y), (x, x), ((nb050_alpha_dummy_001 x A B), (nb050_alpha_dummy_002 x y A B))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb050_alpha_dummy_015 x A B) (nb050_alpha_dummy_016 x y) (nb050_wpp_notmem_0060 x A B) (nb050_wpp_notmem_0061 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_011 x A B) (nb050_alpha_dummy_013 x y) (nb050_wpp_notmem_0062 x A B) (nb050_wpp_notmem_0063 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_012 x A B) (nb050_alpha_dummy_014 x y) (nb050_wpp_notmem_0064 x A B) (nb050_wpp_notmem_0065 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_004 x A B) (nb050_alpha_dummy_006 x y) (nb050_wpp_notmem_0066 x A B) (nb050_wpp_notmem_0067 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_003 x A B) (nb050_alpha_dummy_005 x y) (nb050_wpp_notmem_0068 x A B) (nb050_wpp_notmem_0069 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_009 x A B) (nb050_alpha_dummy_010 x y) (nb050_wpp_notmem_0070 x A B) (nb050_wpp_notmem_0071 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_007 x A B) (nb050_alpha_dummy_008 x y) (nb050_wpp_notmem_0072 x A B) (nb050_wpp_notmem_0073 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_000 x A B) y (nb050_wpp_notmem_0074 x A B) (nb050_wpp_notmem_0075 y) (TEnvFresh.consSame x (TEnvFresh.consFresh (nb050_alpha_dummy_001 x A B) (nb050_alpha_dummy_002 x y A B) (nb050_wpp_notmem_0076 x A B) (nb050_wpp_notmem_0077 x y A B) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))

noncomputable def nb050_wpp_refl_0003 (x : Var) (y : Var) (A : Class) (B : Class) : TReflOn [((nb050_alpha_dummy_015 x A B), (nb050_alpha_dummy_016 x y)), ((nb050_alpha_dummy_011 x A B), (nb050_alpha_dummy_013 x y)), ((nb050_alpha_dummy_012 x A B), (nb050_alpha_dummy_014 x y)), ((nb050_alpha_dummy_004 x A B), (nb050_alpha_dummy_006 x y)), ((nb050_alpha_dummy_003 x A B), (nb050_alpha_dummy_005 x y)), ((nb050_alpha_dummy_009 x A B), (nb050_alpha_dummy_010 x y)), ((nb050_alpha_dummy_007 x A B), (nb050_alpha_dummy_008 x y)), ((nb050_alpha_dummy_000 x A B), y), (x, x), ((nb050_alpha_dummy_001 x A B), (nb050_alpha_dummy_002 x y A B))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb050_compact_envfresh_0003 x y A B)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
