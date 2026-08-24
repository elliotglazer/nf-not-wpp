import NA50WN14DPart022

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

theorem nb050_compact_envfresh_0007 (x : Var) (y : Var) (A : Class) (B : Class) : TEnvFresh [((nb050_alpha_dummy_035 x A B), (nb050_alpha_dummy_036 x y)), ((nb050_alpha_dummy_004 x A B), (nb050_alpha_dummy_006 x y)), ((nb050_alpha_dummy_003 x A B), (nb050_alpha_dummy_005 x y)), ((nb050_alpha_dummy_033 x A B), (nb050_alpha_dummy_034 x y)), ((nb050_alpha_dummy_007 x A B), (nb050_alpha_dummy_008 x y)), ((nb050_alpha_dummy_000 x A B), y), (x, x), ((nb050_alpha_dummy_001 x A B), (nb050_alpha_dummy_002 x y A B))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb050_alpha_dummy_035 x A B) (nb050_alpha_dummy_036 x y) (nb050_wpp_notmem_0096 x A B) (nb050_wpp_notmem_0097 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_004 x A B) (nb050_alpha_dummy_006 x y) (nb050_wpp_notmem_0098 x A B) (nb050_wpp_notmem_0099 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_003 x A B) (nb050_alpha_dummy_005 x y) (nb050_wpp_notmem_0100 x A B) (nb050_wpp_notmem_0101 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_033 x A B) (nb050_alpha_dummy_034 x y) (nb050_wpp_notmem_0102 x A B) (nb050_wpp_notmem_0103 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_007 x A B) (nb050_alpha_dummy_008 x y) (nb050_wpp_notmem_0104 x A B) (nb050_wpp_notmem_0105 x y) (TEnvFresh.consFresh (nb050_alpha_dummy_000 x A B) y (nb050_wpp_notmem_0106 x A B) (nb050_wpp_notmem_0107 y) (TEnvFresh.consSame x (TEnvFresh.consFresh (nb050_alpha_dummy_001 x A B) (nb050_alpha_dummy_002 x y A B) (nb050_wpp_notmem_0108 x A B) (nb050_wpp_notmem_0109 x y A B) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))

noncomputable def nb050_wpp_refl_0007 (x : Var) (y : Var) (A : Class) (B : Class) : TReflOn [((nb050_alpha_dummy_035 x A B), (nb050_alpha_dummy_036 x y)), ((nb050_alpha_dummy_004 x A B), (nb050_alpha_dummy_006 x y)), ((nb050_alpha_dummy_003 x A B), (nb050_alpha_dummy_005 x y)), ((nb050_alpha_dummy_033 x A B), (nb050_alpha_dummy_034 x y)), ((nb050_alpha_dummy_007 x A B), (nb050_alpha_dummy_008 x y)), ((nb050_alpha_dummy_000 x A B), y), (x, x), ((nb050_alpha_dummy_001 x A B), (nb050_alpha_dummy_002 x y A B))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb050_compact_envfresh_0007 x y A B)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
