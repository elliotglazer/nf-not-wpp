import NAPD051C001Part022

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

theorem nb051_compact_envfresh_0007 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) : TEnvFresh [((nb051_alpha_dummy_035 x y A B C), (nb051_alpha_dummy_036 x y z)), ((nb051_alpha_dummy_004 x y A B C), (nb051_alpha_dummy_006 x y z)), ((nb051_alpha_dummy_003 x y A B C), (nb051_alpha_dummy_005 x y z)), ((nb051_alpha_dummy_033 x y A B C), (nb051_alpha_dummy_034 x y z)), ((nb051_alpha_dummy_007 x y A B C), (nb051_alpha_dummy_008 x y z)), ((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x), ((nb051_alpha_dummy_001 x y A B C), (nb051_alpha_dummy_002 x y z A B C))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb051_alpha_dummy_035 x y A B C) (nb051_alpha_dummy_036 x y z) (nb051_wpp_notmem_0096 x y A B C) (nb051_wpp_notmem_0097 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_004 x y A B C) (nb051_alpha_dummy_006 x y z) (nb051_wpp_notmem_0098 x y A B C) (nb051_wpp_notmem_0099 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_003 x y A B C) (nb051_alpha_dummy_005 x y z) (nb051_wpp_notmem_0100 x y A B C) (nb051_wpp_notmem_0101 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_033 x y A B C) (nb051_alpha_dummy_034 x y z) (nb051_wpp_notmem_0102 x y A B C) (nb051_wpp_notmem_0103 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_007 x y A B C) (nb051_alpha_dummy_008 x y z) (nb051_wpp_notmem_0104 x y A B C) (nb051_wpp_notmem_0105 x y z) (TEnvFresh.consFresh (nb051_alpha_dummy_000 x y A B C) z (nb051_wpp_notmem_0106 x y A B C) (nb051_wpp_notmem_0107 z) (TEnvFresh.consSame y (TEnvFresh.consSame x (TEnvFresh.consFresh (nb051_alpha_dummy_001 x y A B C) (nb051_alpha_dummy_002 x y z A B C) (nb051_wpp_notmem_0108 x y A B C) (nb051_wpp_notmem_0109 x y z A B C) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))))

noncomputable def nb051_wpp_refl_0007 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) (C : Class) : TReflOn [((nb051_alpha_dummy_035 x y A B C), (nb051_alpha_dummy_036 x y z)), ((nb051_alpha_dummy_004 x y A B C), (nb051_alpha_dummy_006 x y z)), ((nb051_alpha_dummy_003 x y A B C), (nb051_alpha_dummy_005 x y z)), ((nb051_alpha_dummy_033 x y A B C), (nb051_alpha_dummy_034 x y z)), ((nb051_alpha_dummy_007 x y A B C), (nb051_alpha_dummy_008 x y z)), ((nb051_alpha_dummy_000 x y A B C), z), (y, y), (x, x), ((nb051_alpha_dummy_001 x y A B C), (nb051_alpha_dummy_002 x y z A B C))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb051_compact_envfresh_0007 x y z A B C)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
