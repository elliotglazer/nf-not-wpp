import NAR4C077C001Part013

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

theorem nb077_compact_fv_empty_0083 (x : Var) : (nb077_alpha_dummy_121 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0273 (x : Var) : (nb077_alpha_dummy_121 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_121, fv_syn_c1c] using (nb077_compact_fv_empty_0083 x)

theorem nb077_compact_fv_empty_0084 (F : Class) (I : Class) : (nb077_alpha_dummy_117 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0274 (F : Class) (I : Class) : (nb077_alpha_dummy_117 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_117, fv_syn_c1c] using (nb077_compact_fv_empty_0084 F I)

theorem nb077_compact_fv_empty_0085 (x : Var) : (nb077_alpha_dummy_120 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0275 (x : Var) : (nb077_alpha_dummy_120 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_120, fv_syn_c1c] using (nb077_compact_fv_empty_0085 x)

theorem nb077_compact_fv_empty_0086 (F : Class) (I : Class) : (nb077_alpha_dummy_115 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0276 (F : Class) (I : Class) : (nb077_alpha_dummy_115 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_115, fv_syn_c1c] using (nb077_compact_fv_empty_0086 F I)

theorem nb077_compact_fv_empty_0087 (x : Var) : (nb077_alpha_dummy_116 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0277 (x : Var) : (nb077_alpha_dummy_116 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_116, fv_syn_c1c] using (nb077_compact_fv_empty_0087 x)

theorem nb077_compact_fv_empty_0088 (F : Class) (I : Class) : (nb077_alpha_dummy_111 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0278 (F : Class) (I : Class) : (nb077_alpha_dummy_111 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_111, fv_syn_c1c] using (nb077_compact_fv_empty_0088 F I)

theorem nb077_compact_fv_empty_0089 (x : Var) : (nb077_alpha_dummy_113 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0279 (x : Var) : (nb077_alpha_dummy_113 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_113, fv_syn_c1c] using (nb077_compact_fv_empty_0089 x)

theorem nb077_compact_fv_empty_0090 (F : Class) (I : Class) : (nb077_alpha_dummy_112 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0280 (F : Class) (I : Class) : (nb077_alpha_dummy_112 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_112, fv_syn_c1c] using (nb077_compact_fv_empty_0090 F I)

theorem nb077_compact_fv_empty_0091 (x : Var) : (nb077_alpha_dummy_114 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0281 (x : Var) : (nb077_alpha_dummy_114 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_114, fv_syn_c1c] using (nb077_compact_fv_empty_0091 x)

theorem nb077_compact_fv_empty_0092 (F : Class) (I : Class) : (nb077_alpha_dummy_104 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0282 (F : Class) (I : Class) : (nb077_alpha_dummy_104 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_104, fv_syn_c1c] using (nb077_compact_fv_empty_0092 F I)

theorem nb077_compact_fv_empty_0093 (x : Var) : (nb077_alpha_dummy_106 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0283 (x : Var) : (nb077_alpha_dummy_106 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_106, fv_syn_c1c] using (nb077_compact_fv_empty_0093 x)

theorem nb077_compact_fv_empty_0094 (F : Class) (I : Class) : (nb077_alpha_dummy_103 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0284 (F : Class) (I : Class) : (nb077_alpha_dummy_103 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_103, fv_syn_c1c] using (nb077_compact_fv_empty_0094 F I)

theorem nb077_compact_fv_empty_0095 (x : Var) : (nb077_alpha_dummy_105 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0285 (x : Var) : (nb077_alpha_dummy_105 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_105, fv_syn_c1c] using (nb077_compact_fv_empty_0095 x)

theorem nb077_compact_fv_empty_0096 (F : Class) (I : Class) : (nb077_alpha_dummy_109 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0286 (F : Class) (I : Class) : (nb077_alpha_dummy_109 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_109, fv_syn_c1c] using (nb077_compact_fv_empty_0096 F I)

theorem nb077_compact_fv_empty_0097 (x : Var) : (nb077_alpha_dummy_110 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0287 (x : Var) : (nb077_alpha_dummy_110 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_110, fv_syn_c1c] using (nb077_compact_fv_empty_0097 x)

theorem nb077_compact_fv_empty_0098 (F : Class) (I : Class) : (nb077_alpha_dummy_107 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0288 (F : Class) (I : Class) : (nb077_alpha_dummy_107 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_107, fv_syn_c1c] using (nb077_compact_fv_empty_0098 F I)

theorem nb077_compact_fv_empty_0099 (x : Var) : (nb077_alpha_dummy_108 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0289 (x : Var) : (nb077_alpha_dummy_108 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_108, fv_syn_c1c] using (nb077_compact_fv_empty_0099 x)

theorem nb077_compact_fv_empty_0100 (F : Class) (I : Class) : (nb077_alpha_dummy_061 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0290 (F : Class) (I : Class) : (nb077_alpha_dummy_061 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_061, fv_syn_c1c] using (nb077_compact_fv_empty_0100 F I)

theorem nb077_compact_fv_empty_0101 (x : Var) : (nb077_alpha_dummy_064 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0291 (x : Var) : (nb077_alpha_dummy_064 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_064, fv_syn_c1c] using (nb077_compact_fv_empty_0101 x)

theorem nb077_compact_envfresh_0016 (x : Var) (F : Class) (I : Class) : TEnvFresh [((nb077_alpha_dummy_119 F I), (nb077_alpha_dummy_122 x)), ((nb077_alpha_dummy_118 F I), (nb077_alpha_dummy_121 x)), ((nb077_alpha_dummy_117 F I), (nb077_alpha_dummy_120 x)), ((nb077_alpha_dummy_115 F I), (nb077_alpha_dummy_116 x)), ((nb077_alpha_dummy_111 F I), (nb077_alpha_dummy_113 x)), ((nb077_alpha_dummy_112 F I), (nb077_alpha_dummy_114 x)), ((nb077_alpha_dummy_104 F I), (nb077_alpha_dummy_106 x)), ((nb077_alpha_dummy_103 F I), (nb077_alpha_dummy_105 x)), ((nb077_alpha_dummy_109 F I), (nb077_alpha_dummy_110 x)), ((nb077_alpha_dummy_107 F I), (nb077_alpha_dummy_108 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb077_alpha_dummy_119 F I) (nb077_alpha_dummy_122 x) (nb077_wpp_notmem_0270 F I) (nb077_wpp_notmem_0271 x) (TEnvFresh.consFresh (nb077_alpha_dummy_118 F I) (nb077_alpha_dummy_121 x) (nb077_wpp_notmem_0272 F I) (nb077_wpp_notmem_0273 x) (TEnvFresh.consFresh (nb077_alpha_dummy_117 F I) (nb077_alpha_dummy_120 x) (nb077_wpp_notmem_0274 F I) (nb077_wpp_notmem_0275 x) (TEnvFresh.consFresh (nb077_alpha_dummy_115 F I) (nb077_alpha_dummy_116 x) (nb077_wpp_notmem_0276 F I) (nb077_wpp_notmem_0277 x) (TEnvFresh.consFresh (nb077_alpha_dummy_111 F I) (nb077_alpha_dummy_113 x) (nb077_wpp_notmem_0278 F I) (nb077_wpp_notmem_0279 x) (TEnvFresh.consFresh (nb077_alpha_dummy_112 F I) (nb077_alpha_dummy_114 x) (nb077_wpp_notmem_0280 F I) (nb077_wpp_notmem_0281 x) (TEnvFresh.consFresh (nb077_alpha_dummy_104 F I) (nb077_alpha_dummy_106 x) (nb077_wpp_notmem_0282 F I) (nb077_wpp_notmem_0283 x) (TEnvFresh.consFresh (nb077_alpha_dummy_103 F I) (nb077_alpha_dummy_105 x) (nb077_wpp_notmem_0284 F I) (nb077_wpp_notmem_0285 x) (TEnvFresh.consFresh (nb077_alpha_dummy_109 F I) (nb077_alpha_dummy_110 x) (nb077_wpp_notmem_0286 F I) (nb077_wpp_notmem_0287 x) (TEnvFresh.consFresh (nb077_alpha_dummy_107 F I) (nb077_alpha_dummy_108 x) (nb077_wpp_notmem_0288 F I) (nb077_wpp_notmem_0289 x) (TEnvFresh.consFresh (nb077_alpha_dummy_061 F I) (nb077_alpha_dummy_064 x) (nb077_wpp_notmem_0290 F I) (nb077_wpp_notmem_0291 x) (TEnvFresh.consFresh (nb077_alpha_dummy_060 F I) (nb077_alpha_dummy_063 x) (nb077_wpp_notmem_0168 F I) (nb077_wpp_notmem_0169 x) (TEnvFresh.consFresh (nb077_alpha_dummy_059 F I) (nb077_alpha_dummy_062 x) (nb077_wpp_notmem_0170 F I) (nb077_wpp_notmem_0171 x) (TEnvFresh.consFresh (nb077_alpha_dummy_065 F I) (nb077_alpha_dummy_066 x) (nb077_wpp_notmem_0172 F I) (nb077_wpp_notmem_0173 x) (TEnvFresh.consFresh (nb077_alpha_dummy_057 F I) (nb077_alpha_dummy_058 x F) (nb077_wpp_notmem_0174 F I) (nb077_wpp_notmem_0175 x F) (TEnvFresh.consFresh (nb077_alpha_dummy_055 F I) (nb077_alpha_dummy_056 x F) (nb077_wpp_notmem_0176 F I) (nb077_wpp_notmem_0177 x F) (TEnvFresh.consFresh (nb077_alpha_dummy_016 F I) (nb077_alpha_dummy_018 x F I) (nb077_wpp_notmem_0030 F I) (nb077_wpp_notmem_0031 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_015 F I) (nb077_alpha_dummy_017 x F I) (nb077_wpp_notmem_0032 F I) (nb077_wpp_notmem_0033 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_013 F I) (nb077_alpha_dummy_014 x F I) (nb077_wpp_notmem_0034 F I) (nb077_wpp_notmem_0035 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_011 F I) (nb077_alpha_dummy_012 x F I) (nb077_wpp_notmem_0036 F I) (nb077_wpp_notmem_0037 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_001 F I) (nb077_alpha_dummy_002 x F I) (nb077_wpp_notmem_0038 F I) (nb077_wpp_notmem_0039 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_004 F I) (nb077_alpha_dummy_006 x F I) (nb077_wpp_notmem_0040 F I) (nb077_wpp_notmem_0041 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_003 F I) (nb077_alpha_dummy_005 x F I) (nb077_wpp_notmem_0042 F I) (nb077_wpp_notmem_0043 x F I) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))))))

noncomputable def nb077_wpp_refl_0016 (x : Var) (F : Class) (I : Class) : TReflOn [((nb077_alpha_dummy_119 F I), (nb077_alpha_dummy_122 x)), ((nb077_alpha_dummy_118 F I), (nb077_alpha_dummy_121 x)), ((nb077_alpha_dummy_117 F I), (nb077_alpha_dummy_120 x)), ((nb077_alpha_dummy_115 F I), (nb077_alpha_dummy_116 x)), ((nb077_alpha_dummy_111 F I), (nb077_alpha_dummy_113 x)), ((nb077_alpha_dummy_112 F I), (nb077_alpha_dummy_114 x)), ((nb077_alpha_dummy_104 F I), (nb077_alpha_dummy_106 x)), ((nb077_alpha_dummy_103 F I), (nb077_alpha_dummy_105 x)), ((nb077_alpha_dummy_109 F I), (nb077_alpha_dummy_110 x)), ((nb077_alpha_dummy_107 F I), (nb077_alpha_dummy_108 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb077_compact_envfresh_0016 x F I)

theorem nb077_wpp_notmem_0292 (F : Class) (I : Class) : (nb077_alpha_dummy_119 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_119, fv_syn_c0] using (nb077_compact_fv_empty_0080 F I)

theorem nb077_wpp_notmem_0293 (x : Var) : (nb077_alpha_dummy_122 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_122, fv_syn_c0] using (nb077_compact_fv_empty_0081 x)

theorem nb077_wpp_notmem_0294 (F : Class) (I : Class) : (nb077_alpha_dummy_118 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_118, fv_syn_c0] using (nb077_compact_fv_empty_0082 F I)

theorem nb077_wpp_notmem_0295 (x : Var) : (nb077_alpha_dummy_121 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_121, fv_syn_c0] using (nb077_compact_fv_empty_0083 x)

theorem nb077_wpp_notmem_0296 (F : Class) (I : Class) : (nb077_alpha_dummy_117 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_117, fv_syn_c0] using (nb077_compact_fv_empty_0084 F I)

theorem nb077_wpp_notmem_0297 (x : Var) : (nb077_alpha_dummy_120 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_120, fv_syn_c0] using (nb077_compact_fv_empty_0085 x)

theorem nb077_wpp_notmem_0298 (F : Class) (I : Class) : (nb077_alpha_dummy_115 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_115, fv_syn_c0] using (nb077_compact_fv_empty_0086 F I)

theorem nb077_wpp_notmem_0299 (x : Var) : (nb077_alpha_dummy_116 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_116, fv_syn_c0] using (nb077_compact_fv_empty_0087 x)

theorem nb077_wpp_notmem_0300 (F : Class) (I : Class) : (nb077_alpha_dummy_111 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_111, fv_syn_c0] using (nb077_compact_fv_empty_0088 F I)

theorem nb077_wpp_notmem_0301 (x : Var) : (nb077_alpha_dummy_113 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_113, fv_syn_c0] using (nb077_compact_fv_empty_0089 x)

theorem nb077_wpp_notmem_0302 (F : Class) (I : Class) : (nb077_alpha_dummy_112 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_112, fv_syn_c0] using (nb077_compact_fv_empty_0090 F I)

theorem nb077_wpp_notmem_0303 (x : Var) : (nb077_alpha_dummy_114 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_114, fv_syn_c0] using (nb077_compact_fv_empty_0091 x)

theorem nb077_wpp_notmem_0304 (F : Class) (I : Class) : (nb077_alpha_dummy_104 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_104, fv_syn_c0] using (nb077_compact_fv_empty_0092 F I)

theorem nb077_wpp_notmem_0305 (x : Var) : (nb077_alpha_dummy_106 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_106, fv_syn_c0] using (nb077_compact_fv_empty_0093 x)

theorem nb077_wpp_notmem_0306 (F : Class) (I : Class) : (nb077_alpha_dummy_103 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_103, fv_syn_c0] using (nb077_compact_fv_empty_0094 F I)

theorem nb077_wpp_notmem_0307 (x : Var) : (nb077_alpha_dummy_105 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_105, fv_syn_c0] using (nb077_compact_fv_empty_0095 x)

theorem nb077_wpp_notmem_0308 (F : Class) (I : Class) : (nb077_alpha_dummy_109 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_109, fv_syn_c0] using (nb077_compact_fv_empty_0096 F I)

theorem nb077_wpp_notmem_0309 (x : Var) : (nb077_alpha_dummy_110 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_110, fv_syn_c0] using (nb077_compact_fv_empty_0097 x)

theorem nb077_wpp_notmem_0310 (F : Class) (I : Class) : (nb077_alpha_dummy_107 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_107, fv_syn_c0] using (nb077_compact_fv_empty_0098 F I)

theorem nb077_wpp_notmem_0311 (x : Var) : (nb077_alpha_dummy_108 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_108, fv_syn_c0] using (nb077_compact_fv_empty_0099 x)

theorem nb077_wpp_notmem_0312 (F : Class) (I : Class) : (nb077_alpha_dummy_061 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_061, fv_syn_c0] using (nb077_compact_fv_empty_0100 F I)

theorem nb077_wpp_notmem_0313 (x : Var) : (nb077_alpha_dummy_064 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_064, fv_syn_c0] using (nb077_compact_fv_empty_0101 x)

theorem nb077_compact_envfresh_0017 (x : Var) (F : Class) (I : Class) : TEnvFresh [((nb077_alpha_dummy_119 F I), (nb077_alpha_dummy_122 x)), ((nb077_alpha_dummy_118 F I), (nb077_alpha_dummy_121 x)), ((nb077_alpha_dummy_117 F I), (nb077_alpha_dummy_120 x)), ((nb077_alpha_dummy_115 F I), (nb077_alpha_dummy_116 x)), ((nb077_alpha_dummy_111 F I), (nb077_alpha_dummy_113 x)), ((nb077_alpha_dummy_112 F I), (nb077_alpha_dummy_114 x)), ((nb077_alpha_dummy_104 F I), (nb077_alpha_dummy_106 x)), ((nb077_alpha_dummy_103 F I), (nb077_alpha_dummy_105 x)), ((nb077_alpha_dummy_109 F I), (nb077_alpha_dummy_110 x)), ((nb077_alpha_dummy_107 F I), (nb077_alpha_dummy_108 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb077_alpha_dummy_119 F I) (nb077_alpha_dummy_122 x) (nb077_wpp_notmem_0292 F I) (nb077_wpp_notmem_0293 x) (TEnvFresh.consFresh (nb077_alpha_dummy_118 F I) (nb077_alpha_dummy_121 x) (nb077_wpp_notmem_0294 F I) (nb077_wpp_notmem_0295 x) (TEnvFresh.consFresh (nb077_alpha_dummy_117 F I) (nb077_alpha_dummy_120 x) (nb077_wpp_notmem_0296 F I) (nb077_wpp_notmem_0297 x) (TEnvFresh.consFresh (nb077_alpha_dummy_115 F I) (nb077_alpha_dummy_116 x) (nb077_wpp_notmem_0298 F I) (nb077_wpp_notmem_0299 x) (TEnvFresh.consFresh (nb077_alpha_dummy_111 F I) (nb077_alpha_dummy_113 x) (nb077_wpp_notmem_0300 F I) (nb077_wpp_notmem_0301 x) (TEnvFresh.consFresh (nb077_alpha_dummy_112 F I) (nb077_alpha_dummy_114 x) (nb077_wpp_notmem_0302 F I) (nb077_wpp_notmem_0303 x) (TEnvFresh.consFresh (nb077_alpha_dummy_104 F I) (nb077_alpha_dummy_106 x) (nb077_wpp_notmem_0304 F I) (nb077_wpp_notmem_0305 x) (TEnvFresh.consFresh (nb077_alpha_dummy_103 F I) (nb077_alpha_dummy_105 x) (nb077_wpp_notmem_0306 F I) (nb077_wpp_notmem_0307 x) (TEnvFresh.consFresh (nb077_alpha_dummy_109 F I) (nb077_alpha_dummy_110 x) (nb077_wpp_notmem_0308 F I) (nb077_wpp_notmem_0309 x) (TEnvFresh.consFresh (nb077_alpha_dummy_107 F I) (nb077_alpha_dummy_108 x) (nb077_wpp_notmem_0310 F I) (nb077_wpp_notmem_0311 x) (TEnvFresh.consFresh (nb077_alpha_dummy_061 F I) (nb077_alpha_dummy_064 x) (nb077_wpp_notmem_0312 F I) (nb077_wpp_notmem_0313 x) (TEnvFresh.consFresh (nb077_alpha_dummy_060 F I) (nb077_alpha_dummy_063 x) (nb077_wpp_notmem_0198 F I) (nb077_wpp_notmem_0199 x) (TEnvFresh.consFresh (nb077_alpha_dummy_059 F I) (nb077_alpha_dummy_062 x) (nb077_wpp_notmem_0200 F I) (nb077_wpp_notmem_0201 x) (TEnvFresh.consFresh (nb077_alpha_dummy_065 F I) (nb077_alpha_dummy_066 x) (nb077_wpp_notmem_0202 F I) (nb077_wpp_notmem_0203 x) (TEnvFresh.consFresh (nb077_alpha_dummy_057 F I) (nb077_alpha_dummy_058 x F) (nb077_wpp_notmem_0204 F I) (nb077_wpp_notmem_0205 x F) (TEnvFresh.consFresh (nb077_alpha_dummy_055 F I) (nb077_alpha_dummy_056 x F) (nb077_wpp_notmem_0206 F I) (nb077_wpp_notmem_0207 x F) (TEnvFresh.consFresh (nb077_alpha_dummy_016 F I) (nb077_alpha_dummy_018 x F I) (nb077_wpp_notmem_0064 F I) (nb077_wpp_notmem_0065 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_015 F I) (nb077_alpha_dummy_017 x F I) (nb077_wpp_notmem_0066 F I) (nb077_wpp_notmem_0067 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_013 F I) (nb077_alpha_dummy_014 x F I) (nb077_wpp_notmem_0068 F I) (nb077_wpp_notmem_0069 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_011 F I) (nb077_alpha_dummy_012 x F I) (nb077_wpp_notmem_0070 F I) (nb077_wpp_notmem_0071 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_001 F I) (nb077_alpha_dummy_002 x F I) (nb077_wpp_notmem_0072 F I) (nb077_wpp_notmem_0073 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_004 F I) (nb077_alpha_dummy_006 x F I) (nb077_wpp_notmem_0074 F I) (nb077_wpp_notmem_0075 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_003 F I) (nb077_alpha_dummy_005 x F I) (nb077_wpp_notmem_0076 F I) (nb077_wpp_notmem_0077 x F I) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))))))))

noncomputable def nb077_wpp_refl_0017 (x : Var) (F : Class) (I : Class) : TReflOn [((nb077_alpha_dummy_119 F I), (nb077_alpha_dummy_122 x)), ((nb077_alpha_dummy_118 F I), (nb077_alpha_dummy_121 x)), ((nb077_alpha_dummy_117 F I), (nb077_alpha_dummy_120 x)), ((nb077_alpha_dummy_115 F I), (nb077_alpha_dummy_116 x)), ((nb077_alpha_dummy_111 F I), (nb077_alpha_dummy_113 x)), ((nb077_alpha_dummy_112 F I), (nb077_alpha_dummy_114 x)), ((nb077_alpha_dummy_104 F I), (nb077_alpha_dummy_106 x)), ((nb077_alpha_dummy_103 F I), (nb077_alpha_dummy_105 x)), ((nb077_alpha_dummy_109 F I), (nb077_alpha_dummy_110 x)), ((nb077_alpha_dummy_107 F I), (nb077_alpha_dummy_108 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb077_compact_envfresh_0017 x F I)

theorem nb077_wpp_notmem_0314 (F : Class) (I : Class) : (nb077_alpha_dummy_115 F I) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_115, fv_syn_cnnc] using (nb077_compact_fv_empty_0086 F I)

theorem nb077_wpp_notmem_0315 (x : Var) : (nb077_alpha_dummy_116 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_116, fv_syn_cnnc] using (nb077_compact_fv_empty_0087 x)

theorem nb077_wpp_notmem_0316 (F : Class) (I : Class) : (nb077_alpha_dummy_111 F I) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_111, fv_syn_cnnc] using (nb077_compact_fv_empty_0088 F I)

theorem nb077_wpp_notmem_0317 (x : Var) : (nb077_alpha_dummy_113 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_113, fv_syn_cnnc] using (nb077_compact_fv_empty_0089 x)

theorem nb077_wpp_notmem_0318 (F : Class) (I : Class) : (nb077_alpha_dummy_112 F I) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_112, fv_syn_cnnc] using (nb077_compact_fv_empty_0090 F I)

theorem nb077_wpp_notmem_0319 (x : Var) : (nb077_alpha_dummy_114 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_114, fv_syn_cnnc] using (nb077_compact_fv_empty_0091 x)

theorem nb077_wpp_notmem_0320 (F : Class) (I : Class) : (nb077_alpha_dummy_104 F I) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_104, fv_syn_cnnc] using (nb077_compact_fv_empty_0092 F I)

theorem nb077_wpp_notmem_0321 (x : Var) : (nb077_alpha_dummy_106 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_106, fv_syn_cnnc] using (nb077_compact_fv_empty_0093 x)

theorem nb077_wpp_notmem_0322 (F : Class) (I : Class) : (nb077_alpha_dummy_103 F I) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_103, fv_syn_cnnc] using (nb077_compact_fv_empty_0094 F I)

theorem nb077_wpp_notmem_0323 (x : Var) : (nb077_alpha_dummy_105 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_105, fv_syn_cnnc] using (nb077_compact_fv_empty_0095 x)

theorem nb077_wpp_notmem_0324 (F : Class) (I : Class) : (nb077_alpha_dummy_109 F I) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_109, fv_syn_cnnc] using (nb077_compact_fv_empty_0096 F I)

theorem nb077_wpp_notmem_0325 (x : Var) : (nb077_alpha_dummy_110 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_110, fv_syn_cnnc] using (nb077_compact_fv_empty_0097 x)

theorem nb077_wpp_notmem_0326 (F : Class) (I : Class) : (nb077_alpha_dummy_107 F I) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_107, fv_syn_cnnc] using (nb077_compact_fv_empty_0098 F I)

theorem nb077_wpp_notmem_0327 (x : Var) : (nb077_alpha_dummy_108 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_108, fv_syn_cnnc] using (nb077_compact_fv_empty_0099 x)

theorem nb077_wpp_notmem_0328 (F : Class) (I : Class) : (nb077_alpha_dummy_061 F I) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_061, fv_syn_cnnc] using (nb077_compact_fv_empty_0100 F I)

theorem nb077_wpp_notmem_0329 (x : Var) : (nb077_alpha_dummy_064 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_064, fv_syn_cnnc] using (nb077_compact_fv_empty_0101 x)

theorem nb077_compact_envfresh_0018 (x : Var) (F : Class) (I : Class) : TEnvFresh [((nb077_alpha_dummy_115 F I), (nb077_alpha_dummy_116 x)), ((nb077_alpha_dummy_111 F I), (nb077_alpha_dummy_113 x)), ((nb077_alpha_dummy_112 F I), (nb077_alpha_dummy_114 x)), ((nb077_alpha_dummy_104 F I), (nb077_alpha_dummy_106 x)), ((nb077_alpha_dummy_103 F I), (nb077_alpha_dummy_105 x)), ((nb077_alpha_dummy_109 F I), (nb077_alpha_dummy_110 x)), ((nb077_alpha_dummy_107 F I), (nb077_alpha_dummy_108 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb077_alpha_dummy_115 F I) (nb077_alpha_dummy_116 x) (nb077_wpp_notmem_0314 F I) (nb077_wpp_notmem_0315 x) (TEnvFresh.consFresh (nb077_alpha_dummy_111 F I) (nb077_alpha_dummy_113 x) (nb077_wpp_notmem_0316 F I) (nb077_wpp_notmem_0317 x) (TEnvFresh.consFresh (nb077_alpha_dummy_112 F I) (nb077_alpha_dummy_114 x) (nb077_wpp_notmem_0318 F I) (nb077_wpp_notmem_0319 x) (TEnvFresh.consFresh (nb077_alpha_dummy_104 F I) (nb077_alpha_dummy_106 x) (nb077_wpp_notmem_0320 F I) (nb077_wpp_notmem_0321 x) (TEnvFresh.consFresh (nb077_alpha_dummy_103 F I) (nb077_alpha_dummy_105 x) (nb077_wpp_notmem_0322 F I) (nb077_wpp_notmem_0323 x) (TEnvFresh.consFresh (nb077_alpha_dummy_109 F I) (nb077_alpha_dummy_110 x) (nb077_wpp_notmem_0324 F I) (nb077_wpp_notmem_0325 x) (TEnvFresh.consFresh (nb077_alpha_dummy_107 F I) (nb077_alpha_dummy_108 x) (nb077_wpp_notmem_0326 F I) (nb077_wpp_notmem_0327 x) (TEnvFresh.consFresh (nb077_alpha_dummy_061 F I) (nb077_alpha_dummy_064 x) (nb077_wpp_notmem_0328 F I) (nb077_wpp_notmem_0329 x) (TEnvFresh.consFresh (nb077_alpha_dummy_060 F I) (nb077_alpha_dummy_063 x) (nb077_wpp_notmem_0222 F I) (nb077_wpp_notmem_0223 x) (TEnvFresh.consFresh (nb077_alpha_dummy_059 F I) (nb077_alpha_dummy_062 x) (nb077_wpp_notmem_0224 F I) (nb077_wpp_notmem_0225 x) (TEnvFresh.consFresh (nb077_alpha_dummy_065 F I) (nb077_alpha_dummy_066 x) (nb077_wpp_notmem_0226 F I) (nb077_wpp_notmem_0227 x) (TEnvFresh.consFresh (nb077_alpha_dummy_057 F I) (nb077_alpha_dummy_058 x F) (nb077_wpp_notmem_0228 F I) (nb077_wpp_notmem_0229 x F) (TEnvFresh.consFresh (nb077_alpha_dummy_055 F I) (nb077_alpha_dummy_056 x F) (nb077_wpp_notmem_0230 F I) (nb077_wpp_notmem_0231 x F) (TEnvFresh.consFresh (nb077_alpha_dummy_016 F I) (nb077_alpha_dummy_018 x F I) (nb077_wpp_notmem_0092 F I) (nb077_wpp_notmem_0093 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_015 F I) (nb077_alpha_dummy_017 x F I) (nb077_wpp_notmem_0094 F I) (nb077_wpp_notmem_0095 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_013 F I) (nb077_alpha_dummy_014 x F I) (nb077_wpp_notmem_0096 F I) (nb077_wpp_notmem_0097 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_011 F I) (nb077_alpha_dummy_012 x F I) (nb077_wpp_notmem_0098 F I) (nb077_wpp_notmem_0099 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_001 F I) (nb077_alpha_dummy_002 x F I) (nb077_wpp_notmem_0100 F I) (nb077_wpp_notmem_0101 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_004 F I) (nb077_alpha_dummy_006 x F I) (nb077_wpp_notmem_0102 F I) (nb077_wpp_notmem_0103 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_003 F I) (nb077_alpha_dummy_005 x F I) (nb077_wpp_notmem_0104 F I) (nb077_wpp_notmem_0105 x F I) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))))))))

noncomputable def nb077_wpp_refl_0018 (x : Var) (F : Class) (I : Class) : TReflOn [((nb077_alpha_dummy_115 F I), (nb077_alpha_dummy_116 x)), ((nb077_alpha_dummy_111 F I), (nb077_alpha_dummy_113 x)), ((nb077_alpha_dummy_112 F I), (nb077_alpha_dummy_114 x)), ((nb077_alpha_dummy_104 F I), (nb077_alpha_dummy_106 x)), ((nb077_alpha_dummy_103 F I), (nb077_alpha_dummy_105 x)), ((nb077_alpha_dummy_109 F I), (nb077_alpha_dummy_110 x)), ((nb077_alpha_dummy_107 F I), (nb077_alpha_dummy_108 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb077_compact_envfresh_0018 x F I)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
