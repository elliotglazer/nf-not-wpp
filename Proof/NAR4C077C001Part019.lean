import NAR4C077C001Part018

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

theorem nb077_wpp_notmem_0479 (x : Var) : (nb077_alpha_dummy_186 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_186, fv_syn_c1c] using (nb077_compact_fv_empty_0153 x)

theorem nb077_compact_fv_empty_0154 (F : Class) (I : Class) : (nb077_alpha_dummy_183 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0480 (F : Class) (I : Class) : (nb077_alpha_dummy_183 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_183, fv_syn_c1c] using (nb077_compact_fv_empty_0154 F I)

theorem nb077_compact_fv_empty_0155 (x : Var) : (nb077_alpha_dummy_185 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0481 (x : Var) : (nb077_alpha_dummy_185 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_185, fv_syn_c1c] using (nb077_compact_fv_empty_0155 x)

theorem nb077_compact_fv_empty_0156 (F : Class) (I : Class) : (nb077_alpha_dummy_189 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0482 (F : Class) (I : Class) : (nb077_alpha_dummy_189 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_189, fv_syn_c1c] using (nb077_compact_fv_empty_0156 F I)

theorem nb077_compact_fv_empty_0157 (x : Var) : (nb077_alpha_dummy_190 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0483 (x : Var) : (nb077_alpha_dummy_190 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_190, fv_syn_c1c] using (nb077_compact_fv_empty_0157 x)

theorem nb077_compact_fv_empty_0158 (F : Class) (I : Class) : (nb077_alpha_dummy_187 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0484 (F : Class) (I : Class) : (nb077_alpha_dummy_187 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_187, fv_syn_c1c] using (nb077_compact_fv_empty_0158 F I)

theorem nb077_compact_fv_empty_0159 (x : Var) : (nb077_alpha_dummy_188 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0485 (x : Var) : (nb077_alpha_dummy_188 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_188, fv_syn_c1c] using (nb077_compact_fv_empty_0159 x)

theorem nb077_compact_fv_empty_0160 (F : Class) (I : Class) : (nb077_alpha_dummy_141 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0486 (F : Class) (I : Class) : (nb077_alpha_dummy_141 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_141, fv_syn_c1c] using (nb077_compact_fv_empty_0160 F I)

theorem nb077_compact_fv_empty_0161 (x : Var) : (nb077_alpha_dummy_144 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0487 (x : Var) : (nb077_alpha_dummy_144 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_144, fv_syn_c1c] using (nb077_compact_fv_empty_0161 x)

theorem nb077_compact_envfresh_0030 (x : Var) (F : Class) (I : Class) : TEnvFresh [((nb077_alpha_dummy_199 F I), (nb077_alpha_dummy_202 x)), ((nb077_alpha_dummy_198 F I), (nb077_alpha_dummy_201 x)), ((nb077_alpha_dummy_197 F I), (nb077_alpha_dummy_200 x)), ((nb077_alpha_dummy_195 F I), (nb077_alpha_dummy_196 x)), ((nb077_alpha_dummy_191 F I), (nb077_alpha_dummy_193 x)), ((nb077_alpha_dummy_192 F I), (nb077_alpha_dummy_194 x)), ((nb077_alpha_dummy_184 F I), (nb077_alpha_dummy_186 x)), ((nb077_alpha_dummy_183 F I), (nb077_alpha_dummy_185 x)), ((nb077_alpha_dummy_189 F I), (nb077_alpha_dummy_190 x)), ((nb077_alpha_dummy_187 F I), (nb077_alpha_dummy_188 x)), ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb077_alpha_dummy_199 F I) (nb077_alpha_dummy_202 x) (nb077_wpp_notmem_0466 F I) (nb077_wpp_notmem_0467 x) (TEnvFresh.consFresh (nb077_alpha_dummy_198 F I) (nb077_alpha_dummy_201 x) (nb077_wpp_notmem_0468 F I) (nb077_wpp_notmem_0469 x) (TEnvFresh.consFresh (nb077_alpha_dummy_197 F I) (nb077_alpha_dummy_200 x) (nb077_wpp_notmem_0470 F I) (nb077_wpp_notmem_0471 x) (TEnvFresh.consFresh (nb077_alpha_dummy_195 F I) (nb077_alpha_dummy_196 x) (nb077_wpp_notmem_0472 F I) (nb077_wpp_notmem_0473 x) (TEnvFresh.consFresh (nb077_alpha_dummy_191 F I) (nb077_alpha_dummy_193 x) (nb077_wpp_notmem_0474 F I) (nb077_wpp_notmem_0475 x) (TEnvFresh.consFresh (nb077_alpha_dummy_192 F I) (nb077_alpha_dummy_194 x) (nb077_wpp_notmem_0476 F I) (nb077_wpp_notmem_0477 x) (TEnvFresh.consFresh (nb077_alpha_dummy_184 F I) (nb077_alpha_dummy_186 x) (nb077_wpp_notmem_0478 F I) (nb077_wpp_notmem_0479 x) (TEnvFresh.consFresh (nb077_alpha_dummy_183 F I) (nb077_alpha_dummy_185 x) (nb077_wpp_notmem_0480 F I) (nb077_wpp_notmem_0481 x) (TEnvFresh.consFresh (nb077_alpha_dummy_189 F I) (nb077_alpha_dummy_190 x) (nb077_wpp_notmem_0482 F I) (nb077_wpp_notmem_0483 x) (TEnvFresh.consFresh (nb077_alpha_dummy_187 F I) (nb077_alpha_dummy_188 x) (nb077_wpp_notmem_0484 F I) (nb077_wpp_notmem_0485 x) (TEnvFresh.consFresh (nb077_alpha_dummy_141 F I) (nb077_alpha_dummy_144 x) (nb077_wpp_notmem_0486 F I) (nb077_wpp_notmem_0487 x) (TEnvFresh.consFresh (nb077_alpha_dummy_140 F I) (nb077_alpha_dummy_143 x) (nb077_wpp_notmem_0380 F I) (nb077_wpp_notmem_0381 x) (TEnvFresh.consFresh (nb077_alpha_dummy_139 F I) (nb077_alpha_dummy_142 x) (nb077_wpp_notmem_0382 F I) (nb077_wpp_notmem_0383 x) (TEnvFresh.consFresh (nb077_alpha_dummy_145 F I) (nb077_alpha_dummy_146 x) (nb077_wpp_notmem_0384 F I) (nb077_wpp_notmem_0385 x) (TEnvFresh.consFresh (nb077_alpha_dummy_061 F I) (nb077_alpha_dummy_064 x) (nb077_wpp_notmem_0290 F I) (nb077_wpp_notmem_0291 x) (TEnvFresh.consFresh (nb077_alpha_dummy_060 F I) (nb077_alpha_dummy_063 x) (nb077_wpp_notmem_0168 F I) (nb077_wpp_notmem_0169 x) (TEnvFresh.consFresh (nb077_alpha_dummy_059 F I) (nb077_alpha_dummy_062 x) (nb077_wpp_notmem_0170 F I) (nb077_wpp_notmem_0171 x) (TEnvFresh.consFresh (nb077_alpha_dummy_065 F I) (nb077_alpha_dummy_066 x) (nb077_wpp_notmem_0172 F I) (nb077_wpp_notmem_0173 x) (TEnvFresh.consFresh (nb077_alpha_dummy_057 F I) (nb077_alpha_dummy_058 x F) (nb077_wpp_notmem_0174 F I) (nb077_wpp_notmem_0175 x F) (TEnvFresh.consFresh (nb077_alpha_dummy_055 F I) (nb077_alpha_dummy_056 x F) (nb077_wpp_notmem_0176 F I) (nb077_wpp_notmem_0177 x F) (TEnvFresh.consFresh (nb077_alpha_dummy_016 F I) (nb077_alpha_dummy_018 x F I) (nb077_wpp_notmem_0030 F I) (nb077_wpp_notmem_0031 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_015 F I) (nb077_alpha_dummy_017 x F I) (nb077_wpp_notmem_0032 F I) (nb077_wpp_notmem_0033 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_013 F I) (nb077_alpha_dummy_014 x F I) (nb077_wpp_notmem_0034 F I) (nb077_wpp_notmem_0035 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_011 F I) (nb077_alpha_dummy_012 x F I) (nb077_wpp_notmem_0036 F I) (nb077_wpp_notmem_0037 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_001 F I) (nb077_alpha_dummy_002 x F I) (nb077_wpp_notmem_0038 F I) (nb077_wpp_notmem_0039 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_004 F I) (nb077_alpha_dummy_006 x F I) (nb077_wpp_notmem_0040 F I) (nb077_wpp_notmem_0041 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_003 F I) (nb077_alpha_dummy_005 x F I) (nb077_wpp_notmem_0042 F I) (nb077_wpp_notmem_0043 x F I) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))))))))))

noncomputable def nb077_wpp_refl_0030 (x : Var) (F : Class) (I : Class) : TReflOn [((nb077_alpha_dummy_199 F I), (nb077_alpha_dummy_202 x)), ((nb077_alpha_dummy_198 F I), (nb077_alpha_dummy_201 x)), ((nb077_alpha_dummy_197 F I), (nb077_alpha_dummy_200 x)), ((nb077_alpha_dummy_195 F I), (nb077_alpha_dummy_196 x)), ((nb077_alpha_dummy_191 F I), (nb077_alpha_dummy_193 x)), ((nb077_alpha_dummy_192 F I), (nb077_alpha_dummy_194 x)), ((nb077_alpha_dummy_184 F I), (nb077_alpha_dummy_186 x)), ((nb077_alpha_dummy_183 F I), (nb077_alpha_dummy_185 x)), ((nb077_alpha_dummy_189 F I), (nb077_alpha_dummy_190 x)), ((nb077_alpha_dummy_187 F I), (nb077_alpha_dummy_188 x)), ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb077_compact_envfresh_0030 x F I)

theorem nb077_wpp_notmem_0488 (F : Class) (I : Class) : (nb077_alpha_dummy_199 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_199, fv_syn_c0] using (nb077_compact_fv_empty_0140 F I)

theorem nb077_wpp_notmem_0489 (x : Var) : (nb077_alpha_dummy_202 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_202, fv_syn_c0] using (nb077_compact_fv_empty_0141 x)

theorem nb077_wpp_notmem_0490 (F : Class) (I : Class) : (nb077_alpha_dummy_198 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_198, fv_syn_c0] using (nb077_compact_fv_empty_0142 F I)

theorem nb077_wpp_notmem_0491 (x : Var) : (nb077_alpha_dummy_201 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_201, fv_syn_c0] using (nb077_compact_fv_empty_0143 x)

theorem nb077_wpp_notmem_0492 (F : Class) (I : Class) : (nb077_alpha_dummy_197 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_197, fv_syn_c0] using (nb077_compact_fv_empty_0144 F I)

theorem nb077_wpp_notmem_0493 (x : Var) : (nb077_alpha_dummy_200 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_200, fv_syn_c0] using (nb077_compact_fv_empty_0145 x)

theorem nb077_wpp_notmem_0494 (F : Class) (I : Class) : (nb077_alpha_dummy_195 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_195, fv_syn_c0] using (nb077_compact_fv_empty_0146 F I)

theorem nb077_wpp_notmem_0495 (x : Var) : (nb077_alpha_dummy_196 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_196, fv_syn_c0] using (nb077_compact_fv_empty_0147 x)

theorem nb077_wpp_notmem_0496 (F : Class) (I : Class) : (nb077_alpha_dummy_191 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_191, fv_syn_c0] using (nb077_compact_fv_empty_0148 F I)

theorem nb077_wpp_notmem_0497 (x : Var) : (nb077_alpha_dummy_193 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_193, fv_syn_c0] using (nb077_compact_fv_empty_0149 x)

theorem nb077_wpp_notmem_0498 (F : Class) (I : Class) : (nb077_alpha_dummy_192 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_192, fv_syn_c0] using (nb077_compact_fv_empty_0150 F I)

theorem nb077_wpp_notmem_0499 (x : Var) : (nb077_alpha_dummy_194 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_194, fv_syn_c0] using (nb077_compact_fv_empty_0151 x)

theorem nb077_wpp_notmem_0500 (F : Class) (I : Class) : (nb077_alpha_dummy_184 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_184, fv_syn_c0] using (nb077_compact_fv_empty_0152 F I)

theorem nb077_wpp_notmem_0501 (x : Var) : (nb077_alpha_dummy_186 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_186, fv_syn_c0] using (nb077_compact_fv_empty_0153 x)

theorem nb077_wpp_notmem_0502 (F : Class) (I : Class) : (nb077_alpha_dummy_183 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_183, fv_syn_c0] using (nb077_compact_fv_empty_0154 F I)

theorem nb077_wpp_notmem_0503 (x : Var) : (nb077_alpha_dummy_185 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_185, fv_syn_c0] using (nb077_compact_fv_empty_0155 x)

theorem nb077_wpp_notmem_0504 (F : Class) (I : Class) : (nb077_alpha_dummy_189 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_189, fv_syn_c0] using (nb077_compact_fv_empty_0156 F I)

theorem nb077_wpp_notmem_0505 (x : Var) : (nb077_alpha_dummy_190 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_190, fv_syn_c0] using (nb077_compact_fv_empty_0157 x)

theorem nb077_wpp_notmem_0506 (F : Class) (I : Class) : (nb077_alpha_dummy_187 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_187, fv_syn_c0] using (nb077_compact_fv_empty_0158 F I)

theorem nb077_wpp_notmem_0507 (x : Var) : (nb077_alpha_dummy_188 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_188, fv_syn_c0] using (nb077_compact_fv_empty_0159 x)

theorem nb077_wpp_notmem_0508 (F : Class) (I : Class) : (nb077_alpha_dummy_141 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_141, fv_syn_c0] using (nb077_compact_fv_empty_0160 F I)

theorem nb077_wpp_notmem_0509 (x : Var) : (nb077_alpha_dummy_144 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_144, fv_syn_c0] using (nb077_compact_fv_empty_0161 x)

theorem nb077_compact_envfresh_0031 (x : Var) (F : Class) (I : Class) : TEnvFresh [((nb077_alpha_dummy_199 F I), (nb077_alpha_dummy_202 x)), ((nb077_alpha_dummy_198 F I), (nb077_alpha_dummy_201 x)), ((nb077_alpha_dummy_197 F I), (nb077_alpha_dummy_200 x)), ((nb077_alpha_dummy_195 F I), (nb077_alpha_dummy_196 x)), ((nb077_alpha_dummy_191 F I), (nb077_alpha_dummy_193 x)), ((nb077_alpha_dummy_192 F I), (nb077_alpha_dummy_194 x)), ((nb077_alpha_dummy_184 F I), (nb077_alpha_dummy_186 x)), ((nb077_alpha_dummy_183 F I), (nb077_alpha_dummy_185 x)), ((nb077_alpha_dummy_189 F I), (nb077_alpha_dummy_190 x)), ((nb077_alpha_dummy_187 F I), (nb077_alpha_dummy_188 x)), ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb077_alpha_dummy_199 F I) (nb077_alpha_dummy_202 x) (nb077_wpp_notmem_0488 F I) (nb077_wpp_notmem_0489 x) (TEnvFresh.consFresh (nb077_alpha_dummy_198 F I) (nb077_alpha_dummy_201 x) (nb077_wpp_notmem_0490 F I) (nb077_wpp_notmem_0491 x) (TEnvFresh.consFresh (nb077_alpha_dummy_197 F I) (nb077_alpha_dummy_200 x) (nb077_wpp_notmem_0492 F I) (nb077_wpp_notmem_0493 x) (TEnvFresh.consFresh (nb077_alpha_dummy_195 F I) (nb077_alpha_dummy_196 x) (nb077_wpp_notmem_0494 F I) (nb077_wpp_notmem_0495 x) (TEnvFresh.consFresh (nb077_alpha_dummy_191 F I) (nb077_alpha_dummy_193 x) (nb077_wpp_notmem_0496 F I) (nb077_wpp_notmem_0497 x) (TEnvFresh.consFresh (nb077_alpha_dummy_192 F I) (nb077_alpha_dummy_194 x) (nb077_wpp_notmem_0498 F I) (nb077_wpp_notmem_0499 x) (TEnvFresh.consFresh (nb077_alpha_dummy_184 F I) (nb077_alpha_dummy_186 x) (nb077_wpp_notmem_0500 F I) (nb077_wpp_notmem_0501 x) (TEnvFresh.consFresh (nb077_alpha_dummy_183 F I) (nb077_alpha_dummy_185 x) (nb077_wpp_notmem_0502 F I) (nb077_wpp_notmem_0503 x) (TEnvFresh.consFresh (nb077_alpha_dummy_189 F I) (nb077_alpha_dummy_190 x) (nb077_wpp_notmem_0504 F I) (nb077_wpp_notmem_0505 x) (TEnvFresh.consFresh (nb077_alpha_dummy_187 F I) (nb077_alpha_dummy_188 x) (nb077_wpp_notmem_0506 F I) (nb077_wpp_notmem_0507 x) (TEnvFresh.consFresh (nb077_alpha_dummy_141 F I) (nb077_alpha_dummy_144 x) (nb077_wpp_notmem_0508 F I) (nb077_wpp_notmem_0509 x) (TEnvFresh.consFresh (nb077_alpha_dummy_140 F I) (nb077_alpha_dummy_143 x) (nb077_wpp_notmem_0406 F I) (nb077_wpp_notmem_0407 x) (TEnvFresh.consFresh (nb077_alpha_dummy_139 F I) (nb077_alpha_dummy_142 x) (nb077_wpp_notmem_0408 F I) (nb077_wpp_notmem_0409 x) (TEnvFresh.consFresh (nb077_alpha_dummy_145 F I) (nb077_alpha_dummy_146 x) (nb077_wpp_notmem_0410 F I) (nb077_wpp_notmem_0411 x) (TEnvFresh.consFresh (nb077_alpha_dummy_061 F I) (nb077_alpha_dummy_064 x) (nb077_wpp_notmem_0312 F I) (nb077_wpp_notmem_0313 x) (TEnvFresh.consFresh (nb077_alpha_dummy_060 F I) (nb077_alpha_dummy_063 x) (nb077_wpp_notmem_0198 F I) (nb077_wpp_notmem_0199 x) (TEnvFresh.consFresh (nb077_alpha_dummy_059 F I) (nb077_alpha_dummy_062 x) (nb077_wpp_notmem_0200 F I) (nb077_wpp_notmem_0201 x) (TEnvFresh.consFresh (nb077_alpha_dummy_065 F I) (nb077_alpha_dummy_066 x) (nb077_wpp_notmem_0202 F I) (nb077_wpp_notmem_0203 x) (TEnvFresh.consFresh (nb077_alpha_dummy_057 F I) (nb077_alpha_dummy_058 x F) (nb077_wpp_notmem_0204 F I) (nb077_wpp_notmem_0205 x F) (TEnvFresh.consFresh (nb077_alpha_dummy_055 F I) (nb077_alpha_dummy_056 x F) (nb077_wpp_notmem_0206 F I) (nb077_wpp_notmem_0207 x F) (TEnvFresh.consFresh (nb077_alpha_dummy_016 F I) (nb077_alpha_dummy_018 x F I) (nb077_wpp_notmem_0064 F I) (nb077_wpp_notmem_0065 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_015 F I) (nb077_alpha_dummy_017 x F I) (nb077_wpp_notmem_0066 F I) (nb077_wpp_notmem_0067 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_013 F I) (nb077_alpha_dummy_014 x F I) (nb077_wpp_notmem_0068 F I) (nb077_wpp_notmem_0069 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_011 F I) (nb077_alpha_dummy_012 x F I) (nb077_wpp_notmem_0070 F I) (nb077_wpp_notmem_0071 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_001 F I) (nb077_alpha_dummy_002 x F I) (nb077_wpp_notmem_0072 F I) (nb077_wpp_notmem_0073 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_004 F I) (nb077_alpha_dummy_006 x F I) (nb077_wpp_notmem_0074 F I) (nb077_wpp_notmem_0075 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_003 F I) (nb077_alpha_dummy_005 x F I) (nb077_wpp_notmem_0076 F I) (nb077_wpp_notmem_0077 x F I) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))))))))))))

noncomputable def nb077_wpp_refl_0031 (x : Var) (F : Class) (I : Class) : TReflOn [((nb077_alpha_dummy_199 F I), (nb077_alpha_dummy_202 x)), ((nb077_alpha_dummy_198 F I), (nb077_alpha_dummy_201 x)), ((nb077_alpha_dummy_197 F I), (nb077_alpha_dummy_200 x)), ((nb077_alpha_dummy_195 F I), (nb077_alpha_dummy_196 x)), ((nb077_alpha_dummy_191 F I), (nb077_alpha_dummy_193 x)), ((nb077_alpha_dummy_192 F I), (nb077_alpha_dummy_194 x)), ((nb077_alpha_dummy_184 F I), (nb077_alpha_dummy_186 x)), ((nb077_alpha_dummy_183 F I), (nb077_alpha_dummy_185 x)), ((nb077_alpha_dummy_189 F I), (nb077_alpha_dummy_190 x)), ((nb077_alpha_dummy_187 F I), (nb077_alpha_dummy_188 x)), ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb077_compact_envfresh_0031 x F I)

theorem nb077_wpp_notmem_0510 (F : Class) (I : Class) : (nb077_alpha_dummy_195 F I) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_195, fv_syn_cnnc] using (nb077_compact_fv_empty_0146 F I)

theorem nb077_wpp_notmem_0511 (x : Var) : (nb077_alpha_dummy_196 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_196, fv_syn_cnnc] using (nb077_compact_fv_empty_0147 x)

theorem nb077_wpp_notmem_0512 (F : Class) (I : Class) : (nb077_alpha_dummy_191 F I) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_191, fv_syn_cnnc] using (nb077_compact_fv_empty_0148 F I)

theorem nb077_wpp_notmem_0513 (x : Var) : (nb077_alpha_dummy_193 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_193, fv_syn_cnnc] using (nb077_compact_fv_empty_0149 x)

theorem nb077_wpp_notmem_0514 (F : Class) (I : Class) : (nb077_alpha_dummy_192 F I) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_192, fv_syn_cnnc] using (nb077_compact_fv_empty_0150 F I)

theorem nb077_wpp_notmem_0515 (x : Var) : (nb077_alpha_dummy_194 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_194, fv_syn_cnnc] using (nb077_compact_fv_empty_0151 x)

theorem nb077_wpp_notmem_0516 (F : Class) (I : Class) : (nb077_alpha_dummy_184 F I) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_184, fv_syn_cnnc] using (nb077_compact_fv_empty_0152 F I)

theorem nb077_wpp_notmem_0517 (x : Var) : (nb077_alpha_dummy_186 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_186, fv_syn_cnnc] using (nb077_compact_fv_empty_0153 x)

theorem nb077_wpp_notmem_0518 (F : Class) (I : Class) : (nb077_alpha_dummy_183 F I) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_183, fv_syn_cnnc] using (nb077_compact_fv_empty_0154 F I)

theorem nb077_wpp_notmem_0519 (x : Var) : (nb077_alpha_dummy_185 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_185, fv_syn_cnnc] using (nb077_compact_fv_empty_0155 x)

theorem nb077_wpp_notmem_0520 (F : Class) (I : Class) : (nb077_alpha_dummy_189 F I) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_189, fv_syn_cnnc] using (nb077_compact_fv_empty_0156 F I)

theorem nb077_wpp_notmem_0521 (x : Var) : (nb077_alpha_dummy_190 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_190, fv_syn_cnnc] using (nb077_compact_fv_empty_0157 x)

theorem nb077_wpp_notmem_0522 (F : Class) (I : Class) : (nb077_alpha_dummy_187 F I) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_187, fv_syn_cnnc] using (nb077_compact_fv_empty_0158 F I)

theorem nb077_wpp_notmem_0523 (x : Var) : (nb077_alpha_dummy_188 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_188, fv_syn_cnnc] using (nb077_compact_fv_empty_0159 x)

theorem nb077_wpp_notmem_0524 (F : Class) (I : Class) : (nb077_alpha_dummy_141 F I) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_141, fv_syn_cnnc] using (nb077_compact_fv_empty_0160 F I)

theorem nb077_wpp_notmem_0525 (x : Var) : (nb077_alpha_dummy_144 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_144, fv_syn_cnnc] using (nb077_compact_fv_empty_0161 x)

theorem nb077_compact_envfresh_0032 (x : Var) (F : Class) (I : Class) : TEnvFresh [((nb077_alpha_dummy_195 F I), (nb077_alpha_dummy_196 x)), ((nb077_alpha_dummy_191 F I), (nb077_alpha_dummy_193 x)), ((nb077_alpha_dummy_192 F I), (nb077_alpha_dummy_194 x)), ((nb077_alpha_dummy_184 F I), (nb077_alpha_dummy_186 x)), ((nb077_alpha_dummy_183 F I), (nb077_alpha_dummy_185 x)), ((nb077_alpha_dummy_189 F I), (nb077_alpha_dummy_190 x)), ((nb077_alpha_dummy_187 F I), (nb077_alpha_dummy_188 x)), ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb077_alpha_dummy_195 F I) (nb077_alpha_dummy_196 x) (nb077_wpp_notmem_0510 F I) (nb077_wpp_notmem_0511 x) (TEnvFresh.consFresh (nb077_alpha_dummy_191 F I) (nb077_alpha_dummy_193 x) (nb077_wpp_notmem_0512 F I) (nb077_wpp_notmem_0513 x) (TEnvFresh.consFresh (nb077_alpha_dummy_192 F I) (nb077_alpha_dummy_194 x) (nb077_wpp_notmem_0514 F I) (nb077_wpp_notmem_0515 x) (TEnvFresh.consFresh (nb077_alpha_dummy_184 F I) (nb077_alpha_dummy_186 x) (nb077_wpp_notmem_0516 F I) (nb077_wpp_notmem_0517 x) (TEnvFresh.consFresh (nb077_alpha_dummy_183 F I) (nb077_alpha_dummy_185 x) (nb077_wpp_notmem_0518 F I) (nb077_wpp_notmem_0519 x) (TEnvFresh.consFresh (nb077_alpha_dummy_189 F I) (nb077_alpha_dummy_190 x) (nb077_wpp_notmem_0520 F I) (nb077_wpp_notmem_0521 x) (TEnvFresh.consFresh (nb077_alpha_dummy_187 F I) (nb077_alpha_dummy_188 x) (nb077_wpp_notmem_0522 F I) (nb077_wpp_notmem_0523 x) (TEnvFresh.consFresh (nb077_alpha_dummy_141 F I) (nb077_alpha_dummy_144 x) (nb077_wpp_notmem_0524 F I) (nb077_wpp_notmem_0525 x) (TEnvFresh.consFresh (nb077_alpha_dummy_140 F I) (nb077_alpha_dummy_143 x) (nb077_wpp_notmem_0426 F I) (nb077_wpp_notmem_0427 x) (TEnvFresh.consFresh (nb077_alpha_dummy_139 F I) (nb077_alpha_dummy_142 x) (nb077_wpp_notmem_0428 F I) (nb077_wpp_notmem_0429 x) (TEnvFresh.consFresh (nb077_alpha_dummy_145 F I) (nb077_alpha_dummy_146 x) (nb077_wpp_notmem_0430 F I) (nb077_wpp_notmem_0431 x) (TEnvFresh.consFresh (nb077_alpha_dummy_061 F I) (nb077_alpha_dummy_064 x) (nb077_wpp_notmem_0328 F I) (nb077_wpp_notmem_0329 x) (TEnvFresh.consFresh (nb077_alpha_dummy_060 F I) (nb077_alpha_dummy_063 x) (nb077_wpp_notmem_0222 F I) (nb077_wpp_notmem_0223 x) (TEnvFresh.consFresh (nb077_alpha_dummy_059 F I) (nb077_alpha_dummy_062 x) (nb077_wpp_notmem_0224 F I) (nb077_wpp_notmem_0225 x) (TEnvFresh.consFresh (nb077_alpha_dummy_065 F I) (nb077_alpha_dummy_066 x) (nb077_wpp_notmem_0226 F I) (nb077_wpp_notmem_0227 x) (TEnvFresh.consFresh (nb077_alpha_dummy_057 F I) (nb077_alpha_dummy_058 x F) (nb077_wpp_notmem_0228 F I) (nb077_wpp_notmem_0229 x F) (TEnvFresh.consFresh (nb077_alpha_dummy_055 F I) (nb077_alpha_dummy_056 x F) (nb077_wpp_notmem_0230 F I) (nb077_wpp_notmem_0231 x F) (TEnvFresh.consFresh (nb077_alpha_dummy_016 F I) (nb077_alpha_dummy_018 x F I) (nb077_wpp_notmem_0092 F I) (nb077_wpp_notmem_0093 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_015 F I) (nb077_alpha_dummy_017 x F I) (nb077_wpp_notmem_0094 F I) (nb077_wpp_notmem_0095 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_013 F I) (nb077_alpha_dummy_014 x F I) (nb077_wpp_notmem_0096 F I) (nb077_wpp_notmem_0097 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_011 F I) (nb077_alpha_dummy_012 x F I) (nb077_wpp_notmem_0098 F I) (nb077_wpp_notmem_0099 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_001 F I) (nb077_alpha_dummy_002 x F I) (nb077_wpp_notmem_0100 F I) (nb077_wpp_notmem_0101 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_004 F I) (nb077_alpha_dummy_006 x F I) (nb077_wpp_notmem_0102 F I) (nb077_wpp_notmem_0103 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_003 F I) (nb077_alpha_dummy_005 x F I) (nb077_wpp_notmem_0104 F I) (nb077_wpp_notmem_0105 x F I) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))))))))))))

noncomputable def nb077_wpp_refl_0032 (x : Var) (F : Class) (I : Class) : TReflOn [((nb077_alpha_dummy_195 F I), (nb077_alpha_dummy_196 x)), ((nb077_alpha_dummy_191 F I), (nb077_alpha_dummy_193 x)), ((nb077_alpha_dummy_192 F I), (nb077_alpha_dummy_194 x)), ((nb077_alpha_dummy_184 F I), (nb077_alpha_dummy_186 x)), ((nb077_alpha_dummy_183 F I), (nb077_alpha_dummy_185 x)), ((nb077_alpha_dummy_189 F I), (nb077_alpha_dummy_190 x)), ((nb077_alpha_dummy_187 F I), (nb077_alpha_dummy_188 x)), ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb077_compact_envfresh_0032 x F I)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
