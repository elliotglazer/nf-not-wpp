import NAR4C067C001Part015

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

theorem nb067_compact_fv_empty_0133 (f : Var) : (nb067_alpha_dummy_182 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0433 (f : Var) : (nb067_alpha_dummy_182 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_182, fv_syn_c1c] using (nb067_compact_fv_empty_0133 f)

theorem nb067_compact_fv_empty_0134 : (nb067_alpha_dummy_177) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0434 : (nb067_alpha_dummy_177) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_177, fv_syn_c1c] using (nb067_compact_fv_empty_0134)

theorem nb067_compact_fv_empty_0135 (f : Var) : (nb067_alpha_dummy_179 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0435 (f : Var) : (nb067_alpha_dummy_179 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_179, fv_syn_c1c] using (nb067_compact_fv_empty_0135 f)

theorem nb067_compact_fv_empty_0136 : (nb067_alpha_dummy_178) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0436 : (nb067_alpha_dummy_178) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_178, fv_syn_c1c] using (nb067_compact_fv_empty_0136)

theorem nb067_compact_fv_empty_0137 (f : Var) : (nb067_alpha_dummy_180 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0437 (f : Var) : (nb067_alpha_dummy_180 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_180, fv_syn_c1c] using (nb067_compact_fv_empty_0137 f)

theorem nb067_compact_fv_empty_0138 : (nb067_alpha_dummy_170) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0438 : (nb067_alpha_dummy_170) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_170, fv_syn_c1c] using (nb067_compact_fv_empty_0138)

theorem nb067_compact_fv_empty_0139 (f : Var) : (nb067_alpha_dummy_172 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0439 (f : Var) : (nb067_alpha_dummy_172 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_172, fv_syn_c1c] using (nb067_compact_fv_empty_0139 f)

theorem nb067_compact_fv_empty_0140 : (nb067_alpha_dummy_169) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0440 : (nb067_alpha_dummy_169) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_169, fv_syn_c1c] using (nb067_compact_fv_empty_0140)

theorem nb067_compact_fv_empty_0141 (f : Var) : (nb067_alpha_dummy_171 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0441 (f : Var) : (nb067_alpha_dummy_171 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_171, fv_syn_c1c] using (nb067_compact_fv_empty_0141 f)

theorem nb067_compact_fv_empty_0142 : (nb067_alpha_dummy_175) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0442 : (nb067_alpha_dummy_175) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_175, fv_syn_c1c] using (nb067_compact_fv_empty_0142)

theorem nb067_compact_fv_empty_0143 (f : Var) : (nb067_alpha_dummy_176 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0443 (f : Var) : (nb067_alpha_dummy_176 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_176, fv_syn_c1c] using (nb067_compact_fv_empty_0143 f)

theorem nb067_compact_fv_empty_0144 : (nb067_alpha_dummy_173) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0444 : (nb067_alpha_dummy_173) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_173, fv_syn_c1c] using (nb067_compact_fv_empty_0144)

theorem nb067_compact_fv_empty_0145 (f : Var) : (nb067_alpha_dummy_174 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0445 (f : Var) : (nb067_alpha_dummy_174 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_174, fv_syn_c1c] using (nb067_compact_fv_empty_0145 f)

theorem nb067_compact_fv_empty_0146 : (nb067_alpha_dummy_164) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0446 : (nb067_alpha_dummy_164) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_164, fv_syn_c1c] using (nb067_compact_fv_empty_0146)

theorem nb067_compact_fv_empty_0147 (f : Var) : (nb067_alpha_dummy_166 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0447 (f : Var) : (nb067_alpha_dummy_166 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_166, fv_syn_c1c] using (nb067_compact_fv_empty_0147 f)

theorem nb067_compact_fv_empty_0148 : (nb067_alpha_dummy_163) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0448 : (nb067_alpha_dummy_163) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_163, fv_syn_c1c] using (nb067_compact_fv_empty_0148)

theorem nb067_compact_fv_empty_0149 (f : Var) : (nb067_alpha_dummy_165 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0449 (f : Var) : (nb067_alpha_dummy_165 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_165, fv_syn_c1c] using (nb067_compact_fv_empty_0149 f)

theorem nb067_compact_fv_empty_0150 : (nb067_alpha_dummy_167) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0450 : (nb067_alpha_dummy_167) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_167, fv_syn_c1c] using (nb067_compact_fv_empty_0150)

theorem nb067_compact_fv_empty_0151 (f : Var) : (nb067_alpha_dummy_168 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0451 (f : Var) : (nb067_alpha_dummy_168 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_168, fv_syn_c1c] using (nb067_compact_fv_empty_0151 f)

theorem nb067_compact_envfresh_0029 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb067_alpha_dummy_185), (nb067_alpha_dummy_188 f)), ((nb067_alpha_dummy_184), (nb067_alpha_dummy_187 f)), ((nb067_alpha_dummy_183), (nb067_alpha_dummy_186 f)), ((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)), ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)), ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)), ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)), ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)), ((nb067_alpha_dummy_175), (nb067_alpha_dummy_176 f)), ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)), ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)), ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)), ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb067_alpha_dummy_185) (nb067_alpha_dummy_188 f) (nb067_wpp_notmem_0426) (nb067_wpp_notmem_0427 f) (TEnvFresh.consFresh (nb067_alpha_dummy_184) (nb067_alpha_dummy_187 f) (nb067_wpp_notmem_0428) (nb067_wpp_notmem_0429 f) (TEnvFresh.consFresh (nb067_alpha_dummy_183) (nb067_alpha_dummy_186 f) (nb067_wpp_notmem_0430) (nb067_wpp_notmem_0431 f) (TEnvFresh.consFresh (nb067_alpha_dummy_181) (nb067_alpha_dummy_182 f) (nb067_wpp_notmem_0432) (nb067_wpp_notmem_0433 f) (TEnvFresh.consFresh (nb067_alpha_dummy_177) (nb067_alpha_dummy_179 f) (nb067_wpp_notmem_0434) (nb067_wpp_notmem_0435 f) (TEnvFresh.consFresh (nb067_alpha_dummy_178) (nb067_alpha_dummy_180 f) (nb067_wpp_notmem_0436) (nb067_wpp_notmem_0437 f) (TEnvFresh.consFresh (nb067_alpha_dummy_170) (nb067_alpha_dummy_172 f) (nb067_wpp_notmem_0438) (nb067_wpp_notmem_0439 f) (TEnvFresh.consFresh (nb067_alpha_dummy_169) (nb067_alpha_dummy_171 f) (nb067_wpp_notmem_0440) (nb067_wpp_notmem_0441 f) (TEnvFresh.consFresh (nb067_alpha_dummy_175) (nb067_alpha_dummy_176 f) (nb067_wpp_notmem_0442) (nb067_wpp_notmem_0443 f) (TEnvFresh.consFresh (nb067_alpha_dummy_173) (nb067_alpha_dummy_174 f) (nb067_wpp_notmem_0444) (nb067_wpp_notmem_0445 f) (TEnvFresh.consFresh (nb067_alpha_dummy_164) (nb067_alpha_dummy_166 f) (nb067_wpp_notmem_0446) (nb067_wpp_notmem_0447 f) (TEnvFresh.consFresh (nb067_alpha_dummy_163) (nb067_alpha_dummy_165 f) (nb067_wpp_notmem_0448) (nb067_wpp_notmem_0449 f) (TEnvFresh.consFresh (nb067_alpha_dummy_167) (nb067_alpha_dummy_168 f) (nb067_wpp_notmem_0450) (nb067_wpp_notmem_0451 f) (TEnvFresh.consFresh (nb067_alpha_dummy_085) (nb067_alpha_dummy_088 f) (nb067_wpp_notmem_0356) (nb067_wpp_notmem_0357 f) (TEnvFresh.consFresh (nb067_alpha_dummy_084) (nb067_alpha_dummy_087 f) (nb067_wpp_notmem_0226) (nb067_wpp_notmem_0227 f) (TEnvFresh.consFresh (nb067_alpha_dummy_083) (nb067_alpha_dummy_086 f) (nb067_wpp_notmem_0228) (nb067_wpp_notmem_0229 f) (TEnvFresh.consFresh (nb067_alpha_dummy_089) (nb067_alpha_dummy_090 f) (nb067_wpp_notmem_0230) (nb067_wpp_notmem_0231 f) (TEnvFresh.consFresh (nb067_alpha_dummy_081) (nb067_alpha_dummy_082 f) (nb067_wpp_notmem_0232) (nb067_wpp_notmem_0233 f) (TEnvFresh.consFresh (nb067_alpha_dummy_079) (nb067_alpha_dummy_080 f) (nb067_wpp_notmem_0234) (nb067_wpp_notmem_0235 f) (TEnvFresh.consFresh (nb067_alpha_dummy_000) f (nb067_wpp_notmem_0236) (nb067_wpp_notmem_0237 f) (TEnvFresh.consFresh (nb067_alpha_dummy_003) (nb067_alpha_dummy_004 x y f) (nb067_wpp_notmem_0028) (nb067_wpp_notmem_0029 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_002) y (nb067_wpp_notmem_0030) (nb067_wpp_notmem_0031 y) (TEnvFresh.consFresh (nb067_alpha_dummy_001) x (nb067_wpp_notmem_0032) (nb067_wpp_notmem_0033 x) (TEnvFresh.consFresh (nb067_alpha_dummy_005) (nb067_alpha_dummy_006 x y f) (nb067_wpp_notmem_0034) (nb067_wpp_notmem_0035 x y f) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))))))

noncomputable def nb067_wpp_refl_0029 (x : Var) (y : Var) (f : Var) : TReflOn [((nb067_alpha_dummy_185), (nb067_alpha_dummy_188 f)), ((nb067_alpha_dummy_184), (nb067_alpha_dummy_187 f)), ((nb067_alpha_dummy_183), (nb067_alpha_dummy_186 f)), ((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)), ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)), ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)), ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)), ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)), ((nb067_alpha_dummy_175), (nb067_alpha_dummy_176 f)), ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)), ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)), ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)), ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb067_compact_envfresh_0029 x y f)

theorem nb067_wpp_notmem_0452 : (nb067_alpha_dummy_185) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_185, fv_syn_c0] using (nb067_compact_fv_empty_0126)

theorem nb067_wpp_notmem_0453 (f : Var) : (nb067_alpha_dummy_188 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_188, fv_syn_c0] using (nb067_compact_fv_empty_0127 f)

theorem nb067_wpp_notmem_0454 : (nb067_alpha_dummy_184) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_184, fv_syn_c0] using (nb067_compact_fv_empty_0128)

theorem nb067_wpp_notmem_0455 (f : Var) : (nb067_alpha_dummy_187 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_187, fv_syn_c0] using (nb067_compact_fv_empty_0129 f)

theorem nb067_wpp_notmem_0456 : (nb067_alpha_dummy_183) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_183, fv_syn_c0] using (nb067_compact_fv_empty_0130)

theorem nb067_wpp_notmem_0457 (f : Var) : (nb067_alpha_dummy_186 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_186, fv_syn_c0] using (nb067_compact_fv_empty_0131 f)

theorem nb067_wpp_notmem_0458 : (nb067_alpha_dummy_181) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_181, fv_syn_c0] using (nb067_compact_fv_empty_0132)

theorem nb067_wpp_notmem_0459 (f : Var) : (nb067_alpha_dummy_182 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_182, fv_syn_c0] using (nb067_compact_fv_empty_0133 f)

theorem nb067_wpp_notmem_0460 : (nb067_alpha_dummy_177) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_177, fv_syn_c0] using (nb067_compact_fv_empty_0134)

theorem nb067_wpp_notmem_0461 (f : Var) : (nb067_alpha_dummy_179 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_179, fv_syn_c0] using (nb067_compact_fv_empty_0135 f)

theorem nb067_wpp_notmem_0462 : (nb067_alpha_dummy_178) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_178, fv_syn_c0] using (nb067_compact_fv_empty_0136)

theorem nb067_wpp_notmem_0463 (f : Var) : (nb067_alpha_dummy_180 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_180, fv_syn_c0] using (nb067_compact_fv_empty_0137 f)

theorem nb067_wpp_notmem_0464 : (nb067_alpha_dummy_170) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_170, fv_syn_c0] using (nb067_compact_fv_empty_0138)

theorem nb067_wpp_notmem_0465 (f : Var) : (nb067_alpha_dummy_172 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_172, fv_syn_c0] using (nb067_compact_fv_empty_0139 f)

theorem nb067_wpp_notmem_0466 : (nb067_alpha_dummy_169) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_169, fv_syn_c0] using (nb067_compact_fv_empty_0140)

theorem nb067_wpp_notmem_0467 (f : Var) : (nb067_alpha_dummy_171 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_171, fv_syn_c0] using (nb067_compact_fv_empty_0141 f)

theorem nb067_wpp_notmem_0468 : (nb067_alpha_dummy_175) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_175, fv_syn_c0] using (nb067_compact_fv_empty_0142)

theorem nb067_wpp_notmem_0469 (f : Var) : (nb067_alpha_dummy_176 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_176, fv_syn_c0] using (nb067_compact_fv_empty_0143 f)

theorem nb067_wpp_notmem_0470 : (nb067_alpha_dummy_173) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_173, fv_syn_c0] using (nb067_compact_fv_empty_0144)

theorem nb067_wpp_notmem_0471 (f : Var) : (nb067_alpha_dummy_174 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_174, fv_syn_c0] using (nb067_compact_fv_empty_0145 f)

theorem nb067_wpp_notmem_0472 : (nb067_alpha_dummy_164) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_164, fv_syn_c0] using (nb067_compact_fv_empty_0146)

theorem nb067_wpp_notmem_0473 (f : Var) : (nb067_alpha_dummy_166 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_166, fv_syn_c0] using (nb067_compact_fv_empty_0147 f)

theorem nb067_wpp_notmem_0474 : (nb067_alpha_dummy_163) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_163, fv_syn_c0] using (nb067_compact_fv_empty_0148)

theorem nb067_wpp_notmem_0475 (f : Var) : (nb067_alpha_dummy_165 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_165, fv_syn_c0] using (nb067_compact_fv_empty_0149 f)

theorem nb067_wpp_notmem_0476 : (nb067_alpha_dummy_167) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_167, fv_syn_c0] using (nb067_compact_fv_empty_0150)

theorem nb067_wpp_notmem_0477 (f : Var) : (nb067_alpha_dummy_168 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_168, fv_syn_c0] using (nb067_compact_fv_empty_0151 f)

theorem nb067_compact_envfresh_0030 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb067_alpha_dummy_185), (nb067_alpha_dummy_188 f)), ((nb067_alpha_dummy_184), (nb067_alpha_dummy_187 f)), ((nb067_alpha_dummy_183), (nb067_alpha_dummy_186 f)), ((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)), ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)), ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)), ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)), ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)), ((nb067_alpha_dummy_175), (nb067_alpha_dummy_176 f)), ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)), ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)), ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)), ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb067_alpha_dummy_185) (nb067_alpha_dummy_188 f) (nb067_wpp_notmem_0452) (nb067_wpp_notmem_0453 f) (TEnvFresh.consFresh (nb067_alpha_dummy_184) (nb067_alpha_dummy_187 f) (nb067_wpp_notmem_0454) (nb067_wpp_notmem_0455 f) (TEnvFresh.consFresh (nb067_alpha_dummy_183) (nb067_alpha_dummy_186 f) (nb067_wpp_notmem_0456) (nb067_wpp_notmem_0457 f) (TEnvFresh.consFresh (nb067_alpha_dummy_181) (nb067_alpha_dummy_182 f) (nb067_wpp_notmem_0458) (nb067_wpp_notmem_0459 f) (TEnvFresh.consFresh (nb067_alpha_dummy_177) (nb067_alpha_dummy_179 f) (nb067_wpp_notmem_0460) (nb067_wpp_notmem_0461 f) (TEnvFresh.consFresh (nb067_alpha_dummy_178) (nb067_alpha_dummy_180 f) (nb067_wpp_notmem_0462) (nb067_wpp_notmem_0463 f) (TEnvFresh.consFresh (nb067_alpha_dummy_170) (nb067_alpha_dummy_172 f) (nb067_wpp_notmem_0464) (nb067_wpp_notmem_0465 f) (TEnvFresh.consFresh (nb067_alpha_dummy_169) (nb067_alpha_dummy_171 f) (nb067_wpp_notmem_0466) (nb067_wpp_notmem_0467 f) (TEnvFresh.consFresh (nb067_alpha_dummy_175) (nb067_alpha_dummy_176 f) (nb067_wpp_notmem_0468) (nb067_wpp_notmem_0469 f) (TEnvFresh.consFresh (nb067_alpha_dummy_173) (nb067_alpha_dummy_174 f) (nb067_wpp_notmem_0470) (nb067_wpp_notmem_0471 f) (TEnvFresh.consFresh (nb067_alpha_dummy_164) (nb067_alpha_dummy_166 f) (nb067_wpp_notmem_0472) (nb067_wpp_notmem_0473 f) (TEnvFresh.consFresh (nb067_alpha_dummy_163) (nb067_alpha_dummy_165 f) (nb067_wpp_notmem_0474) (nb067_wpp_notmem_0475 f) (TEnvFresh.consFresh (nb067_alpha_dummy_167) (nb067_alpha_dummy_168 f) (nb067_wpp_notmem_0476) (nb067_wpp_notmem_0477 f) (TEnvFresh.consFresh (nb067_alpha_dummy_085) (nb067_alpha_dummy_088 f) (nb067_wpp_notmem_0378) (nb067_wpp_notmem_0379 f) (TEnvFresh.consFresh (nb067_alpha_dummy_084) (nb067_alpha_dummy_087 f) (nb067_wpp_notmem_0258) (nb067_wpp_notmem_0259 f) (TEnvFresh.consFresh (nb067_alpha_dummy_083) (nb067_alpha_dummy_086 f) (nb067_wpp_notmem_0260) (nb067_wpp_notmem_0261 f) (TEnvFresh.consFresh (nb067_alpha_dummy_089) (nb067_alpha_dummy_090 f) (nb067_wpp_notmem_0262) (nb067_wpp_notmem_0263 f) (TEnvFresh.consFresh (nb067_alpha_dummy_081) (nb067_alpha_dummy_082 f) (nb067_wpp_notmem_0264) (nb067_wpp_notmem_0265 f) (TEnvFresh.consFresh (nb067_alpha_dummy_079) (nb067_alpha_dummy_080 f) (nb067_wpp_notmem_0266) (nb067_wpp_notmem_0267 f) (TEnvFresh.consFresh (nb067_alpha_dummy_000) f (nb067_wpp_notmem_0268) (nb067_wpp_notmem_0269 f) (TEnvFresh.consFresh (nb067_alpha_dummy_003) (nb067_alpha_dummy_004 x y f) (nb067_wpp_notmem_0064) (nb067_wpp_notmem_0065 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_002) y (nb067_wpp_notmem_0066) (nb067_wpp_notmem_0067 y) (TEnvFresh.consFresh (nb067_alpha_dummy_001) x (nb067_wpp_notmem_0068) (nb067_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb067_alpha_dummy_005) (nb067_alpha_dummy_006 x y f) (nb067_wpp_notmem_0070) (nb067_wpp_notmem_0071 x y f) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))))))))

noncomputable def nb067_wpp_refl_0030 (x : Var) (y : Var) (f : Var) : TReflOn [((nb067_alpha_dummy_185), (nb067_alpha_dummy_188 f)), ((nb067_alpha_dummy_184), (nb067_alpha_dummy_187 f)), ((nb067_alpha_dummy_183), (nb067_alpha_dummy_186 f)), ((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)), ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)), ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)), ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)), ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)), ((nb067_alpha_dummy_175), (nb067_alpha_dummy_176 f)), ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)), ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)), ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)), ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb067_compact_envfresh_0030 x y f)

noncomputable def nb067_split_alpha_0020 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb067_alpha_dummy_185), (nb067_alpha_dummy_188 f)), ((nb067_alpha_dummy_184), (nb067_alpha_dummy_187 f)), ((nb067_alpha_dummy_183), (nb067_alpha_dummy_186 f)), ((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)), ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)), ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)), ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)), ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)), ((nb067_alpha_dummy_175), (nb067_alpha_dummy_176 f)), ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)), ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)), ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)), ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_184)) (Class.cv (nb067_alpha_dummy_185))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_183)) (syn_cun (Class.cv (nb067_alpha_dummy_184)) (Class.cv (nb067_alpha_dummy_185)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_187 f)) (Class.cv (nb067_alpha_dummy_188 f))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_186 f)) (syn_cun (Class.cv (nb067_alpha_dummy_187 f)) (Class.cv (nb067_alpha_dummy_188 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0190) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0191 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0188) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0189 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0194) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0195 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0192) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0193 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0190) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0191 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0188) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0189 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0194) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0195 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0192) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0193 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_185), (nb067_alpha_dummy_188 f)), ((nb067_alpha_dummy_184), (nb067_alpha_dummy_187 f)), ((nb067_alpha_dummy_183), (nb067_alpha_dummy_186 f)), ((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)), ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)), ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)), ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)), ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)), ((nb067_alpha_dummy_175), (nb067_alpha_dummy_176 f)), ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)), ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)), ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)), ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_c0) (nb067_wpp_refl_0030 x y f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0198) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0199 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0196) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0197 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0198) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0199 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0196) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0197 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_177))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_179 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0202) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0203 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0200) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0201 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0202) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0203 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0200) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0201 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb067_wpp_notmem_0478 : (nb067_alpha_dummy_181) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_181, fv_syn_cnnc] using (nb067_compact_fv_empty_0132)

theorem nb067_wpp_notmem_0479 (f : Var) : (nb067_alpha_dummy_182 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_182, fv_syn_cnnc] using (nb067_compact_fv_empty_0133 f)

theorem nb067_wpp_notmem_0480 : (nb067_alpha_dummy_177) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_177, fv_syn_cnnc] using (nb067_compact_fv_empty_0134)

theorem nb067_wpp_notmem_0481 (f : Var) : (nb067_alpha_dummy_179 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_179, fv_syn_cnnc] using (nb067_compact_fv_empty_0135 f)

theorem nb067_wpp_notmem_0482 : (nb067_alpha_dummy_178) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_178, fv_syn_cnnc] using (nb067_compact_fv_empty_0136)

theorem nb067_wpp_notmem_0483 (f : Var) : (nb067_alpha_dummy_180 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_180, fv_syn_cnnc] using (nb067_compact_fv_empty_0137 f)

theorem nb067_wpp_notmem_0484 : (nb067_alpha_dummy_170) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_170, fv_syn_cnnc] using (nb067_compact_fv_empty_0138)

theorem nb067_wpp_notmem_0485 (f : Var) : (nb067_alpha_dummy_172 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_172, fv_syn_cnnc] using (nb067_compact_fv_empty_0139 f)

theorem nb067_wpp_notmem_0486 : (nb067_alpha_dummy_169) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_169, fv_syn_cnnc] using (nb067_compact_fv_empty_0140)

theorem nb067_wpp_notmem_0487 (f : Var) : (nb067_alpha_dummy_171 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_171, fv_syn_cnnc] using (nb067_compact_fv_empty_0141 f)

theorem nb067_wpp_notmem_0488 : (nb067_alpha_dummy_175) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_175, fv_syn_cnnc] using (nb067_compact_fv_empty_0142)

theorem nb067_wpp_notmem_0489 (f : Var) : (nb067_alpha_dummy_176 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_176, fv_syn_cnnc] using (nb067_compact_fv_empty_0143 f)

theorem nb067_wpp_notmem_0490 : (nb067_alpha_dummy_173) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_173, fv_syn_cnnc] using (nb067_compact_fv_empty_0144)

theorem nb067_wpp_notmem_0491 (f : Var) : (nb067_alpha_dummy_174 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_174, fv_syn_cnnc] using (nb067_compact_fv_empty_0145 f)

theorem nb067_wpp_notmem_0492 : (nb067_alpha_dummy_164) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_164, fv_syn_cnnc] using (nb067_compact_fv_empty_0146)

theorem nb067_wpp_notmem_0493 (f : Var) : (nb067_alpha_dummy_166 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_166, fv_syn_cnnc] using (nb067_compact_fv_empty_0147 f)

theorem nb067_wpp_notmem_0494 : (nb067_alpha_dummy_163) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_163, fv_syn_cnnc] using (nb067_compact_fv_empty_0148)

theorem nb067_wpp_notmem_0495 (f : Var) : (nb067_alpha_dummy_165 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_165, fv_syn_cnnc] using (nb067_compact_fv_empty_0149 f)

theorem nb067_wpp_notmem_0496 : (nb067_alpha_dummy_167) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_167, fv_syn_cnnc] using (nb067_compact_fv_empty_0150)

theorem nb067_wpp_notmem_0497 (f : Var) : (nb067_alpha_dummy_168 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_168, fv_syn_cnnc] using (nb067_compact_fv_empty_0151 f)

theorem nb067_compact_envfresh_0031 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)), ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)), ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)), ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)), ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)), ((nb067_alpha_dummy_175), (nb067_alpha_dummy_176 f)), ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)), ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)), ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)), ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb067_alpha_dummy_181) (nb067_alpha_dummy_182 f) (nb067_wpp_notmem_0478) (nb067_wpp_notmem_0479 f) (TEnvFresh.consFresh (nb067_alpha_dummy_177) (nb067_alpha_dummy_179 f) (nb067_wpp_notmem_0480) (nb067_wpp_notmem_0481 f) (TEnvFresh.consFresh (nb067_alpha_dummy_178) (nb067_alpha_dummy_180 f) (nb067_wpp_notmem_0482) (nb067_wpp_notmem_0483 f) (TEnvFresh.consFresh (nb067_alpha_dummy_170) (nb067_alpha_dummy_172 f) (nb067_wpp_notmem_0484) (nb067_wpp_notmem_0485 f) (TEnvFresh.consFresh (nb067_alpha_dummy_169) (nb067_alpha_dummy_171 f) (nb067_wpp_notmem_0486) (nb067_wpp_notmem_0487 f) (TEnvFresh.consFresh (nb067_alpha_dummy_175) (nb067_alpha_dummy_176 f) (nb067_wpp_notmem_0488) (nb067_wpp_notmem_0489 f) (TEnvFresh.consFresh (nb067_alpha_dummy_173) (nb067_alpha_dummy_174 f) (nb067_wpp_notmem_0490) (nb067_wpp_notmem_0491 f) (TEnvFresh.consFresh (nb067_alpha_dummy_164) (nb067_alpha_dummy_166 f) (nb067_wpp_notmem_0492) (nb067_wpp_notmem_0493 f) (TEnvFresh.consFresh (nb067_alpha_dummy_163) (nb067_alpha_dummy_165 f) (nb067_wpp_notmem_0494) (nb067_wpp_notmem_0495 f) (TEnvFresh.consFresh (nb067_alpha_dummy_167) (nb067_alpha_dummy_168 f) (nb067_wpp_notmem_0496) (nb067_wpp_notmem_0497 f) (TEnvFresh.consFresh (nb067_alpha_dummy_085) (nb067_alpha_dummy_088 f) (nb067_wpp_notmem_0394) (nb067_wpp_notmem_0395 f) (TEnvFresh.consFresh (nb067_alpha_dummy_084) (nb067_alpha_dummy_087 f) (nb067_wpp_notmem_0284) (nb067_wpp_notmem_0285 f) (TEnvFresh.consFresh (nb067_alpha_dummy_083) (nb067_alpha_dummy_086 f) (nb067_wpp_notmem_0286) (nb067_wpp_notmem_0287 f) (TEnvFresh.consFresh (nb067_alpha_dummy_089) (nb067_alpha_dummy_090 f) (nb067_wpp_notmem_0288) (nb067_wpp_notmem_0289 f) (TEnvFresh.consFresh (nb067_alpha_dummy_081) (nb067_alpha_dummy_082 f) (nb067_wpp_notmem_0290) (nb067_wpp_notmem_0291 f) (TEnvFresh.consFresh (nb067_alpha_dummy_079) (nb067_alpha_dummy_080 f) (nb067_wpp_notmem_0292) (nb067_wpp_notmem_0293 f) (TEnvFresh.consFresh (nb067_alpha_dummy_000) f (nb067_wpp_notmem_0294) (nb067_wpp_notmem_0295 f) (TEnvFresh.consFresh (nb067_alpha_dummy_003) (nb067_alpha_dummy_004 x y f) (nb067_wpp_notmem_0094) (nb067_wpp_notmem_0095 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_002) y (nb067_wpp_notmem_0096) (nb067_wpp_notmem_0097 y) (TEnvFresh.consFresh (nb067_alpha_dummy_001) x (nb067_wpp_notmem_0098) (nb067_wpp_notmem_0099 x) (TEnvFresh.consFresh (nb067_alpha_dummy_005) (nb067_alpha_dummy_006 x y f) (nb067_wpp_notmem_0100) (nb067_wpp_notmem_0101 x y f) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))))))))

noncomputable def nb067_wpp_refl_0031 (x : Var) (y : Var) (f : Var) : TReflOn [((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)), ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)), ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)), ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)), ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)), ((nb067_alpha_dummy_175), (nb067_alpha_dummy_176 f)), ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)), ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)), ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)), ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb067_compact_envfresh_0031 x y f)

noncomputable def nb067_split_alpha_0021 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)), ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)), ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)), ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)), ((nb067_alpha_dummy_175), (nb067_alpha_dummy_176 f)), ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)), ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)), ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)), ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (Wff.classEq (Class.cv (nb067_alpha_dummy_178)) (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_177)) (syn_cnnc)) (syn_cplc (Class.cv (nb067_alpha_dummy_177)) (syn_c1c)) (Class.cv (nb067_alpha_dummy_177)))) (Wff.classEq (Class.cv (nb067_alpha_dummy_180 f)) (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_179 f)) (syn_cnnc)) (syn_cplc (Class.cv (nb067_alpha_dummy_179 f)) (syn_c1c)) (Class.cv (nb067_alpha_dummy_179 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_170))).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_172 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0186) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0187 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0186) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0187 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0184) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0185 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_185), (nb067_alpha_dummy_188 f)), ((nb067_alpha_dummy_184), (nb067_alpha_dummy_187 f)), ((nb067_alpha_dummy_183), (nb067_alpha_dummy_186 f)), ((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)), ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)), ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)), ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)), ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)), ((nb067_alpha_dummy_175), (nb067_alpha_dummy_176 f)), ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)), ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)), ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)), ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_c1c) (nb067_wpp_refl_0029 x y f))) (TAlphaWff.neg (TAlphaWff.neg (nb067_split_alpha_0020 x y f)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0184) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0185 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)), ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)), ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)), ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)), ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)), ((nb067_alpha_dummy_175), (nb067_alpha_dummy_176 f)), ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)), ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)), ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)), ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_cnnc) (nb067_wpp_refl_0031 x y f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0184) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0185 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0184) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0185 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)), ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)), ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)), ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)), ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)), ((nb067_alpha_dummy_175), (nb067_alpha_dummy_176 f)), ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)), ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)), ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)), ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_cnnc) (nb067_wpp_refl_0031 x y f))))))))))

theorem nb067_compact_fv_empty_0152 : (nb067_alpha_dummy_203) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0498 : (nb067_alpha_dummy_203) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_203, fv_syn_c1c] using (nb067_compact_fv_empty_0152)

theorem nb067_compact_fv_empty_0153 (f : Var) : (nb067_alpha_dummy_204 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0499 (f : Var) : (nb067_alpha_dummy_204 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_204, fv_syn_c1c] using (nb067_compact_fv_empty_0153 f)

theorem nb067_compact_fv_empty_0154 : (nb067_alpha_dummy_201) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0500 : (nb067_alpha_dummy_201) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_201, fv_syn_c1c] using (nb067_compact_fv_empty_0154)

theorem nb067_compact_fv_empty_0155 (f : Var) : (nb067_alpha_dummy_202 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0501 (f : Var) : (nb067_alpha_dummy_202 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_202, fv_syn_c1c] using (nb067_compact_fv_empty_0155 f)

theorem nb067_compact_fv_empty_0156 : (nb067_alpha_dummy_199) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0502 : (nb067_alpha_dummy_199) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_199, fv_syn_c1c] using (nb067_compact_fv_empty_0156)

theorem nb067_compact_fv_empty_0157 (f : Var) : (nb067_alpha_dummy_200 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0503 (f : Var) : (nb067_alpha_dummy_200 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_200, fv_syn_c1c] using (nb067_compact_fv_empty_0157 f)

theorem nb067_compact_envfresh_0032 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb067_alpha_dummy_185), (nb067_alpha_dummy_188 f)), ((nb067_alpha_dummy_184), (nb067_alpha_dummy_187 f)), ((nb067_alpha_dummy_183), (nb067_alpha_dummy_186 f)), ((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)), ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)), ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)), ((nb067_alpha_dummy_203), (nb067_alpha_dummy_204 f)), ((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)), ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)), ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)), ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)), ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)), ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)), ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)), ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb067_alpha_dummy_185) (nb067_alpha_dummy_188 f) (nb067_wpp_notmem_0426) (nb067_wpp_notmem_0427 f) (TEnvFresh.consFresh (nb067_alpha_dummy_184) (nb067_alpha_dummy_187 f) (nb067_wpp_notmem_0428) (nb067_wpp_notmem_0429 f) (TEnvFresh.consFresh (nb067_alpha_dummy_183) (nb067_alpha_dummy_186 f) (nb067_wpp_notmem_0430) (nb067_wpp_notmem_0431 f) (TEnvFresh.consFresh (nb067_alpha_dummy_181) (nb067_alpha_dummy_182 f) (nb067_wpp_notmem_0432) (nb067_wpp_notmem_0433 f) (TEnvFresh.consFresh (nb067_alpha_dummy_177) (nb067_alpha_dummy_179 f) (nb067_wpp_notmem_0434) (nb067_wpp_notmem_0435 f) (TEnvFresh.consFresh (nb067_alpha_dummy_178) (nb067_alpha_dummy_180 f) (nb067_wpp_notmem_0436) (nb067_wpp_notmem_0437 f) (TEnvFresh.consFresh (nb067_alpha_dummy_203) (nb067_alpha_dummy_204 f) (nb067_wpp_notmem_0498) (nb067_wpp_notmem_0499 f) (TEnvFresh.consFresh (nb067_alpha_dummy_201) (nb067_alpha_dummy_202 f) (nb067_wpp_notmem_0500) (nb067_wpp_notmem_0501 f) (TEnvFresh.consFresh (nb067_alpha_dummy_170) (nb067_alpha_dummy_172 f) (nb067_wpp_notmem_0438) (nb067_wpp_notmem_0439 f) (TEnvFresh.consFresh (nb067_alpha_dummy_169) (nb067_alpha_dummy_171 f) (nb067_wpp_notmem_0440) (nb067_wpp_notmem_0441 f) (TEnvFresh.consFresh (nb067_alpha_dummy_199) (nb067_alpha_dummy_200 f) (nb067_wpp_notmem_0502) (nb067_wpp_notmem_0503 f) (TEnvFresh.consFresh (nb067_alpha_dummy_173) (nb067_alpha_dummy_174 f) (nb067_wpp_notmem_0444) (nb067_wpp_notmem_0445 f) (TEnvFresh.consFresh (nb067_alpha_dummy_164) (nb067_alpha_dummy_166 f) (nb067_wpp_notmem_0446) (nb067_wpp_notmem_0447 f) (TEnvFresh.consFresh (nb067_alpha_dummy_163) (nb067_alpha_dummy_165 f) (nb067_wpp_notmem_0448) (nb067_wpp_notmem_0449 f) (TEnvFresh.consFresh (nb067_alpha_dummy_167) (nb067_alpha_dummy_168 f) (nb067_wpp_notmem_0450) (nb067_wpp_notmem_0451 f) (TEnvFresh.consFresh (nb067_alpha_dummy_085) (nb067_alpha_dummy_088 f) (nb067_wpp_notmem_0356) (nb067_wpp_notmem_0357 f) (TEnvFresh.consFresh (nb067_alpha_dummy_084) (nb067_alpha_dummy_087 f) (nb067_wpp_notmem_0226) (nb067_wpp_notmem_0227 f) (TEnvFresh.consFresh (nb067_alpha_dummy_083) (nb067_alpha_dummy_086 f) (nb067_wpp_notmem_0228) (nb067_wpp_notmem_0229 f) (TEnvFresh.consFresh (nb067_alpha_dummy_089) (nb067_alpha_dummy_090 f) (nb067_wpp_notmem_0230) (nb067_wpp_notmem_0231 f) (TEnvFresh.consFresh (nb067_alpha_dummy_081) (nb067_alpha_dummy_082 f) (nb067_wpp_notmem_0232) (nb067_wpp_notmem_0233 f) (TEnvFresh.consFresh (nb067_alpha_dummy_079) (nb067_alpha_dummy_080 f) (nb067_wpp_notmem_0234) (nb067_wpp_notmem_0235 f) (TEnvFresh.consFresh (nb067_alpha_dummy_000) f (nb067_wpp_notmem_0236) (nb067_wpp_notmem_0237 f) (TEnvFresh.consFresh (nb067_alpha_dummy_003) (nb067_alpha_dummy_004 x y f) (nb067_wpp_notmem_0028) (nb067_wpp_notmem_0029 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_002) y (nb067_wpp_notmem_0030) (nb067_wpp_notmem_0031 y) (TEnvFresh.consFresh (nb067_alpha_dummy_001) x (nb067_wpp_notmem_0032) (nb067_wpp_notmem_0033 x) (TEnvFresh.consFresh (nb067_alpha_dummy_005) (nb067_alpha_dummy_006 x y f) (nb067_wpp_notmem_0034) (nb067_wpp_notmem_0035 x y f) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))))))))

noncomputable def nb067_wpp_refl_0032 (x : Var) (y : Var) (f : Var) : TReflOn [((nb067_alpha_dummy_185), (nb067_alpha_dummy_188 f)), ((nb067_alpha_dummy_184), (nb067_alpha_dummy_187 f)), ((nb067_alpha_dummy_183), (nb067_alpha_dummy_186 f)), ((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)), ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)), ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)), ((nb067_alpha_dummy_203), (nb067_alpha_dummy_204 f)), ((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)), ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)), ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)), ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)), ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)), ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)), ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)), ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb067_compact_envfresh_0032 x y f)

theorem nb067_wpp_notmem_0504 : (nb067_alpha_dummy_203) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_203, fv_syn_c0] using (nb067_compact_fv_empty_0152)

theorem nb067_wpp_notmem_0505 (f : Var) : (nb067_alpha_dummy_204 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_204, fv_syn_c0] using (nb067_compact_fv_empty_0153 f)

theorem nb067_wpp_notmem_0506 : (nb067_alpha_dummy_201) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_201, fv_syn_c0] using (nb067_compact_fv_empty_0154)

theorem nb067_wpp_notmem_0507 (f : Var) : (nb067_alpha_dummy_202 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_202, fv_syn_c0] using (nb067_compact_fv_empty_0155 f)

theorem nb067_wpp_notmem_0508 : (nb067_alpha_dummy_199) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_199, fv_syn_c0] using (nb067_compact_fv_empty_0156)

theorem nb067_wpp_notmem_0509 (f : Var) : (nb067_alpha_dummy_200 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_200, fv_syn_c0] using (nb067_compact_fv_empty_0157 f)

theorem nb067_compact_envfresh_0033 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb067_alpha_dummy_185), (nb067_alpha_dummy_188 f)), ((nb067_alpha_dummy_184), (nb067_alpha_dummy_187 f)), ((nb067_alpha_dummy_183), (nb067_alpha_dummy_186 f)), ((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)), ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)), ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)), ((nb067_alpha_dummy_203), (nb067_alpha_dummy_204 f)), ((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)), ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)), ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)), ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)), ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)), ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)), ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)), ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb067_alpha_dummy_185) (nb067_alpha_dummy_188 f) (nb067_wpp_notmem_0452) (nb067_wpp_notmem_0453 f) (TEnvFresh.consFresh (nb067_alpha_dummy_184) (nb067_alpha_dummy_187 f) (nb067_wpp_notmem_0454) (nb067_wpp_notmem_0455 f) (TEnvFresh.consFresh (nb067_alpha_dummy_183) (nb067_alpha_dummy_186 f) (nb067_wpp_notmem_0456) (nb067_wpp_notmem_0457 f) (TEnvFresh.consFresh (nb067_alpha_dummy_181) (nb067_alpha_dummy_182 f) (nb067_wpp_notmem_0458) (nb067_wpp_notmem_0459 f) (TEnvFresh.consFresh (nb067_alpha_dummy_177) (nb067_alpha_dummy_179 f) (nb067_wpp_notmem_0460) (nb067_wpp_notmem_0461 f) (TEnvFresh.consFresh (nb067_alpha_dummy_178) (nb067_alpha_dummy_180 f) (nb067_wpp_notmem_0462) (nb067_wpp_notmem_0463 f) (TEnvFresh.consFresh (nb067_alpha_dummy_203) (nb067_alpha_dummy_204 f) (nb067_wpp_notmem_0504) (nb067_wpp_notmem_0505 f) (TEnvFresh.consFresh (nb067_alpha_dummy_201) (nb067_alpha_dummy_202 f) (nb067_wpp_notmem_0506) (nb067_wpp_notmem_0507 f) (TEnvFresh.consFresh (nb067_alpha_dummy_170) (nb067_alpha_dummy_172 f) (nb067_wpp_notmem_0464) (nb067_wpp_notmem_0465 f) (TEnvFresh.consFresh (nb067_alpha_dummy_169) (nb067_alpha_dummy_171 f) (nb067_wpp_notmem_0466) (nb067_wpp_notmem_0467 f) (TEnvFresh.consFresh (nb067_alpha_dummy_199) (nb067_alpha_dummy_200 f) (nb067_wpp_notmem_0508) (nb067_wpp_notmem_0509 f) (TEnvFresh.consFresh (nb067_alpha_dummy_173) (nb067_alpha_dummy_174 f) (nb067_wpp_notmem_0470) (nb067_wpp_notmem_0471 f) (TEnvFresh.consFresh (nb067_alpha_dummy_164) (nb067_alpha_dummy_166 f) (nb067_wpp_notmem_0472) (nb067_wpp_notmem_0473 f) (TEnvFresh.consFresh (nb067_alpha_dummy_163) (nb067_alpha_dummy_165 f) (nb067_wpp_notmem_0474) (nb067_wpp_notmem_0475 f) (TEnvFresh.consFresh (nb067_alpha_dummy_167) (nb067_alpha_dummy_168 f) (nb067_wpp_notmem_0476) (nb067_wpp_notmem_0477 f) (TEnvFresh.consFresh (nb067_alpha_dummy_085) (nb067_alpha_dummy_088 f) (nb067_wpp_notmem_0378) (nb067_wpp_notmem_0379 f) (TEnvFresh.consFresh (nb067_alpha_dummy_084) (nb067_alpha_dummy_087 f) (nb067_wpp_notmem_0258) (nb067_wpp_notmem_0259 f) (TEnvFresh.consFresh (nb067_alpha_dummy_083) (nb067_alpha_dummy_086 f) (nb067_wpp_notmem_0260) (nb067_wpp_notmem_0261 f) (TEnvFresh.consFresh (nb067_alpha_dummy_089) (nb067_alpha_dummy_090 f) (nb067_wpp_notmem_0262) (nb067_wpp_notmem_0263 f) (TEnvFresh.consFresh (nb067_alpha_dummy_081) (nb067_alpha_dummy_082 f) (nb067_wpp_notmem_0264) (nb067_wpp_notmem_0265 f) (TEnvFresh.consFresh (nb067_alpha_dummy_079) (nb067_alpha_dummy_080 f) (nb067_wpp_notmem_0266) (nb067_wpp_notmem_0267 f) (TEnvFresh.consFresh (nb067_alpha_dummy_000) f (nb067_wpp_notmem_0268) (nb067_wpp_notmem_0269 f) (TEnvFresh.consFresh (nb067_alpha_dummy_003) (nb067_alpha_dummy_004 x y f) (nb067_wpp_notmem_0064) (nb067_wpp_notmem_0065 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_002) y (nb067_wpp_notmem_0066) (nb067_wpp_notmem_0067 y) (TEnvFresh.consFresh (nb067_alpha_dummy_001) x (nb067_wpp_notmem_0068) (nb067_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb067_alpha_dummy_005) (nb067_alpha_dummy_006 x y f) (nb067_wpp_notmem_0070) (nb067_wpp_notmem_0071 x y f) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))))))))))

noncomputable def nb067_wpp_refl_0033 (x : Var) (y : Var) (f : Var) : TReflOn [((nb067_alpha_dummy_185), (nb067_alpha_dummy_188 f)), ((nb067_alpha_dummy_184), (nb067_alpha_dummy_187 f)), ((nb067_alpha_dummy_183), (nb067_alpha_dummy_186 f)), ((nb067_alpha_dummy_181), (nb067_alpha_dummy_182 f)), ((nb067_alpha_dummy_177), (nb067_alpha_dummy_179 f)), ((nb067_alpha_dummy_178), (nb067_alpha_dummy_180 f)), ((nb067_alpha_dummy_203), (nb067_alpha_dummy_204 f)), ((nb067_alpha_dummy_201), (nb067_alpha_dummy_202 f)), ((nb067_alpha_dummy_170), (nb067_alpha_dummy_172 f)), ((nb067_alpha_dummy_169), (nb067_alpha_dummy_171 f)), ((nb067_alpha_dummy_199), (nb067_alpha_dummy_200 f)), ((nb067_alpha_dummy_173), (nb067_alpha_dummy_174 f)), ((nb067_alpha_dummy_164), (nb067_alpha_dummy_166 f)), ((nb067_alpha_dummy_163), (nb067_alpha_dummy_165 f)), ((nb067_alpha_dummy_167), (nb067_alpha_dummy_168 f)), ((nb067_alpha_dummy_085), (nb067_alpha_dummy_088 f)), ((nb067_alpha_dummy_084), (nb067_alpha_dummy_087 f)), ((nb067_alpha_dummy_083), (nb067_alpha_dummy_086 f)), ((nb067_alpha_dummy_089), (nb067_alpha_dummy_090 f)), ((nb067_alpha_dummy_081), (nb067_alpha_dummy_082 f)), ((nb067_alpha_dummy_079), (nb067_alpha_dummy_080 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb067_compact_envfresh_0033 x y f)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
