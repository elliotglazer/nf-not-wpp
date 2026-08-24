import NAR4C077C001Part023

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

theorem nb077_compact_envfresh_0044 (x : Var) (F : Class) (I : Class) : TEnvFresh [((nb077_alpha_dummy_251 F I), (nb077_alpha_dummy_252 x)), ((nb077_alpha_dummy_220 F I), (nb077_alpha_dummy_222 x)), ((nb077_alpha_dummy_219 F I), (nb077_alpha_dummy_221 x)), ((nb077_alpha_dummy_249 F I), (nb077_alpha_dummy_250 x)), ((nb077_alpha_dummy_223 F I), (nb077_alpha_dummy_224 x)), ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb077_alpha_dummy_251 F I) (nb077_alpha_dummy_252 x) (nb077_wpp_notmem_0662 F I) (nb077_wpp_notmem_0663 x) (TEnvFresh.consFresh (nb077_alpha_dummy_220 F I) (nb077_alpha_dummy_222 x) (nb077_wpp_notmem_0664 F I) (nb077_wpp_notmem_0665 x) (TEnvFresh.consFresh (nb077_alpha_dummy_219 F I) (nb077_alpha_dummy_221 x) (nb077_wpp_notmem_0666 F I) (nb077_wpp_notmem_0667 x) (TEnvFresh.consFresh (nb077_alpha_dummy_249 F I) (nb077_alpha_dummy_250 x) (nb077_wpp_notmem_0668 F I) (nb077_wpp_notmem_0669 x) (TEnvFresh.consFresh (nb077_alpha_dummy_223 F I) (nb077_alpha_dummy_224 x) (nb077_wpp_notmem_0670 F I) (nb077_wpp_notmem_0671 x) (TEnvFresh.consFresh (nb077_alpha_dummy_141 F I) (nb077_alpha_dummy_144 x) (nb077_wpp_notmem_0554 F I) (nb077_wpp_notmem_0555 x) (TEnvFresh.consFresh (nb077_alpha_dummy_140 F I) (nb077_alpha_dummy_143 x) (nb077_wpp_notmem_0460 F I) (nb077_wpp_notmem_0461 x) (TEnvFresh.consFresh (nb077_alpha_dummy_139 F I) (nb077_alpha_dummy_142 x) (nb077_wpp_notmem_0462 F I) (nb077_wpp_notmem_0463 x) (TEnvFresh.consFresh (nb077_alpha_dummy_145 F I) (nb077_alpha_dummy_146 x) (nb077_wpp_notmem_0464 F I) (nb077_wpp_notmem_0465 x) (TEnvFresh.consFresh (nb077_alpha_dummy_061 F I) (nb077_alpha_dummy_064 x) (nb077_wpp_notmem_0358 F I) (nb077_wpp_notmem_0359 x) (TEnvFresh.consFresh (nb077_alpha_dummy_060 F I) (nb077_alpha_dummy_063 x) (nb077_wpp_notmem_0260 F I) (nb077_wpp_notmem_0261 x) (TEnvFresh.consFresh (nb077_alpha_dummy_059 F I) (nb077_alpha_dummy_062 x) (nb077_wpp_notmem_0262 F I) (nb077_wpp_notmem_0263 x) (TEnvFresh.consFresh (nb077_alpha_dummy_065 F I) (nb077_alpha_dummy_066 x) (nb077_wpp_notmem_0264 F I) (nb077_wpp_notmem_0265 x) (TEnvFresh.consFresh (nb077_alpha_dummy_057 F I) (nb077_alpha_dummy_058 x F) (nb077_wpp_notmem_0266 F I) (nb077_wpp_notmem_0267 x F) (TEnvFresh.consFresh (nb077_alpha_dummy_055 F I) (nb077_alpha_dummy_056 x F) (nb077_wpp_notmem_0268 F I) (nb077_wpp_notmem_0269 x F) (TEnvFresh.consFresh (nb077_alpha_dummy_016 F I) (nb077_alpha_dummy_018 x F I) (nb077_wpp_notmem_0134 F I) (nb077_wpp_notmem_0135 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_015 F I) (nb077_alpha_dummy_017 x F I) (nb077_wpp_notmem_0136 F I) (nb077_wpp_notmem_0137 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_013 F I) (nb077_alpha_dummy_014 x F I) (nb077_wpp_notmem_0138 F I) (nb077_wpp_notmem_0139 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_011 F I) (nb077_alpha_dummy_012 x F I) (nb077_wpp_notmem_0140 F I) (nb077_wpp_notmem_0141 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_001 F I) (nb077_alpha_dummy_002 x F I) (nb077_wpp_notmem_0142 F I) (nb077_wpp_notmem_0143 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_004 F I) (nb077_alpha_dummy_006 x F I) (nb077_wpp_notmem_0144 F I) (nb077_wpp_notmem_0145 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_003 F I) (nb077_alpha_dummy_005 x F I) (nb077_wpp_notmem_0146 F I) (nb077_wpp_notmem_0147 x F I) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))))))))))))))))

noncomputable def nb077_wpp_refl_0044 (x : Var) (F : Class) (I : Class) : TReflOn [((nb077_alpha_dummy_251 F I), (nb077_alpha_dummy_252 x)), ((nb077_alpha_dummy_220 F I), (nb077_alpha_dummy_222 x)), ((nb077_alpha_dummy_219 F I), (nb077_alpha_dummy_221 x)), ((nb077_alpha_dummy_249 F I), (nb077_alpha_dummy_250 x)), ((nb077_alpha_dummy_223 F I), (nb077_alpha_dummy_224 x)), ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb077_compact_envfresh_0044 x F I)

theorem nb077_compact_fv_empty_0194 (F : Class) (I : Class) : (nb077_alpha_dummy_275 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0672 (F : Class) (I : Class) : (nb077_alpha_dummy_275 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_275, fv_syn_c1c] using (nb077_compact_fv_empty_0194 F I)

theorem nb077_compact_fv_empty_0195 (x : Var) : (nb077_alpha_dummy_278 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0673 (x : Var) : (nb077_alpha_dummy_278 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_278, fv_syn_c1c] using (nb077_compact_fv_empty_0195 x)

theorem nb077_compact_fv_empty_0196 (F : Class) (I : Class) : (nb077_alpha_dummy_274 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0674 (F : Class) (I : Class) : (nb077_alpha_dummy_274 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_274, fv_syn_c1c] using (nb077_compact_fv_empty_0196 F I)

theorem nb077_compact_fv_empty_0197 (x : Var) : (nb077_alpha_dummy_277 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0675 (x : Var) : (nb077_alpha_dummy_277 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_277, fv_syn_c1c] using (nb077_compact_fv_empty_0197 x)

theorem nb077_compact_fv_empty_0198 (F : Class) (I : Class) : (nb077_alpha_dummy_273 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0676 (F : Class) (I : Class) : (nb077_alpha_dummy_273 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_273, fv_syn_c1c] using (nb077_compact_fv_empty_0198 F I)

theorem nb077_compact_fv_empty_0199 (x : Var) : (nb077_alpha_dummy_276 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0677 (x : Var) : (nb077_alpha_dummy_276 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_276, fv_syn_c1c] using (nb077_compact_fv_empty_0199 x)

theorem nb077_compact_fv_empty_0200 (F : Class) (I : Class) : (nb077_alpha_dummy_271 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0678 (F : Class) (I : Class) : (nb077_alpha_dummy_271 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_271, fv_syn_c1c] using (nb077_compact_fv_empty_0200 F I)

theorem nb077_compact_fv_empty_0201 (x : Var) : (nb077_alpha_dummy_272 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0679 (x : Var) : (nb077_alpha_dummy_272 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_272, fv_syn_c1c] using (nb077_compact_fv_empty_0201 x)

theorem nb077_compact_fv_empty_0202 (F : Class) (I : Class) : (nb077_alpha_dummy_267 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0680 (F : Class) (I : Class) : (nb077_alpha_dummy_267 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_267, fv_syn_c1c] using (nb077_compact_fv_empty_0202 F I)

theorem nb077_compact_fv_empty_0203 (x : Var) : (nb077_alpha_dummy_269 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0681 (x : Var) : (nb077_alpha_dummy_269 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_269, fv_syn_c1c] using (nb077_compact_fv_empty_0203 x)

theorem nb077_compact_fv_empty_0204 (F : Class) (I : Class) : (nb077_alpha_dummy_268 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0682 (F : Class) (I : Class) : (nb077_alpha_dummy_268 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_268, fv_syn_c1c] using (nb077_compact_fv_empty_0204 F I)

theorem nb077_compact_fv_empty_0205 (x : Var) : (nb077_alpha_dummy_270 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0683 (x : Var) : (nb077_alpha_dummy_270 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_270, fv_syn_c1c] using (nb077_compact_fv_empty_0205 x)

theorem nb077_compact_fv_empty_0206 (F : Class) (I : Class) : (nb077_alpha_dummy_260 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0684 (F : Class) (I : Class) : (nb077_alpha_dummy_260 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_260, fv_syn_c1c] using (nb077_compact_fv_empty_0206 F I)

theorem nb077_compact_fv_empty_0207 (x : Var) : (nb077_alpha_dummy_262 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0685 (x : Var) : (nb077_alpha_dummy_262 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_262, fv_syn_c1c] using (nb077_compact_fv_empty_0207 x)

theorem nb077_compact_fv_empty_0208 (F : Class) (I : Class) : (nb077_alpha_dummy_259 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0686 (F : Class) (I : Class) : (nb077_alpha_dummy_259 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_259, fv_syn_c1c] using (nb077_compact_fv_empty_0208 F I)

theorem nb077_compact_fv_empty_0209 (x : Var) : (nb077_alpha_dummy_261 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0687 (x : Var) : (nb077_alpha_dummy_261 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_261, fv_syn_c1c] using (nb077_compact_fv_empty_0209 x)

theorem nb077_compact_fv_empty_0210 (F : Class) (I : Class) : (nb077_alpha_dummy_265 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0688 (F : Class) (I : Class) : (nb077_alpha_dummy_265 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_265, fv_syn_c1c] using (nb077_compact_fv_empty_0210 F I)

theorem nb077_compact_fv_empty_0211 (x : Var) : (nb077_alpha_dummy_266 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0689 (x : Var) : (nb077_alpha_dummy_266 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_266, fv_syn_c1c] using (nb077_compact_fv_empty_0211 x)

theorem nb077_compact_fv_empty_0212 (F : Class) (I : Class) : (nb077_alpha_dummy_263 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0690 (F : Class) (I : Class) : (nb077_alpha_dummy_263 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_263, fv_syn_c1c] using (nb077_compact_fv_empty_0212 F I)

theorem nb077_compact_fv_empty_0213 (x : Var) : (nb077_alpha_dummy_264 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0691 (x : Var) : (nb077_alpha_dummy_264 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_264, fv_syn_c1c] using (nb077_compact_fv_empty_0213 x)

theorem nb077_compact_fv_empty_0214 (F : Class) (I : Class) : (nb077_alpha_dummy_255 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0692 (F : Class) (I : Class) : (nb077_alpha_dummy_255 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_255, fv_syn_c1c] using (nb077_compact_fv_empty_0214 F I)

theorem nb077_compact_fv_empty_0215 (x : Var) : (nb077_alpha_dummy_256 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0693 (x : Var) : (nb077_alpha_dummy_256 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_256, fv_syn_c1c] using (nb077_compact_fv_empty_0215 x)

theorem nb077_compact_fv_empty_0216 (F : Class) (I : Class) : (nb077_alpha_dummy_000 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0694 (F : Class) (I : Class) : (nb077_alpha_dummy_000 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_000, fv_syn_c1c] using (nb077_compact_fv_empty_0216 F I)

theorem nb077_compact_fv_empty_0217 (x : Var) : x ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0695 (x : Var) : x ∉ ((syn_c1c)).fv := by
  simpa only [fv_syn_c1c] using (nb077_compact_fv_empty_0217 x)

theorem nb077_compact_fv_empty_0218 (F : Class) (I : Class) : (nb077_alpha_dummy_257 F I) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0696 (F : Class) (I : Class) : (nb077_alpha_dummy_257 F I) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_257, fv_syn_c1c] using (nb077_compact_fv_empty_0218 F I)

theorem nb077_compact_fv_empty_0219 (x : Var) : (nb077_alpha_dummy_258 x) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb077_wpp_notmem_0697 (x : Var) : (nb077_alpha_dummy_258 x) ∉ ((syn_c1c)).fv := by
  simpa only [nb077_alpha_dummy_258, fv_syn_c1c] using (nb077_compact_fv_empty_0219 x)

theorem nb077_compact_envfresh_0045 (x : Var) (F : Class) (I : Class) : TEnvFresh [((nb077_alpha_dummy_275 F I), (nb077_alpha_dummy_278 x)), ((nb077_alpha_dummy_274 F I), (nb077_alpha_dummy_277 x)), ((nb077_alpha_dummy_273 F I), (nb077_alpha_dummy_276 x)), ((nb077_alpha_dummy_271 F I), (nb077_alpha_dummy_272 x)), ((nb077_alpha_dummy_267 F I), (nb077_alpha_dummy_269 x)), ((nb077_alpha_dummy_268 F I), (nb077_alpha_dummy_270 x)), ((nb077_alpha_dummy_260 F I), (nb077_alpha_dummy_262 x)), ((nb077_alpha_dummy_259 F I), (nb077_alpha_dummy_261 x)), ((nb077_alpha_dummy_265 F I), (nb077_alpha_dummy_266 x)), ((nb077_alpha_dummy_263 F I), (nb077_alpha_dummy_264 x)), ((nb077_alpha_dummy_255 F I), (nb077_alpha_dummy_256 x)), ((nb077_alpha_dummy_000 F I), x), ((nb077_alpha_dummy_257 F I), (nb077_alpha_dummy_258 x)), ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb077_alpha_dummy_275 F I) (nb077_alpha_dummy_278 x) (nb077_wpp_notmem_0672 F I) (nb077_wpp_notmem_0673 x) (TEnvFresh.consFresh (nb077_alpha_dummy_274 F I) (nb077_alpha_dummy_277 x) (nb077_wpp_notmem_0674 F I) (nb077_wpp_notmem_0675 x) (TEnvFresh.consFresh (nb077_alpha_dummy_273 F I) (nb077_alpha_dummy_276 x) (nb077_wpp_notmem_0676 F I) (nb077_wpp_notmem_0677 x) (TEnvFresh.consFresh (nb077_alpha_dummy_271 F I) (nb077_alpha_dummy_272 x) (nb077_wpp_notmem_0678 F I) (nb077_wpp_notmem_0679 x) (TEnvFresh.consFresh (nb077_alpha_dummy_267 F I) (nb077_alpha_dummy_269 x) (nb077_wpp_notmem_0680 F I) (nb077_wpp_notmem_0681 x) (TEnvFresh.consFresh (nb077_alpha_dummy_268 F I) (nb077_alpha_dummy_270 x) (nb077_wpp_notmem_0682 F I) (nb077_wpp_notmem_0683 x) (TEnvFresh.consFresh (nb077_alpha_dummy_260 F I) (nb077_alpha_dummy_262 x) (nb077_wpp_notmem_0684 F I) (nb077_wpp_notmem_0685 x) (TEnvFresh.consFresh (nb077_alpha_dummy_259 F I) (nb077_alpha_dummy_261 x) (nb077_wpp_notmem_0686 F I) (nb077_wpp_notmem_0687 x) (TEnvFresh.consFresh (nb077_alpha_dummy_265 F I) (nb077_alpha_dummy_266 x) (nb077_wpp_notmem_0688 F I) (nb077_wpp_notmem_0689 x) (TEnvFresh.consFresh (nb077_alpha_dummy_263 F I) (nb077_alpha_dummy_264 x) (nb077_wpp_notmem_0690 F I) (nb077_wpp_notmem_0691 x) (TEnvFresh.consFresh (nb077_alpha_dummy_255 F I) (nb077_alpha_dummy_256 x) (nb077_wpp_notmem_0692 F I) (nb077_wpp_notmem_0693 x) (TEnvFresh.consFresh (nb077_alpha_dummy_000 F I) x (nb077_wpp_notmem_0694 F I) (nb077_wpp_notmem_0695 x) (TEnvFresh.consFresh (nb077_alpha_dummy_257 F I) (nb077_alpha_dummy_258 x) (nb077_wpp_notmem_0696 F I) (nb077_wpp_notmem_0697 x) (TEnvFresh.consFresh (nb077_alpha_dummy_141 F I) (nb077_alpha_dummy_144 x) (nb077_wpp_notmem_0486 F I) (nb077_wpp_notmem_0487 x) (TEnvFresh.consFresh (nb077_alpha_dummy_140 F I) (nb077_alpha_dummy_143 x) (nb077_wpp_notmem_0380 F I) (nb077_wpp_notmem_0381 x) (TEnvFresh.consFresh (nb077_alpha_dummy_139 F I) (nb077_alpha_dummy_142 x) (nb077_wpp_notmem_0382 F I) (nb077_wpp_notmem_0383 x) (TEnvFresh.consFresh (nb077_alpha_dummy_145 F I) (nb077_alpha_dummy_146 x) (nb077_wpp_notmem_0384 F I) (nb077_wpp_notmem_0385 x) (TEnvFresh.consFresh (nb077_alpha_dummy_061 F I) (nb077_alpha_dummy_064 x) (nb077_wpp_notmem_0290 F I) (nb077_wpp_notmem_0291 x) (TEnvFresh.consFresh (nb077_alpha_dummy_060 F I) (nb077_alpha_dummy_063 x) (nb077_wpp_notmem_0168 F I) (nb077_wpp_notmem_0169 x) (TEnvFresh.consFresh (nb077_alpha_dummy_059 F I) (nb077_alpha_dummy_062 x) (nb077_wpp_notmem_0170 F I) (nb077_wpp_notmem_0171 x) (TEnvFresh.consFresh (nb077_alpha_dummy_065 F I) (nb077_alpha_dummy_066 x) (nb077_wpp_notmem_0172 F I) (nb077_wpp_notmem_0173 x) (TEnvFresh.consFresh (nb077_alpha_dummy_057 F I) (nb077_alpha_dummy_058 x F) (nb077_wpp_notmem_0174 F I) (nb077_wpp_notmem_0175 x F) (TEnvFresh.consFresh (nb077_alpha_dummy_055 F I) (nb077_alpha_dummy_056 x F) (nb077_wpp_notmem_0176 F I) (nb077_wpp_notmem_0177 x F) (TEnvFresh.consFresh (nb077_alpha_dummy_016 F I) (nb077_alpha_dummy_018 x F I) (nb077_wpp_notmem_0030 F I) (nb077_wpp_notmem_0031 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_015 F I) (nb077_alpha_dummy_017 x F I) (nb077_wpp_notmem_0032 F I) (nb077_wpp_notmem_0033 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_013 F I) (nb077_alpha_dummy_014 x F I) (nb077_wpp_notmem_0034 F I) (nb077_wpp_notmem_0035 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_011 F I) (nb077_alpha_dummy_012 x F I) (nb077_wpp_notmem_0036 F I) (nb077_wpp_notmem_0037 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_001 F I) (nb077_alpha_dummy_002 x F I) (nb077_wpp_notmem_0038 F I) (nb077_wpp_notmem_0039 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_004 F I) (nb077_alpha_dummy_006 x F I) (nb077_wpp_notmem_0040 F I) (nb077_wpp_notmem_0041 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_003 F I) (nb077_alpha_dummy_005 x F I) (nb077_wpp_notmem_0042 F I) (nb077_wpp_notmem_0043 x F I) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))))))))))))

noncomputable def nb077_wpp_refl_0045 (x : Var) (F : Class) (I : Class) : TReflOn [((nb077_alpha_dummy_275 F I), (nb077_alpha_dummy_278 x)), ((nb077_alpha_dummy_274 F I), (nb077_alpha_dummy_277 x)), ((nb077_alpha_dummy_273 F I), (nb077_alpha_dummy_276 x)), ((nb077_alpha_dummy_271 F I), (nb077_alpha_dummy_272 x)), ((nb077_alpha_dummy_267 F I), (nb077_alpha_dummy_269 x)), ((nb077_alpha_dummy_268 F I), (nb077_alpha_dummy_270 x)), ((nb077_alpha_dummy_260 F I), (nb077_alpha_dummy_262 x)), ((nb077_alpha_dummy_259 F I), (nb077_alpha_dummy_261 x)), ((nb077_alpha_dummy_265 F I), (nb077_alpha_dummy_266 x)), ((nb077_alpha_dummy_263 F I), (nb077_alpha_dummy_264 x)), ((nb077_alpha_dummy_255 F I), (nb077_alpha_dummy_256 x)), ((nb077_alpha_dummy_000 F I), x), ((nb077_alpha_dummy_257 F I), (nb077_alpha_dummy_258 x)), ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb077_compact_envfresh_0045 x F I)

theorem nb077_wpp_notmem_0698 (F : Class) (I : Class) : (nb077_alpha_dummy_275 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_275, fv_syn_c0] using (nb077_compact_fv_empty_0194 F I)

theorem nb077_wpp_notmem_0699 (x : Var) : (nb077_alpha_dummy_278 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_278, fv_syn_c0] using (nb077_compact_fv_empty_0195 x)

theorem nb077_wpp_notmem_0700 (F : Class) (I : Class) : (nb077_alpha_dummy_274 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_274, fv_syn_c0] using (nb077_compact_fv_empty_0196 F I)

theorem nb077_wpp_notmem_0701 (x : Var) : (nb077_alpha_dummy_277 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_277, fv_syn_c0] using (nb077_compact_fv_empty_0197 x)

theorem nb077_wpp_notmem_0702 (F : Class) (I : Class) : (nb077_alpha_dummy_273 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_273, fv_syn_c0] using (nb077_compact_fv_empty_0198 F I)

theorem nb077_wpp_notmem_0703 (x : Var) : (nb077_alpha_dummy_276 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_276, fv_syn_c0] using (nb077_compact_fv_empty_0199 x)

theorem nb077_wpp_notmem_0704 (F : Class) (I : Class) : (nb077_alpha_dummy_271 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_271, fv_syn_c0] using (nb077_compact_fv_empty_0200 F I)

theorem nb077_wpp_notmem_0705 (x : Var) : (nb077_alpha_dummy_272 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_272, fv_syn_c0] using (nb077_compact_fv_empty_0201 x)

theorem nb077_wpp_notmem_0706 (F : Class) (I : Class) : (nb077_alpha_dummy_267 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_267, fv_syn_c0] using (nb077_compact_fv_empty_0202 F I)

theorem nb077_wpp_notmem_0707 (x : Var) : (nb077_alpha_dummy_269 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_269, fv_syn_c0] using (nb077_compact_fv_empty_0203 x)

theorem nb077_wpp_notmem_0708 (F : Class) (I : Class) : (nb077_alpha_dummy_268 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_268, fv_syn_c0] using (nb077_compact_fv_empty_0204 F I)

theorem nb077_wpp_notmem_0709 (x : Var) : (nb077_alpha_dummy_270 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_270, fv_syn_c0] using (nb077_compact_fv_empty_0205 x)

theorem nb077_wpp_notmem_0710 (F : Class) (I : Class) : (nb077_alpha_dummy_260 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_260, fv_syn_c0] using (nb077_compact_fv_empty_0206 F I)

theorem nb077_wpp_notmem_0711 (x : Var) : (nb077_alpha_dummy_262 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_262, fv_syn_c0] using (nb077_compact_fv_empty_0207 x)

theorem nb077_wpp_notmem_0712 (F : Class) (I : Class) : (nb077_alpha_dummy_259 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_259, fv_syn_c0] using (nb077_compact_fv_empty_0208 F I)

theorem nb077_wpp_notmem_0713 (x : Var) : (nb077_alpha_dummy_261 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_261, fv_syn_c0] using (nb077_compact_fv_empty_0209 x)

theorem nb077_wpp_notmem_0714 (F : Class) (I : Class) : (nb077_alpha_dummy_265 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_265, fv_syn_c0] using (nb077_compact_fv_empty_0210 F I)

theorem nb077_wpp_notmem_0715 (x : Var) : (nb077_alpha_dummy_266 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_266, fv_syn_c0] using (nb077_compact_fv_empty_0211 x)

theorem nb077_wpp_notmem_0716 (F : Class) (I : Class) : (nb077_alpha_dummy_263 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_263, fv_syn_c0] using (nb077_compact_fv_empty_0212 F I)

theorem nb077_wpp_notmem_0717 (x : Var) : (nb077_alpha_dummy_264 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_264, fv_syn_c0] using (nb077_compact_fv_empty_0213 x)

theorem nb077_wpp_notmem_0718 (F : Class) (I : Class) : (nb077_alpha_dummy_255 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_255, fv_syn_c0] using (nb077_compact_fv_empty_0214 F I)

theorem nb077_wpp_notmem_0719 (x : Var) : (nb077_alpha_dummy_256 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_256, fv_syn_c0] using (nb077_compact_fv_empty_0215 x)

theorem nb077_wpp_notmem_0720 (F : Class) (I : Class) : (nb077_alpha_dummy_000 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_000, fv_syn_c0] using (nb077_compact_fv_empty_0216 F I)

theorem nb077_wpp_notmem_0721 (x : Var) : x ∉ ((syn_c0)).fv := by
  simpa only [fv_syn_c0] using (nb077_compact_fv_empty_0217 x)

theorem nb077_wpp_notmem_0722 (F : Class) (I : Class) : (nb077_alpha_dummy_257 F I) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_257, fv_syn_c0] using (nb077_compact_fv_empty_0218 F I)

theorem nb077_wpp_notmem_0723 (x : Var) : (nb077_alpha_dummy_258 x) ∉ ((syn_c0)).fv := by
  simpa only [nb077_alpha_dummy_258, fv_syn_c0] using (nb077_compact_fv_empty_0219 x)

theorem nb077_compact_envfresh_0046 (x : Var) (F : Class) (I : Class) : TEnvFresh [((nb077_alpha_dummy_275 F I), (nb077_alpha_dummy_278 x)), ((nb077_alpha_dummy_274 F I), (nb077_alpha_dummy_277 x)), ((nb077_alpha_dummy_273 F I), (nb077_alpha_dummy_276 x)), ((nb077_alpha_dummy_271 F I), (nb077_alpha_dummy_272 x)), ((nb077_alpha_dummy_267 F I), (nb077_alpha_dummy_269 x)), ((nb077_alpha_dummy_268 F I), (nb077_alpha_dummy_270 x)), ((nb077_alpha_dummy_260 F I), (nb077_alpha_dummy_262 x)), ((nb077_alpha_dummy_259 F I), (nb077_alpha_dummy_261 x)), ((nb077_alpha_dummy_265 F I), (nb077_alpha_dummy_266 x)), ((nb077_alpha_dummy_263 F I), (nb077_alpha_dummy_264 x)), ((nb077_alpha_dummy_255 F I), (nb077_alpha_dummy_256 x)), ((nb077_alpha_dummy_000 F I), x), ((nb077_alpha_dummy_257 F I), (nb077_alpha_dummy_258 x)), ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb077_alpha_dummy_275 F I) (nb077_alpha_dummy_278 x) (nb077_wpp_notmem_0698 F I) (nb077_wpp_notmem_0699 x) (TEnvFresh.consFresh (nb077_alpha_dummy_274 F I) (nb077_alpha_dummy_277 x) (nb077_wpp_notmem_0700 F I) (nb077_wpp_notmem_0701 x) (TEnvFresh.consFresh (nb077_alpha_dummy_273 F I) (nb077_alpha_dummy_276 x) (nb077_wpp_notmem_0702 F I) (nb077_wpp_notmem_0703 x) (TEnvFresh.consFresh (nb077_alpha_dummy_271 F I) (nb077_alpha_dummy_272 x) (nb077_wpp_notmem_0704 F I) (nb077_wpp_notmem_0705 x) (TEnvFresh.consFresh (nb077_alpha_dummy_267 F I) (nb077_alpha_dummy_269 x) (nb077_wpp_notmem_0706 F I) (nb077_wpp_notmem_0707 x) (TEnvFresh.consFresh (nb077_alpha_dummy_268 F I) (nb077_alpha_dummy_270 x) (nb077_wpp_notmem_0708 F I) (nb077_wpp_notmem_0709 x) (TEnvFresh.consFresh (nb077_alpha_dummy_260 F I) (nb077_alpha_dummy_262 x) (nb077_wpp_notmem_0710 F I) (nb077_wpp_notmem_0711 x) (TEnvFresh.consFresh (nb077_alpha_dummy_259 F I) (nb077_alpha_dummy_261 x) (nb077_wpp_notmem_0712 F I) (nb077_wpp_notmem_0713 x) (TEnvFresh.consFresh (nb077_alpha_dummy_265 F I) (nb077_alpha_dummy_266 x) (nb077_wpp_notmem_0714 F I) (nb077_wpp_notmem_0715 x) (TEnvFresh.consFresh (nb077_alpha_dummy_263 F I) (nb077_alpha_dummy_264 x) (nb077_wpp_notmem_0716 F I) (nb077_wpp_notmem_0717 x) (TEnvFresh.consFresh (nb077_alpha_dummy_255 F I) (nb077_alpha_dummy_256 x) (nb077_wpp_notmem_0718 F I) (nb077_wpp_notmem_0719 x) (TEnvFresh.consFresh (nb077_alpha_dummy_000 F I) x (nb077_wpp_notmem_0720 F I) (nb077_wpp_notmem_0721 x) (TEnvFresh.consFresh (nb077_alpha_dummy_257 F I) (nb077_alpha_dummy_258 x) (nb077_wpp_notmem_0722 F I) (nb077_wpp_notmem_0723 x) (TEnvFresh.consFresh (nb077_alpha_dummy_141 F I) (nb077_alpha_dummy_144 x) (nb077_wpp_notmem_0508 F I) (nb077_wpp_notmem_0509 x) (TEnvFresh.consFresh (nb077_alpha_dummy_140 F I) (nb077_alpha_dummy_143 x) (nb077_wpp_notmem_0406 F I) (nb077_wpp_notmem_0407 x) (TEnvFresh.consFresh (nb077_alpha_dummy_139 F I) (nb077_alpha_dummy_142 x) (nb077_wpp_notmem_0408 F I) (nb077_wpp_notmem_0409 x) (TEnvFresh.consFresh (nb077_alpha_dummy_145 F I) (nb077_alpha_dummy_146 x) (nb077_wpp_notmem_0410 F I) (nb077_wpp_notmem_0411 x) (TEnvFresh.consFresh (nb077_alpha_dummy_061 F I) (nb077_alpha_dummy_064 x) (nb077_wpp_notmem_0312 F I) (nb077_wpp_notmem_0313 x) (TEnvFresh.consFresh (nb077_alpha_dummy_060 F I) (nb077_alpha_dummy_063 x) (nb077_wpp_notmem_0198 F I) (nb077_wpp_notmem_0199 x) (TEnvFresh.consFresh (nb077_alpha_dummy_059 F I) (nb077_alpha_dummy_062 x) (nb077_wpp_notmem_0200 F I) (nb077_wpp_notmem_0201 x) (TEnvFresh.consFresh (nb077_alpha_dummy_065 F I) (nb077_alpha_dummy_066 x) (nb077_wpp_notmem_0202 F I) (nb077_wpp_notmem_0203 x) (TEnvFresh.consFresh (nb077_alpha_dummy_057 F I) (nb077_alpha_dummy_058 x F) (nb077_wpp_notmem_0204 F I) (nb077_wpp_notmem_0205 x F) (TEnvFresh.consFresh (nb077_alpha_dummy_055 F I) (nb077_alpha_dummy_056 x F) (nb077_wpp_notmem_0206 F I) (nb077_wpp_notmem_0207 x F) (TEnvFresh.consFresh (nb077_alpha_dummy_016 F I) (nb077_alpha_dummy_018 x F I) (nb077_wpp_notmem_0064 F I) (nb077_wpp_notmem_0065 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_015 F I) (nb077_alpha_dummy_017 x F I) (nb077_wpp_notmem_0066 F I) (nb077_wpp_notmem_0067 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_013 F I) (nb077_alpha_dummy_014 x F I) (nb077_wpp_notmem_0068 F I) (nb077_wpp_notmem_0069 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_011 F I) (nb077_alpha_dummy_012 x F I) (nb077_wpp_notmem_0070 F I) (nb077_wpp_notmem_0071 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_001 F I) (nb077_alpha_dummy_002 x F I) (nb077_wpp_notmem_0072 F I) (nb077_wpp_notmem_0073 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_004 F I) (nb077_alpha_dummy_006 x F I) (nb077_wpp_notmem_0074 F I) (nb077_wpp_notmem_0075 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_003 F I) (nb077_alpha_dummy_005 x F I) (nb077_wpp_notmem_0076 F I) (nb077_wpp_notmem_0077 x F I) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))))))))))))))

noncomputable def nb077_wpp_refl_0046 (x : Var) (F : Class) (I : Class) : TReflOn [((nb077_alpha_dummy_275 F I), (nb077_alpha_dummy_278 x)), ((nb077_alpha_dummy_274 F I), (nb077_alpha_dummy_277 x)), ((nb077_alpha_dummy_273 F I), (nb077_alpha_dummy_276 x)), ((nb077_alpha_dummy_271 F I), (nb077_alpha_dummy_272 x)), ((nb077_alpha_dummy_267 F I), (nb077_alpha_dummy_269 x)), ((nb077_alpha_dummy_268 F I), (nb077_alpha_dummy_270 x)), ((nb077_alpha_dummy_260 F I), (nb077_alpha_dummy_262 x)), ((nb077_alpha_dummy_259 F I), (nb077_alpha_dummy_261 x)), ((nb077_alpha_dummy_265 F I), (nb077_alpha_dummy_266 x)), ((nb077_alpha_dummy_263 F I), (nb077_alpha_dummy_264 x)), ((nb077_alpha_dummy_255 F I), (nb077_alpha_dummy_256 x)), ((nb077_alpha_dummy_000 F I), x), ((nb077_alpha_dummy_257 F I), (nb077_alpha_dummy_258 x)), ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb077_compact_envfresh_0046 x F I)

theorem nb077_wpp_notmem_0724 (F : Class) (I : Class) : (nb077_alpha_dummy_271 F I) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_271, fv_syn_cnnc] using (nb077_compact_fv_empty_0200 F I)

theorem nb077_wpp_notmem_0725 (x : Var) : (nb077_alpha_dummy_272 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_272, fv_syn_cnnc] using (nb077_compact_fv_empty_0201 x)

theorem nb077_wpp_notmem_0726 (F : Class) (I : Class) : (nb077_alpha_dummy_267 F I) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_267, fv_syn_cnnc] using (nb077_compact_fv_empty_0202 F I)

theorem nb077_wpp_notmem_0727 (x : Var) : (nb077_alpha_dummy_269 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_269, fv_syn_cnnc] using (nb077_compact_fv_empty_0203 x)

theorem nb077_wpp_notmem_0728 (F : Class) (I : Class) : (nb077_alpha_dummy_268 F I) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_268, fv_syn_cnnc] using (nb077_compact_fv_empty_0204 F I)

theorem nb077_wpp_notmem_0729 (x : Var) : (nb077_alpha_dummy_270 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_270, fv_syn_cnnc] using (nb077_compact_fv_empty_0205 x)

theorem nb077_wpp_notmem_0730 (F : Class) (I : Class) : (nb077_alpha_dummy_260 F I) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_260, fv_syn_cnnc] using (nb077_compact_fv_empty_0206 F I)

theorem nb077_wpp_notmem_0731 (x : Var) : (nb077_alpha_dummy_262 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_262, fv_syn_cnnc] using (nb077_compact_fv_empty_0207 x)

theorem nb077_wpp_notmem_0732 (F : Class) (I : Class) : (nb077_alpha_dummy_259 F I) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_259, fv_syn_cnnc] using (nb077_compact_fv_empty_0208 F I)

theorem nb077_wpp_notmem_0733 (x : Var) : (nb077_alpha_dummy_261 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_261, fv_syn_cnnc] using (nb077_compact_fv_empty_0209 x)

theorem nb077_wpp_notmem_0734 (F : Class) (I : Class) : (nb077_alpha_dummy_265 F I) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_265, fv_syn_cnnc] using (nb077_compact_fv_empty_0210 F I)

theorem nb077_wpp_notmem_0735 (x : Var) : (nb077_alpha_dummy_266 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_266, fv_syn_cnnc] using (nb077_compact_fv_empty_0211 x)

theorem nb077_wpp_notmem_0736 (F : Class) (I : Class) : (nb077_alpha_dummy_263 F I) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_263, fv_syn_cnnc] using (nb077_compact_fv_empty_0212 F I)

theorem nb077_wpp_notmem_0737 (x : Var) : (nb077_alpha_dummy_264 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_264, fv_syn_cnnc] using (nb077_compact_fv_empty_0213 x)

theorem nb077_wpp_notmem_0738 (F : Class) (I : Class) : (nb077_alpha_dummy_255 F I) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_255, fv_syn_cnnc] using (nb077_compact_fv_empty_0214 F I)

theorem nb077_wpp_notmem_0739 (x : Var) : (nb077_alpha_dummy_256 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_256, fv_syn_cnnc] using (nb077_compact_fv_empty_0215 x)

theorem nb077_wpp_notmem_0740 (F : Class) (I : Class) : (nb077_alpha_dummy_000 F I) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_000, fv_syn_cnnc] using (nb077_compact_fv_empty_0216 F I)

theorem nb077_wpp_notmem_0741 (x : Var) : x ∉ ((syn_cnnc)).fv := by
  simpa only [fv_syn_cnnc] using (nb077_compact_fv_empty_0217 x)

theorem nb077_wpp_notmem_0742 (F : Class) (I : Class) : (nb077_alpha_dummy_257 F I) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_257, fv_syn_cnnc] using (nb077_compact_fv_empty_0218 F I)

theorem nb077_wpp_notmem_0743 (x : Var) : (nb077_alpha_dummy_258 x) ∉ ((syn_cnnc)).fv := by
  simpa only [nb077_alpha_dummy_258, fv_syn_cnnc] using (nb077_compact_fv_empty_0219 x)

theorem nb077_compact_envfresh_0047 (x : Var) (F : Class) (I : Class) : TEnvFresh [((nb077_alpha_dummy_271 F I), (nb077_alpha_dummy_272 x)), ((nb077_alpha_dummy_267 F I), (nb077_alpha_dummy_269 x)), ((nb077_alpha_dummy_268 F I), (nb077_alpha_dummy_270 x)), ((nb077_alpha_dummy_260 F I), (nb077_alpha_dummy_262 x)), ((nb077_alpha_dummy_259 F I), (nb077_alpha_dummy_261 x)), ((nb077_alpha_dummy_265 F I), (nb077_alpha_dummy_266 x)), ((nb077_alpha_dummy_263 F I), (nb077_alpha_dummy_264 x)), ((nb077_alpha_dummy_255 F I), (nb077_alpha_dummy_256 x)), ((nb077_alpha_dummy_000 F I), x), ((nb077_alpha_dummy_257 F I), (nb077_alpha_dummy_258 x)), ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb077_alpha_dummy_271 F I) (nb077_alpha_dummy_272 x) (nb077_wpp_notmem_0724 F I) (nb077_wpp_notmem_0725 x) (TEnvFresh.consFresh (nb077_alpha_dummy_267 F I) (nb077_alpha_dummy_269 x) (nb077_wpp_notmem_0726 F I) (nb077_wpp_notmem_0727 x) (TEnvFresh.consFresh (nb077_alpha_dummy_268 F I) (nb077_alpha_dummy_270 x) (nb077_wpp_notmem_0728 F I) (nb077_wpp_notmem_0729 x) (TEnvFresh.consFresh (nb077_alpha_dummy_260 F I) (nb077_alpha_dummy_262 x) (nb077_wpp_notmem_0730 F I) (nb077_wpp_notmem_0731 x) (TEnvFresh.consFresh (nb077_alpha_dummy_259 F I) (nb077_alpha_dummy_261 x) (nb077_wpp_notmem_0732 F I) (nb077_wpp_notmem_0733 x) (TEnvFresh.consFresh (nb077_alpha_dummy_265 F I) (nb077_alpha_dummy_266 x) (nb077_wpp_notmem_0734 F I) (nb077_wpp_notmem_0735 x) (TEnvFresh.consFresh (nb077_alpha_dummy_263 F I) (nb077_alpha_dummy_264 x) (nb077_wpp_notmem_0736 F I) (nb077_wpp_notmem_0737 x) (TEnvFresh.consFresh (nb077_alpha_dummy_255 F I) (nb077_alpha_dummy_256 x) (nb077_wpp_notmem_0738 F I) (nb077_wpp_notmem_0739 x) (TEnvFresh.consFresh (nb077_alpha_dummy_000 F I) x (nb077_wpp_notmem_0740 F I) (nb077_wpp_notmem_0741 x) (TEnvFresh.consFresh (nb077_alpha_dummy_257 F I) (nb077_alpha_dummy_258 x) (nb077_wpp_notmem_0742 F I) (nb077_wpp_notmem_0743 x) (TEnvFresh.consFresh (nb077_alpha_dummy_141 F I) (nb077_alpha_dummy_144 x) (nb077_wpp_notmem_0524 F I) (nb077_wpp_notmem_0525 x) (TEnvFresh.consFresh (nb077_alpha_dummy_140 F I) (nb077_alpha_dummy_143 x) (nb077_wpp_notmem_0426 F I) (nb077_wpp_notmem_0427 x) (TEnvFresh.consFresh (nb077_alpha_dummy_139 F I) (nb077_alpha_dummy_142 x) (nb077_wpp_notmem_0428 F I) (nb077_wpp_notmem_0429 x) (TEnvFresh.consFresh (nb077_alpha_dummy_145 F I) (nb077_alpha_dummy_146 x) (nb077_wpp_notmem_0430 F I) (nb077_wpp_notmem_0431 x) (TEnvFresh.consFresh (nb077_alpha_dummy_061 F I) (nb077_alpha_dummy_064 x) (nb077_wpp_notmem_0328 F I) (nb077_wpp_notmem_0329 x) (TEnvFresh.consFresh (nb077_alpha_dummy_060 F I) (nb077_alpha_dummy_063 x) (nb077_wpp_notmem_0222 F I) (nb077_wpp_notmem_0223 x) (TEnvFresh.consFresh (nb077_alpha_dummy_059 F I) (nb077_alpha_dummy_062 x) (nb077_wpp_notmem_0224 F I) (nb077_wpp_notmem_0225 x) (TEnvFresh.consFresh (nb077_alpha_dummy_065 F I) (nb077_alpha_dummy_066 x) (nb077_wpp_notmem_0226 F I) (nb077_wpp_notmem_0227 x) (TEnvFresh.consFresh (nb077_alpha_dummy_057 F I) (nb077_alpha_dummy_058 x F) (nb077_wpp_notmem_0228 F I) (nb077_wpp_notmem_0229 x F) (TEnvFresh.consFresh (nb077_alpha_dummy_055 F I) (nb077_alpha_dummy_056 x F) (nb077_wpp_notmem_0230 F I) (nb077_wpp_notmem_0231 x F) (TEnvFresh.consFresh (nb077_alpha_dummy_016 F I) (nb077_alpha_dummy_018 x F I) (nb077_wpp_notmem_0092 F I) (nb077_wpp_notmem_0093 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_015 F I) (nb077_alpha_dummy_017 x F I) (nb077_wpp_notmem_0094 F I) (nb077_wpp_notmem_0095 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_013 F I) (nb077_alpha_dummy_014 x F I) (nb077_wpp_notmem_0096 F I) (nb077_wpp_notmem_0097 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_011 F I) (nb077_alpha_dummy_012 x F I) (nb077_wpp_notmem_0098 F I) (nb077_wpp_notmem_0099 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_001 F I) (nb077_alpha_dummy_002 x F I) (nb077_wpp_notmem_0100 F I) (nb077_wpp_notmem_0101 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_004 F I) (nb077_alpha_dummy_006 x F I) (nb077_wpp_notmem_0102 F I) (nb077_wpp_notmem_0103 x F I) (TEnvFresh.consFresh (nb077_alpha_dummy_003 F I) (nb077_alpha_dummy_005 x F I) (nb077_wpp_notmem_0104 F I) (nb077_wpp_notmem_0105 x F I) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))))))))))))))

noncomputable def nb077_wpp_refl_0047 (x : Var) (F : Class) (I : Class) : TReflOn [((nb077_alpha_dummy_271 F I), (nb077_alpha_dummy_272 x)), ((nb077_alpha_dummy_267 F I), (nb077_alpha_dummy_269 x)), ((nb077_alpha_dummy_268 F I), (nb077_alpha_dummy_270 x)), ((nb077_alpha_dummy_260 F I), (nb077_alpha_dummy_262 x)), ((nb077_alpha_dummy_259 F I), (nb077_alpha_dummy_261 x)), ((nb077_alpha_dummy_265 F I), (nb077_alpha_dummy_266 x)), ((nb077_alpha_dummy_263 F I), (nb077_alpha_dummy_264 x)), ((nb077_alpha_dummy_255 F I), (nb077_alpha_dummy_256 x)), ((nb077_alpha_dummy_000 F I), x), ((nb077_alpha_dummy_257 F I), (nb077_alpha_dummy_258 x)), ((nb077_alpha_dummy_141 F I), (nb077_alpha_dummy_144 x)), ((nb077_alpha_dummy_140 F I), (nb077_alpha_dummy_143 x)), ((nb077_alpha_dummy_139 F I), (nb077_alpha_dummy_142 x)), ((nb077_alpha_dummy_145 F I), (nb077_alpha_dummy_146 x)), ((nb077_alpha_dummy_061 F I), (nb077_alpha_dummy_064 x)), ((nb077_alpha_dummy_060 F I), (nb077_alpha_dummy_063 x)), ((nb077_alpha_dummy_059 F I), (nb077_alpha_dummy_062 x)), ((nb077_alpha_dummy_065 F I), (nb077_alpha_dummy_066 x)), ((nb077_alpha_dummy_057 F I), (nb077_alpha_dummy_058 x F)), ((nb077_alpha_dummy_055 F I), (nb077_alpha_dummy_056 x F)), ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)), ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)), ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)), ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)), ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)), ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)), ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb077_compact_envfresh_0047 x F I)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
