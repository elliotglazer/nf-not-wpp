import NAR4C090C001Part045

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

theorem nb090_compact_fv_empty_0201 (h : Var) : (nb090_alpha_dummy_249 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0641 (h : Var) : (nb090_alpha_dummy_249 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_249, fv_syn_c1c] using (nb090_compact_fv_empty_0201 h)

theorem nb090_compact_fv_empty_0202 (A : Class) : (nb090_alpha_dummy_253 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0642 (A : Class) : (nb090_alpha_dummy_253 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_253, fv_syn_c1c] using (nb090_compact_fv_empty_0202 A)

theorem nb090_compact_fv_empty_0203 (h : Var) : (nb090_alpha_dummy_254 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0643 (h : Var) : (nb090_alpha_dummy_254 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_254, fv_syn_c1c] using (nb090_compact_fv_empty_0203 h)

theorem nb090_compact_fv_empty_0204 (A : Class) : (nb090_alpha_dummy_251 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0644 (A : Class) : (nb090_alpha_dummy_251 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_251, fv_syn_c1c] using (nb090_compact_fv_empty_0204 A)

theorem nb090_compact_fv_empty_0205 (h : Var) : (nb090_alpha_dummy_252 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0645 (h : Var) : (nb090_alpha_dummy_252 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_252, fv_syn_c1c] using (nb090_compact_fv_empty_0205 h)

theorem nb090_wpp_notmem_0646 (A : Class) : (nb090_alpha_dummy_244 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_244, fv_syn_c1c] using (nb090_compact_fv_empty_0182 A)

theorem nb090_wpp_notmem_0647 (h : Var) : (nb090_alpha_dummy_246 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_246, fv_syn_c1c] using (nb090_compact_fv_empty_0183 h)

theorem nb090_wpp_notmem_0648 (A : Class) : (nb090_alpha_dummy_243 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_243, fv_syn_c1c] using (nb090_compact_fv_empty_0184 A)

theorem nb090_wpp_notmem_0649 (h : Var) : (nb090_alpha_dummy_245 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_245, fv_syn_c1c] using (nb090_compact_fv_empty_0185 h)

theorem nb090_compact_envfresh_0080 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_263 A), (nb090_alpha_dummy_266 h)), ((nb090_alpha_dummy_262 A), (nb090_alpha_dummy_265 h)), ((nb090_alpha_dummy_261 A), (nb090_alpha_dummy_264 h)), ((nb090_alpha_dummy_259 A), (nb090_alpha_dummy_260 h)), ((nb090_alpha_dummy_255 A), (nb090_alpha_dummy_257 h)), ((nb090_alpha_dummy_256 A), (nb090_alpha_dummy_258 h)), ((nb090_alpha_dummy_248 A), (nb090_alpha_dummy_250 h)), ((nb090_alpha_dummy_247 A), (nb090_alpha_dummy_249 h)), ((nb090_alpha_dummy_253 A), (nb090_alpha_dummy_254 h)), ((nb090_alpha_dummy_251 A), (nb090_alpha_dummy_252 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_263 A) (nb090_alpha_dummy_266 h) (nb090_wpp_notmem_0626 A) (nb090_wpp_notmem_0627 h) (TEnvFresh.consFresh (nb090_alpha_dummy_262 A) (nb090_alpha_dummy_265 h) (nb090_wpp_notmem_0628 A) (nb090_wpp_notmem_0629 h) (TEnvFresh.consFresh (nb090_alpha_dummy_261 A) (nb090_alpha_dummy_264 h) (nb090_wpp_notmem_0630 A) (nb090_wpp_notmem_0631 h) (TEnvFresh.consFresh (nb090_alpha_dummy_259 A) (nb090_alpha_dummy_260 h) (nb090_wpp_notmem_0632 A) (nb090_wpp_notmem_0633 h) (TEnvFresh.consFresh (nb090_alpha_dummy_255 A) (nb090_alpha_dummy_257 h) (nb090_wpp_notmem_0634 A) (nb090_wpp_notmem_0635 h) (TEnvFresh.consFresh (nb090_alpha_dummy_256 A) (nb090_alpha_dummy_258 h) (nb090_wpp_notmem_0636 A) (nb090_wpp_notmem_0637 h) (TEnvFresh.consFresh (nb090_alpha_dummy_248 A) (nb090_alpha_dummy_250 h) (nb090_wpp_notmem_0638 A) (nb090_wpp_notmem_0639 h) (TEnvFresh.consFresh (nb090_alpha_dummy_247 A) (nb090_alpha_dummy_249 h) (nb090_wpp_notmem_0640 A) (nb090_wpp_notmem_0641 h) (TEnvFresh.consFresh (nb090_alpha_dummy_253 A) (nb090_alpha_dummy_254 h) (nb090_wpp_notmem_0642 A) (nb090_wpp_notmem_0643 h) (TEnvFresh.consFresh (nb090_alpha_dummy_251 A) (nb090_alpha_dummy_252 h) (nb090_wpp_notmem_0644 A) (nb090_wpp_notmem_0645 h) (TEnvFresh.consFresh (nb090_alpha_dummy_244 A) (nb090_alpha_dummy_246 h) (nb090_wpp_notmem_0646 A) (nb090_wpp_notmem_0647 h) (TEnvFresh.consFresh (nb090_alpha_dummy_243 A) (nb090_alpha_dummy_245 h) (nb090_wpp_notmem_0648 A) (nb090_wpp_notmem_0649 h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0142 A) (nb090_wpp_notmem_0143 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0020 A) (nb090_wpp_notmem_0021 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0022 A) (nb090_wpp_notmem_0023 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0024 A) (nb090_wpp_notmem_0025 v u A h) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))

noncomputable def nb090_wpp_refl_0080 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_263 A), (nb090_alpha_dummy_266 h)), ((nb090_alpha_dummy_262 A), (nb090_alpha_dummy_265 h)), ((nb090_alpha_dummy_261 A), (nb090_alpha_dummy_264 h)), ((nb090_alpha_dummy_259 A), (nb090_alpha_dummy_260 h)), ((nb090_alpha_dummy_255 A), (nb090_alpha_dummy_257 h)), ((nb090_alpha_dummy_256 A), (nb090_alpha_dummy_258 h)), ((nb090_alpha_dummy_248 A), (nb090_alpha_dummy_250 h)), ((nb090_alpha_dummy_247 A), (nb090_alpha_dummy_249 h)), ((nb090_alpha_dummy_253 A), (nb090_alpha_dummy_254 h)), ((nb090_alpha_dummy_251 A), (nb090_alpha_dummy_252 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0080 v u A h)

theorem nb090_wpp_notmem_0650 (A : Class) : (nb090_alpha_dummy_263 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_263, fv_syn_c0] using (nb090_compact_fv_empty_0186 A)

theorem nb090_wpp_notmem_0651 (h : Var) : (nb090_alpha_dummy_266 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_266, fv_syn_c0] using (nb090_compact_fv_empty_0187 h)

theorem nb090_wpp_notmem_0652 (A : Class) : (nb090_alpha_dummy_262 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_262, fv_syn_c0] using (nb090_compact_fv_empty_0188 A)

theorem nb090_wpp_notmem_0653 (h : Var) : (nb090_alpha_dummy_265 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_265, fv_syn_c0] using (nb090_compact_fv_empty_0189 h)

theorem nb090_wpp_notmem_0654 (A : Class) : (nb090_alpha_dummy_261 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_261, fv_syn_c0] using (nb090_compact_fv_empty_0190 A)

theorem nb090_wpp_notmem_0655 (h : Var) : (nb090_alpha_dummy_264 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_264, fv_syn_c0] using (nb090_compact_fv_empty_0191 h)

theorem nb090_wpp_notmem_0656 (A : Class) : (nb090_alpha_dummy_259 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_259, fv_syn_c0] using (nb090_compact_fv_empty_0192 A)

theorem nb090_wpp_notmem_0657 (h : Var) : (nb090_alpha_dummy_260 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_260, fv_syn_c0] using (nb090_compact_fv_empty_0193 h)

theorem nb090_wpp_notmem_0658 (A : Class) : (nb090_alpha_dummy_255 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_255, fv_syn_c0] using (nb090_compact_fv_empty_0194 A)

theorem nb090_wpp_notmem_0659 (h : Var) : (nb090_alpha_dummy_257 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_257, fv_syn_c0] using (nb090_compact_fv_empty_0195 h)

theorem nb090_wpp_notmem_0660 (A : Class) : (nb090_alpha_dummy_256 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_256, fv_syn_c0] using (nb090_compact_fv_empty_0196 A)

theorem nb090_wpp_notmem_0661 (h : Var) : (nb090_alpha_dummy_258 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_258, fv_syn_c0] using (nb090_compact_fv_empty_0197 h)

theorem nb090_wpp_notmem_0662 (A : Class) : (nb090_alpha_dummy_248 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_248, fv_syn_c0] using (nb090_compact_fv_empty_0198 A)

theorem nb090_wpp_notmem_0663 (h : Var) : (nb090_alpha_dummy_250 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_250, fv_syn_c0] using (nb090_compact_fv_empty_0199 h)

theorem nb090_wpp_notmem_0664 (A : Class) : (nb090_alpha_dummy_247 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_247, fv_syn_c0] using (nb090_compact_fv_empty_0200 A)

theorem nb090_wpp_notmem_0665 (h : Var) : (nb090_alpha_dummy_249 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_249, fv_syn_c0] using (nb090_compact_fv_empty_0201 h)

theorem nb090_wpp_notmem_0666 (A : Class) : (nb090_alpha_dummy_253 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_253, fv_syn_c0] using (nb090_compact_fv_empty_0202 A)

theorem nb090_wpp_notmem_0667 (h : Var) : (nb090_alpha_dummy_254 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_254, fv_syn_c0] using (nb090_compact_fv_empty_0203 h)

theorem nb090_wpp_notmem_0668 (A : Class) : (nb090_alpha_dummy_251 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_251, fv_syn_c0] using (nb090_compact_fv_empty_0204 A)

theorem nb090_wpp_notmem_0669 (h : Var) : (nb090_alpha_dummy_252 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_252, fv_syn_c0] using (nb090_compact_fv_empty_0205 h)

theorem nb090_wpp_notmem_0670 (A : Class) : (nb090_alpha_dummy_244 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_244, fv_syn_c0] using (nb090_compact_fv_empty_0182 A)

theorem nb090_wpp_notmem_0671 (h : Var) : (nb090_alpha_dummy_246 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_246, fv_syn_c0] using (nb090_compact_fv_empty_0183 h)

theorem nb090_wpp_notmem_0672 (A : Class) : (nb090_alpha_dummy_243 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_243, fv_syn_c0] using (nb090_compact_fv_empty_0184 A)

theorem nb090_wpp_notmem_0673 (h : Var) : (nb090_alpha_dummy_245 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_245, fv_syn_c0] using (nb090_compact_fv_empty_0185 h)

theorem nb090_compact_envfresh_0081 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_263 A), (nb090_alpha_dummy_266 h)), ((nb090_alpha_dummy_262 A), (nb090_alpha_dummy_265 h)), ((nb090_alpha_dummy_261 A), (nb090_alpha_dummy_264 h)), ((nb090_alpha_dummy_259 A), (nb090_alpha_dummy_260 h)), ((nb090_alpha_dummy_255 A), (nb090_alpha_dummy_257 h)), ((nb090_alpha_dummy_256 A), (nb090_alpha_dummy_258 h)), ((nb090_alpha_dummy_248 A), (nb090_alpha_dummy_250 h)), ((nb090_alpha_dummy_247 A), (nb090_alpha_dummy_249 h)), ((nb090_alpha_dummy_253 A), (nb090_alpha_dummy_254 h)), ((nb090_alpha_dummy_251 A), (nb090_alpha_dummy_252 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_263 A) (nb090_alpha_dummy_266 h) (nb090_wpp_notmem_0650 A) (nb090_wpp_notmem_0651 h) (TEnvFresh.consFresh (nb090_alpha_dummy_262 A) (nb090_alpha_dummy_265 h) (nb090_wpp_notmem_0652 A) (nb090_wpp_notmem_0653 h) (TEnvFresh.consFresh (nb090_alpha_dummy_261 A) (nb090_alpha_dummy_264 h) (nb090_wpp_notmem_0654 A) (nb090_wpp_notmem_0655 h) (TEnvFresh.consFresh (nb090_alpha_dummy_259 A) (nb090_alpha_dummy_260 h) (nb090_wpp_notmem_0656 A) (nb090_wpp_notmem_0657 h) (TEnvFresh.consFresh (nb090_alpha_dummy_255 A) (nb090_alpha_dummy_257 h) (nb090_wpp_notmem_0658 A) (nb090_wpp_notmem_0659 h) (TEnvFresh.consFresh (nb090_alpha_dummy_256 A) (nb090_alpha_dummy_258 h) (nb090_wpp_notmem_0660 A) (nb090_wpp_notmem_0661 h) (TEnvFresh.consFresh (nb090_alpha_dummy_248 A) (nb090_alpha_dummy_250 h) (nb090_wpp_notmem_0662 A) (nb090_wpp_notmem_0663 h) (TEnvFresh.consFresh (nb090_alpha_dummy_247 A) (nb090_alpha_dummy_249 h) (nb090_wpp_notmem_0664 A) (nb090_wpp_notmem_0665 h) (TEnvFresh.consFresh (nb090_alpha_dummy_253 A) (nb090_alpha_dummy_254 h) (nb090_wpp_notmem_0666 A) (nb090_wpp_notmem_0667 h) (TEnvFresh.consFresh (nb090_alpha_dummy_251 A) (nb090_alpha_dummy_252 h) (nb090_wpp_notmem_0668 A) (nb090_wpp_notmem_0669 h) (TEnvFresh.consFresh (nb090_alpha_dummy_244 A) (nb090_alpha_dummy_246 h) (nb090_wpp_notmem_0670 A) (nb090_wpp_notmem_0671 h) (TEnvFresh.consFresh (nb090_alpha_dummy_243 A) (nb090_alpha_dummy_245 h) (nb090_wpp_notmem_0672 A) (nb090_wpp_notmem_0673 h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0174 A) (nb090_wpp_notmem_0175 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0046 A) (nb090_wpp_notmem_0047 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0048 A) (nb090_wpp_notmem_0049 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0050 A) (nb090_wpp_notmem_0051 v u A h) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))

noncomputable def nb090_wpp_refl_0081 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_263 A), (nb090_alpha_dummy_266 h)), ((nb090_alpha_dummy_262 A), (nb090_alpha_dummy_265 h)), ((nb090_alpha_dummy_261 A), (nb090_alpha_dummy_264 h)), ((nb090_alpha_dummy_259 A), (nb090_alpha_dummy_260 h)), ((nb090_alpha_dummy_255 A), (nb090_alpha_dummy_257 h)), ((nb090_alpha_dummy_256 A), (nb090_alpha_dummy_258 h)), ((nb090_alpha_dummy_248 A), (nb090_alpha_dummy_250 h)), ((nb090_alpha_dummy_247 A), (nb090_alpha_dummy_249 h)), ((nb090_alpha_dummy_253 A), (nb090_alpha_dummy_254 h)), ((nb090_alpha_dummy_251 A), (nb090_alpha_dummy_252 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0081 v u A h)

theorem nb090_wpp_notmem_0674 (A : Class) : (nb090_alpha_dummy_259 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_259, fv_syn_cnnc] using (nb090_compact_fv_empty_0192 A)

theorem nb090_wpp_notmem_0675 (h : Var) : (nb090_alpha_dummy_260 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_260, fv_syn_cnnc] using (nb090_compact_fv_empty_0193 h)

theorem nb090_wpp_notmem_0676 (A : Class) : (nb090_alpha_dummy_255 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_255, fv_syn_cnnc] using (nb090_compact_fv_empty_0194 A)

theorem nb090_wpp_notmem_0677 (h : Var) : (nb090_alpha_dummy_257 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_257, fv_syn_cnnc] using (nb090_compact_fv_empty_0195 h)

theorem nb090_wpp_notmem_0678 (A : Class) : (nb090_alpha_dummy_256 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_256, fv_syn_cnnc] using (nb090_compact_fv_empty_0196 A)

theorem nb090_wpp_notmem_0679 (h : Var) : (nb090_alpha_dummy_258 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_258, fv_syn_cnnc] using (nb090_compact_fv_empty_0197 h)

theorem nb090_wpp_notmem_0680 (A : Class) : (nb090_alpha_dummy_248 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_248, fv_syn_cnnc] using (nb090_compact_fv_empty_0198 A)

theorem nb090_wpp_notmem_0681 (h : Var) : (nb090_alpha_dummy_250 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_250, fv_syn_cnnc] using (nb090_compact_fv_empty_0199 h)

theorem nb090_wpp_notmem_0682 (A : Class) : (nb090_alpha_dummy_247 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_247, fv_syn_cnnc] using (nb090_compact_fv_empty_0200 A)

theorem nb090_wpp_notmem_0683 (h : Var) : (nb090_alpha_dummy_249 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_249, fv_syn_cnnc] using (nb090_compact_fv_empty_0201 h)

theorem nb090_wpp_notmem_0684 (A : Class) : (nb090_alpha_dummy_253 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_253, fv_syn_cnnc] using (nb090_compact_fv_empty_0202 A)

theorem nb090_wpp_notmem_0685 (h : Var) : (nb090_alpha_dummy_254 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_254, fv_syn_cnnc] using (nb090_compact_fv_empty_0203 h)

theorem nb090_wpp_notmem_0686 (A : Class) : (nb090_alpha_dummy_251 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_251, fv_syn_cnnc] using (nb090_compact_fv_empty_0204 A)

theorem nb090_wpp_notmem_0687 (h : Var) : (nb090_alpha_dummy_252 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_252, fv_syn_cnnc] using (nb090_compact_fv_empty_0205 h)

theorem nb090_wpp_notmem_0688 (A : Class) : (nb090_alpha_dummy_244 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_244, fv_syn_cnnc] using (nb090_compact_fv_empty_0182 A)

theorem nb090_wpp_notmem_0689 (h : Var) : (nb090_alpha_dummy_246 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_246, fv_syn_cnnc] using (nb090_compact_fv_empty_0183 h)

theorem nb090_wpp_notmem_0690 (A : Class) : (nb090_alpha_dummy_243 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_243, fv_syn_cnnc] using (nb090_compact_fv_empty_0184 A)

theorem nb090_wpp_notmem_0691 (h : Var) : (nb090_alpha_dummy_245 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_245, fv_syn_cnnc] using (nb090_compact_fv_empty_0185 h)

theorem nb090_compact_envfresh_0082 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_259 A), (nb090_alpha_dummy_260 h)), ((nb090_alpha_dummy_255 A), (nb090_alpha_dummy_257 h)), ((nb090_alpha_dummy_256 A), (nb090_alpha_dummy_258 h)), ((nb090_alpha_dummy_248 A), (nb090_alpha_dummy_250 h)), ((nb090_alpha_dummy_247 A), (nb090_alpha_dummy_249 h)), ((nb090_alpha_dummy_253 A), (nb090_alpha_dummy_254 h)), ((nb090_alpha_dummy_251 A), (nb090_alpha_dummy_252 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_259 A) (nb090_alpha_dummy_260 h) (nb090_wpp_notmem_0674 A) (nb090_wpp_notmem_0675 h) (TEnvFresh.consFresh (nb090_alpha_dummy_255 A) (nb090_alpha_dummy_257 h) (nb090_wpp_notmem_0676 A) (nb090_wpp_notmem_0677 h) (TEnvFresh.consFresh (nb090_alpha_dummy_256 A) (nb090_alpha_dummy_258 h) (nb090_wpp_notmem_0678 A) (nb090_wpp_notmem_0679 h) (TEnvFresh.consFresh (nb090_alpha_dummy_248 A) (nb090_alpha_dummy_250 h) (nb090_wpp_notmem_0680 A) (nb090_wpp_notmem_0681 h) (TEnvFresh.consFresh (nb090_alpha_dummy_247 A) (nb090_alpha_dummy_249 h) (nb090_wpp_notmem_0682 A) (nb090_wpp_notmem_0683 h) (TEnvFresh.consFresh (nb090_alpha_dummy_253 A) (nb090_alpha_dummy_254 h) (nb090_wpp_notmem_0684 A) (nb090_wpp_notmem_0685 h) (TEnvFresh.consFresh (nb090_alpha_dummy_251 A) (nb090_alpha_dummy_252 h) (nb090_wpp_notmem_0686 A) (nb090_wpp_notmem_0687 h) (TEnvFresh.consFresh (nb090_alpha_dummy_244 A) (nb090_alpha_dummy_246 h) (nb090_wpp_notmem_0688 A) (nb090_wpp_notmem_0689 h) (TEnvFresh.consFresh (nb090_alpha_dummy_243 A) (nb090_alpha_dummy_245 h) (nb090_wpp_notmem_0690 A) (nb090_wpp_notmem_0691 h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0200 A) (nb090_wpp_notmem_0201 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0066 A) (nb090_wpp_notmem_0067 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0068 A) (nb090_wpp_notmem_0069 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0070 A) (nb090_wpp_notmem_0071 v u A h) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))

noncomputable def nb090_wpp_refl_0082 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_259 A), (nb090_alpha_dummy_260 h)), ((nb090_alpha_dummy_255 A), (nb090_alpha_dummy_257 h)), ((nb090_alpha_dummy_256 A), (nb090_alpha_dummy_258 h)), ((nb090_alpha_dummy_248 A), (nb090_alpha_dummy_250 h)), ((nb090_alpha_dummy_247 A), (nb090_alpha_dummy_249 h)), ((nb090_alpha_dummy_253 A), (nb090_alpha_dummy_254 h)), ((nb090_alpha_dummy_251 A), (nb090_alpha_dummy_252 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0082 v u A h)

noncomputable def nb090_split_alpha_0023 (v : Var) (u : Var) (A : Class) (h : Var) : TAlphaWff [((nb090_alpha_dummy_251 A), (nb090_alpha_dummy_252 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (Wff.classMem (Class.cv (nb090_alpha_dummy_251 A)) (syn_ccompl (Class.cab (nb090_alpha_dummy_247 A) (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_244 A)) (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))))))) (Wff.classMem (Class.cv (nb090_alpha_dummy_252 h)) (syn_ccompl (Class.cab (nb090_alpha_dummy_249 h) (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_246 h)) (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h)) (syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0252 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0254 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0252 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0254 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0256 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0257 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0253 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0255 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_244 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_243 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_246 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_245 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0258 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0259 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0258 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0259 h) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_248 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_250 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0262 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0263 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0262 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0263 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0260 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0261 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_263 A), (nb090_alpha_dummy_266 h)), ((nb090_alpha_dummy_262 A), (nb090_alpha_dummy_265 h)), ((nb090_alpha_dummy_261 A), (nb090_alpha_dummy_264 h)), ((nb090_alpha_dummy_259 A), (nb090_alpha_dummy_260 h)), ((nb090_alpha_dummy_255 A), (nb090_alpha_dummy_257 h)), ((nb090_alpha_dummy_256 A), (nb090_alpha_dummy_258 h)), ((nb090_alpha_dummy_248 A), (nb090_alpha_dummy_250 h)), ((nb090_alpha_dummy_247 A), (nb090_alpha_dummy_249 h)), ((nb090_alpha_dummy_253 A), (nb090_alpha_dummy_254 h)), ((nb090_alpha_dummy_251 A), (nb090_alpha_dummy_252 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (nb090_wpp_refl_0080 v u A h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0266 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0267 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0264 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0265 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0270 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0271 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0268 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0269 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0266 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0267 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0264 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0265 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0270 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0271 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0268 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0269 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_263 A), (nb090_alpha_dummy_266 h)), ((nb090_alpha_dummy_262 A), (nb090_alpha_dummy_265 h)), ((nb090_alpha_dummy_261 A), (nb090_alpha_dummy_264 h)), ((nb090_alpha_dummy_259 A), (nb090_alpha_dummy_260 h)), ((nb090_alpha_dummy_255 A), (nb090_alpha_dummy_257 h)), ((nb090_alpha_dummy_256 A), (nb090_alpha_dummy_258 h)), ((nb090_alpha_dummy_248 A), (nb090_alpha_dummy_250 h)), ((nb090_alpha_dummy_247 A), (nb090_alpha_dummy_249 h)), ((nb090_alpha_dummy_253 A), (nb090_alpha_dummy_254 h)), ((nb090_alpha_dummy_251 A), (nb090_alpha_dummy_252 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c0) (nb090_wpp_refl_0081 v u A h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0274 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0275 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0272 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0273 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0274 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0275 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0272 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0273 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0278 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0279 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0276 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0277 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0278 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0279 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0276 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0277 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0260 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0261 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_259 A), (nb090_alpha_dummy_260 h)), ((nb090_alpha_dummy_255 A), (nb090_alpha_dummy_257 h)), ((nb090_alpha_dummy_256 A), (nb090_alpha_dummy_258 h)), ((nb090_alpha_dummy_248 A), (nb090_alpha_dummy_250 h)), ((nb090_alpha_dummy_247 A), (nb090_alpha_dummy_249 h)), ((nb090_alpha_dummy_253 A), (nb090_alpha_dummy_254 h)), ((nb090_alpha_dummy_251 A), (nb090_alpha_dummy_252 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0082 v u A h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0260 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0261 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0260 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0261 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_259 A), (nb090_alpha_dummy_260 h)), ((nb090_alpha_dummy_255 A), (nb090_alpha_dummy_257 h)), ((nb090_alpha_dummy_256 A), (nb090_alpha_dummy_258 h)), ((nb090_alpha_dummy_248 A), (nb090_alpha_dummy_250 h)), ((nb090_alpha_dummy_247 A), (nb090_alpha_dummy_249 h)), ((nb090_alpha_dummy_253 A), (nb090_alpha_dummy_254 h)), ((nb090_alpha_dummy_251 A), (nb090_alpha_dummy_252 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0082 v u A h)))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0252 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0254 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0252 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0254 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0256 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0257 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0253 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0255 h) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_244 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_243 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_246 h))).fv ∪ ((Class.cv (nb090_alpha_dummy_245 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0258 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0259 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0258 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0259 h) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_248 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_250 h))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0262 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0263 h) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0262 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0263 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0260 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0261 h) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_263 A), (nb090_alpha_dummy_266 h)), ((nb090_alpha_dummy_262 A), (nb090_alpha_dummy_265 h)), ((nb090_alpha_dummy_261 A), (nb090_alpha_dummy_264 h)), ((nb090_alpha_dummy_259 A), (nb090_alpha_dummy_260 h)), ((nb090_alpha_dummy_255 A), (nb090_alpha_dummy_257 h)), ((nb090_alpha_dummy_256 A), (nb090_alpha_dummy_258 h)), ((nb090_alpha_dummy_248 A), (nb090_alpha_dummy_250 h)), ((nb090_alpha_dummy_247 A), (nb090_alpha_dummy_249 h)), ((nb090_alpha_dummy_253 A), (nb090_alpha_dummy_254 h)), ((nb090_alpha_dummy_251 A), (nb090_alpha_dummy_252 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (nb090_wpp_refl_0080 v u A h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0266 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0267 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0264 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0265 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0270 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0271 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0268 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0269 h) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0266 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0267 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0264 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0265 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0270 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0271 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0268 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0269 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_263 A), (nb090_alpha_dummy_266 h)), ((nb090_alpha_dummy_262 A), (nb090_alpha_dummy_265 h)), ((nb090_alpha_dummy_261 A), (nb090_alpha_dummy_264 h)), ((nb090_alpha_dummy_259 A), (nb090_alpha_dummy_260 h)), ((nb090_alpha_dummy_255 A), (nb090_alpha_dummy_257 h)), ((nb090_alpha_dummy_256 A), (nb090_alpha_dummy_258 h)), ((nb090_alpha_dummy_248 A), (nb090_alpha_dummy_250 h)), ((nb090_alpha_dummy_247 A), (nb090_alpha_dummy_249 h)), ((nb090_alpha_dummy_253 A), (nb090_alpha_dummy_254 h)), ((nb090_alpha_dummy_251 A), (nb090_alpha_dummy_252 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c0) (nb090_wpp_refl_0081 v u A h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0274 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0275 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0272 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0273 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0274 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0275 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0272 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0273 h) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0278 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0279 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0276 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0277 h) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0278 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0279 h) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0276 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0277 h) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0260 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0261 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_259 A), (nb090_alpha_dummy_260 h)), ((nb090_alpha_dummy_255 A), (nb090_alpha_dummy_257 h)), ((nb090_alpha_dummy_256 A), (nb090_alpha_dummy_258 h)), ((nb090_alpha_dummy_248 A), (nb090_alpha_dummy_250 h)), ((nb090_alpha_dummy_247 A), (nb090_alpha_dummy_249 h)), ((nb090_alpha_dummy_253 A), (nb090_alpha_dummy_254 h)), ((nb090_alpha_dummy_251 A), (nb090_alpha_dummy_252 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0082 v u A h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0260 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0261 h) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0260 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0261 h) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_259 A), (nb090_alpha_dummy_260 h)), ((nb090_alpha_dummy_255 A), (nb090_alpha_dummy_257 h)), ((nb090_alpha_dummy_256 A), (nb090_alpha_dummy_258 h)), ((nb090_alpha_dummy_248 A), (nb090_alpha_dummy_250 h)), ((nb090_alpha_dummy_247 A), (nb090_alpha_dummy_249 h)), ((nb090_alpha_dummy_253 A), (nb090_alpha_dummy_254 h)), ((nb090_alpha_dummy_251 A), (nb090_alpha_dummy_252 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0082 v u A h))))))))))))))))))))))))))))))))

theorem nb090_compact_fv_empty_0206 (A : Class) : (nb090_alpha_dummy_281 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0692 (A : Class) : (nb090_alpha_dummy_281 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_281, fv_syn_c1c] using (nb090_compact_fv_empty_0206 A)

theorem nb090_compact_fv_empty_0207 (h : Var) : (nb090_alpha_dummy_282 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0693 (h : Var) : (nb090_alpha_dummy_282 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_282, fv_syn_c1c] using (nb090_compact_fv_empty_0207 h)

theorem nb090_compact_fv_empty_0208 (A : Class) : (nb090_alpha_dummy_279 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0694 (A : Class) : (nb090_alpha_dummy_279 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_279, fv_syn_c1c] using (nb090_compact_fv_empty_0208 A)

theorem nb090_compact_fv_empty_0209 (h : Var) : (nb090_alpha_dummy_280 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0695 (h : Var) : (nb090_alpha_dummy_280 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_280, fv_syn_c1c] using (nb090_compact_fv_empty_0209 h)

theorem nb090_compact_fv_empty_0210 (A : Class) : (nb090_alpha_dummy_277 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0696 (A : Class) : (nb090_alpha_dummy_277 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_277, fv_syn_c1c] using (nb090_compact_fv_empty_0210 A)

theorem nb090_compact_fv_empty_0211 (h : Var) : (nb090_alpha_dummy_278 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0697 (h : Var) : (nb090_alpha_dummy_278 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_278, fv_syn_c1c] using (nb090_compact_fv_empty_0211 h)

theorem nb090_compact_envfresh_0083 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_263 A), (nb090_alpha_dummy_266 h)), ((nb090_alpha_dummy_262 A), (nb090_alpha_dummy_265 h)), ((nb090_alpha_dummy_261 A), (nb090_alpha_dummy_264 h)), ((nb090_alpha_dummy_259 A), (nb090_alpha_dummy_260 h)), ((nb090_alpha_dummy_255 A), (nb090_alpha_dummy_257 h)), ((nb090_alpha_dummy_256 A), (nb090_alpha_dummy_258 h)), ((nb090_alpha_dummy_281 A), (nb090_alpha_dummy_282 h)), ((nb090_alpha_dummy_279 A), (nb090_alpha_dummy_280 h)), ((nb090_alpha_dummy_248 A), (nb090_alpha_dummy_250 h)), ((nb090_alpha_dummy_247 A), (nb090_alpha_dummy_249 h)), ((nb090_alpha_dummy_277 A), (nb090_alpha_dummy_278 h)), ((nb090_alpha_dummy_251 A), (nb090_alpha_dummy_252 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_263 A) (nb090_alpha_dummy_266 h) (nb090_wpp_notmem_0626 A) (nb090_wpp_notmem_0627 h) (TEnvFresh.consFresh (nb090_alpha_dummy_262 A) (nb090_alpha_dummy_265 h) (nb090_wpp_notmem_0628 A) (nb090_wpp_notmem_0629 h) (TEnvFresh.consFresh (nb090_alpha_dummy_261 A) (nb090_alpha_dummy_264 h) (nb090_wpp_notmem_0630 A) (nb090_wpp_notmem_0631 h) (TEnvFresh.consFresh (nb090_alpha_dummy_259 A) (nb090_alpha_dummy_260 h) (nb090_wpp_notmem_0632 A) (nb090_wpp_notmem_0633 h) (TEnvFresh.consFresh (nb090_alpha_dummy_255 A) (nb090_alpha_dummy_257 h) (nb090_wpp_notmem_0634 A) (nb090_wpp_notmem_0635 h) (TEnvFresh.consFresh (nb090_alpha_dummy_256 A) (nb090_alpha_dummy_258 h) (nb090_wpp_notmem_0636 A) (nb090_wpp_notmem_0637 h) (TEnvFresh.consFresh (nb090_alpha_dummy_281 A) (nb090_alpha_dummy_282 h) (nb090_wpp_notmem_0692 A) (nb090_wpp_notmem_0693 h) (TEnvFresh.consFresh (nb090_alpha_dummy_279 A) (nb090_alpha_dummy_280 h) (nb090_wpp_notmem_0694 A) (nb090_wpp_notmem_0695 h) (TEnvFresh.consFresh (nb090_alpha_dummy_248 A) (nb090_alpha_dummy_250 h) (nb090_wpp_notmem_0638 A) (nb090_wpp_notmem_0639 h) (TEnvFresh.consFresh (nb090_alpha_dummy_247 A) (nb090_alpha_dummy_249 h) (nb090_wpp_notmem_0640 A) (nb090_wpp_notmem_0641 h) (TEnvFresh.consFresh (nb090_alpha_dummy_277 A) (nb090_alpha_dummy_278 h) (nb090_wpp_notmem_0696 A) (nb090_wpp_notmem_0697 h) (TEnvFresh.consFresh (nb090_alpha_dummy_251 A) (nb090_alpha_dummy_252 h) (nb090_wpp_notmem_0644 A) (nb090_wpp_notmem_0645 h) (TEnvFresh.consFresh (nb090_alpha_dummy_244 A) (nb090_alpha_dummy_246 h) (nb090_wpp_notmem_0646 A) (nb090_wpp_notmem_0647 h) (TEnvFresh.consFresh (nb090_alpha_dummy_243 A) (nb090_alpha_dummy_245 h) (nb090_wpp_notmem_0648 A) (nb090_wpp_notmem_0649 h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0142 A) (nb090_wpp_notmem_0143 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0020 A) (nb090_wpp_notmem_0021 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0022 A) (nb090_wpp_notmem_0023 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0024 A) (nb090_wpp_notmem_0025 v u A h) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))

noncomputable def nb090_wpp_refl_0083 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_263 A), (nb090_alpha_dummy_266 h)), ((nb090_alpha_dummy_262 A), (nb090_alpha_dummy_265 h)), ((nb090_alpha_dummy_261 A), (nb090_alpha_dummy_264 h)), ((nb090_alpha_dummy_259 A), (nb090_alpha_dummy_260 h)), ((nb090_alpha_dummy_255 A), (nb090_alpha_dummy_257 h)), ((nb090_alpha_dummy_256 A), (nb090_alpha_dummy_258 h)), ((nb090_alpha_dummy_281 A), (nb090_alpha_dummy_282 h)), ((nb090_alpha_dummy_279 A), (nb090_alpha_dummy_280 h)), ((nb090_alpha_dummy_248 A), (nb090_alpha_dummy_250 h)), ((nb090_alpha_dummy_247 A), (nb090_alpha_dummy_249 h)), ((nb090_alpha_dummy_277 A), (nb090_alpha_dummy_278 h)), ((nb090_alpha_dummy_251 A), (nb090_alpha_dummy_252 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0083 v u A h)

theorem nb090_wpp_notmem_0698 (A : Class) : (nb090_alpha_dummy_281 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_281, fv_syn_c0] using (nb090_compact_fv_empty_0206 A)

theorem nb090_wpp_notmem_0699 (h : Var) : (nb090_alpha_dummy_282 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_282, fv_syn_c0] using (nb090_compact_fv_empty_0207 h)

theorem nb090_wpp_notmem_0700 (A : Class) : (nb090_alpha_dummy_279 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_279, fv_syn_c0] using (nb090_compact_fv_empty_0208 A)

theorem nb090_wpp_notmem_0701 (h : Var) : (nb090_alpha_dummy_280 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_280, fv_syn_c0] using (nb090_compact_fv_empty_0209 h)

theorem nb090_wpp_notmem_0702 (A : Class) : (nb090_alpha_dummy_277 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_277, fv_syn_c0] using (nb090_compact_fv_empty_0210 A)

theorem nb090_wpp_notmem_0703 (h : Var) : (nb090_alpha_dummy_278 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_278, fv_syn_c0] using (nb090_compact_fv_empty_0211 h)

theorem nb090_compact_envfresh_0084 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_263 A), (nb090_alpha_dummy_266 h)), ((nb090_alpha_dummy_262 A), (nb090_alpha_dummy_265 h)), ((nb090_alpha_dummy_261 A), (nb090_alpha_dummy_264 h)), ((nb090_alpha_dummy_259 A), (nb090_alpha_dummy_260 h)), ((nb090_alpha_dummy_255 A), (nb090_alpha_dummy_257 h)), ((nb090_alpha_dummy_256 A), (nb090_alpha_dummy_258 h)), ((nb090_alpha_dummy_281 A), (nb090_alpha_dummy_282 h)), ((nb090_alpha_dummy_279 A), (nb090_alpha_dummy_280 h)), ((nb090_alpha_dummy_248 A), (nb090_alpha_dummy_250 h)), ((nb090_alpha_dummy_247 A), (nb090_alpha_dummy_249 h)), ((nb090_alpha_dummy_277 A), (nb090_alpha_dummy_278 h)), ((nb090_alpha_dummy_251 A), (nb090_alpha_dummy_252 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_263 A) (nb090_alpha_dummy_266 h) (nb090_wpp_notmem_0650 A) (nb090_wpp_notmem_0651 h) (TEnvFresh.consFresh (nb090_alpha_dummy_262 A) (nb090_alpha_dummy_265 h) (nb090_wpp_notmem_0652 A) (nb090_wpp_notmem_0653 h) (TEnvFresh.consFresh (nb090_alpha_dummy_261 A) (nb090_alpha_dummy_264 h) (nb090_wpp_notmem_0654 A) (nb090_wpp_notmem_0655 h) (TEnvFresh.consFresh (nb090_alpha_dummy_259 A) (nb090_alpha_dummy_260 h) (nb090_wpp_notmem_0656 A) (nb090_wpp_notmem_0657 h) (TEnvFresh.consFresh (nb090_alpha_dummy_255 A) (nb090_alpha_dummy_257 h) (nb090_wpp_notmem_0658 A) (nb090_wpp_notmem_0659 h) (TEnvFresh.consFresh (nb090_alpha_dummy_256 A) (nb090_alpha_dummy_258 h) (nb090_wpp_notmem_0660 A) (nb090_wpp_notmem_0661 h) (TEnvFresh.consFresh (nb090_alpha_dummy_281 A) (nb090_alpha_dummy_282 h) (nb090_wpp_notmem_0698 A) (nb090_wpp_notmem_0699 h) (TEnvFresh.consFresh (nb090_alpha_dummy_279 A) (nb090_alpha_dummy_280 h) (nb090_wpp_notmem_0700 A) (nb090_wpp_notmem_0701 h) (TEnvFresh.consFresh (nb090_alpha_dummy_248 A) (nb090_alpha_dummy_250 h) (nb090_wpp_notmem_0662 A) (nb090_wpp_notmem_0663 h) (TEnvFresh.consFresh (nb090_alpha_dummy_247 A) (nb090_alpha_dummy_249 h) (nb090_wpp_notmem_0664 A) (nb090_wpp_notmem_0665 h) (TEnvFresh.consFresh (nb090_alpha_dummy_277 A) (nb090_alpha_dummy_278 h) (nb090_wpp_notmem_0702 A) (nb090_wpp_notmem_0703 h) (TEnvFresh.consFresh (nb090_alpha_dummy_251 A) (nb090_alpha_dummy_252 h) (nb090_wpp_notmem_0668 A) (nb090_wpp_notmem_0669 h) (TEnvFresh.consFresh (nb090_alpha_dummy_244 A) (nb090_alpha_dummy_246 h) (nb090_wpp_notmem_0670 A) (nb090_wpp_notmem_0671 h) (TEnvFresh.consFresh (nb090_alpha_dummy_243 A) (nb090_alpha_dummy_245 h) (nb090_wpp_notmem_0672 A) (nb090_wpp_notmem_0673 h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0174 A) (nb090_wpp_notmem_0175 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0046 A) (nb090_wpp_notmem_0047 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0048 A) (nb090_wpp_notmem_0049 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0050 A) (nb090_wpp_notmem_0051 v u A h) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))

noncomputable def nb090_wpp_refl_0084 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_263 A), (nb090_alpha_dummy_266 h)), ((nb090_alpha_dummy_262 A), (nb090_alpha_dummy_265 h)), ((nb090_alpha_dummy_261 A), (nb090_alpha_dummy_264 h)), ((nb090_alpha_dummy_259 A), (nb090_alpha_dummy_260 h)), ((nb090_alpha_dummy_255 A), (nb090_alpha_dummy_257 h)), ((nb090_alpha_dummy_256 A), (nb090_alpha_dummy_258 h)), ((nb090_alpha_dummy_281 A), (nb090_alpha_dummy_282 h)), ((nb090_alpha_dummy_279 A), (nb090_alpha_dummy_280 h)), ((nb090_alpha_dummy_248 A), (nb090_alpha_dummy_250 h)), ((nb090_alpha_dummy_247 A), (nb090_alpha_dummy_249 h)), ((nb090_alpha_dummy_277 A), (nb090_alpha_dummy_278 h)), ((nb090_alpha_dummy_251 A), (nb090_alpha_dummy_252 h)), ((nb090_alpha_dummy_244 A), (nb090_alpha_dummy_246 h)), ((nb090_alpha_dummy_243 A), (nb090_alpha_dummy_245 h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0084 v u A h)

theorem nb090_wpp_notmem_0704 (A : Class) : (nb090_alpha_dummy_281 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_281, fv_syn_cnnc] using (nb090_compact_fv_empty_0206 A)

theorem nb090_wpp_notmem_0705 (h : Var) : (nb090_alpha_dummy_282 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_282, fv_syn_cnnc] using (nb090_compact_fv_empty_0207 h)

theorem nb090_wpp_notmem_0706 (A : Class) : (nb090_alpha_dummy_279 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_279, fv_syn_cnnc] using (nb090_compact_fv_empty_0208 A)

theorem nb090_wpp_notmem_0707 (h : Var) : (nb090_alpha_dummy_280 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_280, fv_syn_cnnc] using (nb090_compact_fv_empty_0209 h)

theorem nb090_wpp_notmem_0708 (A : Class) : (nb090_alpha_dummy_277 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_277, fv_syn_cnnc] using (nb090_compact_fv_empty_0210 A)

theorem nb090_wpp_notmem_0709 (h : Var) : (nb090_alpha_dummy_278 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_278, fv_syn_cnnc] using (nb090_compact_fv_empty_0211 h)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
