import NAR4C078C001Part057

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

theorem nb078_compact_fv_empty_0195 (f : Var) : (nb078_alpha_dummy_260 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0635 (f : Var) : (nb078_alpha_dummy_260 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_260, fv_syn_c1c] using (nb078_compact_fv_empty_0195 f)

theorem nb078_compact_fv_empty_0196 : (nb078_alpha_dummy_255) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0636 : (nb078_alpha_dummy_255) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_255, fv_syn_c1c] using (nb078_compact_fv_empty_0196)

theorem nb078_compact_fv_empty_0197 (f : Var) : (nb078_alpha_dummy_257 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0637 (f : Var) : (nb078_alpha_dummy_257 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_257, fv_syn_c1c] using (nb078_compact_fv_empty_0197 f)

theorem nb078_compact_fv_empty_0198 : (nb078_alpha_dummy_256) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0638 : (nb078_alpha_dummy_256) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_256, fv_syn_c1c] using (nb078_compact_fv_empty_0198)

theorem nb078_compact_fv_empty_0199 (f : Var) : (nb078_alpha_dummy_258 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0639 (f : Var) : (nb078_alpha_dummy_258 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_258, fv_syn_c1c] using (nb078_compact_fv_empty_0199 f)

theorem nb078_compact_fv_empty_0200 : (nb078_alpha_dummy_248) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0640 : (nb078_alpha_dummy_248) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_248, fv_syn_c1c] using (nb078_compact_fv_empty_0200)

theorem nb078_compact_fv_empty_0201 (f : Var) : (nb078_alpha_dummy_250 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0641 (f : Var) : (nb078_alpha_dummy_250 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_250, fv_syn_c1c] using (nb078_compact_fv_empty_0201 f)

theorem nb078_compact_fv_empty_0202 : (nb078_alpha_dummy_247) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0642 : (nb078_alpha_dummy_247) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_247, fv_syn_c1c] using (nb078_compact_fv_empty_0202)

theorem nb078_compact_fv_empty_0203 (f : Var) : (nb078_alpha_dummy_249 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0643 (f : Var) : (nb078_alpha_dummy_249 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_249, fv_syn_c1c] using (nb078_compact_fv_empty_0203 f)

theorem nb078_compact_fv_empty_0204 : (nb078_alpha_dummy_253) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0644 : (nb078_alpha_dummy_253) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_253, fv_syn_c1c] using (nb078_compact_fv_empty_0204)

theorem nb078_compact_fv_empty_0205 (f : Var) : (nb078_alpha_dummy_254 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0645 (f : Var) : (nb078_alpha_dummy_254 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_254, fv_syn_c1c] using (nb078_compact_fv_empty_0205 f)

theorem nb078_compact_fv_empty_0206 : (nb078_alpha_dummy_251) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0646 : (nb078_alpha_dummy_251) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_251, fv_syn_c1c] using (nb078_compact_fv_empty_0206)

theorem nb078_compact_fv_empty_0207 (f : Var) : (nb078_alpha_dummy_252 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0647 (f : Var) : (nb078_alpha_dummy_252 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_252, fv_syn_c1c] using (nb078_compact_fv_empty_0207 f)

theorem nb078_wpp_notmem_0648 : (nb078_alpha_dummy_244) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_244, fv_syn_c1c] using (nb078_compact_fv_empty_0184)

theorem nb078_wpp_notmem_0649 (f : Var) : (nb078_alpha_dummy_246 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_246, fv_syn_c1c] using (nb078_compact_fv_empty_0185 f)

theorem nb078_wpp_notmem_0650 : (nb078_alpha_dummy_243) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_243, fv_syn_c1c] using (nb078_compact_fv_empty_0186)

theorem nb078_wpp_notmem_0651 (f : Var) : (nb078_alpha_dummy_245 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_245, fv_syn_c1c] using (nb078_compact_fv_empty_0187 f)

theorem nb078_compact_envfresh_0094 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb078_alpha_dummy_263), (nb078_alpha_dummy_266 f)), ((nb078_alpha_dummy_262), (nb078_alpha_dummy_265 f)), ((nb078_alpha_dummy_261), (nb078_alpha_dummy_264 f)), ((nb078_alpha_dummy_259), (nb078_alpha_dummy_260 f)), ((nb078_alpha_dummy_255), (nb078_alpha_dummy_257 f)), ((nb078_alpha_dummy_256), (nb078_alpha_dummy_258 f)), ((nb078_alpha_dummy_248), (nb078_alpha_dummy_250 f)), ((nb078_alpha_dummy_247), (nb078_alpha_dummy_249 f)), ((nb078_alpha_dummy_253), (nb078_alpha_dummy_254 f)), ((nb078_alpha_dummy_251), (nb078_alpha_dummy_252 f)), ((nb078_alpha_dummy_244), (nb078_alpha_dummy_246 f)), ((nb078_alpha_dummy_243), (nb078_alpha_dummy_245 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_263) (nb078_alpha_dummy_266 f) (nb078_wpp_notmem_0628) (nb078_wpp_notmem_0629 f) (TEnvFresh.consFresh (nb078_alpha_dummy_262) (nb078_alpha_dummy_265 f) (nb078_wpp_notmem_0630) (nb078_wpp_notmem_0631 f) (TEnvFresh.consFresh (nb078_alpha_dummy_261) (nb078_alpha_dummy_264 f) (nb078_wpp_notmem_0632) (nb078_wpp_notmem_0633 f) (TEnvFresh.consFresh (nb078_alpha_dummy_259) (nb078_alpha_dummy_260 f) (nb078_wpp_notmem_0634) (nb078_wpp_notmem_0635 f) (TEnvFresh.consFresh (nb078_alpha_dummy_255) (nb078_alpha_dummy_257 f) (nb078_wpp_notmem_0636) (nb078_wpp_notmem_0637 f) (TEnvFresh.consFresh (nb078_alpha_dummy_256) (nb078_alpha_dummy_258 f) (nb078_wpp_notmem_0638) (nb078_wpp_notmem_0639 f) (TEnvFresh.consFresh (nb078_alpha_dummy_248) (nb078_alpha_dummy_250 f) (nb078_wpp_notmem_0640) (nb078_wpp_notmem_0641 f) (TEnvFresh.consFresh (nb078_alpha_dummy_247) (nb078_alpha_dummy_249 f) (nb078_wpp_notmem_0642) (nb078_wpp_notmem_0643 f) (TEnvFresh.consFresh (nb078_alpha_dummy_253) (nb078_alpha_dummy_254 f) (nb078_wpp_notmem_0644) (nb078_wpp_notmem_0645 f) (TEnvFresh.consFresh (nb078_alpha_dummy_251) (nb078_alpha_dummy_252 f) (nb078_wpp_notmem_0646) (nb078_wpp_notmem_0647 f) (TEnvFresh.consFresh (nb078_alpha_dummy_244) (nb078_alpha_dummy_246 f) (nb078_wpp_notmem_0648) (nb078_wpp_notmem_0649 f) (TEnvFresh.consFresh (nb078_alpha_dummy_243) (nb078_alpha_dummy_245 f) (nb078_wpp_notmem_0650) (nb078_wpp_notmem_0651 f) (TEnvFresh.consFresh (nb078_alpha_dummy_000) f (nb078_wpp_notmem_0030) (nb078_wpp_notmem_0031 f) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))

noncomputable def nb078_wpp_refl_0094 (x : Var) (y : Var) (f : Var) : TReflOn [((nb078_alpha_dummy_263), (nb078_alpha_dummy_266 f)), ((nb078_alpha_dummy_262), (nb078_alpha_dummy_265 f)), ((nb078_alpha_dummy_261), (nb078_alpha_dummy_264 f)), ((nb078_alpha_dummy_259), (nb078_alpha_dummy_260 f)), ((nb078_alpha_dummy_255), (nb078_alpha_dummy_257 f)), ((nb078_alpha_dummy_256), (nb078_alpha_dummy_258 f)), ((nb078_alpha_dummy_248), (nb078_alpha_dummy_250 f)), ((nb078_alpha_dummy_247), (nb078_alpha_dummy_249 f)), ((nb078_alpha_dummy_253), (nb078_alpha_dummy_254 f)), ((nb078_alpha_dummy_251), (nb078_alpha_dummy_252 f)), ((nb078_alpha_dummy_244), (nb078_alpha_dummy_246 f)), ((nb078_alpha_dummy_243), (nb078_alpha_dummy_245 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0094 x y f)

theorem nb078_wpp_notmem_0652 : (nb078_alpha_dummy_263) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_263, fv_syn_c0] using (nb078_compact_fv_empty_0188)

theorem nb078_wpp_notmem_0653 (f : Var) : (nb078_alpha_dummy_266 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_266, fv_syn_c0] using (nb078_compact_fv_empty_0189 f)

theorem nb078_wpp_notmem_0654 : (nb078_alpha_dummy_262) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_262, fv_syn_c0] using (nb078_compact_fv_empty_0190)

theorem nb078_wpp_notmem_0655 (f : Var) : (nb078_alpha_dummy_265 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_265, fv_syn_c0] using (nb078_compact_fv_empty_0191 f)

theorem nb078_wpp_notmem_0656 : (nb078_alpha_dummy_261) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_261, fv_syn_c0] using (nb078_compact_fv_empty_0192)

theorem nb078_wpp_notmem_0657 (f : Var) : (nb078_alpha_dummy_264 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_264, fv_syn_c0] using (nb078_compact_fv_empty_0193 f)

theorem nb078_wpp_notmem_0658 : (nb078_alpha_dummy_259) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_259, fv_syn_c0] using (nb078_compact_fv_empty_0194)

theorem nb078_wpp_notmem_0659 (f : Var) : (nb078_alpha_dummy_260 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_260, fv_syn_c0] using (nb078_compact_fv_empty_0195 f)

theorem nb078_wpp_notmem_0660 : (nb078_alpha_dummy_255) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_255, fv_syn_c0] using (nb078_compact_fv_empty_0196)

theorem nb078_wpp_notmem_0661 (f : Var) : (nb078_alpha_dummy_257 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_257, fv_syn_c0] using (nb078_compact_fv_empty_0197 f)

theorem nb078_wpp_notmem_0662 : (nb078_alpha_dummy_256) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_256, fv_syn_c0] using (nb078_compact_fv_empty_0198)

theorem nb078_wpp_notmem_0663 (f : Var) : (nb078_alpha_dummy_258 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_258, fv_syn_c0] using (nb078_compact_fv_empty_0199 f)

theorem nb078_wpp_notmem_0664 : (nb078_alpha_dummy_248) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_248, fv_syn_c0] using (nb078_compact_fv_empty_0200)

theorem nb078_wpp_notmem_0665 (f : Var) : (nb078_alpha_dummy_250 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_250, fv_syn_c0] using (nb078_compact_fv_empty_0201 f)

theorem nb078_wpp_notmem_0666 : (nb078_alpha_dummy_247) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_247, fv_syn_c0] using (nb078_compact_fv_empty_0202)

theorem nb078_wpp_notmem_0667 (f : Var) : (nb078_alpha_dummy_249 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_249, fv_syn_c0] using (nb078_compact_fv_empty_0203 f)

theorem nb078_wpp_notmem_0668 : (nb078_alpha_dummy_253) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_253, fv_syn_c0] using (nb078_compact_fv_empty_0204)

theorem nb078_wpp_notmem_0669 (f : Var) : (nb078_alpha_dummy_254 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_254, fv_syn_c0] using (nb078_compact_fv_empty_0205 f)

theorem nb078_wpp_notmem_0670 : (nb078_alpha_dummy_251) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_251, fv_syn_c0] using (nb078_compact_fv_empty_0206)

theorem nb078_wpp_notmem_0671 (f : Var) : (nb078_alpha_dummy_252 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_252, fv_syn_c0] using (nb078_compact_fv_empty_0207 f)

theorem nb078_wpp_notmem_0672 : (nb078_alpha_dummy_244) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_244, fv_syn_c0] using (nb078_compact_fv_empty_0184)

theorem nb078_wpp_notmem_0673 (f : Var) : (nb078_alpha_dummy_246 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_246, fv_syn_c0] using (nb078_compact_fv_empty_0185 f)

theorem nb078_wpp_notmem_0674 : (nb078_alpha_dummy_243) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_243, fv_syn_c0] using (nb078_compact_fv_empty_0186)

theorem nb078_wpp_notmem_0675 (f : Var) : (nb078_alpha_dummy_245 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_245, fv_syn_c0] using (nb078_compact_fv_empty_0187 f)

theorem nb078_compact_envfresh_0095 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb078_alpha_dummy_263), (nb078_alpha_dummy_266 f)), ((nb078_alpha_dummy_262), (nb078_alpha_dummy_265 f)), ((nb078_alpha_dummy_261), (nb078_alpha_dummy_264 f)), ((nb078_alpha_dummy_259), (nb078_alpha_dummy_260 f)), ((nb078_alpha_dummy_255), (nb078_alpha_dummy_257 f)), ((nb078_alpha_dummy_256), (nb078_alpha_dummy_258 f)), ((nb078_alpha_dummy_248), (nb078_alpha_dummy_250 f)), ((nb078_alpha_dummy_247), (nb078_alpha_dummy_249 f)), ((nb078_alpha_dummy_253), (nb078_alpha_dummy_254 f)), ((nb078_alpha_dummy_251), (nb078_alpha_dummy_252 f)), ((nb078_alpha_dummy_244), (nb078_alpha_dummy_246 f)), ((nb078_alpha_dummy_243), (nb078_alpha_dummy_245 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_263) (nb078_alpha_dummy_266 f) (nb078_wpp_notmem_0652) (nb078_wpp_notmem_0653 f) (TEnvFresh.consFresh (nb078_alpha_dummy_262) (nb078_alpha_dummy_265 f) (nb078_wpp_notmem_0654) (nb078_wpp_notmem_0655 f) (TEnvFresh.consFresh (nb078_alpha_dummy_261) (nb078_alpha_dummy_264 f) (nb078_wpp_notmem_0656) (nb078_wpp_notmem_0657 f) (TEnvFresh.consFresh (nb078_alpha_dummy_259) (nb078_alpha_dummy_260 f) (nb078_wpp_notmem_0658) (nb078_wpp_notmem_0659 f) (TEnvFresh.consFresh (nb078_alpha_dummy_255) (nb078_alpha_dummy_257 f) (nb078_wpp_notmem_0660) (nb078_wpp_notmem_0661 f) (TEnvFresh.consFresh (nb078_alpha_dummy_256) (nb078_alpha_dummy_258 f) (nb078_wpp_notmem_0662) (nb078_wpp_notmem_0663 f) (TEnvFresh.consFresh (nb078_alpha_dummy_248) (nb078_alpha_dummy_250 f) (nb078_wpp_notmem_0664) (nb078_wpp_notmem_0665 f) (TEnvFresh.consFresh (nb078_alpha_dummy_247) (nb078_alpha_dummy_249 f) (nb078_wpp_notmem_0666) (nb078_wpp_notmem_0667 f) (TEnvFresh.consFresh (nb078_alpha_dummy_253) (nb078_alpha_dummy_254 f) (nb078_wpp_notmem_0668) (nb078_wpp_notmem_0669 f) (TEnvFresh.consFresh (nb078_alpha_dummy_251) (nb078_alpha_dummy_252 f) (nb078_wpp_notmem_0670) (nb078_wpp_notmem_0671 f) (TEnvFresh.consFresh (nb078_alpha_dummy_244) (nb078_alpha_dummy_246 f) (nb078_wpp_notmem_0672) (nb078_wpp_notmem_0673 f) (TEnvFresh.consFresh (nb078_alpha_dummy_243) (nb078_alpha_dummy_245 f) (nb078_wpp_notmem_0674) (nb078_wpp_notmem_0675 f) (TEnvFresh.consFresh (nb078_alpha_dummy_000) f (nb078_wpp_notmem_0066) (nb078_wpp_notmem_0067 f) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0068) (nb078_wpp_notmem_0069 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0070) (nb078_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))

noncomputable def nb078_wpp_refl_0095 (x : Var) (y : Var) (f : Var) : TReflOn [((nb078_alpha_dummy_263), (nb078_alpha_dummy_266 f)), ((nb078_alpha_dummy_262), (nb078_alpha_dummy_265 f)), ((nb078_alpha_dummy_261), (nb078_alpha_dummy_264 f)), ((nb078_alpha_dummy_259), (nb078_alpha_dummy_260 f)), ((nb078_alpha_dummy_255), (nb078_alpha_dummy_257 f)), ((nb078_alpha_dummy_256), (nb078_alpha_dummy_258 f)), ((nb078_alpha_dummy_248), (nb078_alpha_dummy_250 f)), ((nb078_alpha_dummy_247), (nb078_alpha_dummy_249 f)), ((nb078_alpha_dummy_253), (nb078_alpha_dummy_254 f)), ((nb078_alpha_dummy_251), (nb078_alpha_dummy_252 f)), ((nb078_alpha_dummy_244), (nb078_alpha_dummy_246 f)), ((nb078_alpha_dummy_243), (nb078_alpha_dummy_245 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0095 x y f)

theorem nb078_wpp_notmem_0676 : (nb078_alpha_dummy_259) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_259, fv_syn_cnnc] using (nb078_compact_fv_empty_0194)

theorem nb078_wpp_notmem_0677 (f : Var) : (nb078_alpha_dummy_260 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_260, fv_syn_cnnc] using (nb078_compact_fv_empty_0195 f)

theorem nb078_wpp_notmem_0678 : (nb078_alpha_dummy_255) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_255, fv_syn_cnnc] using (nb078_compact_fv_empty_0196)

theorem nb078_wpp_notmem_0679 (f : Var) : (nb078_alpha_dummy_257 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_257, fv_syn_cnnc] using (nb078_compact_fv_empty_0197 f)

theorem nb078_wpp_notmem_0680 : (nb078_alpha_dummy_256) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_256, fv_syn_cnnc] using (nb078_compact_fv_empty_0198)

theorem nb078_wpp_notmem_0681 (f : Var) : (nb078_alpha_dummy_258 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_258, fv_syn_cnnc] using (nb078_compact_fv_empty_0199 f)

theorem nb078_wpp_notmem_0682 : (nb078_alpha_dummy_248) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_248, fv_syn_cnnc] using (nb078_compact_fv_empty_0200)

theorem nb078_wpp_notmem_0683 (f : Var) : (nb078_alpha_dummy_250 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_250, fv_syn_cnnc] using (nb078_compact_fv_empty_0201 f)

theorem nb078_wpp_notmem_0684 : (nb078_alpha_dummy_247) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_247, fv_syn_cnnc] using (nb078_compact_fv_empty_0202)

theorem nb078_wpp_notmem_0685 (f : Var) : (nb078_alpha_dummy_249 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_249, fv_syn_cnnc] using (nb078_compact_fv_empty_0203 f)

theorem nb078_wpp_notmem_0686 : (nb078_alpha_dummy_253) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_253, fv_syn_cnnc] using (nb078_compact_fv_empty_0204)

theorem nb078_wpp_notmem_0687 (f : Var) : (nb078_alpha_dummy_254 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_254, fv_syn_cnnc] using (nb078_compact_fv_empty_0205 f)

theorem nb078_wpp_notmem_0688 : (nb078_alpha_dummy_251) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_251, fv_syn_cnnc] using (nb078_compact_fv_empty_0206)

theorem nb078_wpp_notmem_0689 (f : Var) : (nb078_alpha_dummy_252 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_252, fv_syn_cnnc] using (nb078_compact_fv_empty_0207 f)

theorem nb078_wpp_notmem_0690 : (nb078_alpha_dummy_244) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_244, fv_syn_cnnc] using (nb078_compact_fv_empty_0184)

theorem nb078_wpp_notmem_0691 (f : Var) : (nb078_alpha_dummy_246 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_246, fv_syn_cnnc] using (nb078_compact_fv_empty_0185 f)

theorem nb078_wpp_notmem_0692 : (nb078_alpha_dummy_243) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_243, fv_syn_cnnc] using (nb078_compact_fv_empty_0186)

theorem nb078_wpp_notmem_0693 (f : Var) : (nb078_alpha_dummy_245 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_245, fv_syn_cnnc] using (nb078_compact_fv_empty_0187 f)

theorem nb078_compact_envfresh_0096 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb078_alpha_dummy_259), (nb078_alpha_dummy_260 f)), ((nb078_alpha_dummy_255), (nb078_alpha_dummy_257 f)), ((nb078_alpha_dummy_256), (nb078_alpha_dummy_258 f)), ((nb078_alpha_dummy_248), (nb078_alpha_dummy_250 f)), ((nb078_alpha_dummy_247), (nb078_alpha_dummy_249 f)), ((nb078_alpha_dummy_253), (nb078_alpha_dummy_254 f)), ((nb078_alpha_dummy_251), (nb078_alpha_dummy_252 f)), ((nb078_alpha_dummy_244), (nb078_alpha_dummy_246 f)), ((nb078_alpha_dummy_243), (nb078_alpha_dummy_245 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_259) (nb078_alpha_dummy_260 f) (nb078_wpp_notmem_0676) (nb078_wpp_notmem_0677 f) (TEnvFresh.consFresh (nb078_alpha_dummy_255) (nb078_alpha_dummy_257 f) (nb078_wpp_notmem_0678) (nb078_wpp_notmem_0679 f) (TEnvFresh.consFresh (nb078_alpha_dummy_256) (nb078_alpha_dummy_258 f) (nb078_wpp_notmem_0680) (nb078_wpp_notmem_0681 f) (TEnvFresh.consFresh (nb078_alpha_dummy_248) (nb078_alpha_dummy_250 f) (nb078_wpp_notmem_0682) (nb078_wpp_notmem_0683 f) (TEnvFresh.consFresh (nb078_alpha_dummy_247) (nb078_alpha_dummy_249 f) (nb078_wpp_notmem_0684) (nb078_wpp_notmem_0685 f) (TEnvFresh.consFresh (nb078_alpha_dummy_253) (nb078_alpha_dummy_254 f) (nb078_wpp_notmem_0686) (nb078_wpp_notmem_0687 f) (TEnvFresh.consFresh (nb078_alpha_dummy_251) (nb078_alpha_dummy_252 f) (nb078_wpp_notmem_0688) (nb078_wpp_notmem_0689 f) (TEnvFresh.consFresh (nb078_alpha_dummy_244) (nb078_alpha_dummy_246 f) (nb078_wpp_notmem_0690) (nb078_wpp_notmem_0691 f) (TEnvFresh.consFresh (nb078_alpha_dummy_243) (nb078_alpha_dummy_245 f) (nb078_wpp_notmem_0692) (nb078_wpp_notmem_0693 f) (TEnvFresh.consFresh (nb078_alpha_dummy_000) f (nb078_wpp_notmem_0096) (nb078_wpp_notmem_0097 f) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0098) (nb078_wpp_notmem_0099 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0100) (nb078_wpp_notmem_0101 x) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))

noncomputable def nb078_wpp_refl_0096 (x : Var) (y : Var) (f : Var) : TReflOn [((nb078_alpha_dummy_259), (nb078_alpha_dummy_260 f)), ((nb078_alpha_dummy_255), (nb078_alpha_dummy_257 f)), ((nb078_alpha_dummy_256), (nb078_alpha_dummy_258 f)), ((nb078_alpha_dummy_248), (nb078_alpha_dummy_250 f)), ((nb078_alpha_dummy_247), (nb078_alpha_dummy_249 f)), ((nb078_alpha_dummy_253), (nb078_alpha_dummy_254 f)), ((nb078_alpha_dummy_251), (nb078_alpha_dummy_252 f)), ((nb078_alpha_dummy_244), (nb078_alpha_dummy_246 f)), ((nb078_alpha_dummy_243), (nb078_alpha_dummy_245 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0096 x y f)

theorem nb078_compact_fv_empty_0208 : (nb078_alpha_dummy_281) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0694 : (nb078_alpha_dummy_281) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_281, fv_syn_c1c] using (nb078_compact_fv_empty_0208)

theorem nb078_compact_fv_empty_0209 (f : Var) : (nb078_alpha_dummy_282 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0695 (f : Var) : (nb078_alpha_dummy_282 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_282, fv_syn_c1c] using (nb078_compact_fv_empty_0209 f)

theorem nb078_compact_fv_empty_0210 : (nb078_alpha_dummy_279) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0696 : (nb078_alpha_dummy_279) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_279, fv_syn_c1c] using (nb078_compact_fv_empty_0210)

theorem nb078_compact_fv_empty_0211 (f : Var) : (nb078_alpha_dummy_280 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0697 (f : Var) : (nb078_alpha_dummy_280 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_280, fv_syn_c1c] using (nb078_compact_fv_empty_0211 f)

theorem nb078_compact_fv_empty_0212 : (nb078_alpha_dummy_277) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0698 : (nb078_alpha_dummy_277) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_277, fv_syn_c1c] using (nb078_compact_fv_empty_0212)

theorem nb078_compact_fv_empty_0213 (f : Var) : (nb078_alpha_dummy_278 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0699 (f : Var) : (nb078_alpha_dummy_278 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_278, fv_syn_c1c] using (nb078_compact_fv_empty_0213 f)

theorem nb078_compact_envfresh_0097 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb078_alpha_dummy_263), (nb078_alpha_dummy_266 f)), ((nb078_alpha_dummy_262), (nb078_alpha_dummy_265 f)), ((nb078_alpha_dummy_261), (nb078_alpha_dummy_264 f)), ((nb078_alpha_dummy_259), (nb078_alpha_dummy_260 f)), ((nb078_alpha_dummy_255), (nb078_alpha_dummy_257 f)), ((nb078_alpha_dummy_256), (nb078_alpha_dummy_258 f)), ((nb078_alpha_dummy_281), (nb078_alpha_dummy_282 f)), ((nb078_alpha_dummy_279), (nb078_alpha_dummy_280 f)), ((nb078_alpha_dummy_248), (nb078_alpha_dummy_250 f)), ((nb078_alpha_dummy_247), (nb078_alpha_dummy_249 f)), ((nb078_alpha_dummy_277), (nb078_alpha_dummy_278 f)), ((nb078_alpha_dummy_251), (nb078_alpha_dummy_252 f)), ((nb078_alpha_dummy_244), (nb078_alpha_dummy_246 f)), ((nb078_alpha_dummy_243), (nb078_alpha_dummy_245 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_263) (nb078_alpha_dummy_266 f) (nb078_wpp_notmem_0628) (nb078_wpp_notmem_0629 f) (TEnvFresh.consFresh (nb078_alpha_dummy_262) (nb078_alpha_dummy_265 f) (nb078_wpp_notmem_0630) (nb078_wpp_notmem_0631 f) (TEnvFresh.consFresh (nb078_alpha_dummy_261) (nb078_alpha_dummy_264 f) (nb078_wpp_notmem_0632) (nb078_wpp_notmem_0633 f) (TEnvFresh.consFresh (nb078_alpha_dummy_259) (nb078_alpha_dummy_260 f) (nb078_wpp_notmem_0634) (nb078_wpp_notmem_0635 f) (TEnvFresh.consFresh (nb078_alpha_dummy_255) (nb078_alpha_dummy_257 f) (nb078_wpp_notmem_0636) (nb078_wpp_notmem_0637 f) (TEnvFresh.consFresh (nb078_alpha_dummy_256) (nb078_alpha_dummy_258 f) (nb078_wpp_notmem_0638) (nb078_wpp_notmem_0639 f) (TEnvFresh.consFresh (nb078_alpha_dummy_281) (nb078_alpha_dummy_282 f) (nb078_wpp_notmem_0694) (nb078_wpp_notmem_0695 f) (TEnvFresh.consFresh (nb078_alpha_dummy_279) (nb078_alpha_dummy_280 f) (nb078_wpp_notmem_0696) (nb078_wpp_notmem_0697 f) (TEnvFresh.consFresh (nb078_alpha_dummy_248) (nb078_alpha_dummy_250 f) (nb078_wpp_notmem_0640) (nb078_wpp_notmem_0641 f) (TEnvFresh.consFresh (nb078_alpha_dummy_247) (nb078_alpha_dummy_249 f) (nb078_wpp_notmem_0642) (nb078_wpp_notmem_0643 f) (TEnvFresh.consFresh (nb078_alpha_dummy_277) (nb078_alpha_dummy_278 f) (nb078_wpp_notmem_0698) (nb078_wpp_notmem_0699 f) (TEnvFresh.consFresh (nb078_alpha_dummy_251) (nb078_alpha_dummy_252 f) (nb078_wpp_notmem_0646) (nb078_wpp_notmem_0647 f) (TEnvFresh.consFresh (nb078_alpha_dummy_244) (nb078_alpha_dummy_246 f) (nb078_wpp_notmem_0648) (nb078_wpp_notmem_0649 f) (TEnvFresh.consFresh (nb078_alpha_dummy_243) (nb078_alpha_dummy_245 f) (nb078_wpp_notmem_0650) (nb078_wpp_notmem_0651 f) (TEnvFresh.consFresh (nb078_alpha_dummy_000) f (nb078_wpp_notmem_0030) (nb078_wpp_notmem_0031 f) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))

noncomputable def nb078_wpp_refl_0097 (x : Var) (y : Var) (f : Var) : TReflOn [((nb078_alpha_dummy_263), (nb078_alpha_dummy_266 f)), ((nb078_alpha_dummy_262), (nb078_alpha_dummy_265 f)), ((nb078_alpha_dummy_261), (nb078_alpha_dummy_264 f)), ((nb078_alpha_dummy_259), (nb078_alpha_dummy_260 f)), ((nb078_alpha_dummy_255), (nb078_alpha_dummy_257 f)), ((nb078_alpha_dummy_256), (nb078_alpha_dummy_258 f)), ((nb078_alpha_dummy_281), (nb078_alpha_dummy_282 f)), ((nb078_alpha_dummy_279), (nb078_alpha_dummy_280 f)), ((nb078_alpha_dummy_248), (nb078_alpha_dummy_250 f)), ((nb078_alpha_dummy_247), (nb078_alpha_dummy_249 f)), ((nb078_alpha_dummy_277), (nb078_alpha_dummy_278 f)), ((nb078_alpha_dummy_251), (nb078_alpha_dummy_252 f)), ((nb078_alpha_dummy_244), (nb078_alpha_dummy_246 f)), ((nb078_alpha_dummy_243), (nb078_alpha_dummy_245 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0097 x y f)

theorem nb078_wpp_notmem_0700 : (nb078_alpha_dummy_281) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_281, fv_syn_c0] using (nb078_compact_fv_empty_0208)

theorem nb078_wpp_notmem_0701 (f : Var) : (nb078_alpha_dummy_282 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_282, fv_syn_c0] using (nb078_compact_fv_empty_0209 f)

theorem nb078_wpp_notmem_0702 : (nb078_alpha_dummy_279) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_279, fv_syn_c0] using (nb078_compact_fv_empty_0210)

theorem nb078_wpp_notmem_0703 (f : Var) : (nb078_alpha_dummy_280 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_280, fv_syn_c0] using (nb078_compact_fv_empty_0211 f)

theorem nb078_wpp_notmem_0704 : (nb078_alpha_dummy_277) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_277, fv_syn_c0] using (nb078_compact_fv_empty_0212)

theorem nb078_wpp_notmem_0705 (f : Var) : (nb078_alpha_dummy_278 f) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_278, fv_syn_c0] using (nb078_compact_fv_empty_0213 f)

theorem nb078_compact_envfresh_0098 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb078_alpha_dummy_263), (nb078_alpha_dummy_266 f)), ((nb078_alpha_dummy_262), (nb078_alpha_dummy_265 f)), ((nb078_alpha_dummy_261), (nb078_alpha_dummy_264 f)), ((nb078_alpha_dummy_259), (nb078_alpha_dummy_260 f)), ((nb078_alpha_dummy_255), (nb078_alpha_dummy_257 f)), ((nb078_alpha_dummy_256), (nb078_alpha_dummy_258 f)), ((nb078_alpha_dummy_281), (nb078_alpha_dummy_282 f)), ((nb078_alpha_dummy_279), (nb078_alpha_dummy_280 f)), ((nb078_alpha_dummy_248), (nb078_alpha_dummy_250 f)), ((nb078_alpha_dummy_247), (nb078_alpha_dummy_249 f)), ((nb078_alpha_dummy_277), (nb078_alpha_dummy_278 f)), ((nb078_alpha_dummy_251), (nb078_alpha_dummy_252 f)), ((nb078_alpha_dummy_244), (nb078_alpha_dummy_246 f)), ((nb078_alpha_dummy_243), (nb078_alpha_dummy_245 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_263) (nb078_alpha_dummy_266 f) (nb078_wpp_notmem_0652) (nb078_wpp_notmem_0653 f) (TEnvFresh.consFresh (nb078_alpha_dummy_262) (nb078_alpha_dummy_265 f) (nb078_wpp_notmem_0654) (nb078_wpp_notmem_0655 f) (TEnvFresh.consFresh (nb078_alpha_dummy_261) (nb078_alpha_dummy_264 f) (nb078_wpp_notmem_0656) (nb078_wpp_notmem_0657 f) (TEnvFresh.consFresh (nb078_alpha_dummy_259) (nb078_alpha_dummy_260 f) (nb078_wpp_notmem_0658) (nb078_wpp_notmem_0659 f) (TEnvFresh.consFresh (nb078_alpha_dummy_255) (nb078_alpha_dummy_257 f) (nb078_wpp_notmem_0660) (nb078_wpp_notmem_0661 f) (TEnvFresh.consFresh (nb078_alpha_dummy_256) (nb078_alpha_dummy_258 f) (nb078_wpp_notmem_0662) (nb078_wpp_notmem_0663 f) (TEnvFresh.consFresh (nb078_alpha_dummy_281) (nb078_alpha_dummy_282 f) (nb078_wpp_notmem_0700) (nb078_wpp_notmem_0701 f) (TEnvFresh.consFresh (nb078_alpha_dummy_279) (nb078_alpha_dummy_280 f) (nb078_wpp_notmem_0702) (nb078_wpp_notmem_0703 f) (TEnvFresh.consFresh (nb078_alpha_dummy_248) (nb078_alpha_dummy_250 f) (nb078_wpp_notmem_0664) (nb078_wpp_notmem_0665 f) (TEnvFresh.consFresh (nb078_alpha_dummy_247) (nb078_alpha_dummy_249 f) (nb078_wpp_notmem_0666) (nb078_wpp_notmem_0667 f) (TEnvFresh.consFresh (nb078_alpha_dummy_277) (nb078_alpha_dummy_278 f) (nb078_wpp_notmem_0704) (nb078_wpp_notmem_0705 f) (TEnvFresh.consFresh (nb078_alpha_dummy_251) (nb078_alpha_dummy_252 f) (nb078_wpp_notmem_0670) (nb078_wpp_notmem_0671 f) (TEnvFresh.consFresh (nb078_alpha_dummy_244) (nb078_alpha_dummy_246 f) (nb078_wpp_notmem_0672) (nb078_wpp_notmem_0673 f) (TEnvFresh.consFresh (nb078_alpha_dummy_243) (nb078_alpha_dummy_245 f) (nb078_wpp_notmem_0674) (nb078_wpp_notmem_0675 f) (TEnvFresh.consFresh (nb078_alpha_dummy_000) f (nb078_wpp_notmem_0066) (nb078_wpp_notmem_0067 f) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0068) (nb078_wpp_notmem_0069 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0070) (nb078_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))

noncomputable def nb078_wpp_refl_0098 (x : Var) (y : Var) (f : Var) : TReflOn [((nb078_alpha_dummy_263), (nb078_alpha_dummy_266 f)), ((nb078_alpha_dummy_262), (nb078_alpha_dummy_265 f)), ((nb078_alpha_dummy_261), (nb078_alpha_dummy_264 f)), ((nb078_alpha_dummy_259), (nb078_alpha_dummy_260 f)), ((nb078_alpha_dummy_255), (nb078_alpha_dummy_257 f)), ((nb078_alpha_dummy_256), (nb078_alpha_dummy_258 f)), ((nb078_alpha_dummy_281), (nb078_alpha_dummy_282 f)), ((nb078_alpha_dummy_279), (nb078_alpha_dummy_280 f)), ((nb078_alpha_dummy_248), (nb078_alpha_dummy_250 f)), ((nb078_alpha_dummy_247), (nb078_alpha_dummy_249 f)), ((nb078_alpha_dummy_277), (nb078_alpha_dummy_278 f)), ((nb078_alpha_dummy_251), (nb078_alpha_dummy_252 f)), ((nb078_alpha_dummy_244), (nb078_alpha_dummy_246 f)), ((nb078_alpha_dummy_243), (nb078_alpha_dummy_245 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0098 x y f)

theorem nb078_wpp_notmem_0706 : (nb078_alpha_dummy_281) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_281, fv_syn_cnnc] using (nb078_compact_fv_empty_0208)

theorem nb078_wpp_notmem_0707 (f : Var) : (nb078_alpha_dummy_282 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_282, fv_syn_cnnc] using (nb078_compact_fv_empty_0209 f)

theorem nb078_wpp_notmem_0708 : (nb078_alpha_dummy_279) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_279, fv_syn_cnnc] using (nb078_compact_fv_empty_0210)

theorem nb078_wpp_notmem_0709 (f : Var) : (nb078_alpha_dummy_280 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_280, fv_syn_cnnc] using (nb078_compact_fv_empty_0211 f)

theorem nb078_wpp_notmem_0710 : (nb078_alpha_dummy_277) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_277, fv_syn_cnnc] using (nb078_compact_fv_empty_0212)

theorem nb078_wpp_notmem_0711 (f : Var) : (nb078_alpha_dummy_278 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_278, fv_syn_cnnc] using (nb078_compact_fv_empty_0213 f)

theorem nb078_compact_envfresh_0099 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb078_alpha_dummy_259), (nb078_alpha_dummy_260 f)), ((nb078_alpha_dummy_255), (nb078_alpha_dummy_257 f)), ((nb078_alpha_dummy_256), (nb078_alpha_dummy_258 f)), ((nb078_alpha_dummy_281), (nb078_alpha_dummy_282 f)), ((nb078_alpha_dummy_279), (nb078_alpha_dummy_280 f)), ((nb078_alpha_dummy_248), (nb078_alpha_dummy_250 f)), ((nb078_alpha_dummy_247), (nb078_alpha_dummy_249 f)), ((nb078_alpha_dummy_277), (nb078_alpha_dummy_278 f)), ((nb078_alpha_dummy_251), (nb078_alpha_dummy_252 f)), ((nb078_alpha_dummy_244), (nb078_alpha_dummy_246 f)), ((nb078_alpha_dummy_243), (nb078_alpha_dummy_245 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_259) (nb078_alpha_dummy_260 f) (nb078_wpp_notmem_0676) (nb078_wpp_notmem_0677 f) (TEnvFresh.consFresh (nb078_alpha_dummy_255) (nb078_alpha_dummy_257 f) (nb078_wpp_notmem_0678) (nb078_wpp_notmem_0679 f) (TEnvFresh.consFresh (nb078_alpha_dummy_256) (nb078_alpha_dummy_258 f) (nb078_wpp_notmem_0680) (nb078_wpp_notmem_0681 f) (TEnvFresh.consFresh (nb078_alpha_dummy_281) (nb078_alpha_dummy_282 f) (nb078_wpp_notmem_0706) (nb078_wpp_notmem_0707 f) (TEnvFresh.consFresh (nb078_alpha_dummy_279) (nb078_alpha_dummy_280 f) (nb078_wpp_notmem_0708) (nb078_wpp_notmem_0709 f) (TEnvFresh.consFresh (nb078_alpha_dummy_248) (nb078_alpha_dummy_250 f) (nb078_wpp_notmem_0682) (nb078_wpp_notmem_0683 f) (TEnvFresh.consFresh (nb078_alpha_dummy_247) (nb078_alpha_dummy_249 f) (nb078_wpp_notmem_0684) (nb078_wpp_notmem_0685 f) (TEnvFresh.consFresh (nb078_alpha_dummy_277) (nb078_alpha_dummy_278 f) (nb078_wpp_notmem_0710) (nb078_wpp_notmem_0711 f) (TEnvFresh.consFresh (nb078_alpha_dummy_251) (nb078_alpha_dummy_252 f) (nb078_wpp_notmem_0688) (nb078_wpp_notmem_0689 f) (TEnvFresh.consFresh (nb078_alpha_dummy_244) (nb078_alpha_dummy_246 f) (nb078_wpp_notmem_0690) (nb078_wpp_notmem_0691 f) (TEnvFresh.consFresh (nb078_alpha_dummy_243) (nb078_alpha_dummy_245 f) (nb078_wpp_notmem_0692) (nb078_wpp_notmem_0693 f) (TEnvFresh.consFresh (nb078_alpha_dummy_000) f (nb078_wpp_notmem_0096) (nb078_wpp_notmem_0097 f) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0098) (nb078_wpp_notmem_0099 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0100) (nb078_wpp_notmem_0101 x) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))

noncomputable def nb078_wpp_refl_0099 (x : Var) (y : Var) (f : Var) : TReflOn [((nb078_alpha_dummy_259), (nb078_alpha_dummy_260 f)), ((nb078_alpha_dummy_255), (nb078_alpha_dummy_257 f)), ((nb078_alpha_dummy_256), (nb078_alpha_dummy_258 f)), ((nb078_alpha_dummy_281), (nb078_alpha_dummy_282 f)), ((nb078_alpha_dummy_279), (nb078_alpha_dummy_280 f)), ((nb078_alpha_dummy_248), (nb078_alpha_dummy_250 f)), ((nb078_alpha_dummy_247), (nb078_alpha_dummy_249 f)), ((nb078_alpha_dummy_277), (nb078_alpha_dummy_278 f)), ((nb078_alpha_dummy_251), (nb078_alpha_dummy_252 f)), ((nb078_alpha_dummy_244), (nb078_alpha_dummy_246 f)), ((nb078_alpha_dummy_243), (nb078_alpha_dummy_245 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0099 x y f)

theorem nb078_wpp_notmem_0712 : (nb078_alpha_dummy_279) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_279, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0210)

theorem nb078_wpp_notmem_0713 (f : Var) : (nb078_alpha_dummy_280 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_280, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0211 f)

theorem nb078_wpp_notmem_0714 : (nb078_alpha_dummy_248) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_248, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0200)

theorem nb078_wpp_notmem_0715 (f : Var) : (nb078_alpha_dummy_250 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_250, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0201 f)

theorem nb078_wpp_notmem_0716 : (nb078_alpha_dummy_247) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_247, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0202)

theorem nb078_wpp_notmem_0717 (f : Var) : (nb078_alpha_dummy_249 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_249, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0203 f)

theorem nb078_wpp_notmem_0718 : (nb078_alpha_dummy_277) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_277, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0212)

theorem nb078_wpp_notmem_0719 (f : Var) : (nb078_alpha_dummy_278 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_278, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0213 f)

theorem nb078_wpp_notmem_0720 : (nb078_alpha_dummy_251) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_251, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0206)

theorem nb078_wpp_notmem_0721 (f : Var) : (nb078_alpha_dummy_252 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_252, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0207 f)

theorem nb078_wpp_notmem_0722 : (nb078_alpha_dummy_244) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_244, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0184)

theorem nb078_wpp_notmem_0723 (f : Var) : (nb078_alpha_dummy_246 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_246, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0185 f)

theorem nb078_wpp_notmem_0724 : (nb078_alpha_dummy_243) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_243, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0186)

theorem nb078_wpp_notmem_0725 (f : Var) : (nb078_alpha_dummy_245 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_245, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0187 f)

theorem nb078_compact_envfresh_0100 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb078_alpha_dummy_279), (nb078_alpha_dummy_280 f)), ((nb078_alpha_dummy_248), (nb078_alpha_dummy_250 f)), ((nb078_alpha_dummy_247), (nb078_alpha_dummy_249 f)), ((nb078_alpha_dummy_277), (nb078_alpha_dummy_278 f)), ((nb078_alpha_dummy_251), (nb078_alpha_dummy_252 f)), ((nb078_alpha_dummy_244), (nb078_alpha_dummy_246 f)), ((nb078_alpha_dummy_243), (nb078_alpha_dummy_245 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_279) (nb078_alpha_dummy_280 f) (nb078_wpp_notmem_0712) (nb078_wpp_notmem_0713 f) (TEnvFresh.consFresh (nb078_alpha_dummy_248) (nb078_alpha_dummy_250 f) (nb078_wpp_notmem_0714) (nb078_wpp_notmem_0715 f) (TEnvFresh.consFresh (nb078_alpha_dummy_247) (nb078_alpha_dummy_249 f) (nb078_wpp_notmem_0716) (nb078_wpp_notmem_0717 f) (TEnvFresh.consFresh (nb078_alpha_dummy_277) (nb078_alpha_dummy_278 f) (nb078_wpp_notmem_0718) (nb078_wpp_notmem_0719 f) (TEnvFresh.consFresh (nb078_alpha_dummy_251) (nb078_alpha_dummy_252 f) (nb078_wpp_notmem_0720) (nb078_wpp_notmem_0721 f) (TEnvFresh.consFresh (nb078_alpha_dummy_244) (nb078_alpha_dummy_246 f) (nb078_wpp_notmem_0722) (nb078_wpp_notmem_0723 f) (TEnvFresh.consFresh (nb078_alpha_dummy_243) (nb078_alpha_dummy_245 f) (nb078_wpp_notmem_0724) (nb078_wpp_notmem_0725 f) (TEnvFresh.consFresh (nb078_alpha_dummy_000) f (nb078_wpp_notmem_0140) (nb078_wpp_notmem_0141 f) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0142) (nb078_wpp_notmem_0143 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0144) (nb078_wpp_notmem_0145 x) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))))

noncomputable def nb078_wpp_refl_0100 (x : Var) (y : Var) (f : Var) : TReflOn [((nb078_alpha_dummy_279), (nb078_alpha_dummy_280 f)), ((nb078_alpha_dummy_248), (nb078_alpha_dummy_250 f)), ((nb078_alpha_dummy_247), (nb078_alpha_dummy_249 f)), ((nb078_alpha_dummy_277), (nb078_alpha_dummy_278 f)), ((nb078_alpha_dummy_251), (nb078_alpha_dummy_252 f)), ((nb078_alpha_dummy_244), (nb078_alpha_dummy_246 f)), ((nb078_alpha_dummy_243), (nb078_alpha_dummy_245 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0100 x y f)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
