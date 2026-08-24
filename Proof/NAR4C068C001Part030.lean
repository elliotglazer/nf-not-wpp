import NAR4C068C001Part029

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

theorem nb068_wpp_notmem_0634 : (nb068_alpha_dummy_243) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_243, fv_syn_c1c] using (nb068_compact_fv_empty_0200)

theorem nb068_compact_fv_empty_0201 (f : Var) : (nb068_alpha_dummy_245 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0635 (f : Var) : (nb068_alpha_dummy_245 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_245, fv_syn_c1c] using (nb068_compact_fv_empty_0201 f)

theorem nb068_compact_fv_empty_0202 : (nb068_alpha_dummy_249) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0636 : (nb068_alpha_dummy_249) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_249, fv_syn_c1c] using (nb068_compact_fv_empty_0202)

theorem nb068_compact_fv_empty_0203 (f : Var) : (nb068_alpha_dummy_250 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0637 (f : Var) : (nb068_alpha_dummy_250 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_250, fv_syn_c1c] using (nb068_compact_fv_empty_0203 f)

theorem nb068_compact_fv_empty_0204 : (nb068_alpha_dummy_247) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0638 : (nb068_alpha_dummy_247) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_247, fv_syn_c1c] using (nb068_compact_fv_empty_0204)

theorem nb068_compact_fv_empty_0205 (f : Var) : (nb068_alpha_dummy_248 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0639 (f : Var) : (nb068_alpha_dummy_248 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_248, fv_syn_c1c] using (nb068_compact_fv_empty_0205 f)

theorem nb068_wpp_notmem_0640 : (nb068_alpha_dummy_240) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_240, fv_syn_c1c] using (nb068_compact_fv_empty_0182)

theorem nb068_wpp_notmem_0641 (f : Var) : (nb068_alpha_dummy_242 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_242, fv_syn_c1c] using (nb068_compact_fv_empty_0183 f)

theorem nb068_wpp_notmem_0642 : (nb068_alpha_dummy_239) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_239, fv_syn_c1c] using (nb068_compact_fv_empty_0184)

theorem nb068_wpp_notmem_0643 (f : Var) : (nb068_alpha_dummy_241 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_241, fv_syn_c1c] using (nb068_compact_fv_empty_0185 f)

theorem nb068_compact_envfresh_0079 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_259), (nb068_alpha_dummy_262 f)), ((nb068_alpha_dummy_258), (nb068_alpha_dummy_261 f)), ((nb068_alpha_dummy_257), (nb068_alpha_dummy_260 f)), ((nb068_alpha_dummy_255), (nb068_alpha_dummy_256 f)), ((nb068_alpha_dummy_251), (nb068_alpha_dummy_253 f)), ((nb068_alpha_dummy_252), (nb068_alpha_dummy_254 f)), ((nb068_alpha_dummy_244), (nb068_alpha_dummy_246 f)), ((nb068_alpha_dummy_243), (nb068_alpha_dummy_245 f)), ((nb068_alpha_dummy_249), (nb068_alpha_dummy_250 f)), ((nb068_alpha_dummy_247), (nb068_alpha_dummy_248 f)), ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)), ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_259) (nb068_alpha_dummy_262 f) (nb068_wpp_notmem_0620) (nb068_wpp_notmem_0621 f) (TEnvFresh.consFresh (nb068_alpha_dummy_258) (nb068_alpha_dummy_261 f) (nb068_wpp_notmem_0622) (nb068_wpp_notmem_0623 f) (TEnvFresh.consFresh (nb068_alpha_dummy_257) (nb068_alpha_dummy_260 f) (nb068_wpp_notmem_0624) (nb068_wpp_notmem_0625 f) (TEnvFresh.consFresh (nb068_alpha_dummy_255) (nb068_alpha_dummy_256 f) (nb068_wpp_notmem_0626) (nb068_wpp_notmem_0627 f) (TEnvFresh.consFresh (nb068_alpha_dummy_251) (nb068_alpha_dummy_253 f) (nb068_wpp_notmem_0628) (nb068_wpp_notmem_0629 f) (TEnvFresh.consFresh (nb068_alpha_dummy_252) (nb068_alpha_dummy_254 f) (nb068_wpp_notmem_0630) (nb068_wpp_notmem_0631 f) (TEnvFresh.consFresh (nb068_alpha_dummy_244) (nb068_alpha_dummy_246 f) (nb068_wpp_notmem_0632) (nb068_wpp_notmem_0633 f) (TEnvFresh.consFresh (nb068_alpha_dummy_243) (nb068_alpha_dummy_245 f) (nb068_wpp_notmem_0634) (nb068_wpp_notmem_0635 f) (TEnvFresh.consFresh (nb068_alpha_dummy_249) (nb068_alpha_dummy_250 f) (nb068_wpp_notmem_0636) (nb068_wpp_notmem_0637 f) (TEnvFresh.consFresh (nb068_alpha_dummy_247) (nb068_alpha_dummy_248 f) (nb068_wpp_notmem_0638) (nb068_wpp_notmem_0639 f) (TEnvFresh.consFresh (nb068_alpha_dummy_240) (nb068_alpha_dummy_242 f) (nb068_wpp_notmem_0640) (nb068_wpp_notmem_0641 f) (TEnvFresh.consFresh (nb068_alpha_dummy_239) (nb068_alpha_dummy_241 f) (nb068_wpp_notmem_0642) (nb068_wpp_notmem_0643 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0136) (nb068_wpp_notmem_0137 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0020) (nb068_wpp_notmem_0021 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0022) (nb068_wpp_notmem_0023 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0024) (nb068_wpp_notmem_0025 x y f) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))

noncomputable def nb068_wpp_refl_0079 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_259), (nb068_alpha_dummy_262 f)), ((nb068_alpha_dummy_258), (nb068_alpha_dummy_261 f)), ((nb068_alpha_dummy_257), (nb068_alpha_dummy_260 f)), ((nb068_alpha_dummy_255), (nb068_alpha_dummy_256 f)), ((nb068_alpha_dummy_251), (nb068_alpha_dummy_253 f)), ((nb068_alpha_dummy_252), (nb068_alpha_dummy_254 f)), ((nb068_alpha_dummy_244), (nb068_alpha_dummy_246 f)), ((nb068_alpha_dummy_243), (nb068_alpha_dummy_245 f)), ((nb068_alpha_dummy_249), (nb068_alpha_dummy_250 f)), ((nb068_alpha_dummy_247), (nb068_alpha_dummy_248 f)), ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)), ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0079 x y f)

theorem nb068_wpp_notmem_0644 : (nb068_alpha_dummy_259) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_259, fv_syn_c0] using (nb068_compact_fv_empty_0186)

theorem nb068_wpp_notmem_0645 (f : Var) : (nb068_alpha_dummy_262 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_262, fv_syn_c0] using (nb068_compact_fv_empty_0187 f)

theorem nb068_wpp_notmem_0646 : (nb068_alpha_dummy_258) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_258, fv_syn_c0] using (nb068_compact_fv_empty_0188)

theorem nb068_wpp_notmem_0647 (f : Var) : (nb068_alpha_dummy_261 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_261, fv_syn_c0] using (nb068_compact_fv_empty_0189 f)

theorem nb068_wpp_notmem_0648 : (nb068_alpha_dummy_257) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_257, fv_syn_c0] using (nb068_compact_fv_empty_0190)

theorem nb068_wpp_notmem_0649 (f : Var) : (nb068_alpha_dummy_260 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_260, fv_syn_c0] using (nb068_compact_fv_empty_0191 f)

theorem nb068_wpp_notmem_0650 : (nb068_alpha_dummy_255) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_255, fv_syn_c0] using (nb068_compact_fv_empty_0192)

theorem nb068_wpp_notmem_0651 (f : Var) : (nb068_alpha_dummy_256 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_256, fv_syn_c0] using (nb068_compact_fv_empty_0193 f)

theorem nb068_wpp_notmem_0652 : (nb068_alpha_dummy_251) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_251, fv_syn_c0] using (nb068_compact_fv_empty_0194)

theorem nb068_wpp_notmem_0653 (f : Var) : (nb068_alpha_dummy_253 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_253, fv_syn_c0] using (nb068_compact_fv_empty_0195 f)

theorem nb068_wpp_notmem_0654 : (nb068_alpha_dummy_252) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_252, fv_syn_c0] using (nb068_compact_fv_empty_0196)

theorem nb068_wpp_notmem_0655 (f : Var) : (nb068_alpha_dummy_254 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_254, fv_syn_c0] using (nb068_compact_fv_empty_0197 f)

theorem nb068_wpp_notmem_0656 : (nb068_alpha_dummy_244) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_244, fv_syn_c0] using (nb068_compact_fv_empty_0198)

theorem nb068_wpp_notmem_0657 (f : Var) : (nb068_alpha_dummy_246 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_246, fv_syn_c0] using (nb068_compact_fv_empty_0199 f)

theorem nb068_wpp_notmem_0658 : (nb068_alpha_dummy_243) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_243, fv_syn_c0] using (nb068_compact_fv_empty_0200)

theorem nb068_wpp_notmem_0659 (f : Var) : (nb068_alpha_dummy_245 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_245, fv_syn_c0] using (nb068_compact_fv_empty_0201 f)

theorem nb068_wpp_notmem_0660 : (nb068_alpha_dummy_249) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_249, fv_syn_c0] using (nb068_compact_fv_empty_0202)

theorem nb068_wpp_notmem_0661 (f : Var) : (nb068_alpha_dummy_250 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_250, fv_syn_c0] using (nb068_compact_fv_empty_0203 f)

theorem nb068_wpp_notmem_0662 : (nb068_alpha_dummy_247) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_247, fv_syn_c0] using (nb068_compact_fv_empty_0204)

theorem nb068_wpp_notmem_0663 (f : Var) : (nb068_alpha_dummy_248 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_248, fv_syn_c0] using (nb068_compact_fv_empty_0205 f)

theorem nb068_wpp_notmem_0664 : (nb068_alpha_dummy_240) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_240, fv_syn_c0] using (nb068_compact_fv_empty_0182)

theorem nb068_wpp_notmem_0665 (f : Var) : (nb068_alpha_dummy_242 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_242, fv_syn_c0] using (nb068_compact_fv_empty_0183 f)

theorem nb068_wpp_notmem_0666 : (nb068_alpha_dummy_239) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_239, fv_syn_c0] using (nb068_compact_fv_empty_0184)

theorem nb068_wpp_notmem_0667 (f : Var) : (nb068_alpha_dummy_241 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_241, fv_syn_c0] using (nb068_compact_fv_empty_0185 f)

theorem nb068_compact_envfresh_0080 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_259), (nb068_alpha_dummy_262 f)), ((nb068_alpha_dummy_258), (nb068_alpha_dummy_261 f)), ((nb068_alpha_dummy_257), (nb068_alpha_dummy_260 f)), ((nb068_alpha_dummy_255), (nb068_alpha_dummy_256 f)), ((nb068_alpha_dummy_251), (nb068_alpha_dummy_253 f)), ((nb068_alpha_dummy_252), (nb068_alpha_dummy_254 f)), ((nb068_alpha_dummy_244), (nb068_alpha_dummy_246 f)), ((nb068_alpha_dummy_243), (nb068_alpha_dummy_245 f)), ((nb068_alpha_dummy_249), (nb068_alpha_dummy_250 f)), ((nb068_alpha_dummy_247), (nb068_alpha_dummy_248 f)), ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)), ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_259) (nb068_alpha_dummy_262 f) (nb068_wpp_notmem_0644) (nb068_wpp_notmem_0645 f) (TEnvFresh.consFresh (nb068_alpha_dummy_258) (nb068_alpha_dummy_261 f) (nb068_wpp_notmem_0646) (nb068_wpp_notmem_0647 f) (TEnvFresh.consFresh (nb068_alpha_dummy_257) (nb068_alpha_dummy_260 f) (nb068_wpp_notmem_0648) (nb068_wpp_notmem_0649 f) (TEnvFresh.consFresh (nb068_alpha_dummy_255) (nb068_alpha_dummy_256 f) (nb068_wpp_notmem_0650) (nb068_wpp_notmem_0651 f) (TEnvFresh.consFresh (nb068_alpha_dummy_251) (nb068_alpha_dummy_253 f) (nb068_wpp_notmem_0652) (nb068_wpp_notmem_0653 f) (TEnvFresh.consFresh (nb068_alpha_dummy_252) (nb068_alpha_dummy_254 f) (nb068_wpp_notmem_0654) (nb068_wpp_notmem_0655 f) (TEnvFresh.consFresh (nb068_alpha_dummy_244) (nb068_alpha_dummy_246 f) (nb068_wpp_notmem_0656) (nb068_wpp_notmem_0657 f) (TEnvFresh.consFresh (nb068_alpha_dummy_243) (nb068_alpha_dummy_245 f) (nb068_wpp_notmem_0658) (nb068_wpp_notmem_0659 f) (TEnvFresh.consFresh (nb068_alpha_dummy_249) (nb068_alpha_dummy_250 f) (nb068_wpp_notmem_0660) (nb068_wpp_notmem_0661 f) (TEnvFresh.consFresh (nb068_alpha_dummy_247) (nb068_alpha_dummy_248 f) (nb068_wpp_notmem_0662) (nb068_wpp_notmem_0663 f) (TEnvFresh.consFresh (nb068_alpha_dummy_240) (nb068_alpha_dummy_242 f) (nb068_wpp_notmem_0664) (nb068_wpp_notmem_0665 f) (TEnvFresh.consFresh (nb068_alpha_dummy_239) (nb068_alpha_dummy_241 f) (nb068_wpp_notmem_0666) (nb068_wpp_notmem_0667 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0168) (nb068_wpp_notmem_0169 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0046) (nb068_wpp_notmem_0047 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0048) (nb068_wpp_notmem_0049 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0050) (nb068_wpp_notmem_0051 x y f) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))

noncomputable def nb068_wpp_refl_0080 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_259), (nb068_alpha_dummy_262 f)), ((nb068_alpha_dummy_258), (nb068_alpha_dummy_261 f)), ((nb068_alpha_dummy_257), (nb068_alpha_dummy_260 f)), ((nb068_alpha_dummy_255), (nb068_alpha_dummy_256 f)), ((nb068_alpha_dummy_251), (nb068_alpha_dummy_253 f)), ((nb068_alpha_dummy_252), (nb068_alpha_dummy_254 f)), ((nb068_alpha_dummy_244), (nb068_alpha_dummy_246 f)), ((nb068_alpha_dummy_243), (nb068_alpha_dummy_245 f)), ((nb068_alpha_dummy_249), (nb068_alpha_dummy_250 f)), ((nb068_alpha_dummy_247), (nb068_alpha_dummy_248 f)), ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)), ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0080 x y f)

noncomputable def nb068_split_alpha_0061 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb068_alpha_dummy_259), (nb068_alpha_dummy_262 f)), ((nb068_alpha_dummy_258), (nb068_alpha_dummy_261 f)), ((nb068_alpha_dummy_257), (nb068_alpha_dummy_260 f)), ((nb068_alpha_dummy_255), (nb068_alpha_dummy_256 f)), ((nb068_alpha_dummy_251), (nb068_alpha_dummy_253 f)), ((nb068_alpha_dummy_252), (nb068_alpha_dummy_254 f)), ((nb068_alpha_dummy_244), (nb068_alpha_dummy_246 f)), ((nb068_alpha_dummy_243), (nb068_alpha_dummy_245 f)), ((nb068_alpha_dummy_249), (nb068_alpha_dummy_250 f)), ((nb068_alpha_dummy_247), (nb068_alpha_dummy_248 f)), ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)), ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_258)) (Class.cv (nb068_alpha_dummy_259))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_257)) (syn_cun (Class.cv (nb068_alpha_dummy_258)) (Class.cv (nb068_alpha_dummy_259)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_261 f)) (Class.cv (nb068_alpha_dummy_262 f))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_260 f)) (syn_cun (Class.cv (nb068_alpha_dummy_261 f)) (Class.cv (nb068_alpha_dummy_262 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0266) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0267 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0264) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0265 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0270) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0271 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0268) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0269 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0266) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0267 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0264) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0265 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0270) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0271 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0268) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0269 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_259), (nb068_alpha_dummy_262 f)), ((nb068_alpha_dummy_258), (nb068_alpha_dummy_261 f)), ((nb068_alpha_dummy_257), (nb068_alpha_dummy_260 f)), ((nb068_alpha_dummy_255), (nb068_alpha_dummy_256 f)), ((nb068_alpha_dummy_251), (nb068_alpha_dummy_253 f)), ((nb068_alpha_dummy_252), (nb068_alpha_dummy_254 f)), ((nb068_alpha_dummy_244), (nb068_alpha_dummy_246 f)), ((nb068_alpha_dummy_243), (nb068_alpha_dummy_245 f)), ((nb068_alpha_dummy_249), (nb068_alpha_dummy_250 f)), ((nb068_alpha_dummy_247), (nb068_alpha_dummy_248 f)), ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)), ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_c0) (nb068_wpp_refl_0080 x y f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0274) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0275 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0272) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0273 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0274) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0275 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0272) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0273 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0278) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0279 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0276) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0277 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0278) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0279 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0276) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0277 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb068_wpp_notmem_0668 : (nb068_alpha_dummy_255) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_255, fv_syn_cnnc] using (nb068_compact_fv_empty_0192)

theorem nb068_wpp_notmem_0669 (f : Var) : (nb068_alpha_dummy_256 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_256, fv_syn_cnnc] using (nb068_compact_fv_empty_0193 f)

theorem nb068_wpp_notmem_0670 : (nb068_alpha_dummy_251) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_251, fv_syn_cnnc] using (nb068_compact_fv_empty_0194)

theorem nb068_wpp_notmem_0671 (f : Var) : (nb068_alpha_dummy_253 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_253, fv_syn_cnnc] using (nb068_compact_fv_empty_0195 f)

theorem nb068_wpp_notmem_0672 : (nb068_alpha_dummy_252) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_252, fv_syn_cnnc] using (nb068_compact_fv_empty_0196)

theorem nb068_wpp_notmem_0673 (f : Var) : (nb068_alpha_dummy_254 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_254, fv_syn_cnnc] using (nb068_compact_fv_empty_0197 f)

theorem nb068_wpp_notmem_0674 : (nb068_alpha_dummy_244) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_244, fv_syn_cnnc] using (nb068_compact_fv_empty_0198)

theorem nb068_wpp_notmem_0675 (f : Var) : (nb068_alpha_dummy_246 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_246, fv_syn_cnnc] using (nb068_compact_fv_empty_0199 f)

theorem nb068_wpp_notmem_0676 : (nb068_alpha_dummy_243) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_243, fv_syn_cnnc] using (nb068_compact_fv_empty_0200)

theorem nb068_wpp_notmem_0677 (f : Var) : (nb068_alpha_dummy_245 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_245, fv_syn_cnnc] using (nb068_compact_fv_empty_0201 f)

theorem nb068_wpp_notmem_0678 : (nb068_alpha_dummy_249) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_249, fv_syn_cnnc] using (nb068_compact_fv_empty_0202)

theorem nb068_wpp_notmem_0679 (f : Var) : (nb068_alpha_dummy_250 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_250, fv_syn_cnnc] using (nb068_compact_fv_empty_0203 f)

theorem nb068_wpp_notmem_0680 : (nb068_alpha_dummy_247) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_247, fv_syn_cnnc] using (nb068_compact_fv_empty_0204)

theorem nb068_wpp_notmem_0681 (f : Var) : (nb068_alpha_dummy_248 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_248, fv_syn_cnnc] using (nb068_compact_fv_empty_0205 f)

theorem nb068_wpp_notmem_0682 : (nb068_alpha_dummy_240) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_240, fv_syn_cnnc] using (nb068_compact_fv_empty_0182)

theorem nb068_wpp_notmem_0683 (f : Var) : (nb068_alpha_dummy_242 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_242, fv_syn_cnnc] using (nb068_compact_fv_empty_0183 f)

theorem nb068_wpp_notmem_0684 : (nb068_alpha_dummy_239) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_239, fv_syn_cnnc] using (nb068_compact_fv_empty_0184)

theorem nb068_wpp_notmem_0685 (f : Var) : (nb068_alpha_dummy_241 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_241, fv_syn_cnnc] using (nb068_compact_fv_empty_0185 f)

theorem nb068_compact_envfresh_0081 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_255), (nb068_alpha_dummy_256 f)), ((nb068_alpha_dummy_251), (nb068_alpha_dummy_253 f)), ((nb068_alpha_dummy_252), (nb068_alpha_dummy_254 f)), ((nb068_alpha_dummy_244), (nb068_alpha_dummy_246 f)), ((nb068_alpha_dummy_243), (nb068_alpha_dummy_245 f)), ((nb068_alpha_dummy_249), (nb068_alpha_dummy_250 f)), ((nb068_alpha_dummy_247), (nb068_alpha_dummy_248 f)), ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)), ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_255) (nb068_alpha_dummy_256 f) (nb068_wpp_notmem_0668) (nb068_wpp_notmem_0669 f) (TEnvFresh.consFresh (nb068_alpha_dummy_251) (nb068_alpha_dummy_253 f) (nb068_wpp_notmem_0670) (nb068_wpp_notmem_0671 f) (TEnvFresh.consFresh (nb068_alpha_dummy_252) (nb068_alpha_dummy_254 f) (nb068_wpp_notmem_0672) (nb068_wpp_notmem_0673 f) (TEnvFresh.consFresh (nb068_alpha_dummy_244) (nb068_alpha_dummy_246 f) (nb068_wpp_notmem_0674) (nb068_wpp_notmem_0675 f) (TEnvFresh.consFresh (nb068_alpha_dummy_243) (nb068_alpha_dummy_245 f) (nb068_wpp_notmem_0676) (nb068_wpp_notmem_0677 f) (TEnvFresh.consFresh (nb068_alpha_dummy_249) (nb068_alpha_dummy_250 f) (nb068_wpp_notmem_0678) (nb068_wpp_notmem_0679 f) (TEnvFresh.consFresh (nb068_alpha_dummy_247) (nb068_alpha_dummy_248 f) (nb068_wpp_notmem_0680) (nb068_wpp_notmem_0681 f) (TEnvFresh.consFresh (nb068_alpha_dummy_240) (nb068_alpha_dummy_242 f) (nb068_wpp_notmem_0682) (nb068_wpp_notmem_0683 f) (TEnvFresh.consFresh (nb068_alpha_dummy_239) (nb068_alpha_dummy_241 f) (nb068_wpp_notmem_0684) (nb068_wpp_notmem_0685 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0194) (nb068_wpp_notmem_0195 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0066) (nb068_wpp_notmem_0067 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0068) (nb068_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0070) (nb068_wpp_notmem_0071 x y f) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))

noncomputable def nb068_wpp_refl_0081 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_255), (nb068_alpha_dummy_256 f)), ((nb068_alpha_dummy_251), (nb068_alpha_dummy_253 f)), ((nb068_alpha_dummy_252), (nb068_alpha_dummy_254 f)), ((nb068_alpha_dummy_244), (nb068_alpha_dummy_246 f)), ((nb068_alpha_dummy_243), (nb068_alpha_dummy_245 f)), ((nb068_alpha_dummy_249), (nb068_alpha_dummy_250 f)), ((nb068_alpha_dummy_247), (nb068_alpha_dummy_248 f)), ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)), ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0081 x y f)

noncomputable def nb068_split_alpha_0062 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb068_alpha_dummy_244), (nb068_alpha_dummy_246 f)), ((nb068_alpha_dummy_243), (nb068_alpha_dummy_245 f)), ((nb068_alpha_dummy_249), (nb068_alpha_dummy_250 f)), ((nb068_alpha_dummy_247), (nb068_alpha_dummy_248 f)), ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)), ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (Wff.classEq (Class.cv (nb068_alpha_dummy_243)) (syn_cphi (Class.cv (nb068_alpha_dummy_244)))) (Wff.classEq (Class.cv (nb068_alpha_dummy_245 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_246 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_240))).fv ∪ ((Class.cv (nb068_alpha_dummy_239))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_242 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_241 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0258) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0259 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0258) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0259 f) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_244))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_246 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0262) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0263 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0262) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0263 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0260) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0261 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_259), (nb068_alpha_dummy_262 f)), ((nb068_alpha_dummy_258), (nb068_alpha_dummy_261 f)), ((nb068_alpha_dummy_257), (nb068_alpha_dummy_260 f)), ((nb068_alpha_dummy_255), (nb068_alpha_dummy_256 f)), ((nb068_alpha_dummy_251), (nb068_alpha_dummy_253 f)), ((nb068_alpha_dummy_252), (nb068_alpha_dummy_254 f)), ((nb068_alpha_dummy_244), (nb068_alpha_dummy_246 f)), ((nb068_alpha_dummy_243), (nb068_alpha_dummy_245 f)), ((nb068_alpha_dummy_249), (nb068_alpha_dummy_250 f)), ((nb068_alpha_dummy_247), (nb068_alpha_dummy_248 f)), ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)), ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_c1c) (nb068_wpp_refl_0079 x y f))) (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0061 x y f)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0260) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0261 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_255), (nb068_alpha_dummy_256 f)), ((nb068_alpha_dummy_251), (nb068_alpha_dummy_253 f)), ((nb068_alpha_dummy_252), (nb068_alpha_dummy_254 f)), ((nb068_alpha_dummy_244), (nb068_alpha_dummy_246 f)), ((nb068_alpha_dummy_243), (nb068_alpha_dummy_245 f)), ((nb068_alpha_dummy_249), (nb068_alpha_dummy_250 f)), ((nb068_alpha_dummy_247), (nb068_alpha_dummy_248 f)), ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)), ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_cnnc) (nb068_wpp_refl_0081 x y f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0260) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0261 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0260) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0261 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_255), (nb068_alpha_dummy_256 f)), ((nb068_alpha_dummy_251), (nb068_alpha_dummy_253 f)), ((nb068_alpha_dummy_252), (nb068_alpha_dummy_254 f)), ((nb068_alpha_dummy_244), (nb068_alpha_dummy_246 f)), ((nb068_alpha_dummy_243), (nb068_alpha_dummy_245 f)), ((nb068_alpha_dummy_249), (nb068_alpha_dummy_250 f)), ((nb068_alpha_dummy_247), (nb068_alpha_dummy_248 f)), ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)), ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_cnnc) (nb068_wpp_refl_0081 x y f))))))))))))))))))

theorem nb068_compact_fv_empty_0206 : (nb068_alpha_dummy_277) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0686 : (nb068_alpha_dummy_277) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_277, fv_syn_c1c] using (nb068_compact_fv_empty_0206)

theorem nb068_compact_fv_empty_0207 (f : Var) : (nb068_alpha_dummy_278 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0687 (f : Var) : (nb068_alpha_dummy_278 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_278, fv_syn_c1c] using (nb068_compact_fv_empty_0207 f)

theorem nb068_compact_fv_empty_0208 : (nb068_alpha_dummy_275) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0688 : (nb068_alpha_dummy_275) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_275, fv_syn_c1c] using (nb068_compact_fv_empty_0208)

theorem nb068_compact_fv_empty_0209 (f : Var) : (nb068_alpha_dummy_276 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0689 (f : Var) : (nb068_alpha_dummy_276 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_276, fv_syn_c1c] using (nb068_compact_fv_empty_0209 f)

theorem nb068_compact_fv_empty_0210 : (nb068_alpha_dummy_273) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0690 : (nb068_alpha_dummy_273) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_273, fv_syn_c1c] using (nb068_compact_fv_empty_0210)

theorem nb068_compact_fv_empty_0211 (f : Var) : (nb068_alpha_dummy_274 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0691 (f : Var) : (nb068_alpha_dummy_274 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_274, fv_syn_c1c] using (nb068_compact_fv_empty_0211 f)

theorem nb068_compact_envfresh_0082 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_259), (nb068_alpha_dummy_262 f)), ((nb068_alpha_dummy_258), (nb068_alpha_dummy_261 f)), ((nb068_alpha_dummy_257), (nb068_alpha_dummy_260 f)), ((nb068_alpha_dummy_255), (nb068_alpha_dummy_256 f)), ((nb068_alpha_dummy_251), (nb068_alpha_dummy_253 f)), ((nb068_alpha_dummy_252), (nb068_alpha_dummy_254 f)), ((nb068_alpha_dummy_277), (nb068_alpha_dummy_278 f)), ((nb068_alpha_dummy_275), (nb068_alpha_dummy_276 f)), ((nb068_alpha_dummy_244), (nb068_alpha_dummy_246 f)), ((nb068_alpha_dummy_243), (nb068_alpha_dummy_245 f)), ((nb068_alpha_dummy_273), (nb068_alpha_dummy_274 f)), ((nb068_alpha_dummy_247), (nb068_alpha_dummy_248 f)), ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)), ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_259) (nb068_alpha_dummy_262 f) (nb068_wpp_notmem_0620) (nb068_wpp_notmem_0621 f) (TEnvFresh.consFresh (nb068_alpha_dummy_258) (nb068_alpha_dummy_261 f) (nb068_wpp_notmem_0622) (nb068_wpp_notmem_0623 f) (TEnvFresh.consFresh (nb068_alpha_dummy_257) (nb068_alpha_dummy_260 f) (nb068_wpp_notmem_0624) (nb068_wpp_notmem_0625 f) (TEnvFresh.consFresh (nb068_alpha_dummy_255) (nb068_alpha_dummy_256 f) (nb068_wpp_notmem_0626) (nb068_wpp_notmem_0627 f) (TEnvFresh.consFresh (nb068_alpha_dummy_251) (nb068_alpha_dummy_253 f) (nb068_wpp_notmem_0628) (nb068_wpp_notmem_0629 f) (TEnvFresh.consFresh (nb068_alpha_dummy_252) (nb068_alpha_dummy_254 f) (nb068_wpp_notmem_0630) (nb068_wpp_notmem_0631 f) (TEnvFresh.consFresh (nb068_alpha_dummy_277) (nb068_alpha_dummy_278 f) (nb068_wpp_notmem_0686) (nb068_wpp_notmem_0687 f) (TEnvFresh.consFresh (nb068_alpha_dummy_275) (nb068_alpha_dummy_276 f) (nb068_wpp_notmem_0688) (nb068_wpp_notmem_0689 f) (TEnvFresh.consFresh (nb068_alpha_dummy_244) (nb068_alpha_dummy_246 f) (nb068_wpp_notmem_0632) (nb068_wpp_notmem_0633 f) (TEnvFresh.consFresh (nb068_alpha_dummy_243) (nb068_alpha_dummy_245 f) (nb068_wpp_notmem_0634) (nb068_wpp_notmem_0635 f) (TEnvFresh.consFresh (nb068_alpha_dummy_273) (nb068_alpha_dummy_274 f) (nb068_wpp_notmem_0690) (nb068_wpp_notmem_0691 f) (TEnvFresh.consFresh (nb068_alpha_dummy_247) (nb068_alpha_dummy_248 f) (nb068_wpp_notmem_0638) (nb068_wpp_notmem_0639 f) (TEnvFresh.consFresh (nb068_alpha_dummy_240) (nb068_alpha_dummy_242 f) (nb068_wpp_notmem_0640) (nb068_wpp_notmem_0641 f) (TEnvFresh.consFresh (nb068_alpha_dummy_239) (nb068_alpha_dummy_241 f) (nb068_wpp_notmem_0642) (nb068_wpp_notmem_0643 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0136) (nb068_wpp_notmem_0137 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0020) (nb068_wpp_notmem_0021 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0022) (nb068_wpp_notmem_0023 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0024) (nb068_wpp_notmem_0025 x y f) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))

noncomputable def nb068_wpp_refl_0082 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_259), (nb068_alpha_dummy_262 f)), ((nb068_alpha_dummy_258), (nb068_alpha_dummy_261 f)), ((nb068_alpha_dummy_257), (nb068_alpha_dummy_260 f)), ((nb068_alpha_dummy_255), (nb068_alpha_dummy_256 f)), ((nb068_alpha_dummy_251), (nb068_alpha_dummy_253 f)), ((nb068_alpha_dummy_252), (nb068_alpha_dummy_254 f)), ((nb068_alpha_dummy_277), (nb068_alpha_dummy_278 f)), ((nb068_alpha_dummy_275), (nb068_alpha_dummy_276 f)), ((nb068_alpha_dummy_244), (nb068_alpha_dummy_246 f)), ((nb068_alpha_dummy_243), (nb068_alpha_dummy_245 f)), ((nb068_alpha_dummy_273), (nb068_alpha_dummy_274 f)), ((nb068_alpha_dummy_247), (nb068_alpha_dummy_248 f)), ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)), ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0082 x y f)

theorem nb068_wpp_notmem_0692 : (nb068_alpha_dummy_277) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_277, fv_syn_c0] using (nb068_compact_fv_empty_0206)

theorem nb068_wpp_notmem_0693 (f : Var) : (nb068_alpha_dummy_278 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_278, fv_syn_c0] using (nb068_compact_fv_empty_0207 f)

theorem nb068_wpp_notmem_0694 : (nb068_alpha_dummy_275) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_275, fv_syn_c0] using (nb068_compact_fv_empty_0208)

theorem nb068_wpp_notmem_0695 (f : Var) : (nb068_alpha_dummy_276 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_276, fv_syn_c0] using (nb068_compact_fv_empty_0209 f)

theorem nb068_wpp_notmem_0696 : (nb068_alpha_dummy_273) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_273, fv_syn_c0] using (nb068_compact_fv_empty_0210)

theorem nb068_wpp_notmem_0697 (f : Var) : (nb068_alpha_dummy_274 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_274, fv_syn_c0] using (nb068_compact_fv_empty_0211 f)

theorem nb068_compact_envfresh_0083 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_259), (nb068_alpha_dummy_262 f)), ((nb068_alpha_dummy_258), (nb068_alpha_dummy_261 f)), ((nb068_alpha_dummy_257), (nb068_alpha_dummy_260 f)), ((nb068_alpha_dummy_255), (nb068_alpha_dummy_256 f)), ((nb068_alpha_dummy_251), (nb068_alpha_dummy_253 f)), ((nb068_alpha_dummy_252), (nb068_alpha_dummy_254 f)), ((nb068_alpha_dummy_277), (nb068_alpha_dummy_278 f)), ((nb068_alpha_dummy_275), (nb068_alpha_dummy_276 f)), ((nb068_alpha_dummy_244), (nb068_alpha_dummy_246 f)), ((nb068_alpha_dummy_243), (nb068_alpha_dummy_245 f)), ((nb068_alpha_dummy_273), (nb068_alpha_dummy_274 f)), ((nb068_alpha_dummy_247), (nb068_alpha_dummy_248 f)), ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)), ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_259) (nb068_alpha_dummy_262 f) (nb068_wpp_notmem_0644) (nb068_wpp_notmem_0645 f) (TEnvFresh.consFresh (nb068_alpha_dummy_258) (nb068_alpha_dummy_261 f) (nb068_wpp_notmem_0646) (nb068_wpp_notmem_0647 f) (TEnvFresh.consFresh (nb068_alpha_dummy_257) (nb068_alpha_dummy_260 f) (nb068_wpp_notmem_0648) (nb068_wpp_notmem_0649 f) (TEnvFresh.consFresh (nb068_alpha_dummy_255) (nb068_alpha_dummy_256 f) (nb068_wpp_notmem_0650) (nb068_wpp_notmem_0651 f) (TEnvFresh.consFresh (nb068_alpha_dummy_251) (nb068_alpha_dummy_253 f) (nb068_wpp_notmem_0652) (nb068_wpp_notmem_0653 f) (TEnvFresh.consFresh (nb068_alpha_dummy_252) (nb068_alpha_dummy_254 f) (nb068_wpp_notmem_0654) (nb068_wpp_notmem_0655 f) (TEnvFresh.consFresh (nb068_alpha_dummy_277) (nb068_alpha_dummy_278 f) (nb068_wpp_notmem_0692) (nb068_wpp_notmem_0693 f) (TEnvFresh.consFresh (nb068_alpha_dummy_275) (nb068_alpha_dummy_276 f) (nb068_wpp_notmem_0694) (nb068_wpp_notmem_0695 f) (TEnvFresh.consFresh (nb068_alpha_dummy_244) (nb068_alpha_dummy_246 f) (nb068_wpp_notmem_0656) (nb068_wpp_notmem_0657 f) (TEnvFresh.consFresh (nb068_alpha_dummy_243) (nb068_alpha_dummy_245 f) (nb068_wpp_notmem_0658) (nb068_wpp_notmem_0659 f) (TEnvFresh.consFresh (nb068_alpha_dummy_273) (nb068_alpha_dummy_274 f) (nb068_wpp_notmem_0696) (nb068_wpp_notmem_0697 f) (TEnvFresh.consFresh (nb068_alpha_dummy_247) (nb068_alpha_dummy_248 f) (nb068_wpp_notmem_0662) (nb068_wpp_notmem_0663 f) (TEnvFresh.consFresh (nb068_alpha_dummy_240) (nb068_alpha_dummy_242 f) (nb068_wpp_notmem_0664) (nb068_wpp_notmem_0665 f) (TEnvFresh.consFresh (nb068_alpha_dummy_239) (nb068_alpha_dummy_241 f) (nb068_wpp_notmem_0666) (nb068_wpp_notmem_0667 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0168) (nb068_wpp_notmem_0169 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0046) (nb068_wpp_notmem_0047 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0048) (nb068_wpp_notmem_0049 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0050) (nb068_wpp_notmem_0051 x y f) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))

noncomputable def nb068_wpp_refl_0083 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_259), (nb068_alpha_dummy_262 f)), ((nb068_alpha_dummy_258), (nb068_alpha_dummy_261 f)), ((nb068_alpha_dummy_257), (nb068_alpha_dummy_260 f)), ((nb068_alpha_dummy_255), (nb068_alpha_dummy_256 f)), ((nb068_alpha_dummy_251), (nb068_alpha_dummy_253 f)), ((nb068_alpha_dummy_252), (nb068_alpha_dummy_254 f)), ((nb068_alpha_dummy_277), (nb068_alpha_dummy_278 f)), ((nb068_alpha_dummy_275), (nb068_alpha_dummy_276 f)), ((nb068_alpha_dummy_244), (nb068_alpha_dummy_246 f)), ((nb068_alpha_dummy_243), (nb068_alpha_dummy_245 f)), ((nb068_alpha_dummy_273), (nb068_alpha_dummy_274 f)), ((nb068_alpha_dummy_247), (nb068_alpha_dummy_248 f)), ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)), ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0083 x y f)

noncomputable def nb068_split_alpha_0063 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb068_alpha_dummy_259), (nb068_alpha_dummy_262 f)), ((nb068_alpha_dummy_258), (nb068_alpha_dummy_261 f)), ((nb068_alpha_dummy_257), (nb068_alpha_dummy_260 f)), ((nb068_alpha_dummy_255), (nb068_alpha_dummy_256 f)), ((nb068_alpha_dummy_251), (nb068_alpha_dummy_253 f)), ((nb068_alpha_dummy_252), (nb068_alpha_dummy_254 f)), ((nb068_alpha_dummy_277), (nb068_alpha_dummy_278 f)), ((nb068_alpha_dummy_275), (nb068_alpha_dummy_276 f)), ((nb068_alpha_dummy_244), (nb068_alpha_dummy_246 f)), ((nb068_alpha_dummy_243), (nb068_alpha_dummy_245 f)), ((nb068_alpha_dummy_273), (nb068_alpha_dummy_274 f)), ((nb068_alpha_dummy_247), (nb068_alpha_dummy_248 f)), ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)), ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_258)) (Class.cv (nb068_alpha_dummy_259))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_257)) (syn_cun (Class.cv (nb068_alpha_dummy_258)) (Class.cv (nb068_alpha_dummy_259)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_261 f)) (Class.cv (nb068_alpha_dummy_262 f))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_260 f)) (syn_cun (Class.cv (nb068_alpha_dummy_261 f)) (Class.cv (nb068_alpha_dummy_262 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0266) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0267 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0264) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0265 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0270) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0271 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0268) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0269 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0266) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0267 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0264) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0265 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0270) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0271 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0268) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0269 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_259), (nb068_alpha_dummy_262 f)), ((nb068_alpha_dummy_258), (nb068_alpha_dummy_261 f)), ((nb068_alpha_dummy_257), (nb068_alpha_dummy_260 f)), ((nb068_alpha_dummy_255), (nb068_alpha_dummy_256 f)), ((nb068_alpha_dummy_251), (nb068_alpha_dummy_253 f)), ((nb068_alpha_dummy_252), (nb068_alpha_dummy_254 f)), ((nb068_alpha_dummy_277), (nb068_alpha_dummy_278 f)), ((nb068_alpha_dummy_275), (nb068_alpha_dummy_276 f)), ((nb068_alpha_dummy_244), (nb068_alpha_dummy_246 f)), ((nb068_alpha_dummy_243), (nb068_alpha_dummy_245 f)), ((nb068_alpha_dummy_273), (nb068_alpha_dummy_274 f)), ((nb068_alpha_dummy_247), (nb068_alpha_dummy_248 f)), ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)), ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_c0) (nb068_wpp_refl_0083 x y f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0274) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0275 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0272) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0273 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0274) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0275 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0272) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0273 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_251))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_253 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0278) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0279 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0276) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0277 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0278) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0279 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0276) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0277 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb068_wpp_notmem_0698 : (nb068_alpha_dummy_277) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_277, fv_syn_cnnc] using (nb068_compact_fv_empty_0206)

theorem nb068_wpp_notmem_0699 (f : Var) : (nb068_alpha_dummy_278 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_278, fv_syn_cnnc] using (nb068_compact_fv_empty_0207 f)

theorem nb068_wpp_notmem_0700 : (nb068_alpha_dummy_275) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_275, fv_syn_cnnc] using (nb068_compact_fv_empty_0208)

theorem nb068_wpp_notmem_0701 (f : Var) : (nb068_alpha_dummy_276 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_276, fv_syn_cnnc] using (nb068_compact_fv_empty_0209 f)

theorem nb068_wpp_notmem_0702 : (nb068_alpha_dummy_273) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_273, fv_syn_cnnc] using (nb068_compact_fv_empty_0210)

theorem nb068_wpp_notmem_0703 (f : Var) : (nb068_alpha_dummy_274 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_274, fv_syn_cnnc] using (nb068_compact_fv_empty_0211 f)

theorem nb068_compact_envfresh_0084 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_255), (nb068_alpha_dummy_256 f)), ((nb068_alpha_dummy_251), (nb068_alpha_dummy_253 f)), ((nb068_alpha_dummy_252), (nb068_alpha_dummy_254 f)), ((nb068_alpha_dummy_277), (nb068_alpha_dummy_278 f)), ((nb068_alpha_dummy_275), (nb068_alpha_dummy_276 f)), ((nb068_alpha_dummy_244), (nb068_alpha_dummy_246 f)), ((nb068_alpha_dummy_243), (nb068_alpha_dummy_245 f)), ((nb068_alpha_dummy_273), (nb068_alpha_dummy_274 f)), ((nb068_alpha_dummy_247), (nb068_alpha_dummy_248 f)), ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)), ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_255) (nb068_alpha_dummy_256 f) (nb068_wpp_notmem_0668) (nb068_wpp_notmem_0669 f) (TEnvFresh.consFresh (nb068_alpha_dummy_251) (nb068_alpha_dummy_253 f) (nb068_wpp_notmem_0670) (nb068_wpp_notmem_0671 f) (TEnvFresh.consFresh (nb068_alpha_dummy_252) (nb068_alpha_dummy_254 f) (nb068_wpp_notmem_0672) (nb068_wpp_notmem_0673 f) (TEnvFresh.consFresh (nb068_alpha_dummy_277) (nb068_alpha_dummy_278 f) (nb068_wpp_notmem_0698) (nb068_wpp_notmem_0699 f) (TEnvFresh.consFresh (nb068_alpha_dummy_275) (nb068_alpha_dummy_276 f) (nb068_wpp_notmem_0700) (nb068_wpp_notmem_0701 f) (TEnvFresh.consFresh (nb068_alpha_dummy_244) (nb068_alpha_dummy_246 f) (nb068_wpp_notmem_0674) (nb068_wpp_notmem_0675 f) (TEnvFresh.consFresh (nb068_alpha_dummy_243) (nb068_alpha_dummy_245 f) (nb068_wpp_notmem_0676) (nb068_wpp_notmem_0677 f) (TEnvFresh.consFresh (nb068_alpha_dummy_273) (nb068_alpha_dummy_274 f) (nb068_wpp_notmem_0702) (nb068_wpp_notmem_0703 f) (TEnvFresh.consFresh (nb068_alpha_dummy_247) (nb068_alpha_dummy_248 f) (nb068_wpp_notmem_0680) (nb068_wpp_notmem_0681 f) (TEnvFresh.consFresh (nb068_alpha_dummy_240) (nb068_alpha_dummy_242 f) (nb068_wpp_notmem_0682) (nb068_wpp_notmem_0683 f) (TEnvFresh.consFresh (nb068_alpha_dummy_239) (nb068_alpha_dummy_241 f) (nb068_wpp_notmem_0684) (nb068_wpp_notmem_0685 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0194) (nb068_wpp_notmem_0195 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0066) (nb068_wpp_notmem_0067 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0068) (nb068_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0070) (nb068_wpp_notmem_0071 x y f) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))

noncomputable def nb068_wpp_refl_0084 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_255), (nb068_alpha_dummy_256 f)), ((nb068_alpha_dummy_251), (nb068_alpha_dummy_253 f)), ((nb068_alpha_dummy_252), (nb068_alpha_dummy_254 f)), ((nb068_alpha_dummy_277), (nb068_alpha_dummy_278 f)), ((nb068_alpha_dummy_275), (nb068_alpha_dummy_276 f)), ((nb068_alpha_dummy_244), (nb068_alpha_dummy_246 f)), ((nb068_alpha_dummy_243), (nb068_alpha_dummy_245 f)), ((nb068_alpha_dummy_273), (nb068_alpha_dummy_274 f)), ((nb068_alpha_dummy_247), (nb068_alpha_dummy_248 f)), ((nb068_alpha_dummy_240), (nb068_alpha_dummy_242 f)), ((nb068_alpha_dummy_239), (nb068_alpha_dummy_241 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0084 x y f)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
