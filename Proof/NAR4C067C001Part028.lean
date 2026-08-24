import NAR4C067C001Part027

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

theorem nb067_compact_fv_empty_0219 (f : Var) : (nb067_alpha_dummy_298 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0721 (f : Var) : (nb067_alpha_dummy_298 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_298, fv_syn_c1c] using (nb067_compact_fv_empty_0219 f)

theorem nb067_compact_fv_empty_0220 : (nb067_alpha_dummy_293) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0722 : (nb067_alpha_dummy_293) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_293, fv_syn_c1c] using (nb067_compact_fv_empty_0220)

theorem nb067_compact_fv_empty_0221 (f : Var) : (nb067_alpha_dummy_294 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0723 (f : Var) : (nb067_alpha_dummy_294 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_294, fv_syn_c1c] using (nb067_compact_fv_empty_0221 f)

theorem nb067_compact_fv_empty_0222 : (nb067_alpha_dummy_289) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0724 : (nb067_alpha_dummy_289) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_289, fv_syn_c1c] using (nb067_compact_fv_empty_0222)

theorem nb067_compact_fv_empty_0223 (f : Var) : (nb067_alpha_dummy_291 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0725 (f : Var) : (nb067_alpha_dummy_291 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_291, fv_syn_c1c] using (nb067_compact_fv_empty_0223 f)

theorem nb067_compact_fv_empty_0224 : (nb067_alpha_dummy_290) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0726 : (nb067_alpha_dummy_290) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_290, fv_syn_c1c] using (nb067_compact_fv_empty_0224)

theorem nb067_compact_fv_empty_0225 (f : Var) : (nb067_alpha_dummy_292 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0727 (f : Var) : (nb067_alpha_dummy_292 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_292, fv_syn_c1c] using (nb067_compact_fv_empty_0225 f)

theorem nb067_compact_fv_empty_0226 : (nb067_alpha_dummy_282) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0728 : (nb067_alpha_dummy_282) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_282, fv_syn_c1c] using (nb067_compact_fv_empty_0226)

theorem nb067_compact_fv_empty_0227 (f : Var) : (nb067_alpha_dummy_284 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0729 (f : Var) : (nb067_alpha_dummy_284 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_284, fv_syn_c1c] using (nb067_compact_fv_empty_0227 f)

theorem nb067_compact_fv_empty_0228 : (nb067_alpha_dummy_281) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0730 : (nb067_alpha_dummy_281) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_281, fv_syn_c1c] using (nb067_compact_fv_empty_0228)

theorem nb067_compact_fv_empty_0229 (f : Var) : (nb067_alpha_dummy_283 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0731 (f : Var) : (nb067_alpha_dummy_283 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_283, fv_syn_c1c] using (nb067_compact_fv_empty_0229 f)

theorem nb067_compact_fv_empty_0230 : (nb067_alpha_dummy_287) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0732 : (nb067_alpha_dummy_287) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_287, fv_syn_c1c] using (nb067_compact_fv_empty_0230)

theorem nb067_compact_fv_empty_0231 (f : Var) : (nb067_alpha_dummy_288 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0733 (f : Var) : (nb067_alpha_dummy_288 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_288, fv_syn_c1c] using (nb067_compact_fv_empty_0231 f)

theorem nb067_compact_fv_empty_0232 : (nb067_alpha_dummy_285) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0734 : (nb067_alpha_dummy_285) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_285, fv_syn_c1c] using (nb067_compact_fv_empty_0232)

theorem nb067_compact_fv_empty_0233 (f : Var) : (nb067_alpha_dummy_286 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0735 (f : Var) : (nb067_alpha_dummy_286 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_286, fv_syn_c1c] using (nb067_compact_fv_empty_0233 f)

theorem nb067_wpp_notmem_0736 : (nb067_alpha_dummy_278) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_278, fv_syn_c1c] using (nb067_compact_fv_empty_0210)

theorem nb067_wpp_notmem_0737 (f : Var) : (nb067_alpha_dummy_280 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_280, fv_syn_c1c] using (nb067_compact_fv_empty_0211 f)

theorem nb067_wpp_notmem_0738 : (nb067_alpha_dummy_277) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_277, fv_syn_c1c] using (nb067_compact_fv_empty_0212)

theorem nb067_wpp_notmem_0739 (f : Var) : (nb067_alpha_dummy_279 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_279, fv_syn_c1c] using (nb067_compact_fv_empty_0213 f)

theorem nb067_compact_envfresh_0087 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb067_alpha_dummy_297), (nb067_alpha_dummy_300 f)), ((nb067_alpha_dummy_296), (nb067_alpha_dummy_299 f)), ((nb067_alpha_dummy_295), (nb067_alpha_dummy_298 f)), ((nb067_alpha_dummy_293), (nb067_alpha_dummy_294 f)), ((nb067_alpha_dummy_289), (nb067_alpha_dummy_291 f)), ((nb067_alpha_dummy_290), (nb067_alpha_dummy_292 f)), ((nb067_alpha_dummy_282), (nb067_alpha_dummy_284 f)), ((nb067_alpha_dummy_281), (nb067_alpha_dummy_283 f)), ((nb067_alpha_dummy_287), (nb067_alpha_dummy_288 f)), ((nb067_alpha_dummy_285), (nb067_alpha_dummy_286 f)), ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)), ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb067_alpha_dummy_297) (nb067_alpha_dummy_300 f) (nb067_wpp_notmem_0716) (nb067_wpp_notmem_0717 f) (TEnvFresh.consFresh (nb067_alpha_dummy_296) (nb067_alpha_dummy_299 f) (nb067_wpp_notmem_0718) (nb067_wpp_notmem_0719 f) (TEnvFresh.consFresh (nb067_alpha_dummy_295) (nb067_alpha_dummy_298 f) (nb067_wpp_notmem_0720) (nb067_wpp_notmem_0721 f) (TEnvFresh.consFresh (nb067_alpha_dummy_293) (nb067_alpha_dummy_294 f) (nb067_wpp_notmem_0722) (nb067_wpp_notmem_0723 f) (TEnvFresh.consFresh (nb067_alpha_dummy_289) (nb067_alpha_dummy_291 f) (nb067_wpp_notmem_0724) (nb067_wpp_notmem_0725 f) (TEnvFresh.consFresh (nb067_alpha_dummy_290) (nb067_alpha_dummy_292 f) (nb067_wpp_notmem_0726) (nb067_wpp_notmem_0727 f) (TEnvFresh.consFresh (nb067_alpha_dummy_282) (nb067_alpha_dummy_284 f) (nb067_wpp_notmem_0728) (nb067_wpp_notmem_0729 f) (TEnvFresh.consFresh (nb067_alpha_dummy_281) (nb067_alpha_dummy_283 f) (nb067_wpp_notmem_0730) (nb067_wpp_notmem_0731 f) (TEnvFresh.consFresh (nb067_alpha_dummy_287) (nb067_alpha_dummy_288 f) (nb067_wpp_notmem_0732) (nb067_wpp_notmem_0733 f) (TEnvFresh.consFresh (nb067_alpha_dummy_285) (nb067_alpha_dummy_286 f) (nb067_wpp_notmem_0734) (nb067_wpp_notmem_0735 f) (TEnvFresh.consFresh (nb067_alpha_dummy_278) (nb067_alpha_dummy_280 f) (nb067_wpp_notmem_0736) (nb067_wpp_notmem_0737 f) (TEnvFresh.consFresh (nb067_alpha_dummy_277) (nb067_alpha_dummy_279 f) (nb067_wpp_notmem_0738) (nb067_wpp_notmem_0739 f) (TEnvFresh.consFresh (nb067_alpha_dummy_000) f (nb067_wpp_notmem_0236) (nb067_wpp_notmem_0237 f) (TEnvFresh.consFresh (nb067_alpha_dummy_003) (nb067_alpha_dummy_004 x y f) (nb067_wpp_notmem_0028) (nb067_wpp_notmem_0029 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_002) y (nb067_wpp_notmem_0030) (nb067_wpp_notmem_0031 y) (TEnvFresh.consFresh (nb067_alpha_dummy_001) x (nb067_wpp_notmem_0032) (nb067_wpp_notmem_0033 x) (TEnvFresh.consFresh (nb067_alpha_dummy_005) (nb067_alpha_dummy_006 x y f) (nb067_wpp_notmem_0034) (nb067_wpp_notmem_0035 x y f) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))

noncomputable def nb067_wpp_refl_0087 (x : Var) (y : Var) (f : Var) : TReflOn [((nb067_alpha_dummy_297), (nb067_alpha_dummy_300 f)), ((nb067_alpha_dummy_296), (nb067_alpha_dummy_299 f)), ((nb067_alpha_dummy_295), (nb067_alpha_dummy_298 f)), ((nb067_alpha_dummy_293), (nb067_alpha_dummy_294 f)), ((nb067_alpha_dummy_289), (nb067_alpha_dummy_291 f)), ((nb067_alpha_dummy_290), (nb067_alpha_dummy_292 f)), ((nb067_alpha_dummy_282), (nb067_alpha_dummy_284 f)), ((nb067_alpha_dummy_281), (nb067_alpha_dummy_283 f)), ((nb067_alpha_dummy_287), (nb067_alpha_dummy_288 f)), ((nb067_alpha_dummy_285), (nb067_alpha_dummy_286 f)), ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)), ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb067_compact_envfresh_0087 x y f)

theorem nb067_wpp_notmem_0740 : (nb067_alpha_dummy_297) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_297, fv_syn_c0] using (nb067_compact_fv_empty_0214)

theorem nb067_wpp_notmem_0741 (f : Var) : (nb067_alpha_dummy_300 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_300, fv_syn_c0] using (nb067_compact_fv_empty_0215 f)

theorem nb067_wpp_notmem_0742 : (nb067_alpha_dummy_296) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_296, fv_syn_c0] using (nb067_compact_fv_empty_0216)

theorem nb067_wpp_notmem_0743 (f : Var) : (nb067_alpha_dummy_299 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_299, fv_syn_c0] using (nb067_compact_fv_empty_0217 f)

theorem nb067_wpp_notmem_0744 : (nb067_alpha_dummy_295) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_295, fv_syn_c0] using (nb067_compact_fv_empty_0218)

theorem nb067_wpp_notmem_0745 (f : Var) : (nb067_alpha_dummy_298 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_298, fv_syn_c0] using (nb067_compact_fv_empty_0219 f)

theorem nb067_wpp_notmem_0746 : (nb067_alpha_dummy_293) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_293, fv_syn_c0] using (nb067_compact_fv_empty_0220)

theorem nb067_wpp_notmem_0747 (f : Var) : (nb067_alpha_dummy_294 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_294, fv_syn_c0] using (nb067_compact_fv_empty_0221 f)

theorem nb067_wpp_notmem_0748 : (nb067_alpha_dummy_289) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_289, fv_syn_c0] using (nb067_compact_fv_empty_0222)

theorem nb067_wpp_notmem_0749 (f : Var) : (nb067_alpha_dummy_291 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_291, fv_syn_c0] using (nb067_compact_fv_empty_0223 f)

theorem nb067_wpp_notmem_0750 : (nb067_alpha_dummy_290) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_290, fv_syn_c0] using (nb067_compact_fv_empty_0224)

theorem nb067_wpp_notmem_0751 (f : Var) : (nb067_alpha_dummy_292 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_292, fv_syn_c0] using (nb067_compact_fv_empty_0225 f)

theorem nb067_wpp_notmem_0752 : (nb067_alpha_dummy_282) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_282, fv_syn_c0] using (nb067_compact_fv_empty_0226)

theorem nb067_wpp_notmem_0753 (f : Var) : (nb067_alpha_dummy_284 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_284, fv_syn_c0] using (nb067_compact_fv_empty_0227 f)

theorem nb067_wpp_notmem_0754 : (nb067_alpha_dummy_281) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_281, fv_syn_c0] using (nb067_compact_fv_empty_0228)

theorem nb067_wpp_notmem_0755 (f : Var) : (nb067_alpha_dummy_283 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_283, fv_syn_c0] using (nb067_compact_fv_empty_0229 f)

theorem nb067_wpp_notmem_0756 : (nb067_alpha_dummy_287) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_287, fv_syn_c0] using (nb067_compact_fv_empty_0230)

theorem nb067_wpp_notmem_0757 (f : Var) : (nb067_alpha_dummy_288 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_288, fv_syn_c0] using (nb067_compact_fv_empty_0231 f)

theorem nb067_wpp_notmem_0758 : (nb067_alpha_dummy_285) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_285, fv_syn_c0] using (nb067_compact_fv_empty_0232)

theorem nb067_wpp_notmem_0759 (f : Var) : (nb067_alpha_dummy_286 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_286, fv_syn_c0] using (nb067_compact_fv_empty_0233 f)

theorem nb067_wpp_notmem_0760 : (nb067_alpha_dummy_278) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_278, fv_syn_c0] using (nb067_compact_fv_empty_0210)

theorem nb067_wpp_notmem_0761 (f : Var) : (nb067_alpha_dummy_280 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_280, fv_syn_c0] using (nb067_compact_fv_empty_0211 f)

theorem nb067_wpp_notmem_0762 : (nb067_alpha_dummy_277) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_277, fv_syn_c0] using (nb067_compact_fv_empty_0212)

theorem nb067_wpp_notmem_0763 (f : Var) : (nb067_alpha_dummy_279 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_279, fv_syn_c0] using (nb067_compact_fv_empty_0213 f)

theorem nb067_compact_envfresh_0088 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb067_alpha_dummy_297), (nb067_alpha_dummy_300 f)), ((nb067_alpha_dummy_296), (nb067_alpha_dummy_299 f)), ((nb067_alpha_dummy_295), (nb067_alpha_dummy_298 f)), ((nb067_alpha_dummy_293), (nb067_alpha_dummy_294 f)), ((nb067_alpha_dummy_289), (nb067_alpha_dummy_291 f)), ((nb067_alpha_dummy_290), (nb067_alpha_dummy_292 f)), ((nb067_alpha_dummy_282), (nb067_alpha_dummy_284 f)), ((nb067_alpha_dummy_281), (nb067_alpha_dummy_283 f)), ((nb067_alpha_dummy_287), (nb067_alpha_dummy_288 f)), ((nb067_alpha_dummy_285), (nb067_alpha_dummy_286 f)), ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)), ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb067_alpha_dummy_297) (nb067_alpha_dummy_300 f) (nb067_wpp_notmem_0740) (nb067_wpp_notmem_0741 f) (TEnvFresh.consFresh (nb067_alpha_dummy_296) (nb067_alpha_dummy_299 f) (nb067_wpp_notmem_0742) (nb067_wpp_notmem_0743 f) (TEnvFresh.consFresh (nb067_alpha_dummy_295) (nb067_alpha_dummy_298 f) (nb067_wpp_notmem_0744) (nb067_wpp_notmem_0745 f) (TEnvFresh.consFresh (nb067_alpha_dummy_293) (nb067_alpha_dummy_294 f) (nb067_wpp_notmem_0746) (nb067_wpp_notmem_0747 f) (TEnvFresh.consFresh (nb067_alpha_dummy_289) (nb067_alpha_dummy_291 f) (nb067_wpp_notmem_0748) (nb067_wpp_notmem_0749 f) (TEnvFresh.consFresh (nb067_alpha_dummy_290) (nb067_alpha_dummy_292 f) (nb067_wpp_notmem_0750) (nb067_wpp_notmem_0751 f) (TEnvFresh.consFresh (nb067_alpha_dummy_282) (nb067_alpha_dummy_284 f) (nb067_wpp_notmem_0752) (nb067_wpp_notmem_0753 f) (TEnvFresh.consFresh (nb067_alpha_dummy_281) (nb067_alpha_dummy_283 f) (nb067_wpp_notmem_0754) (nb067_wpp_notmem_0755 f) (TEnvFresh.consFresh (nb067_alpha_dummy_287) (nb067_alpha_dummy_288 f) (nb067_wpp_notmem_0756) (nb067_wpp_notmem_0757 f) (TEnvFresh.consFresh (nb067_alpha_dummy_285) (nb067_alpha_dummy_286 f) (nb067_wpp_notmem_0758) (nb067_wpp_notmem_0759 f) (TEnvFresh.consFresh (nb067_alpha_dummy_278) (nb067_alpha_dummy_280 f) (nb067_wpp_notmem_0760) (nb067_wpp_notmem_0761 f) (TEnvFresh.consFresh (nb067_alpha_dummy_277) (nb067_alpha_dummy_279 f) (nb067_wpp_notmem_0762) (nb067_wpp_notmem_0763 f) (TEnvFresh.consFresh (nb067_alpha_dummy_000) f (nb067_wpp_notmem_0268) (nb067_wpp_notmem_0269 f) (TEnvFresh.consFresh (nb067_alpha_dummy_003) (nb067_alpha_dummy_004 x y f) (nb067_wpp_notmem_0064) (nb067_wpp_notmem_0065 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_002) y (nb067_wpp_notmem_0066) (nb067_wpp_notmem_0067 y) (TEnvFresh.consFresh (nb067_alpha_dummy_001) x (nb067_wpp_notmem_0068) (nb067_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb067_alpha_dummy_005) (nb067_alpha_dummy_006 x y f) (nb067_wpp_notmem_0070) (nb067_wpp_notmem_0071 x y f) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))

noncomputable def nb067_wpp_refl_0088 (x : Var) (y : Var) (f : Var) : TReflOn [((nb067_alpha_dummy_297), (nb067_alpha_dummy_300 f)), ((nb067_alpha_dummy_296), (nb067_alpha_dummy_299 f)), ((nb067_alpha_dummy_295), (nb067_alpha_dummy_298 f)), ((nb067_alpha_dummy_293), (nb067_alpha_dummy_294 f)), ((nb067_alpha_dummy_289), (nb067_alpha_dummy_291 f)), ((nb067_alpha_dummy_290), (nb067_alpha_dummy_292 f)), ((nb067_alpha_dummy_282), (nb067_alpha_dummy_284 f)), ((nb067_alpha_dummy_281), (nb067_alpha_dummy_283 f)), ((nb067_alpha_dummy_287), (nb067_alpha_dummy_288 f)), ((nb067_alpha_dummy_285), (nb067_alpha_dummy_286 f)), ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)), ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb067_compact_envfresh_0088 x y f)

noncomputable def nb067_split_alpha_0066 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb067_alpha_dummy_297), (nb067_alpha_dummy_300 f)), ((nb067_alpha_dummy_296), (nb067_alpha_dummy_299 f)), ((nb067_alpha_dummy_295), (nb067_alpha_dummy_298 f)), ((nb067_alpha_dummy_293), (nb067_alpha_dummy_294 f)), ((nb067_alpha_dummy_289), (nb067_alpha_dummy_291 f)), ((nb067_alpha_dummy_290), (nb067_alpha_dummy_292 f)), ((nb067_alpha_dummy_282), (nb067_alpha_dummy_284 f)), ((nb067_alpha_dummy_281), (nb067_alpha_dummy_283 f)), ((nb067_alpha_dummy_287), (nb067_alpha_dummy_288 f)), ((nb067_alpha_dummy_285), (nb067_alpha_dummy_286 f)), ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)), ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_296)) (Class.cv (nb067_alpha_dummy_297))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_295)) (syn_cun (Class.cv (nb067_alpha_dummy_296)) (Class.cv (nb067_alpha_dummy_297)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_299 f)) (Class.cv (nb067_alpha_dummy_300 f))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_298 f)) (syn_cun (Class.cv (nb067_alpha_dummy_299 f)) (Class.cv (nb067_alpha_dummy_300 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0316) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0317 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0314) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0315 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0320) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0321 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0318) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0319 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0316) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0317 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0314) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0315 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0320) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0321 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0318) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0319 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_297), (nb067_alpha_dummy_300 f)), ((nb067_alpha_dummy_296), (nb067_alpha_dummy_299 f)), ((nb067_alpha_dummy_295), (nb067_alpha_dummy_298 f)), ((nb067_alpha_dummy_293), (nb067_alpha_dummy_294 f)), ((nb067_alpha_dummy_289), (nb067_alpha_dummy_291 f)), ((nb067_alpha_dummy_290), (nb067_alpha_dummy_292 f)), ((nb067_alpha_dummy_282), (nb067_alpha_dummy_284 f)), ((nb067_alpha_dummy_281), (nb067_alpha_dummy_283 f)), ((nb067_alpha_dummy_287), (nb067_alpha_dummy_288 f)), ((nb067_alpha_dummy_285), (nb067_alpha_dummy_286 f)), ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)), ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_c0) (nb067_wpp_refl_0088 x y f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0324) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0325 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0322) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0323 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0324) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0325 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0322) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0323 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0328) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0329 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0326) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0327 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0328) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0329 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0326) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0327 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb067_wpp_notmem_0764 : (nb067_alpha_dummy_293) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_293, fv_syn_cnnc] using (nb067_compact_fv_empty_0220)

theorem nb067_wpp_notmem_0765 (f : Var) : (nb067_alpha_dummy_294 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_294, fv_syn_cnnc] using (nb067_compact_fv_empty_0221 f)

theorem nb067_wpp_notmem_0766 : (nb067_alpha_dummy_289) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_289, fv_syn_cnnc] using (nb067_compact_fv_empty_0222)

theorem nb067_wpp_notmem_0767 (f : Var) : (nb067_alpha_dummy_291 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_291, fv_syn_cnnc] using (nb067_compact_fv_empty_0223 f)

theorem nb067_wpp_notmem_0768 : (nb067_alpha_dummy_290) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_290, fv_syn_cnnc] using (nb067_compact_fv_empty_0224)

theorem nb067_wpp_notmem_0769 (f : Var) : (nb067_alpha_dummy_292 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_292, fv_syn_cnnc] using (nb067_compact_fv_empty_0225 f)

theorem nb067_wpp_notmem_0770 : (nb067_alpha_dummy_282) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_282, fv_syn_cnnc] using (nb067_compact_fv_empty_0226)

theorem nb067_wpp_notmem_0771 (f : Var) : (nb067_alpha_dummy_284 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_284, fv_syn_cnnc] using (nb067_compact_fv_empty_0227 f)

theorem nb067_wpp_notmem_0772 : (nb067_alpha_dummy_281) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_281, fv_syn_cnnc] using (nb067_compact_fv_empty_0228)

theorem nb067_wpp_notmem_0773 (f : Var) : (nb067_alpha_dummy_283 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_283, fv_syn_cnnc] using (nb067_compact_fv_empty_0229 f)

theorem nb067_wpp_notmem_0774 : (nb067_alpha_dummy_287) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_287, fv_syn_cnnc] using (nb067_compact_fv_empty_0230)

theorem nb067_wpp_notmem_0775 (f : Var) : (nb067_alpha_dummy_288 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_288, fv_syn_cnnc] using (nb067_compact_fv_empty_0231 f)

theorem nb067_wpp_notmem_0776 : (nb067_alpha_dummy_285) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_285, fv_syn_cnnc] using (nb067_compact_fv_empty_0232)

theorem nb067_wpp_notmem_0777 (f : Var) : (nb067_alpha_dummy_286 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_286, fv_syn_cnnc] using (nb067_compact_fv_empty_0233 f)

theorem nb067_wpp_notmem_0778 : (nb067_alpha_dummy_278) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_278, fv_syn_cnnc] using (nb067_compact_fv_empty_0210)

theorem nb067_wpp_notmem_0779 (f : Var) : (nb067_alpha_dummy_280 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_280, fv_syn_cnnc] using (nb067_compact_fv_empty_0211 f)

theorem nb067_wpp_notmem_0780 : (nb067_alpha_dummy_277) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_277, fv_syn_cnnc] using (nb067_compact_fv_empty_0212)

theorem nb067_wpp_notmem_0781 (f : Var) : (nb067_alpha_dummy_279 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_279, fv_syn_cnnc] using (nb067_compact_fv_empty_0213 f)

theorem nb067_compact_envfresh_0089 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb067_alpha_dummy_293), (nb067_alpha_dummy_294 f)), ((nb067_alpha_dummy_289), (nb067_alpha_dummy_291 f)), ((nb067_alpha_dummy_290), (nb067_alpha_dummy_292 f)), ((nb067_alpha_dummy_282), (nb067_alpha_dummy_284 f)), ((nb067_alpha_dummy_281), (nb067_alpha_dummy_283 f)), ((nb067_alpha_dummy_287), (nb067_alpha_dummy_288 f)), ((nb067_alpha_dummy_285), (nb067_alpha_dummy_286 f)), ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)), ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb067_alpha_dummy_293) (nb067_alpha_dummy_294 f) (nb067_wpp_notmem_0764) (nb067_wpp_notmem_0765 f) (TEnvFresh.consFresh (nb067_alpha_dummy_289) (nb067_alpha_dummy_291 f) (nb067_wpp_notmem_0766) (nb067_wpp_notmem_0767 f) (TEnvFresh.consFresh (nb067_alpha_dummy_290) (nb067_alpha_dummy_292 f) (nb067_wpp_notmem_0768) (nb067_wpp_notmem_0769 f) (TEnvFresh.consFresh (nb067_alpha_dummy_282) (nb067_alpha_dummy_284 f) (nb067_wpp_notmem_0770) (nb067_wpp_notmem_0771 f) (TEnvFresh.consFresh (nb067_alpha_dummy_281) (nb067_alpha_dummy_283 f) (nb067_wpp_notmem_0772) (nb067_wpp_notmem_0773 f) (TEnvFresh.consFresh (nb067_alpha_dummy_287) (nb067_alpha_dummy_288 f) (nb067_wpp_notmem_0774) (nb067_wpp_notmem_0775 f) (TEnvFresh.consFresh (nb067_alpha_dummy_285) (nb067_alpha_dummy_286 f) (nb067_wpp_notmem_0776) (nb067_wpp_notmem_0777 f) (TEnvFresh.consFresh (nb067_alpha_dummy_278) (nb067_alpha_dummy_280 f) (nb067_wpp_notmem_0778) (nb067_wpp_notmem_0779 f) (TEnvFresh.consFresh (nb067_alpha_dummy_277) (nb067_alpha_dummy_279 f) (nb067_wpp_notmem_0780) (nb067_wpp_notmem_0781 f) (TEnvFresh.consFresh (nb067_alpha_dummy_000) f (nb067_wpp_notmem_0294) (nb067_wpp_notmem_0295 f) (TEnvFresh.consFresh (nb067_alpha_dummy_003) (nb067_alpha_dummy_004 x y f) (nb067_wpp_notmem_0094) (nb067_wpp_notmem_0095 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_002) y (nb067_wpp_notmem_0096) (nb067_wpp_notmem_0097 y) (TEnvFresh.consFresh (nb067_alpha_dummy_001) x (nb067_wpp_notmem_0098) (nb067_wpp_notmem_0099 x) (TEnvFresh.consFresh (nb067_alpha_dummy_005) (nb067_alpha_dummy_006 x y f) (nb067_wpp_notmem_0100) (nb067_wpp_notmem_0101 x y f) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))

noncomputable def nb067_wpp_refl_0089 (x : Var) (y : Var) (f : Var) : TReflOn [((nb067_alpha_dummy_293), (nb067_alpha_dummy_294 f)), ((nb067_alpha_dummy_289), (nb067_alpha_dummy_291 f)), ((nb067_alpha_dummy_290), (nb067_alpha_dummy_292 f)), ((nb067_alpha_dummy_282), (nb067_alpha_dummy_284 f)), ((nb067_alpha_dummy_281), (nb067_alpha_dummy_283 f)), ((nb067_alpha_dummy_287), (nb067_alpha_dummy_288 f)), ((nb067_alpha_dummy_285), (nb067_alpha_dummy_286 f)), ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)), ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb067_compact_envfresh_0089 x y f)

noncomputable def nb067_split_alpha_0067 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb067_alpha_dummy_282), (nb067_alpha_dummy_284 f)), ((nb067_alpha_dummy_281), (nb067_alpha_dummy_283 f)), ((nb067_alpha_dummy_287), (nb067_alpha_dummy_288 f)), ((nb067_alpha_dummy_285), (nb067_alpha_dummy_286 f)), ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)), ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (Wff.classEq (Class.cv (nb067_alpha_dummy_281)) (syn_cphi (Class.cv (nb067_alpha_dummy_282)))) (Wff.classEq (Class.cv (nb067_alpha_dummy_283 f)) (syn_cphi (Class.cv (nb067_alpha_dummy_284 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_278))).fv ∪ ((Class.cv (nb067_alpha_dummy_277))).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_280 f))).fv ∪ ((Class.cv (nb067_alpha_dummy_279 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0308) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0309 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0308) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0309 f) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_282))).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_284 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0312) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0313 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0312) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0313 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0310) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0311 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_297), (nb067_alpha_dummy_300 f)), ((nb067_alpha_dummy_296), (nb067_alpha_dummy_299 f)), ((nb067_alpha_dummy_295), (nb067_alpha_dummy_298 f)), ((nb067_alpha_dummy_293), (nb067_alpha_dummy_294 f)), ((nb067_alpha_dummy_289), (nb067_alpha_dummy_291 f)), ((nb067_alpha_dummy_290), (nb067_alpha_dummy_292 f)), ((nb067_alpha_dummy_282), (nb067_alpha_dummy_284 f)), ((nb067_alpha_dummy_281), (nb067_alpha_dummy_283 f)), ((nb067_alpha_dummy_287), (nb067_alpha_dummy_288 f)), ((nb067_alpha_dummy_285), (nb067_alpha_dummy_286 f)), ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)), ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_c1c) (nb067_wpp_refl_0087 x y f))) (TAlphaWff.neg (TAlphaWff.neg (nb067_split_alpha_0066 x y f)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0310) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0311 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_293), (nb067_alpha_dummy_294 f)), ((nb067_alpha_dummy_289), (nb067_alpha_dummy_291 f)), ((nb067_alpha_dummy_290), (nb067_alpha_dummy_292 f)), ((nb067_alpha_dummy_282), (nb067_alpha_dummy_284 f)), ((nb067_alpha_dummy_281), (nb067_alpha_dummy_283 f)), ((nb067_alpha_dummy_287), (nb067_alpha_dummy_288 f)), ((nb067_alpha_dummy_285), (nb067_alpha_dummy_286 f)), ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)), ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_cnnc) (nb067_wpp_refl_0089 x y f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0310) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0311 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0310) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0311 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_293), (nb067_alpha_dummy_294 f)), ((nb067_alpha_dummy_289), (nb067_alpha_dummy_291 f)), ((nb067_alpha_dummy_290), (nb067_alpha_dummy_292 f)), ((nb067_alpha_dummy_282), (nb067_alpha_dummy_284 f)), ((nb067_alpha_dummy_281), (nb067_alpha_dummy_283 f)), ((nb067_alpha_dummy_287), (nb067_alpha_dummy_288 f)), ((nb067_alpha_dummy_285), (nb067_alpha_dummy_286 f)), ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)), ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_cnnc) (nb067_wpp_refl_0089 x y f))))))))))))))))))

theorem nb067_compact_fv_empty_0234 : (nb067_alpha_dummy_315) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0782 : (nb067_alpha_dummy_315) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_315, fv_syn_c1c] using (nb067_compact_fv_empty_0234)

theorem nb067_compact_fv_empty_0235 (f : Var) : (nb067_alpha_dummy_316 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0783 (f : Var) : (nb067_alpha_dummy_316 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_316, fv_syn_c1c] using (nb067_compact_fv_empty_0235 f)

theorem nb067_compact_fv_empty_0236 : (nb067_alpha_dummy_313) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0784 : (nb067_alpha_dummy_313) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_313, fv_syn_c1c] using (nb067_compact_fv_empty_0236)

theorem nb067_compact_fv_empty_0237 (f : Var) : (nb067_alpha_dummy_314 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0785 (f : Var) : (nb067_alpha_dummy_314 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_314, fv_syn_c1c] using (nb067_compact_fv_empty_0237 f)

theorem nb067_compact_fv_empty_0238 : (nb067_alpha_dummy_311) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0786 : (nb067_alpha_dummy_311) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_311, fv_syn_c1c] using (nb067_compact_fv_empty_0238)

theorem nb067_compact_fv_empty_0239 (f : Var) : (nb067_alpha_dummy_312 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0787 (f : Var) : (nb067_alpha_dummy_312 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_312, fv_syn_c1c] using (nb067_compact_fv_empty_0239 f)

theorem nb067_compact_envfresh_0090 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb067_alpha_dummy_297), (nb067_alpha_dummy_300 f)), ((nb067_alpha_dummy_296), (nb067_alpha_dummy_299 f)), ((nb067_alpha_dummy_295), (nb067_alpha_dummy_298 f)), ((nb067_alpha_dummy_293), (nb067_alpha_dummy_294 f)), ((nb067_alpha_dummy_289), (nb067_alpha_dummy_291 f)), ((nb067_alpha_dummy_290), (nb067_alpha_dummy_292 f)), ((nb067_alpha_dummy_315), (nb067_alpha_dummy_316 f)), ((nb067_alpha_dummy_313), (nb067_alpha_dummy_314 f)), ((nb067_alpha_dummy_282), (nb067_alpha_dummy_284 f)), ((nb067_alpha_dummy_281), (nb067_alpha_dummy_283 f)), ((nb067_alpha_dummy_311), (nb067_alpha_dummy_312 f)), ((nb067_alpha_dummy_285), (nb067_alpha_dummy_286 f)), ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)), ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb067_alpha_dummy_297) (nb067_alpha_dummy_300 f) (nb067_wpp_notmem_0716) (nb067_wpp_notmem_0717 f) (TEnvFresh.consFresh (nb067_alpha_dummy_296) (nb067_alpha_dummy_299 f) (nb067_wpp_notmem_0718) (nb067_wpp_notmem_0719 f) (TEnvFresh.consFresh (nb067_alpha_dummy_295) (nb067_alpha_dummy_298 f) (nb067_wpp_notmem_0720) (nb067_wpp_notmem_0721 f) (TEnvFresh.consFresh (nb067_alpha_dummy_293) (nb067_alpha_dummy_294 f) (nb067_wpp_notmem_0722) (nb067_wpp_notmem_0723 f) (TEnvFresh.consFresh (nb067_alpha_dummy_289) (nb067_alpha_dummy_291 f) (nb067_wpp_notmem_0724) (nb067_wpp_notmem_0725 f) (TEnvFresh.consFresh (nb067_alpha_dummy_290) (nb067_alpha_dummy_292 f) (nb067_wpp_notmem_0726) (nb067_wpp_notmem_0727 f) (TEnvFresh.consFresh (nb067_alpha_dummy_315) (nb067_alpha_dummy_316 f) (nb067_wpp_notmem_0782) (nb067_wpp_notmem_0783 f) (TEnvFresh.consFresh (nb067_alpha_dummy_313) (nb067_alpha_dummy_314 f) (nb067_wpp_notmem_0784) (nb067_wpp_notmem_0785 f) (TEnvFresh.consFresh (nb067_alpha_dummy_282) (nb067_alpha_dummy_284 f) (nb067_wpp_notmem_0728) (nb067_wpp_notmem_0729 f) (TEnvFresh.consFresh (nb067_alpha_dummy_281) (nb067_alpha_dummy_283 f) (nb067_wpp_notmem_0730) (nb067_wpp_notmem_0731 f) (TEnvFresh.consFresh (nb067_alpha_dummy_311) (nb067_alpha_dummy_312 f) (nb067_wpp_notmem_0786) (nb067_wpp_notmem_0787 f) (TEnvFresh.consFresh (nb067_alpha_dummy_285) (nb067_alpha_dummy_286 f) (nb067_wpp_notmem_0734) (nb067_wpp_notmem_0735 f) (TEnvFresh.consFresh (nb067_alpha_dummy_278) (nb067_alpha_dummy_280 f) (nb067_wpp_notmem_0736) (nb067_wpp_notmem_0737 f) (TEnvFresh.consFresh (nb067_alpha_dummy_277) (nb067_alpha_dummy_279 f) (nb067_wpp_notmem_0738) (nb067_wpp_notmem_0739 f) (TEnvFresh.consFresh (nb067_alpha_dummy_000) f (nb067_wpp_notmem_0236) (nb067_wpp_notmem_0237 f) (TEnvFresh.consFresh (nb067_alpha_dummy_003) (nb067_alpha_dummy_004 x y f) (nb067_wpp_notmem_0028) (nb067_wpp_notmem_0029 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_002) y (nb067_wpp_notmem_0030) (nb067_wpp_notmem_0031 y) (TEnvFresh.consFresh (nb067_alpha_dummy_001) x (nb067_wpp_notmem_0032) (nb067_wpp_notmem_0033 x) (TEnvFresh.consFresh (nb067_alpha_dummy_005) (nb067_alpha_dummy_006 x y f) (nb067_wpp_notmem_0034) (nb067_wpp_notmem_0035 x y f) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))

noncomputable def nb067_wpp_refl_0090 (x : Var) (y : Var) (f : Var) : TReflOn [((nb067_alpha_dummy_297), (nb067_alpha_dummy_300 f)), ((nb067_alpha_dummy_296), (nb067_alpha_dummy_299 f)), ((nb067_alpha_dummy_295), (nb067_alpha_dummy_298 f)), ((nb067_alpha_dummy_293), (nb067_alpha_dummy_294 f)), ((nb067_alpha_dummy_289), (nb067_alpha_dummy_291 f)), ((nb067_alpha_dummy_290), (nb067_alpha_dummy_292 f)), ((nb067_alpha_dummy_315), (nb067_alpha_dummy_316 f)), ((nb067_alpha_dummy_313), (nb067_alpha_dummy_314 f)), ((nb067_alpha_dummy_282), (nb067_alpha_dummy_284 f)), ((nb067_alpha_dummy_281), (nb067_alpha_dummy_283 f)), ((nb067_alpha_dummy_311), (nb067_alpha_dummy_312 f)), ((nb067_alpha_dummy_285), (nb067_alpha_dummy_286 f)), ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)), ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb067_compact_envfresh_0090 x y f)

theorem nb067_wpp_notmem_0788 : (nb067_alpha_dummy_315) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_315, fv_syn_c0] using (nb067_compact_fv_empty_0234)

theorem nb067_wpp_notmem_0789 (f : Var) : (nb067_alpha_dummy_316 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_316, fv_syn_c0] using (nb067_compact_fv_empty_0235 f)

theorem nb067_wpp_notmem_0790 : (nb067_alpha_dummy_313) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_313, fv_syn_c0] using (nb067_compact_fv_empty_0236)

theorem nb067_wpp_notmem_0791 (f : Var) : (nb067_alpha_dummy_314 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_314, fv_syn_c0] using (nb067_compact_fv_empty_0237 f)

theorem nb067_wpp_notmem_0792 : (nb067_alpha_dummy_311) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_311, fv_syn_c0] using (nb067_compact_fv_empty_0238)

theorem nb067_wpp_notmem_0793 (f : Var) : (nb067_alpha_dummy_312 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_312, fv_syn_c0] using (nb067_compact_fv_empty_0239 f)

theorem nb067_compact_envfresh_0091 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb067_alpha_dummy_297), (nb067_alpha_dummy_300 f)), ((nb067_alpha_dummy_296), (nb067_alpha_dummy_299 f)), ((nb067_alpha_dummy_295), (nb067_alpha_dummy_298 f)), ((nb067_alpha_dummy_293), (nb067_alpha_dummy_294 f)), ((nb067_alpha_dummy_289), (nb067_alpha_dummy_291 f)), ((nb067_alpha_dummy_290), (nb067_alpha_dummy_292 f)), ((nb067_alpha_dummy_315), (nb067_alpha_dummy_316 f)), ((nb067_alpha_dummy_313), (nb067_alpha_dummy_314 f)), ((nb067_alpha_dummy_282), (nb067_alpha_dummy_284 f)), ((nb067_alpha_dummy_281), (nb067_alpha_dummy_283 f)), ((nb067_alpha_dummy_311), (nb067_alpha_dummy_312 f)), ((nb067_alpha_dummy_285), (nb067_alpha_dummy_286 f)), ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)), ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb067_alpha_dummy_297) (nb067_alpha_dummy_300 f) (nb067_wpp_notmem_0740) (nb067_wpp_notmem_0741 f) (TEnvFresh.consFresh (nb067_alpha_dummy_296) (nb067_alpha_dummy_299 f) (nb067_wpp_notmem_0742) (nb067_wpp_notmem_0743 f) (TEnvFresh.consFresh (nb067_alpha_dummy_295) (nb067_alpha_dummy_298 f) (nb067_wpp_notmem_0744) (nb067_wpp_notmem_0745 f) (TEnvFresh.consFresh (nb067_alpha_dummy_293) (nb067_alpha_dummy_294 f) (nb067_wpp_notmem_0746) (nb067_wpp_notmem_0747 f) (TEnvFresh.consFresh (nb067_alpha_dummy_289) (nb067_alpha_dummy_291 f) (nb067_wpp_notmem_0748) (nb067_wpp_notmem_0749 f) (TEnvFresh.consFresh (nb067_alpha_dummy_290) (nb067_alpha_dummy_292 f) (nb067_wpp_notmem_0750) (nb067_wpp_notmem_0751 f) (TEnvFresh.consFresh (nb067_alpha_dummy_315) (nb067_alpha_dummy_316 f) (nb067_wpp_notmem_0788) (nb067_wpp_notmem_0789 f) (TEnvFresh.consFresh (nb067_alpha_dummy_313) (nb067_alpha_dummy_314 f) (nb067_wpp_notmem_0790) (nb067_wpp_notmem_0791 f) (TEnvFresh.consFresh (nb067_alpha_dummy_282) (nb067_alpha_dummy_284 f) (nb067_wpp_notmem_0752) (nb067_wpp_notmem_0753 f) (TEnvFresh.consFresh (nb067_alpha_dummy_281) (nb067_alpha_dummy_283 f) (nb067_wpp_notmem_0754) (nb067_wpp_notmem_0755 f) (TEnvFresh.consFresh (nb067_alpha_dummy_311) (nb067_alpha_dummy_312 f) (nb067_wpp_notmem_0792) (nb067_wpp_notmem_0793 f) (TEnvFresh.consFresh (nb067_alpha_dummy_285) (nb067_alpha_dummy_286 f) (nb067_wpp_notmem_0758) (nb067_wpp_notmem_0759 f) (TEnvFresh.consFresh (nb067_alpha_dummy_278) (nb067_alpha_dummy_280 f) (nb067_wpp_notmem_0760) (nb067_wpp_notmem_0761 f) (TEnvFresh.consFresh (nb067_alpha_dummy_277) (nb067_alpha_dummy_279 f) (nb067_wpp_notmem_0762) (nb067_wpp_notmem_0763 f) (TEnvFresh.consFresh (nb067_alpha_dummy_000) f (nb067_wpp_notmem_0268) (nb067_wpp_notmem_0269 f) (TEnvFresh.consFresh (nb067_alpha_dummy_003) (nb067_alpha_dummy_004 x y f) (nb067_wpp_notmem_0064) (nb067_wpp_notmem_0065 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_002) y (nb067_wpp_notmem_0066) (nb067_wpp_notmem_0067 y) (TEnvFresh.consFresh (nb067_alpha_dummy_001) x (nb067_wpp_notmem_0068) (nb067_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb067_alpha_dummy_005) (nb067_alpha_dummy_006 x y f) (nb067_wpp_notmem_0070) (nb067_wpp_notmem_0071 x y f) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))))

noncomputable def nb067_wpp_refl_0091 (x : Var) (y : Var) (f : Var) : TReflOn [((nb067_alpha_dummy_297), (nb067_alpha_dummy_300 f)), ((nb067_alpha_dummy_296), (nb067_alpha_dummy_299 f)), ((nb067_alpha_dummy_295), (nb067_alpha_dummy_298 f)), ((nb067_alpha_dummy_293), (nb067_alpha_dummy_294 f)), ((nb067_alpha_dummy_289), (nb067_alpha_dummy_291 f)), ((nb067_alpha_dummy_290), (nb067_alpha_dummy_292 f)), ((nb067_alpha_dummy_315), (nb067_alpha_dummy_316 f)), ((nb067_alpha_dummy_313), (nb067_alpha_dummy_314 f)), ((nb067_alpha_dummy_282), (nb067_alpha_dummy_284 f)), ((nb067_alpha_dummy_281), (nb067_alpha_dummy_283 f)), ((nb067_alpha_dummy_311), (nb067_alpha_dummy_312 f)), ((nb067_alpha_dummy_285), (nb067_alpha_dummy_286 f)), ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)), ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb067_compact_envfresh_0091 x y f)

noncomputable def nb067_split_alpha_0068 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb067_alpha_dummy_297), (nb067_alpha_dummy_300 f)), ((nb067_alpha_dummy_296), (nb067_alpha_dummy_299 f)), ((nb067_alpha_dummy_295), (nb067_alpha_dummy_298 f)), ((nb067_alpha_dummy_293), (nb067_alpha_dummy_294 f)), ((nb067_alpha_dummy_289), (nb067_alpha_dummy_291 f)), ((nb067_alpha_dummy_290), (nb067_alpha_dummy_292 f)), ((nb067_alpha_dummy_315), (nb067_alpha_dummy_316 f)), ((nb067_alpha_dummy_313), (nb067_alpha_dummy_314 f)), ((nb067_alpha_dummy_282), (nb067_alpha_dummy_284 f)), ((nb067_alpha_dummy_281), (nb067_alpha_dummy_283 f)), ((nb067_alpha_dummy_311), (nb067_alpha_dummy_312 f)), ((nb067_alpha_dummy_285), (nb067_alpha_dummy_286 f)), ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)), ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_296)) (Class.cv (nb067_alpha_dummy_297))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_295)) (syn_cun (Class.cv (nb067_alpha_dummy_296)) (Class.cv (nb067_alpha_dummy_297)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_299 f)) (Class.cv (nb067_alpha_dummy_300 f))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_298 f)) (syn_cun (Class.cv (nb067_alpha_dummy_299 f)) (Class.cv (nb067_alpha_dummy_300 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0316) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0317 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0314) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0315 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0320) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0321 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0318) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0319 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0316) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0317 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0314) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0315 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0320) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0321 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0318) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0319 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_297), (nb067_alpha_dummy_300 f)), ((nb067_alpha_dummy_296), (nb067_alpha_dummy_299 f)), ((nb067_alpha_dummy_295), (nb067_alpha_dummy_298 f)), ((nb067_alpha_dummy_293), (nb067_alpha_dummy_294 f)), ((nb067_alpha_dummy_289), (nb067_alpha_dummy_291 f)), ((nb067_alpha_dummy_290), (nb067_alpha_dummy_292 f)), ((nb067_alpha_dummy_315), (nb067_alpha_dummy_316 f)), ((nb067_alpha_dummy_313), (nb067_alpha_dummy_314 f)), ((nb067_alpha_dummy_282), (nb067_alpha_dummy_284 f)), ((nb067_alpha_dummy_281), (nb067_alpha_dummy_283 f)), ((nb067_alpha_dummy_311), (nb067_alpha_dummy_312 f)), ((nb067_alpha_dummy_285), (nb067_alpha_dummy_286 f)), ((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)), ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_c0) (nb067_wpp_refl_0091 x y f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0324) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0325 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0322) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0323 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0324) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0325 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0322) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0323 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_289))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_291 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0328) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0329 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0326) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0327 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0328) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0329 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0326) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0327 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb067_wpp_notmem_0794 : (nb067_alpha_dummy_315) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_315, fv_syn_cnnc] using (nb067_compact_fv_empty_0234)

theorem nb067_wpp_notmem_0795 (f : Var) : (nb067_alpha_dummy_316 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_316, fv_syn_cnnc] using (nb067_compact_fv_empty_0235 f)

theorem nb067_wpp_notmem_0796 : (nb067_alpha_dummy_313) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_313, fv_syn_cnnc] using (nb067_compact_fv_empty_0236)

theorem nb067_wpp_notmem_0797 (f : Var) : (nb067_alpha_dummy_314 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_314, fv_syn_cnnc] using (nb067_compact_fv_empty_0237 f)

theorem nb067_wpp_notmem_0798 : (nb067_alpha_dummy_311) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_311, fv_syn_cnnc] using (nb067_compact_fv_empty_0238)

theorem nb067_wpp_notmem_0799 (f : Var) : (nb067_alpha_dummy_312 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_312, fv_syn_cnnc] using (nb067_compact_fv_empty_0239 f)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
