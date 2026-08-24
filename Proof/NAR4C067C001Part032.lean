import NAR4C067C001Part031

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

noncomputable def nb067_split_alpha_0082 (x : Var) (y : Var) (f : Var) (dv_f_y : f ≠ y) : TAlphaWff [((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (Wff.imp (syn_wfun (Class.cv (nb067_alpha_dummy_000))) (Wff.neg (Wff.classEq (syn_cdm (Class.cv (nb067_alpha_dummy_000))) (Class.cv (nb067_alpha_dummy_002))))) (Wff.imp (syn_wfun (Class.cv f)) (Wff.neg (Wff.classEq (syn_cdm (Class.cv f)) (Class.cv y)))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (nb067_split_alpha_0038 x y f)) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (nb067_split_alpha_0038 x y f))))))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0094) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0095 f) 0))) (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0092) 0))) (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0093 f) 0))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0096) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0098 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0096) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0098 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0100) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0101 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0097) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0099 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (nb067_split_alpha_0040 x y f))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0096) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0098 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0096) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0098 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0100) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0101 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0097) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0099 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_000))).fv ∪ ((syn_ccnv (Class.cv (nb067_alpha_dummy_000)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (nb067_split_alpha_0040 x y f))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb067_split_alpha_0043 x y f))))))))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb067_split_alpha_0065 x y f)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_278), (nb067_alpha_dummy_280 f)), ((nb067_alpha_dummy_277), (nb067_alpha_dummy_279 f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_cvv) (nb067_wpp_refl_0086 x y f))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0302) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0304 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0302) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0304 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0306) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0307 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0303) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0305 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (nb067_split_alpha_0067 x y f))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0302) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0304 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0302) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0304 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0306) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0307 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0303) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0305 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (nb067_split_alpha_0067 x y f))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (nb067_split_alpha_0070 x y f)))))))))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb067_split_alpha_0081 x y f))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) (Ne.symm dv_f_y) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0042) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0043 x y f) 0)) (TAlphaVar.here _ _ _)))))))

theorem nb067_compact_fv_empty_0240 : (nb067_alpha_dummy_322) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0814 : (nb067_alpha_dummy_322) ∉ ((syn_cvv)).fv := by
  simpa only [nb067_alpha_dummy_322, fv_syn_cvv] using (nb067_compact_fv_empty_0240)

theorem nb067_compact_fv_empty_0241 (f : Var) : (nb067_alpha_dummy_324 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0815 (f : Var) : (nb067_alpha_dummy_324 f) ∉ ((syn_cvv)).fv := by
  simpa only [nb067_alpha_dummy_324, fv_syn_cvv] using (nb067_compact_fv_empty_0241 f)

theorem nb067_compact_fv_empty_0242 : (nb067_alpha_dummy_321) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0816 : (nb067_alpha_dummy_321) ∉ ((syn_cvv)).fv := by
  simpa only [nb067_alpha_dummy_321, fv_syn_cvv] using (nb067_compact_fv_empty_0242)

theorem nb067_compact_fv_empty_0243 (f : Var) : (nb067_alpha_dummy_323 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0817 (f : Var) : (nb067_alpha_dummy_323 f) ∉ ((syn_cvv)).fv := by
  simpa only [nb067_alpha_dummy_323, fv_syn_cvv] using (nb067_compact_fv_empty_0243 f)

theorem nb067_compact_fv_empty_0244 : (nb067_alpha_dummy_319) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0818 : (nb067_alpha_dummy_319) ∉ ((syn_cvv)).fv := by
  simpa only [nb067_alpha_dummy_319, fv_syn_cvv] using (nb067_compact_fv_empty_0244)

theorem nb067_compact_fv_empty_0245 (x : Var) (f : Var) : (nb067_alpha_dummy_320 x f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0819 (x : Var) (f : Var) : (nb067_alpha_dummy_320 x f) ∉ ((syn_cvv)).fv := by
  simpa only [nb067_alpha_dummy_320, fv_syn_cvv] using (nb067_compact_fv_empty_0245 x f)

theorem nb067_compact_fv_empty_0246 : (nb067_alpha_dummy_317) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0820 : (nb067_alpha_dummy_317) ∉ ((syn_cvv)).fv := by
  simpa only [nb067_alpha_dummy_317, fv_syn_cvv] using (nb067_compact_fv_empty_0246)

theorem nb067_compact_fv_empty_0247 (x : Var) (f : Var) : (nb067_alpha_dummy_318 x f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0821 (x : Var) (f : Var) : (nb067_alpha_dummy_318 x f) ∉ ((syn_cvv)).fv := by
  simpa only [nb067_alpha_dummy_318, fv_syn_cvv] using (nb067_compact_fv_empty_0247 x f)

theorem nb067_compact_envfresh_0108 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)), ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)), ((nb067_alpha_dummy_319), (nb067_alpha_dummy_320 x f)), ((nb067_alpha_dummy_317), (nb067_alpha_dummy_318 x f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_cvv)).fv := by
  exact (TEnvFresh.consFresh (nb067_alpha_dummy_322) (nb067_alpha_dummy_324 f) (nb067_wpp_notmem_0814) (nb067_wpp_notmem_0815 f) (TEnvFresh.consFresh (nb067_alpha_dummy_321) (nb067_alpha_dummy_323 f) (nb067_wpp_notmem_0816) (nb067_wpp_notmem_0817 f) (TEnvFresh.consFresh (nb067_alpha_dummy_319) (nb067_alpha_dummy_320 x f) (nb067_wpp_notmem_0818) (nb067_wpp_notmem_0819 x f) (TEnvFresh.consFresh (nb067_alpha_dummy_317) (nb067_alpha_dummy_318 x f) (nb067_wpp_notmem_0820) (nb067_wpp_notmem_0821 x f) (TEnvFresh.consFresh (nb067_alpha_dummy_000) f (nb067_wpp_notmem_0714) (nb067_wpp_notmem_0715 f) (TEnvFresh.consFresh (nb067_alpha_dummy_003) (nb067_alpha_dummy_004 x y f) (nb067_wpp_notmem_0198) (nb067_wpp_notmem_0199 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_002) y (nb067_wpp_notmem_0200) (nb067_wpp_notmem_0201 y) (TEnvFresh.consFresh (nb067_alpha_dummy_001) x (nb067_wpp_notmem_0202) (nb067_wpp_notmem_0203 x) (TEnvFresh.consFresh (nb067_alpha_dummy_005) (nb067_alpha_dummy_006 x y f) (nb067_wpp_notmem_0204) (nb067_wpp_notmem_0205 x y f) (TEnvFresh.nil ((syn_cvv)).fv))))))))))

noncomputable def nb067_wpp_refl_0108 (x : Var) (y : Var) (f : Var) : TReflOn [((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)), ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)), ((nb067_alpha_dummy_319), (nb067_alpha_dummy_320 x f)), ((nb067_alpha_dummy_317), (nb067_alpha_dummy_318 x f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_cvv)).fv :=
  TEnvFresh.reflOn (nb067_compact_envfresh_0108 x y f)

theorem nb067_compact_fv_empty_0248 : (nb067_alpha_dummy_341) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0822 : (nb067_alpha_dummy_341) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_341, fv_syn_c1c] using (nb067_compact_fv_empty_0248)

theorem nb067_compact_fv_empty_0249 (f : Var) : (nb067_alpha_dummy_344 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0823 (f : Var) : (nb067_alpha_dummy_344 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_344, fv_syn_c1c] using (nb067_compact_fv_empty_0249 f)

theorem nb067_compact_fv_empty_0250 : (nb067_alpha_dummy_340) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0824 : (nb067_alpha_dummy_340) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_340, fv_syn_c1c] using (nb067_compact_fv_empty_0250)

theorem nb067_compact_fv_empty_0251 (f : Var) : (nb067_alpha_dummy_343 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0825 (f : Var) : (nb067_alpha_dummy_343 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_343, fv_syn_c1c] using (nb067_compact_fv_empty_0251 f)

theorem nb067_compact_fv_empty_0252 : (nb067_alpha_dummy_339) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0826 : (nb067_alpha_dummy_339) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_339, fv_syn_c1c] using (nb067_compact_fv_empty_0252)

theorem nb067_compact_fv_empty_0253 (f : Var) : (nb067_alpha_dummy_342 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0827 (f : Var) : (nb067_alpha_dummy_342 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_342, fv_syn_c1c] using (nb067_compact_fv_empty_0253 f)

theorem nb067_compact_fv_empty_0254 : (nb067_alpha_dummy_337) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0828 : (nb067_alpha_dummy_337) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_337, fv_syn_c1c] using (nb067_compact_fv_empty_0254)

theorem nb067_compact_fv_empty_0255 (f : Var) : (nb067_alpha_dummy_338 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0829 (f : Var) : (nb067_alpha_dummy_338 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_338, fv_syn_c1c] using (nb067_compact_fv_empty_0255 f)

theorem nb067_compact_fv_empty_0256 : (nb067_alpha_dummy_333) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0830 : (nb067_alpha_dummy_333) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_333, fv_syn_c1c] using (nb067_compact_fv_empty_0256)

theorem nb067_compact_fv_empty_0257 (f : Var) : (nb067_alpha_dummy_335 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0831 (f : Var) : (nb067_alpha_dummy_335 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_335, fv_syn_c1c] using (nb067_compact_fv_empty_0257 f)

theorem nb067_compact_fv_empty_0258 : (nb067_alpha_dummy_334) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0832 : (nb067_alpha_dummy_334) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_334, fv_syn_c1c] using (nb067_compact_fv_empty_0258)

theorem nb067_compact_fv_empty_0259 (f : Var) : (nb067_alpha_dummy_336 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0833 (f : Var) : (nb067_alpha_dummy_336 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_336, fv_syn_c1c] using (nb067_compact_fv_empty_0259 f)

theorem nb067_compact_fv_empty_0260 : (nb067_alpha_dummy_326) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0834 : (nb067_alpha_dummy_326) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_326, fv_syn_c1c] using (nb067_compact_fv_empty_0260)

theorem nb067_compact_fv_empty_0261 (f : Var) : (nb067_alpha_dummy_328 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0835 (f : Var) : (nb067_alpha_dummy_328 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_328, fv_syn_c1c] using (nb067_compact_fv_empty_0261 f)

theorem nb067_compact_fv_empty_0262 : (nb067_alpha_dummy_325) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0836 : (nb067_alpha_dummy_325) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_325, fv_syn_c1c] using (nb067_compact_fv_empty_0262)

theorem nb067_compact_fv_empty_0263 (f : Var) : (nb067_alpha_dummy_327 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0837 (f : Var) : (nb067_alpha_dummy_327 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_327, fv_syn_c1c] using (nb067_compact_fv_empty_0263 f)

theorem nb067_compact_fv_empty_0264 : (nb067_alpha_dummy_331) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0838 : (nb067_alpha_dummy_331) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_331, fv_syn_c1c] using (nb067_compact_fv_empty_0264)

theorem nb067_compact_fv_empty_0265 (f : Var) : (nb067_alpha_dummy_332 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0839 (f : Var) : (nb067_alpha_dummy_332 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_332, fv_syn_c1c] using (nb067_compact_fv_empty_0265 f)

theorem nb067_compact_fv_empty_0266 : (nb067_alpha_dummy_329) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0840 : (nb067_alpha_dummy_329) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_329, fv_syn_c1c] using (nb067_compact_fv_empty_0266)

theorem nb067_compact_fv_empty_0267 (f : Var) : (nb067_alpha_dummy_330 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0841 (f : Var) : (nb067_alpha_dummy_330 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_330, fv_syn_c1c] using (nb067_compact_fv_empty_0267 f)

theorem nb067_wpp_notmem_0842 : (nb067_alpha_dummy_322) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_322, fv_syn_c1c] using (nb067_compact_fv_empty_0240)

theorem nb067_wpp_notmem_0843 (f : Var) : (nb067_alpha_dummy_324 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_324, fv_syn_c1c] using (nb067_compact_fv_empty_0241 f)

theorem nb067_wpp_notmem_0844 : (nb067_alpha_dummy_321) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_321, fv_syn_c1c] using (nb067_compact_fv_empty_0242)

theorem nb067_wpp_notmem_0845 (f : Var) : (nb067_alpha_dummy_323 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_323, fv_syn_c1c] using (nb067_compact_fv_empty_0243 f)

theorem nb067_wpp_notmem_0846 : (nb067_alpha_dummy_319) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_319, fv_syn_c1c] using (nb067_compact_fv_empty_0244)

theorem nb067_wpp_notmem_0847 (x : Var) (f : Var) : (nb067_alpha_dummy_320 x f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_320, fv_syn_c1c] using (nb067_compact_fv_empty_0245 x f)

theorem nb067_wpp_notmem_0848 : (nb067_alpha_dummy_317) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_317, fv_syn_c1c] using (nb067_compact_fv_empty_0246)

theorem nb067_wpp_notmem_0849 (x : Var) (f : Var) : (nb067_alpha_dummy_318 x f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_318, fv_syn_c1c] using (nb067_compact_fv_empty_0247 x f)

theorem nb067_compact_envfresh_0109 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb067_alpha_dummy_341), (nb067_alpha_dummy_344 f)), ((nb067_alpha_dummy_340), (nb067_alpha_dummy_343 f)), ((nb067_alpha_dummy_339), (nb067_alpha_dummy_342 f)), ((nb067_alpha_dummy_337), (nb067_alpha_dummy_338 f)), ((nb067_alpha_dummy_333), (nb067_alpha_dummy_335 f)), ((nb067_alpha_dummy_334), (nb067_alpha_dummy_336 f)), ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)), ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)), ((nb067_alpha_dummy_331), (nb067_alpha_dummy_332 f)), ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)), ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)), ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)), ((nb067_alpha_dummy_319), (nb067_alpha_dummy_320 x f)), ((nb067_alpha_dummy_317), (nb067_alpha_dummy_318 x f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb067_alpha_dummy_341) (nb067_alpha_dummy_344 f) (nb067_wpp_notmem_0822) (nb067_wpp_notmem_0823 f) (TEnvFresh.consFresh (nb067_alpha_dummy_340) (nb067_alpha_dummy_343 f) (nb067_wpp_notmem_0824) (nb067_wpp_notmem_0825 f) (TEnvFresh.consFresh (nb067_alpha_dummy_339) (nb067_alpha_dummy_342 f) (nb067_wpp_notmem_0826) (nb067_wpp_notmem_0827 f) (TEnvFresh.consFresh (nb067_alpha_dummy_337) (nb067_alpha_dummy_338 f) (nb067_wpp_notmem_0828) (nb067_wpp_notmem_0829 f) (TEnvFresh.consFresh (nb067_alpha_dummy_333) (nb067_alpha_dummy_335 f) (nb067_wpp_notmem_0830) (nb067_wpp_notmem_0831 f) (TEnvFresh.consFresh (nb067_alpha_dummy_334) (nb067_alpha_dummy_336 f) (nb067_wpp_notmem_0832) (nb067_wpp_notmem_0833 f) (TEnvFresh.consFresh (nb067_alpha_dummy_326) (nb067_alpha_dummy_328 f) (nb067_wpp_notmem_0834) (nb067_wpp_notmem_0835 f) (TEnvFresh.consFresh (nb067_alpha_dummy_325) (nb067_alpha_dummy_327 f) (nb067_wpp_notmem_0836) (nb067_wpp_notmem_0837 f) (TEnvFresh.consFresh (nb067_alpha_dummy_331) (nb067_alpha_dummy_332 f) (nb067_wpp_notmem_0838) (nb067_wpp_notmem_0839 f) (TEnvFresh.consFresh (nb067_alpha_dummy_329) (nb067_alpha_dummy_330 f) (nb067_wpp_notmem_0840) (nb067_wpp_notmem_0841 f) (TEnvFresh.consFresh (nb067_alpha_dummy_322) (nb067_alpha_dummy_324 f) (nb067_wpp_notmem_0842) (nb067_wpp_notmem_0843 f) (TEnvFresh.consFresh (nb067_alpha_dummy_321) (nb067_alpha_dummy_323 f) (nb067_wpp_notmem_0844) (nb067_wpp_notmem_0845 f) (TEnvFresh.consFresh (nb067_alpha_dummy_319) (nb067_alpha_dummy_320 x f) (nb067_wpp_notmem_0846) (nb067_wpp_notmem_0847 x f) (TEnvFresh.consFresh (nb067_alpha_dummy_317) (nb067_alpha_dummy_318 x f) (nb067_wpp_notmem_0848) (nb067_wpp_notmem_0849 x f) (TEnvFresh.consFresh (nb067_alpha_dummy_000) f (nb067_wpp_notmem_0236) (nb067_wpp_notmem_0237 f) (TEnvFresh.consFresh (nb067_alpha_dummy_003) (nb067_alpha_dummy_004 x y f) (nb067_wpp_notmem_0028) (nb067_wpp_notmem_0029 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_002) y (nb067_wpp_notmem_0030) (nb067_wpp_notmem_0031 y) (TEnvFresh.consFresh (nb067_alpha_dummy_001) x (nb067_wpp_notmem_0032) (nb067_wpp_notmem_0033 x) (TEnvFresh.consFresh (nb067_alpha_dummy_005) (nb067_alpha_dummy_006 x y f) (nb067_wpp_notmem_0034) (nb067_wpp_notmem_0035 x y f) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))

noncomputable def nb067_wpp_refl_0109 (x : Var) (y : Var) (f : Var) : TReflOn [((nb067_alpha_dummy_341), (nb067_alpha_dummy_344 f)), ((nb067_alpha_dummy_340), (nb067_alpha_dummy_343 f)), ((nb067_alpha_dummy_339), (nb067_alpha_dummy_342 f)), ((nb067_alpha_dummy_337), (nb067_alpha_dummy_338 f)), ((nb067_alpha_dummy_333), (nb067_alpha_dummy_335 f)), ((nb067_alpha_dummy_334), (nb067_alpha_dummy_336 f)), ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)), ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)), ((nb067_alpha_dummy_331), (nb067_alpha_dummy_332 f)), ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)), ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)), ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)), ((nb067_alpha_dummy_319), (nb067_alpha_dummy_320 x f)), ((nb067_alpha_dummy_317), (nb067_alpha_dummy_318 x f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb067_compact_envfresh_0109 x y f)

theorem nb067_wpp_notmem_0850 : (nb067_alpha_dummy_341) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_341, fv_syn_c0] using (nb067_compact_fv_empty_0248)

theorem nb067_wpp_notmem_0851 (f : Var) : (nb067_alpha_dummy_344 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_344, fv_syn_c0] using (nb067_compact_fv_empty_0249 f)

theorem nb067_wpp_notmem_0852 : (nb067_alpha_dummy_340) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_340, fv_syn_c0] using (nb067_compact_fv_empty_0250)

theorem nb067_wpp_notmem_0853 (f : Var) : (nb067_alpha_dummy_343 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_343, fv_syn_c0] using (nb067_compact_fv_empty_0251 f)

theorem nb067_wpp_notmem_0854 : (nb067_alpha_dummy_339) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_339, fv_syn_c0] using (nb067_compact_fv_empty_0252)

theorem nb067_wpp_notmem_0855 (f : Var) : (nb067_alpha_dummy_342 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_342, fv_syn_c0] using (nb067_compact_fv_empty_0253 f)

theorem nb067_wpp_notmem_0856 : (nb067_alpha_dummy_337) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_337, fv_syn_c0] using (nb067_compact_fv_empty_0254)

theorem nb067_wpp_notmem_0857 (f : Var) : (nb067_alpha_dummy_338 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_338, fv_syn_c0] using (nb067_compact_fv_empty_0255 f)

theorem nb067_wpp_notmem_0858 : (nb067_alpha_dummy_333) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_333, fv_syn_c0] using (nb067_compact_fv_empty_0256)

theorem nb067_wpp_notmem_0859 (f : Var) : (nb067_alpha_dummy_335 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_335, fv_syn_c0] using (nb067_compact_fv_empty_0257 f)

theorem nb067_wpp_notmem_0860 : (nb067_alpha_dummy_334) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_334, fv_syn_c0] using (nb067_compact_fv_empty_0258)

theorem nb067_wpp_notmem_0861 (f : Var) : (nb067_alpha_dummy_336 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_336, fv_syn_c0] using (nb067_compact_fv_empty_0259 f)

theorem nb067_wpp_notmem_0862 : (nb067_alpha_dummy_326) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_326, fv_syn_c0] using (nb067_compact_fv_empty_0260)

theorem nb067_wpp_notmem_0863 (f : Var) : (nb067_alpha_dummy_328 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_328, fv_syn_c0] using (nb067_compact_fv_empty_0261 f)

theorem nb067_wpp_notmem_0864 : (nb067_alpha_dummy_325) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_325, fv_syn_c0] using (nb067_compact_fv_empty_0262)

theorem nb067_wpp_notmem_0865 (f : Var) : (nb067_alpha_dummy_327 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_327, fv_syn_c0] using (nb067_compact_fv_empty_0263 f)

theorem nb067_wpp_notmem_0866 : (nb067_alpha_dummy_331) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_331, fv_syn_c0] using (nb067_compact_fv_empty_0264)

theorem nb067_wpp_notmem_0867 (f : Var) : (nb067_alpha_dummy_332 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_332, fv_syn_c0] using (nb067_compact_fv_empty_0265 f)

theorem nb067_wpp_notmem_0868 : (nb067_alpha_dummy_329) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_329, fv_syn_c0] using (nb067_compact_fv_empty_0266)

theorem nb067_wpp_notmem_0869 (f : Var) : (nb067_alpha_dummy_330 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_330, fv_syn_c0] using (nb067_compact_fv_empty_0267 f)

theorem nb067_wpp_notmem_0870 : (nb067_alpha_dummy_322) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_322, fv_syn_c0] using (nb067_compact_fv_empty_0240)

theorem nb067_wpp_notmem_0871 (f : Var) : (nb067_alpha_dummy_324 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_324, fv_syn_c0] using (nb067_compact_fv_empty_0241 f)

theorem nb067_wpp_notmem_0872 : (nb067_alpha_dummy_321) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_321, fv_syn_c0] using (nb067_compact_fv_empty_0242)

theorem nb067_wpp_notmem_0873 (f : Var) : (nb067_alpha_dummy_323 f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_323, fv_syn_c0] using (nb067_compact_fv_empty_0243 f)

theorem nb067_wpp_notmem_0874 : (nb067_alpha_dummy_319) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_319, fv_syn_c0] using (nb067_compact_fv_empty_0244)

theorem nb067_wpp_notmem_0875 (x : Var) (f : Var) : (nb067_alpha_dummy_320 x f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_320, fv_syn_c0] using (nb067_compact_fv_empty_0245 x f)

theorem nb067_wpp_notmem_0876 : (nb067_alpha_dummy_317) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_317, fv_syn_c0] using (nb067_compact_fv_empty_0246)

theorem nb067_wpp_notmem_0877 (x : Var) (f : Var) : (nb067_alpha_dummy_318 x f) ∉ ((syn_c0)).fv := by
  simpa only [nb067_alpha_dummy_318, fv_syn_c0] using (nb067_compact_fv_empty_0247 x f)

theorem nb067_compact_envfresh_0110 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb067_alpha_dummy_341), (nb067_alpha_dummy_344 f)), ((nb067_alpha_dummy_340), (nb067_alpha_dummy_343 f)), ((nb067_alpha_dummy_339), (nb067_alpha_dummy_342 f)), ((nb067_alpha_dummy_337), (nb067_alpha_dummy_338 f)), ((nb067_alpha_dummy_333), (nb067_alpha_dummy_335 f)), ((nb067_alpha_dummy_334), (nb067_alpha_dummy_336 f)), ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)), ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)), ((nb067_alpha_dummy_331), (nb067_alpha_dummy_332 f)), ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)), ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)), ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)), ((nb067_alpha_dummy_319), (nb067_alpha_dummy_320 x f)), ((nb067_alpha_dummy_317), (nb067_alpha_dummy_318 x f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb067_alpha_dummy_341) (nb067_alpha_dummy_344 f) (nb067_wpp_notmem_0850) (nb067_wpp_notmem_0851 f) (TEnvFresh.consFresh (nb067_alpha_dummy_340) (nb067_alpha_dummy_343 f) (nb067_wpp_notmem_0852) (nb067_wpp_notmem_0853 f) (TEnvFresh.consFresh (nb067_alpha_dummy_339) (nb067_alpha_dummy_342 f) (nb067_wpp_notmem_0854) (nb067_wpp_notmem_0855 f) (TEnvFresh.consFresh (nb067_alpha_dummy_337) (nb067_alpha_dummy_338 f) (nb067_wpp_notmem_0856) (nb067_wpp_notmem_0857 f) (TEnvFresh.consFresh (nb067_alpha_dummy_333) (nb067_alpha_dummy_335 f) (nb067_wpp_notmem_0858) (nb067_wpp_notmem_0859 f) (TEnvFresh.consFresh (nb067_alpha_dummy_334) (nb067_alpha_dummy_336 f) (nb067_wpp_notmem_0860) (nb067_wpp_notmem_0861 f) (TEnvFresh.consFresh (nb067_alpha_dummy_326) (nb067_alpha_dummy_328 f) (nb067_wpp_notmem_0862) (nb067_wpp_notmem_0863 f) (TEnvFresh.consFresh (nb067_alpha_dummy_325) (nb067_alpha_dummy_327 f) (nb067_wpp_notmem_0864) (nb067_wpp_notmem_0865 f) (TEnvFresh.consFresh (nb067_alpha_dummy_331) (nb067_alpha_dummy_332 f) (nb067_wpp_notmem_0866) (nb067_wpp_notmem_0867 f) (TEnvFresh.consFresh (nb067_alpha_dummy_329) (nb067_alpha_dummy_330 f) (nb067_wpp_notmem_0868) (nb067_wpp_notmem_0869 f) (TEnvFresh.consFresh (nb067_alpha_dummy_322) (nb067_alpha_dummy_324 f) (nb067_wpp_notmem_0870) (nb067_wpp_notmem_0871 f) (TEnvFresh.consFresh (nb067_alpha_dummy_321) (nb067_alpha_dummy_323 f) (nb067_wpp_notmem_0872) (nb067_wpp_notmem_0873 f) (TEnvFresh.consFresh (nb067_alpha_dummy_319) (nb067_alpha_dummy_320 x f) (nb067_wpp_notmem_0874) (nb067_wpp_notmem_0875 x f) (TEnvFresh.consFresh (nb067_alpha_dummy_317) (nb067_alpha_dummy_318 x f) (nb067_wpp_notmem_0876) (nb067_wpp_notmem_0877 x f) (TEnvFresh.consFresh (nb067_alpha_dummy_000) f (nb067_wpp_notmem_0268) (nb067_wpp_notmem_0269 f) (TEnvFresh.consFresh (nb067_alpha_dummy_003) (nb067_alpha_dummy_004 x y f) (nb067_wpp_notmem_0064) (nb067_wpp_notmem_0065 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_002) y (nb067_wpp_notmem_0066) (nb067_wpp_notmem_0067 y) (TEnvFresh.consFresh (nb067_alpha_dummy_001) x (nb067_wpp_notmem_0068) (nb067_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb067_alpha_dummy_005) (nb067_alpha_dummy_006 x y f) (nb067_wpp_notmem_0070) (nb067_wpp_notmem_0071 x y f) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))))

noncomputable def nb067_wpp_refl_0110 (x : Var) (y : Var) (f : Var) : TReflOn [((nb067_alpha_dummy_341), (nb067_alpha_dummy_344 f)), ((nb067_alpha_dummy_340), (nb067_alpha_dummy_343 f)), ((nb067_alpha_dummy_339), (nb067_alpha_dummy_342 f)), ((nb067_alpha_dummy_337), (nb067_alpha_dummy_338 f)), ((nb067_alpha_dummy_333), (nb067_alpha_dummy_335 f)), ((nb067_alpha_dummy_334), (nb067_alpha_dummy_336 f)), ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)), ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)), ((nb067_alpha_dummy_331), (nb067_alpha_dummy_332 f)), ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)), ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)), ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)), ((nb067_alpha_dummy_319), (nb067_alpha_dummy_320 x f)), ((nb067_alpha_dummy_317), (nb067_alpha_dummy_318 x f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb067_compact_envfresh_0110 x y f)

noncomputable def nb067_split_alpha_0083 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb067_alpha_dummy_341), (nb067_alpha_dummy_344 f)), ((nb067_alpha_dummy_340), (nb067_alpha_dummy_343 f)), ((nb067_alpha_dummy_339), (nb067_alpha_dummy_342 f)), ((nb067_alpha_dummy_337), (nb067_alpha_dummy_338 f)), ((nb067_alpha_dummy_333), (nb067_alpha_dummy_335 f)), ((nb067_alpha_dummy_334), (nb067_alpha_dummy_336 f)), ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)), ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)), ((nb067_alpha_dummy_331), (nb067_alpha_dummy_332 f)), ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)), ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)), ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)), ((nb067_alpha_dummy_319), (nb067_alpha_dummy_320 x f)), ((nb067_alpha_dummy_317), (nb067_alpha_dummy_318 x f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_340)) (Class.cv (nb067_alpha_dummy_341))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_339)) (syn_cun (Class.cv (nb067_alpha_dummy_340)) (Class.cv (nb067_alpha_dummy_341)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb067_alpha_dummy_343 f)) (Class.cv (nb067_alpha_dummy_344 f))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb067_alpha_dummy_342 f)) (syn_cun (Class.cv (nb067_alpha_dummy_343 f)) (Class.cv (nb067_alpha_dummy_344 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0356) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0357 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0354) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0355 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0360) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0361 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0358) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0359 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0356) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0357 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0354) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0355 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0360) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0361 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0358) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0359 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_341), (nb067_alpha_dummy_344 f)), ((nb067_alpha_dummy_340), (nb067_alpha_dummy_343 f)), ((nb067_alpha_dummy_339), (nb067_alpha_dummy_342 f)), ((nb067_alpha_dummy_337), (nb067_alpha_dummy_338 f)), ((nb067_alpha_dummy_333), (nb067_alpha_dummy_335 f)), ((nb067_alpha_dummy_334), (nb067_alpha_dummy_336 f)), ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)), ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)), ((nb067_alpha_dummy_331), (nb067_alpha_dummy_332 f)), ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)), ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)), ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)), ((nb067_alpha_dummy_319), (nb067_alpha_dummy_320 x f)), ((nb067_alpha_dummy_317), (nb067_alpha_dummy_318 x f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_c0) (nb067_wpp_refl_0110 x y f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0364) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0365 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0362) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0363 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0364) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0365 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0362) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0363 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_333))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_335 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0368) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0369 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0366) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0367 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0368) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0369 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0366) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0367 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb067_wpp_notmem_0878 : (nb067_alpha_dummy_337) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_337, fv_syn_cnnc] using (nb067_compact_fv_empty_0254)

theorem nb067_wpp_notmem_0879 (f : Var) : (nb067_alpha_dummy_338 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_338, fv_syn_cnnc] using (nb067_compact_fv_empty_0255 f)

theorem nb067_wpp_notmem_0880 : (nb067_alpha_dummy_333) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_333, fv_syn_cnnc] using (nb067_compact_fv_empty_0256)

theorem nb067_wpp_notmem_0881 (f : Var) : (nb067_alpha_dummy_335 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_335, fv_syn_cnnc] using (nb067_compact_fv_empty_0257 f)

theorem nb067_wpp_notmem_0882 : (nb067_alpha_dummy_334) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_334, fv_syn_cnnc] using (nb067_compact_fv_empty_0258)

theorem nb067_wpp_notmem_0883 (f : Var) : (nb067_alpha_dummy_336 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_336, fv_syn_cnnc] using (nb067_compact_fv_empty_0259 f)

theorem nb067_wpp_notmem_0884 : (nb067_alpha_dummy_326) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_326, fv_syn_cnnc] using (nb067_compact_fv_empty_0260)

theorem nb067_wpp_notmem_0885 (f : Var) : (nb067_alpha_dummy_328 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_328, fv_syn_cnnc] using (nb067_compact_fv_empty_0261 f)

theorem nb067_wpp_notmem_0886 : (nb067_alpha_dummy_325) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_325, fv_syn_cnnc] using (nb067_compact_fv_empty_0262)

theorem nb067_wpp_notmem_0887 (f : Var) : (nb067_alpha_dummy_327 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_327, fv_syn_cnnc] using (nb067_compact_fv_empty_0263 f)

theorem nb067_wpp_notmem_0888 : (nb067_alpha_dummy_331) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_331, fv_syn_cnnc] using (nb067_compact_fv_empty_0264)

theorem nb067_wpp_notmem_0889 (f : Var) : (nb067_alpha_dummy_332 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_332, fv_syn_cnnc] using (nb067_compact_fv_empty_0265 f)

theorem nb067_wpp_notmem_0890 : (nb067_alpha_dummy_329) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_329, fv_syn_cnnc] using (nb067_compact_fv_empty_0266)

theorem nb067_wpp_notmem_0891 (f : Var) : (nb067_alpha_dummy_330 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_330, fv_syn_cnnc] using (nb067_compact_fv_empty_0267 f)

theorem nb067_wpp_notmem_0892 : (nb067_alpha_dummy_322) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_322, fv_syn_cnnc] using (nb067_compact_fv_empty_0240)

theorem nb067_wpp_notmem_0893 (f : Var) : (nb067_alpha_dummy_324 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_324, fv_syn_cnnc] using (nb067_compact_fv_empty_0241 f)

theorem nb067_wpp_notmem_0894 : (nb067_alpha_dummy_321) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_321, fv_syn_cnnc] using (nb067_compact_fv_empty_0242)

theorem nb067_wpp_notmem_0895 (f : Var) : (nb067_alpha_dummy_323 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_323, fv_syn_cnnc] using (nb067_compact_fv_empty_0243 f)

theorem nb067_wpp_notmem_0896 : (nb067_alpha_dummy_319) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_319, fv_syn_cnnc] using (nb067_compact_fv_empty_0244)

theorem nb067_wpp_notmem_0897 (x : Var) (f : Var) : (nb067_alpha_dummy_320 x f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_320, fv_syn_cnnc] using (nb067_compact_fv_empty_0245 x f)

theorem nb067_wpp_notmem_0898 : (nb067_alpha_dummy_317) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_317, fv_syn_cnnc] using (nb067_compact_fv_empty_0246)

theorem nb067_wpp_notmem_0899 (x : Var) (f : Var) : (nb067_alpha_dummy_318 x f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb067_alpha_dummy_318, fv_syn_cnnc] using (nb067_compact_fv_empty_0247 x f)

theorem nb067_compact_envfresh_0111 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb067_alpha_dummy_337), (nb067_alpha_dummy_338 f)), ((nb067_alpha_dummy_333), (nb067_alpha_dummy_335 f)), ((nb067_alpha_dummy_334), (nb067_alpha_dummy_336 f)), ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)), ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)), ((nb067_alpha_dummy_331), (nb067_alpha_dummy_332 f)), ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)), ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)), ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)), ((nb067_alpha_dummy_319), (nb067_alpha_dummy_320 x f)), ((nb067_alpha_dummy_317), (nb067_alpha_dummy_318 x f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb067_alpha_dummy_337) (nb067_alpha_dummy_338 f) (nb067_wpp_notmem_0878) (nb067_wpp_notmem_0879 f) (TEnvFresh.consFresh (nb067_alpha_dummy_333) (nb067_alpha_dummy_335 f) (nb067_wpp_notmem_0880) (nb067_wpp_notmem_0881 f) (TEnvFresh.consFresh (nb067_alpha_dummy_334) (nb067_alpha_dummy_336 f) (nb067_wpp_notmem_0882) (nb067_wpp_notmem_0883 f) (TEnvFresh.consFresh (nb067_alpha_dummy_326) (nb067_alpha_dummy_328 f) (nb067_wpp_notmem_0884) (nb067_wpp_notmem_0885 f) (TEnvFresh.consFresh (nb067_alpha_dummy_325) (nb067_alpha_dummy_327 f) (nb067_wpp_notmem_0886) (nb067_wpp_notmem_0887 f) (TEnvFresh.consFresh (nb067_alpha_dummy_331) (nb067_alpha_dummy_332 f) (nb067_wpp_notmem_0888) (nb067_wpp_notmem_0889 f) (TEnvFresh.consFresh (nb067_alpha_dummy_329) (nb067_alpha_dummy_330 f) (nb067_wpp_notmem_0890) (nb067_wpp_notmem_0891 f) (TEnvFresh.consFresh (nb067_alpha_dummy_322) (nb067_alpha_dummy_324 f) (nb067_wpp_notmem_0892) (nb067_wpp_notmem_0893 f) (TEnvFresh.consFresh (nb067_alpha_dummy_321) (nb067_alpha_dummy_323 f) (nb067_wpp_notmem_0894) (nb067_wpp_notmem_0895 f) (TEnvFresh.consFresh (nb067_alpha_dummy_319) (nb067_alpha_dummy_320 x f) (nb067_wpp_notmem_0896) (nb067_wpp_notmem_0897 x f) (TEnvFresh.consFresh (nb067_alpha_dummy_317) (nb067_alpha_dummy_318 x f) (nb067_wpp_notmem_0898) (nb067_wpp_notmem_0899 x f) (TEnvFresh.consFresh (nb067_alpha_dummy_000) f (nb067_wpp_notmem_0294) (nb067_wpp_notmem_0295 f) (TEnvFresh.consFresh (nb067_alpha_dummy_003) (nb067_alpha_dummy_004 x y f) (nb067_wpp_notmem_0094) (nb067_wpp_notmem_0095 x y f) (TEnvFresh.consFresh (nb067_alpha_dummy_002) y (nb067_wpp_notmem_0096) (nb067_wpp_notmem_0097 y) (TEnvFresh.consFresh (nb067_alpha_dummy_001) x (nb067_wpp_notmem_0098) (nb067_wpp_notmem_0099 x) (TEnvFresh.consFresh (nb067_alpha_dummy_005) (nb067_alpha_dummy_006 x y f) (nb067_wpp_notmem_0100) (nb067_wpp_notmem_0101 x y f) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))))

noncomputable def nb067_wpp_refl_0111 (x : Var) (y : Var) (f : Var) : TReflOn [((nb067_alpha_dummy_337), (nb067_alpha_dummy_338 f)), ((nb067_alpha_dummy_333), (nb067_alpha_dummy_335 f)), ((nb067_alpha_dummy_334), (nb067_alpha_dummy_336 f)), ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)), ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)), ((nb067_alpha_dummy_331), (nb067_alpha_dummy_332 f)), ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)), ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)), ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)), ((nb067_alpha_dummy_319), (nb067_alpha_dummy_320 x f)), ((nb067_alpha_dummy_317), (nb067_alpha_dummy_318 x f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb067_compact_envfresh_0111 x y f)

noncomputable def nb067_split_alpha_0084 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb067_alpha_dummy_333), (nb067_alpha_dummy_335 f)), ((nb067_alpha_dummy_334), (nb067_alpha_dummy_336 f)), ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)), ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)), ((nb067_alpha_dummy_331), (nb067_alpha_dummy_332 f)), ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)), ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)), ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)), ((nb067_alpha_dummy_319), (nb067_alpha_dummy_320 x f)), ((nb067_alpha_dummy_317), (nb067_alpha_dummy_318 x f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb067_alpha_dummy_333)) (Class.cv (nb067_alpha_dummy_326))) (Wff.classEq (Class.cv (nb067_alpha_dummy_334)) (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_333)) (syn_cnnc)) (syn_cplc (Class.cv (nb067_alpha_dummy_333)) (syn_c1c)) (Class.cv (nb067_alpha_dummy_333)))))) (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb067_alpha_dummy_335 f)) (Class.cv (nb067_alpha_dummy_328 f))) (Wff.classEq (Class.cv (nb067_alpha_dummy_336 f)) (syn_cif (Wff.classMem (Class.cv (nb067_alpha_dummy_335 f)) (syn_cnnc)) (syn_cplc (Class.cv (nb067_alpha_dummy_335 f)) (syn_c1c)) (Class.cv (nb067_alpha_dummy_335 f)))))) :=
  (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0348) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0349 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0348) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0349 f) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb067_alpha_dummy_326))).fv) (by decide)) (freshVar_injective (((Class.cv (nb067_alpha_dummy_328 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0352) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0353 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0352) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0353 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0350) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0351 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_341), (nb067_alpha_dummy_344 f)), ((nb067_alpha_dummy_340), (nb067_alpha_dummy_343 f)), ((nb067_alpha_dummy_339), (nb067_alpha_dummy_342 f)), ((nb067_alpha_dummy_337), (nb067_alpha_dummy_338 f)), ((nb067_alpha_dummy_333), (nb067_alpha_dummy_335 f)), ((nb067_alpha_dummy_334), (nb067_alpha_dummy_336 f)), ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)), ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)), ((nb067_alpha_dummy_331), (nb067_alpha_dummy_332 f)), ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)), ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)), ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)), ((nb067_alpha_dummy_319), (nb067_alpha_dummy_320 x f)), ((nb067_alpha_dummy_317), (nb067_alpha_dummy_318 x f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_c1c) (nb067_wpp_refl_0109 x y f))) (TAlphaWff.neg (TAlphaWff.neg (nb067_split_alpha_0083 x y f)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0350) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0351 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_337), (nb067_alpha_dummy_338 f)), ((nb067_alpha_dummy_333), (nb067_alpha_dummy_335 f)), ((nb067_alpha_dummy_334), (nb067_alpha_dummy_336 f)), ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)), ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)), ((nb067_alpha_dummy_331), (nb067_alpha_dummy_332 f)), ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)), ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)), ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)), ((nb067_alpha_dummy_319), (nb067_alpha_dummy_320 x f)), ((nb067_alpha_dummy_317), (nb067_alpha_dummy_318 x f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_cnnc) (nb067_wpp_refl_0111 x y f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0350) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0351 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0350) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0351 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb067_alpha_dummy_337), (nb067_alpha_dummy_338 f)), ((nb067_alpha_dummy_333), (nb067_alpha_dummy_335 f)), ((nb067_alpha_dummy_334), (nb067_alpha_dummy_336 f)), ((nb067_alpha_dummy_326), (nb067_alpha_dummy_328 f)), ((nb067_alpha_dummy_325), (nb067_alpha_dummy_327 f)), ((nb067_alpha_dummy_331), (nb067_alpha_dummy_332 f)), ((nb067_alpha_dummy_329), (nb067_alpha_dummy_330 f)), ((nb067_alpha_dummy_322), (nb067_alpha_dummy_324 f)), ((nb067_alpha_dummy_321), (nb067_alpha_dummy_323 f)), ((nb067_alpha_dummy_319), (nb067_alpha_dummy_320 x f)), ((nb067_alpha_dummy_317), (nb067_alpha_dummy_318 x f)), ((nb067_alpha_dummy_000), f), ((nb067_alpha_dummy_003), (nb067_alpha_dummy_004 x y f)), ((nb067_alpha_dummy_002), y), ((nb067_alpha_dummy_001), x), ((nb067_alpha_dummy_005), (nb067_alpha_dummy_006 x y f))] (syn_cnnc) (nb067_wpp_refl_0111 x y f))))))))))))))

theorem nb067_compact_fv_empty_0268 : (nb067_alpha_dummy_359) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0900 : (nb067_alpha_dummy_359) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_359, fv_syn_c1c] using (nb067_compact_fv_empty_0268)

theorem nb067_compact_fv_empty_0269 (f : Var) : (nb067_alpha_dummy_360 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0901 (f : Var) : (nb067_alpha_dummy_360 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_360, fv_syn_c1c] using (nb067_compact_fv_empty_0269 f)

theorem nb067_compact_fv_empty_0270 : (nb067_alpha_dummy_357) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0902 : (nb067_alpha_dummy_357) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_357, fv_syn_c1c] using (nb067_compact_fv_empty_0270)

theorem nb067_compact_fv_empty_0271 (f : Var) : (nb067_alpha_dummy_358 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0903 (f : Var) : (nb067_alpha_dummy_358 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_358, fv_syn_c1c] using (nb067_compact_fv_empty_0271 f)

theorem nb067_compact_fv_empty_0272 : (nb067_alpha_dummy_355) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0904 : (nb067_alpha_dummy_355) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_355, fv_syn_c1c] using (nb067_compact_fv_empty_0272)

theorem nb067_compact_fv_empty_0273 (f : Var) : (nb067_alpha_dummy_356 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb067_wpp_notmem_0905 (f : Var) : (nb067_alpha_dummy_356 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb067_alpha_dummy_356, fv_syn_c1c] using (nb067_compact_fv_empty_0273 f)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
