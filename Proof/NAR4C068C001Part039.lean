import NAR4C068C001Part038

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

noncomputable def nb068_split_alpha_0095 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb068_alpha_dummy_379), (nb068_alpha_dummy_381 f)), ((nb068_alpha_dummy_380), (nb068_alpha_dummy_382 f)), ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)), ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)), ((nb068_alpha_dummy_377), (nb068_alpha_dummy_378 f)), ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_379)) (Class.cv (nb068_alpha_dummy_372))) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_380)) (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_379)) (syn_cnnc)) (syn_cplc (Class.cv (nb068_alpha_dummy_379)) (syn_c1c)) (Class.cv (nb068_alpha_dummy_379)))))) (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_381 f)) (Class.cv (nb068_alpha_dummy_374 f))) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_382 f)) (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_381 f)) (syn_cnnc)) (syn_cplc (Class.cv (nb068_alpha_dummy_381 f)) (syn_c1c)) (Class.cv (nb068_alpha_dummy_381 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0388) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0389 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0388) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0389 f) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_372))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_374 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0392) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0393 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0392) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0393 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0390) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0391 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_387), (nb068_alpha_dummy_390 f)), ((nb068_alpha_dummy_386), (nb068_alpha_dummy_389 f)), ((nb068_alpha_dummy_385), (nb068_alpha_dummy_388 f)), ((nb068_alpha_dummy_383), (nb068_alpha_dummy_384 f)), ((nb068_alpha_dummy_379), (nb068_alpha_dummy_381 f)), ((nb068_alpha_dummy_380), (nb068_alpha_dummy_382 f)), ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)), ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)), ((nb068_alpha_dummy_377), (nb068_alpha_dummy_378 f)), ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_c1c) (nb068_wpp_refl_0123 x y f))) (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0094 x y f)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0390) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0391 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_383), (nb068_alpha_dummy_384 f)), ((nb068_alpha_dummy_379), (nb068_alpha_dummy_381 f)), ((nb068_alpha_dummy_380), (nb068_alpha_dummy_382 f)), ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)), ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)), ((nb068_alpha_dummy_377), (nb068_alpha_dummy_378 f)), ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_cnnc) (nb068_wpp_refl_0125 x y f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0390) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0391 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0390) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0391 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_383), (nb068_alpha_dummy_384 f)), ((nb068_alpha_dummy_379), (nb068_alpha_dummy_381 f)), ((nb068_alpha_dummy_380), (nb068_alpha_dummy_382 f)), ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)), ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)), ((nb068_alpha_dummy_377), (nb068_alpha_dummy_378 f)), ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_cnnc) (nb068_wpp_refl_0125 x y f))))))))))))

theorem nb068_compact_fv_empty_0304 : (nb068_alpha_dummy_405) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1022 : (nb068_alpha_dummy_405) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_405, fv_syn_c1c] using (nb068_compact_fv_empty_0304)

theorem nb068_compact_fv_empty_0305 (f : Var) : (nb068_alpha_dummy_406 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1023 (f : Var) : (nb068_alpha_dummy_406 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_406, fv_syn_c1c] using (nb068_compact_fv_empty_0305 f)

theorem nb068_compact_fv_empty_0306 : (nb068_alpha_dummy_403) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1024 : (nb068_alpha_dummy_403) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_403, fv_syn_c1c] using (nb068_compact_fv_empty_0306)

theorem nb068_compact_fv_empty_0307 (f : Var) : (nb068_alpha_dummy_404 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1025 (f : Var) : (nb068_alpha_dummy_404 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_404, fv_syn_c1c] using (nb068_compact_fv_empty_0307 f)

theorem nb068_compact_fv_empty_0308 : (nb068_alpha_dummy_401) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1026 : (nb068_alpha_dummy_401) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_401, fv_syn_c1c] using (nb068_compact_fv_empty_0308)

theorem nb068_compact_fv_empty_0309 (f : Var) : (nb068_alpha_dummy_402 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1027 (f : Var) : (nb068_alpha_dummy_402 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_402, fv_syn_c1c] using (nb068_compact_fv_empty_0309 f)

theorem nb068_compact_envfresh_0126 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_387), (nb068_alpha_dummy_390 f)), ((nb068_alpha_dummy_386), (nb068_alpha_dummy_389 f)), ((nb068_alpha_dummy_385), (nb068_alpha_dummy_388 f)), ((nb068_alpha_dummy_383), (nb068_alpha_dummy_384 f)), ((nb068_alpha_dummy_379), (nb068_alpha_dummy_381 f)), ((nb068_alpha_dummy_380), (nb068_alpha_dummy_382 f)), ((nb068_alpha_dummy_405), (nb068_alpha_dummy_406 f)), ((nb068_alpha_dummy_403), (nb068_alpha_dummy_404 f)), ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)), ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)), ((nb068_alpha_dummy_401), (nb068_alpha_dummy_402 f)), ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_387) (nb068_alpha_dummy_390 f) (nb068_wpp_notmem_0962) (nb068_wpp_notmem_0963 f) (TEnvFresh.consFresh (nb068_alpha_dummy_386) (nb068_alpha_dummy_389 f) (nb068_wpp_notmem_0964) (nb068_wpp_notmem_0965 f) (TEnvFresh.consFresh (nb068_alpha_dummy_385) (nb068_alpha_dummy_388 f) (nb068_wpp_notmem_0966) (nb068_wpp_notmem_0967 f) (TEnvFresh.consFresh (nb068_alpha_dummy_383) (nb068_alpha_dummy_384 f) (nb068_wpp_notmem_0968) (nb068_wpp_notmem_0969 f) (TEnvFresh.consFresh (nb068_alpha_dummy_379) (nb068_alpha_dummy_381 f) (nb068_wpp_notmem_0970) (nb068_wpp_notmem_0971 f) (TEnvFresh.consFresh (nb068_alpha_dummy_380) (nb068_alpha_dummy_382 f) (nb068_wpp_notmem_0972) (nb068_wpp_notmem_0973 f) (TEnvFresh.consFresh (nb068_alpha_dummy_405) (nb068_alpha_dummy_406 f) (nb068_wpp_notmem_1022) (nb068_wpp_notmem_1023 f) (TEnvFresh.consFresh (nb068_alpha_dummy_403) (nb068_alpha_dummy_404 f) (nb068_wpp_notmem_1024) (nb068_wpp_notmem_1025 f) (TEnvFresh.consFresh (nb068_alpha_dummy_372) (nb068_alpha_dummy_374 f) (nb068_wpp_notmem_0974) (nb068_wpp_notmem_0975 f) (TEnvFresh.consFresh (nb068_alpha_dummy_371) (nb068_alpha_dummy_373 f) (nb068_wpp_notmem_0976) (nb068_wpp_notmem_0977 f) (TEnvFresh.consFresh (nb068_alpha_dummy_401) (nb068_alpha_dummy_402 f) (nb068_wpp_notmem_1026) (nb068_wpp_notmem_1027 f) (TEnvFresh.consFresh (nb068_alpha_dummy_375) (nb068_alpha_dummy_376 f) (nb068_wpp_notmem_0980) (nb068_wpp_notmem_0981 f) (TEnvFresh.consFresh (nb068_alpha_dummy_329) (nb068_alpha_dummy_332 f) (nb068_wpp_notmem_0982) (nb068_wpp_notmem_0983 f) (TEnvFresh.consFresh (nb068_alpha_dummy_328) (nb068_alpha_dummy_331 f) (nb068_wpp_notmem_0860) (nb068_wpp_notmem_0861 f) (TEnvFresh.consFresh (nb068_alpha_dummy_327) (nb068_alpha_dummy_330 f) (nb068_wpp_notmem_0862) (nb068_wpp_notmem_0863 f) (TEnvFresh.consFresh (nb068_alpha_dummy_333) (nb068_alpha_dummy_334 f) (nb068_wpp_notmem_0864) (nb068_wpp_notmem_0865 f) (TEnvFresh.consFresh (nb068_alpha_dummy_325) (nb068_alpha_dummy_326 f) (nb068_wpp_notmem_0866) (nb068_wpp_notmem_0867 f) (TEnvFresh.consFresh (nb068_alpha_dummy_323) (nb068_alpha_dummy_324 f) (nb068_wpp_notmem_0868) (nb068_wpp_notmem_0869 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0136) (nb068_wpp_notmem_0137 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0020) (nb068_wpp_notmem_0021 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0022) (nb068_wpp_notmem_0023 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0024) (nb068_wpp_notmem_0025 x y f) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))))

noncomputable def nb068_wpp_refl_0126 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_387), (nb068_alpha_dummy_390 f)), ((nb068_alpha_dummy_386), (nb068_alpha_dummy_389 f)), ((nb068_alpha_dummy_385), (nb068_alpha_dummy_388 f)), ((nb068_alpha_dummy_383), (nb068_alpha_dummy_384 f)), ((nb068_alpha_dummy_379), (nb068_alpha_dummy_381 f)), ((nb068_alpha_dummy_380), (nb068_alpha_dummy_382 f)), ((nb068_alpha_dummy_405), (nb068_alpha_dummy_406 f)), ((nb068_alpha_dummy_403), (nb068_alpha_dummy_404 f)), ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)), ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)), ((nb068_alpha_dummy_401), (nb068_alpha_dummy_402 f)), ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0126 x y f)

theorem nb068_wpp_notmem_1028 : (nb068_alpha_dummy_405) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_405, fv_syn_c0] using (nb068_compact_fv_empty_0304)

theorem nb068_wpp_notmem_1029 (f : Var) : (nb068_alpha_dummy_406 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_406, fv_syn_c0] using (nb068_compact_fv_empty_0305 f)

theorem nb068_wpp_notmem_1030 : (nb068_alpha_dummy_403) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_403, fv_syn_c0] using (nb068_compact_fv_empty_0306)

theorem nb068_wpp_notmem_1031 (f : Var) : (nb068_alpha_dummy_404 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_404, fv_syn_c0] using (nb068_compact_fv_empty_0307 f)

theorem nb068_wpp_notmem_1032 : (nb068_alpha_dummy_401) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_401, fv_syn_c0] using (nb068_compact_fv_empty_0308)

theorem nb068_wpp_notmem_1033 (f : Var) : (nb068_alpha_dummy_402 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_402, fv_syn_c0] using (nb068_compact_fv_empty_0309 f)

theorem nb068_compact_envfresh_0127 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_387), (nb068_alpha_dummy_390 f)), ((nb068_alpha_dummy_386), (nb068_alpha_dummy_389 f)), ((nb068_alpha_dummy_385), (nb068_alpha_dummy_388 f)), ((nb068_alpha_dummy_383), (nb068_alpha_dummy_384 f)), ((nb068_alpha_dummy_379), (nb068_alpha_dummy_381 f)), ((nb068_alpha_dummy_380), (nb068_alpha_dummy_382 f)), ((nb068_alpha_dummy_405), (nb068_alpha_dummy_406 f)), ((nb068_alpha_dummy_403), (nb068_alpha_dummy_404 f)), ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)), ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)), ((nb068_alpha_dummy_401), (nb068_alpha_dummy_402 f)), ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_387) (nb068_alpha_dummy_390 f) (nb068_wpp_notmem_0984) (nb068_wpp_notmem_0985 f) (TEnvFresh.consFresh (nb068_alpha_dummy_386) (nb068_alpha_dummy_389 f) (nb068_wpp_notmem_0986) (nb068_wpp_notmem_0987 f) (TEnvFresh.consFresh (nb068_alpha_dummy_385) (nb068_alpha_dummy_388 f) (nb068_wpp_notmem_0988) (nb068_wpp_notmem_0989 f) (TEnvFresh.consFresh (nb068_alpha_dummy_383) (nb068_alpha_dummy_384 f) (nb068_wpp_notmem_0990) (nb068_wpp_notmem_0991 f) (TEnvFresh.consFresh (nb068_alpha_dummy_379) (nb068_alpha_dummy_381 f) (nb068_wpp_notmem_0992) (nb068_wpp_notmem_0993 f) (TEnvFresh.consFresh (nb068_alpha_dummy_380) (nb068_alpha_dummy_382 f) (nb068_wpp_notmem_0994) (nb068_wpp_notmem_0995 f) (TEnvFresh.consFresh (nb068_alpha_dummy_405) (nb068_alpha_dummy_406 f) (nb068_wpp_notmem_1028) (nb068_wpp_notmem_1029 f) (TEnvFresh.consFresh (nb068_alpha_dummy_403) (nb068_alpha_dummy_404 f) (nb068_wpp_notmem_1030) (nb068_wpp_notmem_1031 f) (TEnvFresh.consFresh (nb068_alpha_dummy_372) (nb068_alpha_dummy_374 f) (nb068_wpp_notmem_0996) (nb068_wpp_notmem_0997 f) (TEnvFresh.consFresh (nb068_alpha_dummy_371) (nb068_alpha_dummy_373 f) (nb068_wpp_notmem_0998) (nb068_wpp_notmem_0999 f) (TEnvFresh.consFresh (nb068_alpha_dummy_401) (nb068_alpha_dummy_402 f) (nb068_wpp_notmem_1032) (nb068_wpp_notmem_1033 f) (TEnvFresh.consFresh (nb068_alpha_dummy_375) (nb068_alpha_dummy_376 f) (nb068_wpp_notmem_1002) (nb068_wpp_notmem_1003 f) (TEnvFresh.consFresh (nb068_alpha_dummy_329) (nb068_alpha_dummy_332 f) (nb068_wpp_notmem_1004) (nb068_wpp_notmem_1005 f) (TEnvFresh.consFresh (nb068_alpha_dummy_328) (nb068_alpha_dummy_331 f) (nb068_wpp_notmem_0890) (nb068_wpp_notmem_0891 f) (TEnvFresh.consFresh (nb068_alpha_dummy_327) (nb068_alpha_dummy_330 f) (nb068_wpp_notmem_0892) (nb068_wpp_notmem_0893 f) (TEnvFresh.consFresh (nb068_alpha_dummy_333) (nb068_alpha_dummy_334 f) (nb068_wpp_notmem_0894) (nb068_wpp_notmem_0895 f) (TEnvFresh.consFresh (nb068_alpha_dummy_325) (nb068_alpha_dummy_326 f) (nb068_wpp_notmem_0896) (nb068_wpp_notmem_0897 f) (TEnvFresh.consFresh (nb068_alpha_dummy_323) (nb068_alpha_dummy_324 f) (nb068_wpp_notmem_0898) (nb068_wpp_notmem_0899 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0168) (nb068_wpp_notmem_0169 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0046) (nb068_wpp_notmem_0047 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0048) (nb068_wpp_notmem_0049 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0050) (nb068_wpp_notmem_0051 x y f) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))))))

noncomputable def nb068_wpp_refl_0127 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_387), (nb068_alpha_dummy_390 f)), ((nb068_alpha_dummy_386), (nb068_alpha_dummy_389 f)), ((nb068_alpha_dummy_385), (nb068_alpha_dummy_388 f)), ((nb068_alpha_dummy_383), (nb068_alpha_dummy_384 f)), ((nb068_alpha_dummy_379), (nb068_alpha_dummy_381 f)), ((nb068_alpha_dummy_380), (nb068_alpha_dummy_382 f)), ((nb068_alpha_dummy_405), (nb068_alpha_dummy_406 f)), ((nb068_alpha_dummy_403), (nb068_alpha_dummy_404 f)), ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)), ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)), ((nb068_alpha_dummy_401), (nb068_alpha_dummy_402 f)), ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0127 x y f)

noncomputable def nb068_split_alpha_0096 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb068_alpha_dummy_387), (nb068_alpha_dummy_390 f)), ((nb068_alpha_dummy_386), (nb068_alpha_dummy_389 f)), ((nb068_alpha_dummy_385), (nb068_alpha_dummy_388 f)), ((nb068_alpha_dummy_383), (nb068_alpha_dummy_384 f)), ((nb068_alpha_dummy_379), (nb068_alpha_dummy_381 f)), ((nb068_alpha_dummy_380), (nb068_alpha_dummy_382 f)), ((nb068_alpha_dummy_405), (nb068_alpha_dummy_406 f)), ((nb068_alpha_dummy_403), (nb068_alpha_dummy_404 f)), ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)), ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)), ((nb068_alpha_dummy_401), (nb068_alpha_dummy_402 f)), ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_386)) (Class.cv (nb068_alpha_dummy_387))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_385)) (syn_cun (Class.cv (nb068_alpha_dummy_386)) (Class.cv (nb068_alpha_dummy_387)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_389 f)) (Class.cv (nb068_alpha_dummy_390 f))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_388 f)) (syn_cun (Class.cv (nb068_alpha_dummy_389 f)) (Class.cv (nb068_alpha_dummy_390 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0396) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0397 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0394) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0395 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0400) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0401 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0398) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0399 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0396) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0397 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0394) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0395 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0400) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0401 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0398) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0399 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_387), (nb068_alpha_dummy_390 f)), ((nb068_alpha_dummy_386), (nb068_alpha_dummy_389 f)), ((nb068_alpha_dummy_385), (nb068_alpha_dummy_388 f)), ((nb068_alpha_dummy_383), (nb068_alpha_dummy_384 f)), ((nb068_alpha_dummy_379), (nb068_alpha_dummy_381 f)), ((nb068_alpha_dummy_380), (nb068_alpha_dummy_382 f)), ((nb068_alpha_dummy_405), (nb068_alpha_dummy_406 f)), ((nb068_alpha_dummy_403), (nb068_alpha_dummy_404 f)), ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)), ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)), ((nb068_alpha_dummy_401), (nb068_alpha_dummy_402 f)), ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_c0) (nb068_wpp_refl_0127 x y f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0404) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0405 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0402) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0403 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0404) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0405 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0402) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0403 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0408) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0409 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0406) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0407 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0408) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0409 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0406) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0407 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb068_wpp_notmem_1034 : (nb068_alpha_dummy_405) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_405, fv_syn_cnnc] using (nb068_compact_fv_empty_0304)

theorem nb068_wpp_notmem_1035 (f : Var) : (nb068_alpha_dummy_406 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_406, fv_syn_cnnc] using (nb068_compact_fv_empty_0305 f)

theorem nb068_wpp_notmem_1036 : (nb068_alpha_dummy_403) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_403, fv_syn_cnnc] using (nb068_compact_fv_empty_0306)

theorem nb068_wpp_notmem_1037 (f : Var) : (nb068_alpha_dummy_404 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_404, fv_syn_cnnc] using (nb068_compact_fv_empty_0307 f)

theorem nb068_wpp_notmem_1038 : (nb068_alpha_dummy_401) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_401, fv_syn_cnnc] using (nb068_compact_fv_empty_0308)

theorem nb068_wpp_notmem_1039 (f : Var) : (nb068_alpha_dummy_402 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_402, fv_syn_cnnc] using (nb068_compact_fv_empty_0309 f)

theorem nb068_compact_envfresh_0128 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_383), (nb068_alpha_dummy_384 f)), ((nb068_alpha_dummy_379), (nb068_alpha_dummy_381 f)), ((nb068_alpha_dummy_380), (nb068_alpha_dummy_382 f)), ((nb068_alpha_dummy_405), (nb068_alpha_dummy_406 f)), ((nb068_alpha_dummy_403), (nb068_alpha_dummy_404 f)), ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)), ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)), ((nb068_alpha_dummy_401), (nb068_alpha_dummy_402 f)), ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_383) (nb068_alpha_dummy_384 f) (nb068_wpp_notmem_1006) (nb068_wpp_notmem_1007 f) (TEnvFresh.consFresh (nb068_alpha_dummy_379) (nb068_alpha_dummy_381 f) (nb068_wpp_notmem_1008) (nb068_wpp_notmem_1009 f) (TEnvFresh.consFresh (nb068_alpha_dummy_380) (nb068_alpha_dummy_382 f) (nb068_wpp_notmem_1010) (nb068_wpp_notmem_1011 f) (TEnvFresh.consFresh (nb068_alpha_dummy_405) (nb068_alpha_dummy_406 f) (nb068_wpp_notmem_1034) (nb068_wpp_notmem_1035 f) (TEnvFresh.consFresh (nb068_alpha_dummy_403) (nb068_alpha_dummy_404 f) (nb068_wpp_notmem_1036) (nb068_wpp_notmem_1037 f) (TEnvFresh.consFresh (nb068_alpha_dummy_372) (nb068_alpha_dummy_374 f) (nb068_wpp_notmem_1012) (nb068_wpp_notmem_1013 f) (TEnvFresh.consFresh (nb068_alpha_dummy_371) (nb068_alpha_dummy_373 f) (nb068_wpp_notmem_1014) (nb068_wpp_notmem_1015 f) (TEnvFresh.consFresh (nb068_alpha_dummy_401) (nb068_alpha_dummy_402 f) (nb068_wpp_notmem_1038) (nb068_wpp_notmem_1039 f) (TEnvFresh.consFresh (nb068_alpha_dummy_375) (nb068_alpha_dummy_376 f) (nb068_wpp_notmem_1018) (nb068_wpp_notmem_1019 f) (TEnvFresh.consFresh (nb068_alpha_dummy_329) (nb068_alpha_dummy_332 f) (nb068_wpp_notmem_1020) (nb068_wpp_notmem_1021 f) (TEnvFresh.consFresh (nb068_alpha_dummy_328) (nb068_alpha_dummy_331 f) (nb068_wpp_notmem_0914) (nb068_wpp_notmem_0915 f) (TEnvFresh.consFresh (nb068_alpha_dummy_327) (nb068_alpha_dummy_330 f) (nb068_wpp_notmem_0916) (nb068_wpp_notmem_0917 f) (TEnvFresh.consFresh (nb068_alpha_dummy_333) (nb068_alpha_dummy_334 f) (nb068_wpp_notmem_0918) (nb068_wpp_notmem_0919 f) (TEnvFresh.consFresh (nb068_alpha_dummy_325) (nb068_alpha_dummy_326 f) (nb068_wpp_notmem_0920) (nb068_wpp_notmem_0921 f) (TEnvFresh.consFresh (nb068_alpha_dummy_323) (nb068_alpha_dummy_324 f) (nb068_wpp_notmem_0922) (nb068_wpp_notmem_0923 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0194) (nb068_wpp_notmem_0195 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0066) (nb068_wpp_notmem_0067 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0068) (nb068_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0070) (nb068_wpp_notmem_0071 x y f) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))))))

noncomputable def nb068_wpp_refl_0128 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_383), (nb068_alpha_dummy_384 f)), ((nb068_alpha_dummy_379), (nb068_alpha_dummy_381 f)), ((nb068_alpha_dummy_380), (nb068_alpha_dummy_382 f)), ((nb068_alpha_dummy_405), (nb068_alpha_dummy_406 f)), ((nb068_alpha_dummy_403), (nb068_alpha_dummy_404 f)), ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)), ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)), ((nb068_alpha_dummy_401), (nb068_alpha_dummy_402 f)), ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0128 x y f)

noncomputable def nb068_split_alpha_0097 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb068_alpha_dummy_379), (nb068_alpha_dummy_381 f)), ((nb068_alpha_dummy_380), (nb068_alpha_dummy_382 f)), ((nb068_alpha_dummy_405), (nb068_alpha_dummy_406 f)), ((nb068_alpha_dummy_403), (nb068_alpha_dummy_404 f)), ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)), ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)), ((nb068_alpha_dummy_401), (nb068_alpha_dummy_402 f)), ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_379)) (Class.cv (nb068_alpha_dummy_372))) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_380)) (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_379)) (syn_cnnc)) (syn_cplc (Class.cv (nb068_alpha_dummy_379)) (syn_c1c)) (Class.cv (nb068_alpha_dummy_379)))))) (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_381 f)) (Class.cv (nb068_alpha_dummy_374 f))) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_382 f)) (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_381 f)) (syn_cnnc)) (syn_cplc (Class.cv (nb068_alpha_dummy_381 f)) (syn_c1c)) (Class.cv (nb068_alpha_dummy_381 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0388) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0389 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0388) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0389 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0418) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0419 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0416) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0417 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_372))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_374 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0392) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0393 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0392) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0393 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0390) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0391 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_387), (nb068_alpha_dummy_390 f)), ((nb068_alpha_dummy_386), (nb068_alpha_dummy_389 f)), ((nb068_alpha_dummy_385), (nb068_alpha_dummy_388 f)), ((nb068_alpha_dummy_383), (nb068_alpha_dummy_384 f)), ((nb068_alpha_dummy_379), (nb068_alpha_dummy_381 f)), ((nb068_alpha_dummy_380), (nb068_alpha_dummy_382 f)), ((nb068_alpha_dummy_405), (nb068_alpha_dummy_406 f)), ((nb068_alpha_dummy_403), (nb068_alpha_dummy_404 f)), ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)), ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)), ((nb068_alpha_dummy_401), (nb068_alpha_dummy_402 f)), ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_c1c) (nb068_wpp_refl_0126 x y f))) (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0096 x y f)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0390) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0391 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_383), (nb068_alpha_dummy_384 f)), ((nb068_alpha_dummy_379), (nb068_alpha_dummy_381 f)), ((nb068_alpha_dummy_380), (nb068_alpha_dummy_382 f)), ((nb068_alpha_dummy_405), (nb068_alpha_dummy_406 f)), ((nb068_alpha_dummy_403), (nb068_alpha_dummy_404 f)), ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)), ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)), ((nb068_alpha_dummy_401), (nb068_alpha_dummy_402 f)), ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_cnnc) (nb068_wpp_refl_0128 x y f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0390) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0391 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0390) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0391 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_383), (nb068_alpha_dummy_384 f)), ((nb068_alpha_dummy_379), (nb068_alpha_dummy_381 f)), ((nb068_alpha_dummy_380), (nb068_alpha_dummy_382 f)), ((nb068_alpha_dummy_405), (nb068_alpha_dummy_406 f)), ((nb068_alpha_dummy_403), (nb068_alpha_dummy_404 f)), ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)), ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)), ((nb068_alpha_dummy_401), (nb068_alpha_dummy_402 f)), ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_cnnc) (nb068_wpp_refl_0128 x y f))))))))))))

theorem nb068_wpp_notmem_1040 : (nb068_alpha_dummy_403) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_403, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0306)

theorem nb068_wpp_notmem_1041 (f : Var) : (nb068_alpha_dummy_404 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_404, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0307 f)

theorem nb068_wpp_notmem_1042 : (nb068_alpha_dummy_372) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_372, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0294)

theorem nb068_wpp_notmem_1043 (f : Var) : (nb068_alpha_dummy_374 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_374, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0295 f)

theorem nb068_wpp_notmem_1044 : (nb068_alpha_dummy_371) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_371, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0296)

theorem nb068_wpp_notmem_1045 (f : Var) : (nb068_alpha_dummy_373 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_373, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0297 f)

theorem nb068_wpp_notmem_1046 : (nb068_alpha_dummy_401) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_401, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0308)

theorem nb068_wpp_notmem_1047 (f : Var) : (nb068_alpha_dummy_402 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_402, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0309 f)

theorem nb068_wpp_notmem_1048 : (nb068_alpha_dummy_375) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_375, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0300)

theorem nb068_wpp_notmem_1049 (f : Var) : (nb068_alpha_dummy_376 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_376, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0301 f)

theorem nb068_wpp_notmem_1050 : (nb068_alpha_dummy_329) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_329, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0302)

theorem nb068_wpp_notmem_1051 (f : Var) : (nb068_alpha_dummy_332 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_332, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0303 f)

theorem nb068_compact_envfresh_0129 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_403), (nb068_alpha_dummy_404 f)), ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)), ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)), ((nb068_alpha_dummy_401), (nb068_alpha_dummy_402 f)), ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_403) (nb068_alpha_dummy_404 f) (nb068_wpp_notmem_1040) (nb068_wpp_notmem_1041 f) (TEnvFresh.consFresh (nb068_alpha_dummy_372) (nb068_alpha_dummy_374 f) (nb068_wpp_notmem_1042) (nb068_wpp_notmem_1043 f) (TEnvFresh.consFresh (nb068_alpha_dummy_371) (nb068_alpha_dummy_373 f) (nb068_wpp_notmem_1044) (nb068_wpp_notmem_1045 f) (TEnvFresh.consFresh (nb068_alpha_dummy_401) (nb068_alpha_dummy_402 f) (nb068_wpp_notmem_1046) (nb068_wpp_notmem_1047 f) (TEnvFresh.consFresh (nb068_alpha_dummy_375) (nb068_alpha_dummy_376 f) (nb068_wpp_notmem_1048) (nb068_wpp_notmem_1049 f) (TEnvFresh.consFresh (nb068_alpha_dummy_329) (nb068_alpha_dummy_332 f) (nb068_wpp_notmem_1050) (nb068_wpp_notmem_1051 f) (TEnvFresh.consFresh (nb068_alpha_dummy_328) (nb068_alpha_dummy_331 f) (nb068_wpp_notmem_0952) (nb068_wpp_notmem_0953 f) (TEnvFresh.consFresh (nb068_alpha_dummy_327) (nb068_alpha_dummy_330 f) (nb068_wpp_notmem_0954) (nb068_wpp_notmem_0955 f) (TEnvFresh.consFresh (nb068_alpha_dummy_333) (nb068_alpha_dummy_334 f) (nb068_wpp_notmem_0956) (nb068_wpp_notmem_0957 f) (TEnvFresh.consFresh (nb068_alpha_dummy_325) (nb068_alpha_dummy_326 f) (nb068_wpp_notmem_0958) (nb068_wpp_notmem_0959 f) (TEnvFresh.consFresh (nb068_alpha_dummy_323) (nb068_alpha_dummy_324 f) (nb068_wpp_notmem_0960) (nb068_wpp_notmem_0961 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0234) (nb068_wpp_notmem_0235 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0100) (nb068_wpp_notmem_0101 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0102) (nb068_wpp_notmem_0103 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0104) (nb068_wpp_notmem_0105 x y f) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))))))))))

noncomputable def nb068_wpp_refl_0129 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_403), (nb068_alpha_dummy_404 f)), ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)), ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)), ((nb068_alpha_dummy_401), (nb068_alpha_dummy_402 f)), ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0129 x y f)

noncomputable def nb068_split_alpha_0098 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb068_alpha_dummy_401), (nb068_alpha_dummy_402 f)), ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_401)) (Class.cab (nb068_alpha_dummy_371) (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_329)) (Wff.classEq (Class.cv (nb068_alpha_dummy_371)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_372))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_401)) (Class.cab (nb068_alpha_dummy_371) (syn_wrex (nb068_alpha_dummy_372) (Class.cv (nb068_alpha_dummy_329)) (Wff.classEq (Class.cv (nb068_alpha_dummy_371)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_372))) (syn_csn (syn_c0c))))))))) (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_402 f)) (Class.cab (nb068_alpha_dummy_373 f) (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_332 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_374 f))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_402 f)) (Class.cab (nb068_alpha_dummy_373 f) (syn_wrex (nb068_alpha_dummy_374 f) (Class.cv (nb068_alpha_dummy_332 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_373 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_374 f))) (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0410) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0412 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0410) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0412 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0414) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0415 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0411) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0413 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_329))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_332 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0097 x y f))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0097 x y f))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_403), (nb068_alpha_dummy_404 f)), ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)), ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)), ((nb068_alpha_dummy_401), (nb068_alpha_dummy_402 f)), ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_ccompl (syn_csn (syn_c0c))) (nb068_wpp_refl_0129 x y f))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0410) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0412 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0410) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0412 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0414) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0415 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0411) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0413 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_329))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_332 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0097 x y f))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0097 x y f))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_403), (nb068_alpha_dummy_404 f)), ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)), ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)), ((nb068_alpha_dummy_401), (nb068_alpha_dummy_402 f)), ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_ccompl (syn_csn (syn_c0c))) (nb068_wpp_refl_0129 x y f)))))))))))))))))))

theorem nb068_compact_fv_empty_0310 : (nb068_alpha_dummy_429) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1052 : (nb068_alpha_dummy_429) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_429, fv_syn_c1c] using (nb068_compact_fv_empty_0310)

theorem nb068_compact_fv_empty_0311 (f : Var) : (nb068_alpha_dummy_432 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1053 (f : Var) : (nb068_alpha_dummy_432 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_432, fv_syn_c1c] using (nb068_compact_fv_empty_0311 f)

theorem nb068_compact_fv_empty_0312 : (nb068_alpha_dummy_428) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1054 : (nb068_alpha_dummy_428) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_428, fv_syn_c1c] using (nb068_compact_fv_empty_0312)

theorem nb068_compact_fv_empty_0313 (f : Var) : (nb068_alpha_dummy_431 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1055 (f : Var) : (nb068_alpha_dummy_431 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_431, fv_syn_c1c] using (nb068_compact_fv_empty_0313 f)

theorem nb068_compact_fv_empty_0314 : (nb068_alpha_dummy_427) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1056 : (nb068_alpha_dummy_427) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_427, fv_syn_c1c] using (nb068_compact_fv_empty_0314)

theorem nb068_compact_fv_empty_0315 (f : Var) : (nb068_alpha_dummy_430 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1057 (f : Var) : (nb068_alpha_dummy_430 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_430, fv_syn_c1c] using (nb068_compact_fv_empty_0315 f)

theorem nb068_compact_fv_empty_0316 : (nb068_alpha_dummy_425) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1058 : (nb068_alpha_dummy_425) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_425, fv_syn_c1c] using (nb068_compact_fv_empty_0316)

theorem nb068_compact_fv_empty_0317 (f : Var) : (nb068_alpha_dummy_426 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1059 (f : Var) : (nb068_alpha_dummy_426 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_426, fv_syn_c1c] using (nb068_compact_fv_empty_0317 f)

theorem nb068_compact_fv_empty_0318 : (nb068_alpha_dummy_421) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1060 : (nb068_alpha_dummy_421) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_421, fv_syn_c1c] using (nb068_compact_fv_empty_0318)

theorem nb068_compact_fv_empty_0319 (f : Var) : (nb068_alpha_dummy_423 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1061 (f : Var) : (nb068_alpha_dummy_423 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_423, fv_syn_c1c] using (nb068_compact_fv_empty_0319 f)

theorem nb068_compact_fv_empty_0320 : (nb068_alpha_dummy_422) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1062 : (nb068_alpha_dummy_422) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_422, fv_syn_c1c] using (nb068_compact_fv_empty_0320)

theorem nb068_compact_fv_empty_0321 (f : Var) : (nb068_alpha_dummy_424 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1063 (f : Var) : (nb068_alpha_dummy_424 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_424, fv_syn_c1c] using (nb068_compact_fv_empty_0321 f)

theorem nb068_compact_fv_empty_0322 : (nb068_alpha_dummy_414) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1064 : (nb068_alpha_dummy_414) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_414, fv_syn_c1c] using (nb068_compact_fv_empty_0322)

theorem nb068_compact_fv_empty_0323 (f : Var) : (nb068_alpha_dummy_416 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1065 (f : Var) : (nb068_alpha_dummy_416 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_416, fv_syn_c1c] using (nb068_compact_fv_empty_0323 f)

theorem nb068_compact_fv_empty_0324 : (nb068_alpha_dummy_413) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1066 : (nb068_alpha_dummy_413) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_413, fv_syn_c1c] using (nb068_compact_fv_empty_0324)

theorem nb068_compact_fv_empty_0325 (f : Var) : (nb068_alpha_dummy_415 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1067 (f : Var) : (nb068_alpha_dummy_415 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_415, fv_syn_c1c] using (nb068_compact_fv_empty_0325 f)

theorem nb068_compact_fv_empty_0326 : (nb068_alpha_dummy_419) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1068 : (nb068_alpha_dummy_419) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_419, fv_syn_c1c] using (nb068_compact_fv_empty_0326)

theorem nb068_compact_fv_empty_0327 (f : Var) : (nb068_alpha_dummy_420 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1069 (f : Var) : (nb068_alpha_dummy_420 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_420, fv_syn_c1c] using (nb068_compact_fv_empty_0327 f)

theorem nb068_compact_fv_empty_0328 : (nb068_alpha_dummy_417) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1070 : (nb068_alpha_dummy_417) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_417, fv_syn_c1c] using (nb068_compact_fv_empty_0328)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
