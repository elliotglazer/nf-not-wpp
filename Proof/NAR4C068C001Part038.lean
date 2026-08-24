import NAR4C068C001Part037

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

noncomputable def nb068_split_alpha_0092 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb068_alpha_dummy_343), (nb068_alpha_dummy_345 f)), ((nb068_alpha_dummy_344), (nb068_alpha_dummy_346 f)), ((nb068_alpha_dummy_369), (nb068_alpha_dummy_370 f)), ((nb068_alpha_dummy_367), (nb068_alpha_dummy_368 f)), ((nb068_alpha_dummy_336), (nb068_alpha_dummy_338 f)), ((nb068_alpha_dummy_335), (nb068_alpha_dummy_337 f)), ((nb068_alpha_dummy_365), (nb068_alpha_dummy_366 f)), ((nb068_alpha_dummy_339), (nb068_alpha_dummy_340 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_343)) (Class.cv (nb068_alpha_dummy_336))) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_344)) (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_343)) (syn_cnnc)) (syn_cplc (Class.cv (nb068_alpha_dummy_343)) (syn_c1c)) (Class.cv (nb068_alpha_dummy_343)))))) (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_345 f)) (Class.cv (nb068_alpha_dummy_338 f))) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_346 f)) (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_345 f)) (syn_cnnc)) (syn_cplc (Class.cv (nb068_alpha_dummy_345 f)) (syn_c1c)) (Class.cv (nb068_alpha_dummy_345 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0350) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0351 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0350) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0351 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0380) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0381 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0378) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0379 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_336))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_338 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0354) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0355 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0354) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0355 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0352) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0353 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_351), (nb068_alpha_dummy_354 f)), ((nb068_alpha_dummy_350), (nb068_alpha_dummy_353 f)), ((nb068_alpha_dummy_349), (nb068_alpha_dummy_352 f)), ((nb068_alpha_dummy_347), (nb068_alpha_dummy_348 f)), ((nb068_alpha_dummy_343), (nb068_alpha_dummy_345 f)), ((nb068_alpha_dummy_344), (nb068_alpha_dummy_346 f)), ((nb068_alpha_dummy_369), (nb068_alpha_dummy_370 f)), ((nb068_alpha_dummy_367), (nb068_alpha_dummy_368 f)), ((nb068_alpha_dummy_336), (nb068_alpha_dummy_338 f)), ((nb068_alpha_dummy_335), (nb068_alpha_dummy_337 f)), ((nb068_alpha_dummy_365), (nb068_alpha_dummy_366 f)), ((nb068_alpha_dummy_339), (nb068_alpha_dummy_340 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_c1c) (nb068_wpp_refl_0119 x y f))) (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0091 x y f)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0352) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0353 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_347), (nb068_alpha_dummy_348 f)), ((nb068_alpha_dummy_343), (nb068_alpha_dummy_345 f)), ((nb068_alpha_dummy_344), (nb068_alpha_dummy_346 f)), ((nb068_alpha_dummy_369), (nb068_alpha_dummy_370 f)), ((nb068_alpha_dummy_367), (nb068_alpha_dummy_368 f)), ((nb068_alpha_dummy_336), (nb068_alpha_dummy_338 f)), ((nb068_alpha_dummy_335), (nb068_alpha_dummy_337 f)), ((nb068_alpha_dummy_365), (nb068_alpha_dummy_366 f)), ((nb068_alpha_dummy_339), (nb068_alpha_dummy_340 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_cnnc) (nb068_wpp_refl_0121 x y f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0352) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0353 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0352) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0353 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_347), (nb068_alpha_dummy_348 f)), ((nb068_alpha_dummy_343), (nb068_alpha_dummy_345 f)), ((nb068_alpha_dummy_344), (nb068_alpha_dummy_346 f)), ((nb068_alpha_dummy_369), (nb068_alpha_dummy_370 f)), ((nb068_alpha_dummy_367), (nb068_alpha_dummy_368 f)), ((nb068_alpha_dummy_336), (nb068_alpha_dummy_338 f)), ((nb068_alpha_dummy_335), (nb068_alpha_dummy_337 f)), ((nb068_alpha_dummy_365), (nb068_alpha_dummy_366 f)), ((nb068_alpha_dummy_339), (nb068_alpha_dummy_340 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_cnnc) (nb068_wpp_refl_0121 x y f))))))))))))

theorem nb068_wpp_notmem_0942 : (nb068_alpha_dummy_367) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_367, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0278)

theorem nb068_wpp_notmem_0943 (f : Var) : (nb068_alpha_dummy_368 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_368, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0279 f)

theorem nb068_wpp_notmem_0944 : (nb068_alpha_dummy_336) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_336, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0258)

theorem nb068_wpp_notmem_0945 (f : Var) : (nb068_alpha_dummy_338 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_338, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0259 f)

theorem nb068_wpp_notmem_0946 : (nb068_alpha_dummy_335) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_335, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0260)

theorem nb068_wpp_notmem_0947 (f : Var) : (nb068_alpha_dummy_337 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_337, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0261 f)

theorem nb068_wpp_notmem_0948 : (nb068_alpha_dummy_365) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_365, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0280)

theorem nb068_wpp_notmem_0949 (f : Var) : (nb068_alpha_dummy_366 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_366, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0281 f)

theorem nb068_wpp_notmem_0950 : (nb068_alpha_dummy_339) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_339, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0264)

theorem nb068_wpp_notmem_0951 (f : Var) : (nb068_alpha_dummy_340 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_340, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0265 f)

theorem nb068_wpp_notmem_0952 : (nb068_alpha_dummy_328) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_328, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0266)

theorem nb068_wpp_notmem_0953 (f : Var) : (nb068_alpha_dummy_331 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_331, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0267 f)

theorem nb068_wpp_notmem_0954 : (nb068_alpha_dummy_327) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_327, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0268)

theorem nb068_wpp_notmem_0955 (f : Var) : (nb068_alpha_dummy_330 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_330, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0269 f)

theorem nb068_wpp_notmem_0956 : (nb068_alpha_dummy_333) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_333, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0270)

theorem nb068_wpp_notmem_0957 (f : Var) : (nb068_alpha_dummy_334 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_334, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0271 f)

theorem nb068_wpp_notmem_0958 : (nb068_alpha_dummy_325) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_325, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0272)

theorem nb068_wpp_notmem_0959 (f : Var) : (nb068_alpha_dummy_326 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_326, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0273 f)

theorem nb068_wpp_notmem_0960 : (nb068_alpha_dummy_323) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_323, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0274)

theorem nb068_wpp_notmem_0961 (f : Var) : (nb068_alpha_dummy_324 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_324, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0275 f)

theorem nb068_compact_envfresh_0122 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_367), (nb068_alpha_dummy_368 f)), ((nb068_alpha_dummy_336), (nb068_alpha_dummy_338 f)), ((nb068_alpha_dummy_335), (nb068_alpha_dummy_337 f)), ((nb068_alpha_dummy_365), (nb068_alpha_dummy_366 f)), ((nb068_alpha_dummy_339), (nb068_alpha_dummy_340 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_367) (nb068_alpha_dummy_368 f) (nb068_wpp_notmem_0942) (nb068_wpp_notmem_0943 f) (TEnvFresh.consFresh (nb068_alpha_dummy_336) (nb068_alpha_dummy_338 f) (nb068_wpp_notmem_0944) (nb068_wpp_notmem_0945 f) (TEnvFresh.consFresh (nb068_alpha_dummy_335) (nb068_alpha_dummy_337 f) (nb068_wpp_notmem_0946) (nb068_wpp_notmem_0947 f) (TEnvFresh.consFresh (nb068_alpha_dummy_365) (nb068_alpha_dummy_366 f) (nb068_wpp_notmem_0948) (nb068_wpp_notmem_0949 f) (TEnvFresh.consFresh (nb068_alpha_dummy_339) (nb068_alpha_dummy_340 f) (nb068_wpp_notmem_0950) (nb068_wpp_notmem_0951 f) (TEnvFresh.consFresh (nb068_alpha_dummy_328) (nb068_alpha_dummy_331 f) (nb068_wpp_notmem_0952) (nb068_wpp_notmem_0953 f) (TEnvFresh.consFresh (nb068_alpha_dummy_327) (nb068_alpha_dummy_330 f) (nb068_wpp_notmem_0954) (nb068_wpp_notmem_0955 f) (TEnvFresh.consFresh (nb068_alpha_dummy_333) (nb068_alpha_dummy_334 f) (nb068_wpp_notmem_0956) (nb068_wpp_notmem_0957 f) (TEnvFresh.consFresh (nb068_alpha_dummy_325) (nb068_alpha_dummy_326 f) (nb068_wpp_notmem_0958) (nb068_wpp_notmem_0959 f) (TEnvFresh.consFresh (nb068_alpha_dummy_323) (nb068_alpha_dummy_324 f) (nb068_wpp_notmem_0960) (nb068_wpp_notmem_0961 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0234) (nb068_wpp_notmem_0235 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0100) (nb068_wpp_notmem_0101 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0102) (nb068_wpp_notmem_0103 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0104) (nb068_wpp_notmem_0105 x y f) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))))))))

noncomputable def nb068_wpp_refl_0122 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_367), (nb068_alpha_dummy_368 f)), ((nb068_alpha_dummy_336), (nb068_alpha_dummy_338 f)), ((nb068_alpha_dummy_335), (nb068_alpha_dummy_337 f)), ((nb068_alpha_dummy_365), (nb068_alpha_dummy_366 f)), ((nb068_alpha_dummy_339), (nb068_alpha_dummy_340 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0122 x y f)

noncomputable def nb068_split_alpha_0093 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb068_alpha_dummy_365), (nb068_alpha_dummy_366 f)), ((nb068_alpha_dummy_339), (nb068_alpha_dummy_340 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_365)) (Class.cab (nb068_alpha_dummy_335) (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_328)) (Wff.classEq (Class.cv (nb068_alpha_dummy_335)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_336))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_365)) (Class.cab (nb068_alpha_dummy_335) (syn_wrex (nb068_alpha_dummy_336) (Class.cv (nb068_alpha_dummy_328)) (Wff.classEq (Class.cv (nb068_alpha_dummy_335)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_336))) (syn_csn (syn_c0c))))))))) (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_366 f)) (Class.cab (nb068_alpha_dummy_337 f) (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_331 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_338 f))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_366 f)) (Class.cab (nb068_alpha_dummy_337 f) (syn_wrex (nb068_alpha_dummy_338 f) (Class.cv (nb068_alpha_dummy_331 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_337 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_338 f))) (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0372) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0374 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0372) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0374 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0376) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0377 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0373) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0375 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_328))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_331 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0092 x y f))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0092 x y f))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_367), (nb068_alpha_dummy_368 f)), ((nb068_alpha_dummy_336), (nb068_alpha_dummy_338 f)), ((nb068_alpha_dummy_335), (nb068_alpha_dummy_337 f)), ((nb068_alpha_dummy_365), (nb068_alpha_dummy_366 f)), ((nb068_alpha_dummy_339), (nb068_alpha_dummy_340 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_ccompl (syn_csn (syn_c0c))) (nb068_wpp_refl_0122 x y f))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0372) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0374 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0372) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0374 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0376) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0377 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0373) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0375 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_327))).fv ∪ ((Class.cv (nb068_alpha_dummy_328))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_330 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_331 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0092 x y f))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0092 x y f))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_367), (nb068_alpha_dummy_368 f)), ((nb068_alpha_dummy_336), (nb068_alpha_dummy_338 f)), ((nb068_alpha_dummy_335), (nb068_alpha_dummy_337 f)), ((nb068_alpha_dummy_365), (nb068_alpha_dummy_366 f)), ((nb068_alpha_dummy_339), (nb068_alpha_dummy_340 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_ccompl (syn_csn (syn_c0c))) (nb068_wpp_refl_0122 x y f)))))))))))))))))))

theorem nb068_compact_fv_empty_0282 : (nb068_alpha_dummy_387) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0962 : (nb068_alpha_dummy_387) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_387, fv_syn_c1c] using (nb068_compact_fv_empty_0282)

theorem nb068_compact_fv_empty_0283 (f : Var) : (nb068_alpha_dummy_390 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0963 (f : Var) : (nb068_alpha_dummy_390 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_390, fv_syn_c1c] using (nb068_compact_fv_empty_0283 f)

theorem nb068_compact_fv_empty_0284 : (nb068_alpha_dummy_386) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0964 : (nb068_alpha_dummy_386) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_386, fv_syn_c1c] using (nb068_compact_fv_empty_0284)

theorem nb068_compact_fv_empty_0285 (f : Var) : (nb068_alpha_dummy_389 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0965 (f : Var) : (nb068_alpha_dummy_389 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_389, fv_syn_c1c] using (nb068_compact_fv_empty_0285 f)

theorem nb068_compact_fv_empty_0286 : (nb068_alpha_dummy_385) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0966 : (nb068_alpha_dummy_385) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_385, fv_syn_c1c] using (nb068_compact_fv_empty_0286)

theorem nb068_compact_fv_empty_0287 (f : Var) : (nb068_alpha_dummy_388 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0967 (f : Var) : (nb068_alpha_dummy_388 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_388, fv_syn_c1c] using (nb068_compact_fv_empty_0287 f)

theorem nb068_compact_fv_empty_0288 : (nb068_alpha_dummy_383) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0968 : (nb068_alpha_dummy_383) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_383, fv_syn_c1c] using (nb068_compact_fv_empty_0288)

theorem nb068_compact_fv_empty_0289 (f : Var) : (nb068_alpha_dummy_384 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0969 (f : Var) : (nb068_alpha_dummy_384 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_384, fv_syn_c1c] using (nb068_compact_fv_empty_0289 f)

theorem nb068_compact_fv_empty_0290 : (nb068_alpha_dummy_379) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0970 : (nb068_alpha_dummy_379) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_379, fv_syn_c1c] using (nb068_compact_fv_empty_0290)

theorem nb068_compact_fv_empty_0291 (f : Var) : (nb068_alpha_dummy_381 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0971 (f : Var) : (nb068_alpha_dummy_381 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_381, fv_syn_c1c] using (nb068_compact_fv_empty_0291 f)

theorem nb068_compact_fv_empty_0292 : (nb068_alpha_dummy_380) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0972 : (nb068_alpha_dummy_380) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_380, fv_syn_c1c] using (nb068_compact_fv_empty_0292)

theorem nb068_compact_fv_empty_0293 (f : Var) : (nb068_alpha_dummy_382 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0973 (f : Var) : (nb068_alpha_dummy_382 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_382, fv_syn_c1c] using (nb068_compact_fv_empty_0293 f)

theorem nb068_compact_fv_empty_0294 : (nb068_alpha_dummy_372) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0974 : (nb068_alpha_dummy_372) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_372, fv_syn_c1c] using (nb068_compact_fv_empty_0294)

theorem nb068_compact_fv_empty_0295 (f : Var) : (nb068_alpha_dummy_374 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0975 (f : Var) : (nb068_alpha_dummy_374 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_374, fv_syn_c1c] using (nb068_compact_fv_empty_0295 f)

theorem nb068_compact_fv_empty_0296 : (nb068_alpha_dummy_371) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0976 : (nb068_alpha_dummy_371) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_371, fv_syn_c1c] using (nb068_compact_fv_empty_0296)

theorem nb068_compact_fv_empty_0297 (f : Var) : (nb068_alpha_dummy_373 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0977 (f : Var) : (nb068_alpha_dummy_373 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_373, fv_syn_c1c] using (nb068_compact_fv_empty_0297 f)

theorem nb068_compact_fv_empty_0298 : (nb068_alpha_dummy_377) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0978 : (nb068_alpha_dummy_377) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_377, fv_syn_c1c] using (nb068_compact_fv_empty_0298)

theorem nb068_compact_fv_empty_0299 (f : Var) : (nb068_alpha_dummy_378 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0979 (f : Var) : (nb068_alpha_dummy_378 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_378, fv_syn_c1c] using (nb068_compact_fv_empty_0299 f)

theorem nb068_compact_fv_empty_0300 : (nb068_alpha_dummy_375) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0980 : (nb068_alpha_dummy_375) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_375, fv_syn_c1c] using (nb068_compact_fv_empty_0300)

theorem nb068_compact_fv_empty_0301 (f : Var) : (nb068_alpha_dummy_376 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0981 (f : Var) : (nb068_alpha_dummy_376 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_376, fv_syn_c1c] using (nb068_compact_fv_empty_0301 f)

theorem nb068_compact_fv_empty_0302 : (nb068_alpha_dummy_329) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0982 : (nb068_alpha_dummy_329) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_329, fv_syn_c1c] using (nb068_compact_fv_empty_0302)

theorem nb068_compact_fv_empty_0303 (f : Var) : (nb068_alpha_dummy_332 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0983 (f : Var) : (nb068_alpha_dummy_332 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_332, fv_syn_c1c] using (nb068_compact_fv_empty_0303 f)

theorem nb068_compact_envfresh_0123 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_387), (nb068_alpha_dummy_390 f)), ((nb068_alpha_dummy_386), (nb068_alpha_dummy_389 f)), ((nb068_alpha_dummy_385), (nb068_alpha_dummy_388 f)), ((nb068_alpha_dummy_383), (nb068_alpha_dummy_384 f)), ((nb068_alpha_dummy_379), (nb068_alpha_dummy_381 f)), ((nb068_alpha_dummy_380), (nb068_alpha_dummy_382 f)), ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)), ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)), ((nb068_alpha_dummy_377), (nb068_alpha_dummy_378 f)), ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_387) (nb068_alpha_dummy_390 f) (nb068_wpp_notmem_0962) (nb068_wpp_notmem_0963 f) (TEnvFresh.consFresh (nb068_alpha_dummy_386) (nb068_alpha_dummy_389 f) (nb068_wpp_notmem_0964) (nb068_wpp_notmem_0965 f) (TEnvFresh.consFresh (nb068_alpha_dummy_385) (nb068_alpha_dummy_388 f) (nb068_wpp_notmem_0966) (nb068_wpp_notmem_0967 f) (TEnvFresh.consFresh (nb068_alpha_dummy_383) (nb068_alpha_dummy_384 f) (nb068_wpp_notmem_0968) (nb068_wpp_notmem_0969 f) (TEnvFresh.consFresh (nb068_alpha_dummy_379) (nb068_alpha_dummy_381 f) (nb068_wpp_notmem_0970) (nb068_wpp_notmem_0971 f) (TEnvFresh.consFresh (nb068_alpha_dummy_380) (nb068_alpha_dummy_382 f) (nb068_wpp_notmem_0972) (nb068_wpp_notmem_0973 f) (TEnvFresh.consFresh (nb068_alpha_dummy_372) (nb068_alpha_dummy_374 f) (nb068_wpp_notmem_0974) (nb068_wpp_notmem_0975 f) (TEnvFresh.consFresh (nb068_alpha_dummy_371) (nb068_alpha_dummy_373 f) (nb068_wpp_notmem_0976) (nb068_wpp_notmem_0977 f) (TEnvFresh.consFresh (nb068_alpha_dummy_377) (nb068_alpha_dummy_378 f) (nb068_wpp_notmem_0978) (nb068_wpp_notmem_0979 f) (TEnvFresh.consFresh (nb068_alpha_dummy_375) (nb068_alpha_dummy_376 f) (nb068_wpp_notmem_0980) (nb068_wpp_notmem_0981 f) (TEnvFresh.consFresh (nb068_alpha_dummy_329) (nb068_alpha_dummy_332 f) (nb068_wpp_notmem_0982) (nb068_wpp_notmem_0983 f) (TEnvFresh.consFresh (nb068_alpha_dummy_328) (nb068_alpha_dummy_331 f) (nb068_wpp_notmem_0860) (nb068_wpp_notmem_0861 f) (TEnvFresh.consFresh (nb068_alpha_dummy_327) (nb068_alpha_dummy_330 f) (nb068_wpp_notmem_0862) (nb068_wpp_notmem_0863 f) (TEnvFresh.consFresh (nb068_alpha_dummy_333) (nb068_alpha_dummy_334 f) (nb068_wpp_notmem_0864) (nb068_wpp_notmem_0865 f) (TEnvFresh.consFresh (nb068_alpha_dummy_325) (nb068_alpha_dummy_326 f) (nb068_wpp_notmem_0866) (nb068_wpp_notmem_0867 f) (TEnvFresh.consFresh (nb068_alpha_dummy_323) (nb068_alpha_dummy_324 f) (nb068_wpp_notmem_0868) (nb068_wpp_notmem_0869 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0136) (nb068_wpp_notmem_0137 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0020) (nb068_wpp_notmem_0021 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0022) (nb068_wpp_notmem_0023 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0024) (nb068_wpp_notmem_0025 x y f) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))))

noncomputable def nb068_wpp_refl_0123 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_387), (nb068_alpha_dummy_390 f)), ((nb068_alpha_dummy_386), (nb068_alpha_dummy_389 f)), ((nb068_alpha_dummy_385), (nb068_alpha_dummy_388 f)), ((nb068_alpha_dummy_383), (nb068_alpha_dummy_384 f)), ((nb068_alpha_dummy_379), (nb068_alpha_dummy_381 f)), ((nb068_alpha_dummy_380), (nb068_alpha_dummy_382 f)), ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)), ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)), ((nb068_alpha_dummy_377), (nb068_alpha_dummy_378 f)), ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0123 x y f)

theorem nb068_wpp_notmem_0984 : (nb068_alpha_dummy_387) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_387, fv_syn_c0] using (nb068_compact_fv_empty_0282)

theorem nb068_wpp_notmem_0985 (f : Var) : (nb068_alpha_dummy_390 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_390, fv_syn_c0] using (nb068_compact_fv_empty_0283 f)

theorem nb068_wpp_notmem_0986 : (nb068_alpha_dummy_386) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_386, fv_syn_c0] using (nb068_compact_fv_empty_0284)

theorem nb068_wpp_notmem_0987 (f : Var) : (nb068_alpha_dummy_389 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_389, fv_syn_c0] using (nb068_compact_fv_empty_0285 f)

theorem nb068_wpp_notmem_0988 : (nb068_alpha_dummy_385) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_385, fv_syn_c0] using (nb068_compact_fv_empty_0286)

theorem nb068_wpp_notmem_0989 (f : Var) : (nb068_alpha_dummy_388 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_388, fv_syn_c0] using (nb068_compact_fv_empty_0287 f)

theorem nb068_wpp_notmem_0990 : (nb068_alpha_dummy_383) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_383, fv_syn_c0] using (nb068_compact_fv_empty_0288)

theorem nb068_wpp_notmem_0991 (f : Var) : (nb068_alpha_dummy_384 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_384, fv_syn_c0] using (nb068_compact_fv_empty_0289 f)

theorem nb068_wpp_notmem_0992 : (nb068_alpha_dummy_379) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_379, fv_syn_c0] using (nb068_compact_fv_empty_0290)

theorem nb068_wpp_notmem_0993 (f : Var) : (nb068_alpha_dummy_381 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_381, fv_syn_c0] using (nb068_compact_fv_empty_0291 f)

theorem nb068_wpp_notmem_0994 : (nb068_alpha_dummy_380) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_380, fv_syn_c0] using (nb068_compact_fv_empty_0292)

theorem nb068_wpp_notmem_0995 (f : Var) : (nb068_alpha_dummy_382 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_382, fv_syn_c0] using (nb068_compact_fv_empty_0293 f)

theorem nb068_wpp_notmem_0996 : (nb068_alpha_dummy_372) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_372, fv_syn_c0] using (nb068_compact_fv_empty_0294)

theorem nb068_wpp_notmem_0997 (f : Var) : (nb068_alpha_dummy_374 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_374, fv_syn_c0] using (nb068_compact_fv_empty_0295 f)

theorem nb068_wpp_notmem_0998 : (nb068_alpha_dummy_371) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_371, fv_syn_c0] using (nb068_compact_fv_empty_0296)

theorem nb068_wpp_notmem_0999 (f : Var) : (nb068_alpha_dummy_373 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_373, fv_syn_c0] using (nb068_compact_fv_empty_0297 f)

theorem nb068_wpp_notmem_1000 : (nb068_alpha_dummy_377) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_377, fv_syn_c0] using (nb068_compact_fv_empty_0298)

theorem nb068_wpp_notmem_1001 (f : Var) : (nb068_alpha_dummy_378 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_378, fv_syn_c0] using (nb068_compact_fv_empty_0299 f)

theorem nb068_wpp_notmem_1002 : (nb068_alpha_dummy_375) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_375, fv_syn_c0] using (nb068_compact_fv_empty_0300)

theorem nb068_wpp_notmem_1003 (f : Var) : (nb068_alpha_dummy_376 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_376, fv_syn_c0] using (nb068_compact_fv_empty_0301 f)

theorem nb068_wpp_notmem_1004 : (nb068_alpha_dummy_329) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_329, fv_syn_c0] using (nb068_compact_fv_empty_0302)

theorem nb068_wpp_notmem_1005 (f : Var) : (nb068_alpha_dummy_332 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_332, fv_syn_c0] using (nb068_compact_fv_empty_0303 f)

theorem nb068_compact_envfresh_0124 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_387), (nb068_alpha_dummy_390 f)), ((nb068_alpha_dummy_386), (nb068_alpha_dummy_389 f)), ((nb068_alpha_dummy_385), (nb068_alpha_dummy_388 f)), ((nb068_alpha_dummy_383), (nb068_alpha_dummy_384 f)), ((nb068_alpha_dummy_379), (nb068_alpha_dummy_381 f)), ((nb068_alpha_dummy_380), (nb068_alpha_dummy_382 f)), ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)), ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)), ((nb068_alpha_dummy_377), (nb068_alpha_dummy_378 f)), ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_387) (nb068_alpha_dummy_390 f) (nb068_wpp_notmem_0984) (nb068_wpp_notmem_0985 f) (TEnvFresh.consFresh (nb068_alpha_dummy_386) (nb068_alpha_dummy_389 f) (nb068_wpp_notmem_0986) (nb068_wpp_notmem_0987 f) (TEnvFresh.consFresh (nb068_alpha_dummy_385) (nb068_alpha_dummy_388 f) (nb068_wpp_notmem_0988) (nb068_wpp_notmem_0989 f) (TEnvFresh.consFresh (nb068_alpha_dummy_383) (nb068_alpha_dummy_384 f) (nb068_wpp_notmem_0990) (nb068_wpp_notmem_0991 f) (TEnvFresh.consFresh (nb068_alpha_dummy_379) (nb068_alpha_dummy_381 f) (nb068_wpp_notmem_0992) (nb068_wpp_notmem_0993 f) (TEnvFresh.consFresh (nb068_alpha_dummy_380) (nb068_alpha_dummy_382 f) (nb068_wpp_notmem_0994) (nb068_wpp_notmem_0995 f) (TEnvFresh.consFresh (nb068_alpha_dummy_372) (nb068_alpha_dummy_374 f) (nb068_wpp_notmem_0996) (nb068_wpp_notmem_0997 f) (TEnvFresh.consFresh (nb068_alpha_dummy_371) (nb068_alpha_dummy_373 f) (nb068_wpp_notmem_0998) (nb068_wpp_notmem_0999 f) (TEnvFresh.consFresh (nb068_alpha_dummy_377) (nb068_alpha_dummy_378 f) (nb068_wpp_notmem_1000) (nb068_wpp_notmem_1001 f) (TEnvFresh.consFresh (nb068_alpha_dummy_375) (nb068_alpha_dummy_376 f) (nb068_wpp_notmem_1002) (nb068_wpp_notmem_1003 f) (TEnvFresh.consFresh (nb068_alpha_dummy_329) (nb068_alpha_dummy_332 f) (nb068_wpp_notmem_1004) (nb068_wpp_notmem_1005 f) (TEnvFresh.consFresh (nb068_alpha_dummy_328) (nb068_alpha_dummy_331 f) (nb068_wpp_notmem_0890) (nb068_wpp_notmem_0891 f) (TEnvFresh.consFresh (nb068_alpha_dummy_327) (nb068_alpha_dummy_330 f) (nb068_wpp_notmem_0892) (nb068_wpp_notmem_0893 f) (TEnvFresh.consFresh (nb068_alpha_dummy_333) (nb068_alpha_dummy_334 f) (nb068_wpp_notmem_0894) (nb068_wpp_notmem_0895 f) (TEnvFresh.consFresh (nb068_alpha_dummy_325) (nb068_alpha_dummy_326 f) (nb068_wpp_notmem_0896) (nb068_wpp_notmem_0897 f) (TEnvFresh.consFresh (nb068_alpha_dummy_323) (nb068_alpha_dummy_324 f) (nb068_wpp_notmem_0898) (nb068_wpp_notmem_0899 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0168) (nb068_wpp_notmem_0169 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0046) (nb068_wpp_notmem_0047 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0048) (nb068_wpp_notmem_0049 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0050) (nb068_wpp_notmem_0051 x y f) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))))

noncomputable def nb068_wpp_refl_0124 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_387), (nb068_alpha_dummy_390 f)), ((nb068_alpha_dummy_386), (nb068_alpha_dummy_389 f)), ((nb068_alpha_dummy_385), (nb068_alpha_dummy_388 f)), ((nb068_alpha_dummy_383), (nb068_alpha_dummy_384 f)), ((nb068_alpha_dummy_379), (nb068_alpha_dummy_381 f)), ((nb068_alpha_dummy_380), (nb068_alpha_dummy_382 f)), ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)), ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)), ((nb068_alpha_dummy_377), (nb068_alpha_dummy_378 f)), ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0124 x y f)

noncomputable def nb068_split_alpha_0094 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb068_alpha_dummy_387), (nb068_alpha_dummy_390 f)), ((nb068_alpha_dummy_386), (nb068_alpha_dummy_389 f)), ((nb068_alpha_dummy_385), (nb068_alpha_dummy_388 f)), ((nb068_alpha_dummy_383), (nb068_alpha_dummy_384 f)), ((nb068_alpha_dummy_379), (nb068_alpha_dummy_381 f)), ((nb068_alpha_dummy_380), (nb068_alpha_dummy_382 f)), ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)), ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)), ((nb068_alpha_dummy_377), (nb068_alpha_dummy_378 f)), ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_386)) (Class.cv (nb068_alpha_dummy_387))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_385)) (syn_cun (Class.cv (nb068_alpha_dummy_386)) (Class.cv (nb068_alpha_dummy_387)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_389 f)) (Class.cv (nb068_alpha_dummy_390 f))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_388 f)) (syn_cun (Class.cv (nb068_alpha_dummy_389 f)) (Class.cv (nb068_alpha_dummy_390 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0396) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0397 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0394) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0395 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0400) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0401 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0398) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0399 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0396) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0397 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0394) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0395 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0400) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0401 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0398) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0399 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_387), (nb068_alpha_dummy_390 f)), ((nb068_alpha_dummy_386), (nb068_alpha_dummy_389 f)), ((nb068_alpha_dummy_385), (nb068_alpha_dummy_388 f)), ((nb068_alpha_dummy_383), (nb068_alpha_dummy_384 f)), ((nb068_alpha_dummy_379), (nb068_alpha_dummy_381 f)), ((nb068_alpha_dummy_380), (nb068_alpha_dummy_382 f)), ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)), ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)), ((nb068_alpha_dummy_377), (nb068_alpha_dummy_378 f)), ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_c0) (nb068_wpp_refl_0124 x y f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0404) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0405 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0402) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0403 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0404) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0405 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0402) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0403 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_379))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_381 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0408) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0409 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0406) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0407 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0408) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0409 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0406) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0407 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb068_wpp_notmem_1006 : (nb068_alpha_dummy_383) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_383, fv_syn_cnnc] using (nb068_compact_fv_empty_0288)

theorem nb068_wpp_notmem_1007 (f : Var) : (nb068_alpha_dummy_384 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_384, fv_syn_cnnc] using (nb068_compact_fv_empty_0289 f)

theorem nb068_wpp_notmem_1008 : (nb068_alpha_dummy_379) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_379, fv_syn_cnnc] using (nb068_compact_fv_empty_0290)

theorem nb068_wpp_notmem_1009 (f : Var) : (nb068_alpha_dummy_381 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_381, fv_syn_cnnc] using (nb068_compact_fv_empty_0291 f)

theorem nb068_wpp_notmem_1010 : (nb068_alpha_dummy_380) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_380, fv_syn_cnnc] using (nb068_compact_fv_empty_0292)

theorem nb068_wpp_notmem_1011 (f : Var) : (nb068_alpha_dummy_382 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_382, fv_syn_cnnc] using (nb068_compact_fv_empty_0293 f)

theorem nb068_wpp_notmem_1012 : (nb068_alpha_dummy_372) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_372, fv_syn_cnnc] using (nb068_compact_fv_empty_0294)

theorem nb068_wpp_notmem_1013 (f : Var) : (nb068_alpha_dummy_374 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_374, fv_syn_cnnc] using (nb068_compact_fv_empty_0295 f)

theorem nb068_wpp_notmem_1014 : (nb068_alpha_dummy_371) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_371, fv_syn_cnnc] using (nb068_compact_fv_empty_0296)

theorem nb068_wpp_notmem_1015 (f : Var) : (nb068_alpha_dummy_373 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_373, fv_syn_cnnc] using (nb068_compact_fv_empty_0297 f)

theorem nb068_wpp_notmem_1016 : (nb068_alpha_dummy_377) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_377, fv_syn_cnnc] using (nb068_compact_fv_empty_0298)

theorem nb068_wpp_notmem_1017 (f : Var) : (nb068_alpha_dummy_378 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_378, fv_syn_cnnc] using (nb068_compact_fv_empty_0299 f)

theorem nb068_wpp_notmem_1018 : (nb068_alpha_dummy_375) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_375, fv_syn_cnnc] using (nb068_compact_fv_empty_0300)

theorem nb068_wpp_notmem_1019 (f : Var) : (nb068_alpha_dummy_376 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_376, fv_syn_cnnc] using (nb068_compact_fv_empty_0301 f)

theorem nb068_wpp_notmem_1020 : (nb068_alpha_dummy_329) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_329, fv_syn_cnnc] using (nb068_compact_fv_empty_0302)

theorem nb068_wpp_notmem_1021 (f : Var) : (nb068_alpha_dummy_332 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_332, fv_syn_cnnc] using (nb068_compact_fv_empty_0303 f)

theorem nb068_compact_envfresh_0125 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_383), (nb068_alpha_dummy_384 f)), ((nb068_alpha_dummy_379), (nb068_alpha_dummy_381 f)), ((nb068_alpha_dummy_380), (nb068_alpha_dummy_382 f)), ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)), ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)), ((nb068_alpha_dummy_377), (nb068_alpha_dummy_378 f)), ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_383) (nb068_alpha_dummy_384 f) (nb068_wpp_notmem_1006) (nb068_wpp_notmem_1007 f) (TEnvFresh.consFresh (nb068_alpha_dummy_379) (nb068_alpha_dummy_381 f) (nb068_wpp_notmem_1008) (nb068_wpp_notmem_1009 f) (TEnvFresh.consFresh (nb068_alpha_dummy_380) (nb068_alpha_dummy_382 f) (nb068_wpp_notmem_1010) (nb068_wpp_notmem_1011 f) (TEnvFresh.consFresh (nb068_alpha_dummy_372) (nb068_alpha_dummy_374 f) (nb068_wpp_notmem_1012) (nb068_wpp_notmem_1013 f) (TEnvFresh.consFresh (nb068_alpha_dummy_371) (nb068_alpha_dummy_373 f) (nb068_wpp_notmem_1014) (nb068_wpp_notmem_1015 f) (TEnvFresh.consFresh (nb068_alpha_dummy_377) (nb068_alpha_dummy_378 f) (nb068_wpp_notmem_1016) (nb068_wpp_notmem_1017 f) (TEnvFresh.consFresh (nb068_alpha_dummy_375) (nb068_alpha_dummy_376 f) (nb068_wpp_notmem_1018) (nb068_wpp_notmem_1019 f) (TEnvFresh.consFresh (nb068_alpha_dummy_329) (nb068_alpha_dummy_332 f) (nb068_wpp_notmem_1020) (nb068_wpp_notmem_1021 f) (TEnvFresh.consFresh (nb068_alpha_dummy_328) (nb068_alpha_dummy_331 f) (nb068_wpp_notmem_0914) (nb068_wpp_notmem_0915 f) (TEnvFresh.consFresh (nb068_alpha_dummy_327) (nb068_alpha_dummy_330 f) (nb068_wpp_notmem_0916) (nb068_wpp_notmem_0917 f) (TEnvFresh.consFresh (nb068_alpha_dummy_333) (nb068_alpha_dummy_334 f) (nb068_wpp_notmem_0918) (nb068_wpp_notmem_0919 f) (TEnvFresh.consFresh (nb068_alpha_dummy_325) (nb068_alpha_dummy_326 f) (nb068_wpp_notmem_0920) (nb068_wpp_notmem_0921 f) (TEnvFresh.consFresh (nb068_alpha_dummy_323) (nb068_alpha_dummy_324 f) (nb068_wpp_notmem_0922) (nb068_wpp_notmem_0923 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0194) (nb068_wpp_notmem_0195 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0066) (nb068_wpp_notmem_0067 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0068) (nb068_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0070) (nb068_wpp_notmem_0071 x y f) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))))

noncomputable def nb068_wpp_refl_0125 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_383), (nb068_alpha_dummy_384 f)), ((nb068_alpha_dummy_379), (nb068_alpha_dummy_381 f)), ((nb068_alpha_dummy_380), (nb068_alpha_dummy_382 f)), ((nb068_alpha_dummy_372), (nb068_alpha_dummy_374 f)), ((nb068_alpha_dummy_371), (nb068_alpha_dummy_373 f)), ((nb068_alpha_dummy_377), (nb068_alpha_dummy_378 f)), ((nb068_alpha_dummy_375), (nb068_alpha_dummy_376 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0125 x y f)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
