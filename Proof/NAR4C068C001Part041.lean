import NAR4C068C001Part040

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

noncomputable def nb068_split_alpha_0101 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb068_alpha_dummy_429), (nb068_alpha_dummy_432 f)), ((nb068_alpha_dummy_428), (nb068_alpha_dummy_431 f)), ((nb068_alpha_dummy_427), (nb068_alpha_dummy_430 f)), ((nb068_alpha_dummy_425), (nb068_alpha_dummy_426 f)), ((nb068_alpha_dummy_421), (nb068_alpha_dummy_423 f)), ((nb068_alpha_dummy_422), (nb068_alpha_dummy_424 f)), ((nb068_alpha_dummy_447), (nb068_alpha_dummy_448 f)), ((nb068_alpha_dummy_445), (nb068_alpha_dummy_446 f)), ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)), ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)), ((nb068_alpha_dummy_443), (nb068_alpha_dummy_444 f)), ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)), ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)), ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)), ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_428)) (Class.cv (nb068_alpha_dummy_429))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_427)) (syn_cun (Class.cv (nb068_alpha_dummy_428)) (Class.cv (nb068_alpha_dummy_429)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_431 f)) (Class.cv (nb068_alpha_dummy_432 f))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_430 f)) (syn_cun (Class.cv (nb068_alpha_dummy_431 f)) (Class.cv (nb068_alpha_dummy_432 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0438) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0439 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0436) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0437 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0442) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0443 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0440) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0441 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0438) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0439 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0436) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0437 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0442) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0443 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0440) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0441 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_429), (nb068_alpha_dummy_432 f)), ((nb068_alpha_dummy_428), (nb068_alpha_dummy_431 f)), ((nb068_alpha_dummy_427), (nb068_alpha_dummy_430 f)), ((nb068_alpha_dummy_425), (nb068_alpha_dummy_426 f)), ((nb068_alpha_dummy_421), (nb068_alpha_dummy_423 f)), ((nb068_alpha_dummy_422), (nb068_alpha_dummy_424 f)), ((nb068_alpha_dummy_447), (nb068_alpha_dummy_448 f)), ((nb068_alpha_dummy_445), (nb068_alpha_dummy_446 f)), ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)), ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)), ((nb068_alpha_dummy_443), (nb068_alpha_dummy_444 f)), ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)), ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)), ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)), ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_c0) (nb068_wpp_refl_0134 x y f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0446) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0447 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0444) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0445 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0446) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0447 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0444) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0445 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_421))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_423 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0450) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0451 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0448) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0449 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0450) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0451 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0448) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0449 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb068_wpp_notmem_1136 : (nb068_alpha_dummy_447) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_447, fv_syn_cnnc] using (nb068_compact_fv_empty_0336)

theorem nb068_wpp_notmem_1137 (f : Var) : (nb068_alpha_dummy_448 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_448, fv_syn_cnnc] using (nb068_compact_fv_empty_0337 f)

theorem nb068_wpp_notmem_1138 : (nb068_alpha_dummy_445) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_445, fv_syn_cnnc] using (nb068_compact_fv_empty_0338)

theorem nb068_wpp_notmem_1139 (f : Var) : (nb068_alpha_dummy_446 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_446, fv_syn_cnnc] using (nb068_compact_fv_empty_0339 f)

theorem nb068_wpp_notmem_1140 : (nb068_alpha_dummy_443) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_443, fv_syn_cnnc] using (nb068_compact_fv_empty_0340)

theorem nb068_wpp_notmem_1141 (f : Var) : (nb068_alpha_dummy_444 f) ∉ ((syn_cnnc)).fv := by
  simpa only [nb068_alpha_dummy_444, fv_syn_cnnc] using (nb068_compact_fv_empty_0341 f)

theorem nb068_compact_envfresh_0135 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_425), (nb068_alpha_dummy_426 f)), ((nb068_alpha_dummy_421), (nb068_alpha_dummy_423 f)), ((nb068_alpha_dummy_422), (nb068_alpha_dummy_424 f)), ((nb068_alpha_dummy_447), (nb068_alpha_dummy_448 f)), ((nb068_alpha_dummy_445), (nb068_alpha_dummy_446 f)), ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)), ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)), ((nb068_alpha_dummy_443), (nb068_alpha_dummy_444 f)), ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)), ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)), ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)), ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_425) (nb068_alpha_dummy_426 f) (nb068_wpp_notmem_1104) (nb068_wpp_notmem_1105 f) (TEnvFresh.consFresh (nb068_alpha_dummy_421) (nb068_alpha_dummy_423 f) (nb068_wpp_notmem_1106) (nb068_wpp_notmem_1107 f) (TEnvFresh.consFresh (nb068_alpha_dummy_422) (nb068_alpha_dummy_424 f) (nb068_wpp_notmem_1108) (nb068_wpp_notmem_1109 f) (TEnvFresh.consFresh (nb068_alpha_dummy_447) (nb068_alpha_dummy_448 f) (nb068_wpp_notmem_1136) (nb068_wpp_notmem_1137 f) (TEnvFresh.consFresh (nb068_alpha_dummy_445) (nb068_alpha_dummy_446 f) (nb068_wpp_notmem_1138) (nb068_wpp_notmem_1139 f) (TEnvFresh.consFresh (nb068_alpha_dummy_414) (nb068_alpha_dummy_416 f) (nb068_wpp_notmem_1110) (nb068_wpp_notmem_1111 f) (TEnvFresh.consFresh (nb068_alpha_dummy_413) (nb068_alpha_dummy_415 f) (nb068_wpp_notmem_1112) (nb068_wpp_notmem_1113 f) (TEnvFresh.consFresh (nb068_alpha_dummy_443) (nb068_alpha_dummy_444 f) (nb068_wpp_notmem_1140) (nb068_wpp_notmem_1141 f) (TEnvFresh.consFresh (nb068_alpha_dummy_417) (nb068_alpha_dummy_418 f) (nb068_wpp_notmem_1116) (nb068_wpp_notmem_1117 f) (TEnvFresh.consFresh (nb068_alpha_dummy_408) (nb068_alpha_dummy_410 f) (nb068_wpp_notmem_1118) (nb068_wpp_notmem_1119 f) (TEnvFresh.consFresh (nb068_alpha_dummy_407) (nb068_alpha_dummy_409 f) (nb068_wpp_notmem_1120) (nb068_wpp_notmem_1121 f) (TEnvFresh.consFresh (nb068_alpha_dummy_411) (nb068_alpha_dummy_412 f) (nb068_wpp_notmem_1122) (nb068_wpp_notmem_1123 f) (TEnvFresh.consFresh (nb068_alpha_dummy_329) (nb068_alpha_dummy_332 f) (nb068_wpp_notmem_1020) (nb068_wpp_notmem_1021 f) (TEnvFresh.consFresh (nb068_alpha_dummy_328) (nb068_alpha_dummy_331 f) (nb068_wpp_notmem_0914) (nb068_wpp_notmem_0915 f) (TEnvFresh.consFresh (nb068_alpha_dummy_327) (nb068_alpha_dummy_330 f) (nb068_wpp_notmem_0916) (nb068_wpp_notmem_0917 f) (TEnvFresh.consFresh (nb068_alpha_dummy_333) (nb068_alpha_dummy_334 f) (nb068_wpp_notmem_0918) (nb068_wpp_notmem_0919 f) (TEnvFresh.consFresh (nb068_alpha_dummy_325) (nb068_alpha_dummy_326 f) (nb068_wpp_notmem_0920) (nb068_wpp_notmem_0921 f) (TEnvFresh.consFresh (nb068_alpha_dummy_323) (nb068_alpha_dummy_324 f) (nb068_wpp_notmem_0922) (nb068_wpp_notmem_0923 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0194) (nb068_wpp_notmem_0195 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0066) (nb068_wpp_notmem_0067 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0068) (nb068_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0070) (nb068_wpp_notmem_0071 x y f) (TEnvFresh.nil ((syn_cnnc)).fv)))))))))))))))))))))))

noncomputable def nb068_wpp_refl_0135 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_425), (nb068_alpha_dummy_426 f)), ((nb068_alpha_dummy_421), (nb068_alpha_dummy_423 f)), ((nb068_alpha_dummy_422), (nb068_alpha_dummy_424 f)), ((nb068_alpha_dummy_447), (nb068_alpha_dummy_448 f)), ((nb068_alpha_dummy_445), (nb068_alpha_dummy_446 f)), ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)), ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)), ((nb068_alpha_dummy_443), (nb068_alpha_dummy_444 f)), ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)), ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)), ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)), ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0135 x y f)

noncomputable def nb068_split_alpha_0102 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb068_alpha_dummy_425), (nb068_alpha_dummy_426 f)), ((nb068_alpha_dummy_421), (nb068_alpha_dummy_423 f)), ((nb068_alpha_dummy_422), (nb068_alpha_dummy_424 f)), ((nb068_alpha_dummy_447), (nb068_alpha_dummy_448 f)), ((nb068_alpha_dummy_445), (nb068_alpha_dummy_446 f)), ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)), ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)), ((nb068_alpha_dummy_443), (nb068_alpha_dummy_444 f)), ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)), ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)), ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)), ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (Wff.imp (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb068_alpha_dummy_425)) (syn_cplc (Class.cv (nb068_alpha_dummy_421)) (syn_c1c))) (Wff.classMem (Class.cv (nb068_alpha_dummy_421)) (syn_cnnc)))) (syn_wa (Wff.classMem (Class.cv (nb068_alpha_dummy_425)) (Class.cv (nb068_alpha_dummy_421))) (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_421)) (syn_cnnc))))) (Wff.imp (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb068_alpha_dummy_426 f)) (syn_cplc (Class.cv (nb068_alpha_dummy_423 f)) (syn_c1c))) (Wff.classMem (Class.cv (nb068_alpha_dummy_423 f)) (syn_cnnc)))) (syn_wa (Wff.classMem (Class.cv (nb068_alpha_dummy_426 f)) (Class.cv (nb068_alpha_dummy_423 f))) (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_423 f)) (syn_cnnc))))) :=
  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0434) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0435 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0434) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0435 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0432) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0433 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_429), (nb068_alpha_dummy_432 f)), ((nb068_alpha_dummy_428), (nb068_alpha_dummy_431 f)), ((nb068_alpha_dummy_427), (nb068_alpha_dummy_430 f)), ((nb068_alpha_dummy_425), (nb068_alpha_dummy_426 f)), ((nb068_alpha_dummy_421), (nb068_alpha_dummy_423 f)), ((nb068_alpha_dummy_422), (nb068_alpha_dummy_424 f)), ((nb068_alpha_dummy_447), (nb068_alpha_dummy_448 f)), ((nb068_alpha_dummy_445), (nb068_alpha_dummy_446 f)), ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)), ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)), ((nb068_alpha_dummy_443), (nb068_alpha_dummy_444 f)), ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)), ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)), ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)), ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_c1c) (nb068_wpp_refl_0133 x y f))) (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0101 x y f)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0432) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0433 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_425), (nb068_alpha_dummy_426 f)), ((nb068_alpha_dummy_421), (nb068_alpha_dummy_423 f)), ((nb068_alpha_dummy_422), (nb068_alpha_dummy_424 f)), ((nb068_alpha_dummy_447), (nb068_alpha_dummy_448 f)), ((nb068_alpha_dummy_445), (nb068_alpha_dummy_446 f)), ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)), ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)), ((nb068_alpha_dummy_443), (nb068_alpha_dummy_444 f)), ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)), ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)), ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)), ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_cnnc) (nb068_wpp_refl_0135 x y f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0432) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0433 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0432) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0433 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_425), (nb068_alpha_dummy_426 f)), ((nb068_alpha_dummy_421), (nb068_alpha_dummy_423 f)), ((nb068_alpha_dummy_422), (nb068_alpha_dummy_424 f)), ((nb068_alpha_dummy_447), (nb068_alpha_dummy_448 f)), ((nb068_alpha_dummy_445), (nb068_alpha_dummy_446 f)), ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)), ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)), ((nb068_alpha_dummy_443), (nb068_alpha_dummy_444 f)), ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)), ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)), ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)), ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_cnnc) (nb068_wpp_refl_0135 x y f))))))))

theorem nb068_wpp_notmem_1142 : (nb068_alpha_dummy_445) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_445, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0338)

theorem nb068_wpp_notmem_1143 (f : Var) : (nb068_alpha_dummy_446 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_446, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0339 f)

theorem nb068_wpp_notmem_1144 : (nb068_alpha_dummy_414) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_414, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0322)

theorem nb068_wpp_notmem_1145 (f : Var) : (nb068_alpha_dummy_416 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_416, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0323 f)

theorem nb068_wpp_notmem_1146 : (nb068_alpha_dummy_413) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_413, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0324)

theorem nb068_wpp_notmem_1147 (f : Var) : (nb068_alpha_dummy_415 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_415, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0325 f)

theorem nb068_wpp_notmem_1148 : (nb068_alpha_dummy_443) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_443, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0340)

theorem nb068_wpp_notmem_1149 (f : Var) : (nb068_alpha_dummy_444 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_444, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0341 f)

theorem nb068_wpp_notmem_1150 : (nb068_alpha_dummy_417) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_417, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0328)

theorem nb068_wpp_notmem_1151 (f : Var) : (nb068_alpha_dummy_418 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_418, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0329 f)

theorem nb068_wpp_notmem_1152 : (nb068_alpha_dummy_408) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_408, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0330)

theorem nb068_wpp_notmem_1153 (f : Var) : (nb068_alpha_dummy_410 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_410, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0331 f)

theorem nb068_wpp_notmem_1154 : (nb068_alpha_dummy_407) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_407, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0332)

theorem nb068_wpp_notmem_1155 (f : Var) : (nb068_alpha_dummy_409 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_409, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0333 f)

theorem nb068_wpp_notmem_1156 : (nb068_alpha_dummy_411) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_411, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0334)

theorem nb068_wpp_notmem_1157 (f : Var) : (nb068_alpha_dummy_412 f) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb068_alpha_dummy_412, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb068_compact_fv_empty_0335 f)

theorem nb068_compact_envfresh_0136 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_445), (nb068_alpha_dummy_446 f)), ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)), ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)), ((nb068_alpha_dummy_443), (nb068_alpha_dummy_444 f)), ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)), ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)), ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)), ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_445) (nb068_alpha_dummy_446 f) (nb068_wpp_notmem_1142) (nb068_wpp_notmem_1143 f) (TEnvFresh.consFresh (nb068_alpha_dummy_414) (nb068_alpha_dummy_416 f) (nb068_wpp_notmem_1144) (nb068_wpp_notmem_1145 f) (TEnvFresh.consFresh (nb068_alpha_dummy_413) (nb068_alpha_dummy_415 f) (nb068_wpp_notmem_1146) (nb068_wpp_notmem_1147 f) (TEnvFresh.consFresh (nb068_alpha_dummy_443) (nb068_alpha_dummy_444 f) (nb068_wpp_notmem_1148) (nb068_wpp_notmem_1149 f) (TEnvFresh.consFresh (nb068_alpha_dummy_417) (nb068_alpha_dummy_418 f) (nb068_wpp_notmem_1150) (nb068_wpp_notmem_1151 f) (TEnvFresh.consFresh (nb068_alpha_dummy_408) (nb068_alpha_dummy_410 f) (nb068_wpp_notmem_1152) (nb068_wpp_notmem_1153 f) (TEnvFresh.consFresh (nb068_alpha_dummy_407) (nb068_alpha_dummy_409 f) (nb068_wpp_notmem_1154) (nb068_wpp_notmem_1155 f) (TEnvFresh.consFresh (nb068_alpha_dummy_411) (nb068_alpha_dummy_412 f) (nb068_wpp_notmem_1156) (nb068_wpp_notmem_1157 f) (TEnvFresh.consFresh (nb068_alpha_dummy_329) (nb068_alpha_dummy_332 f) (nb068_wpp_notmem_1050) (nb068_wpp_notmem_1051 f) (TEnvFresh.consFresh (nb068_alpha_dummy_328) (nb068_alpha_dummy_331 f) (nb068_wpp_notmem_0952) (nb068_wpp_notmem_0953 f) (TEnvFresh.consFresh (nb068_alpha_dummy_327) (nb068_alpha_dummy_330 f) (nb068_wpp_notmem_0954) (nb068_wpp_notmem_0955 f) (TEnvFresh.consFresh (nb068_alpha_dummy_333) (nb068_alpha_dummy_334 f) (nb068_wpp_notmem_0956) (nb068_wpp_notmem_0957 f) (TEnvFresh.consFresh (nb068_alpha_dummy_325) (nb068_alpha_dummy_326 f) (nb068_wpp_notmem_0958) (nb068_wpp_notmem_0959 f) (TEnvFresh.consFresh (nb068_alpha_dummy_323) (nb068_alpha_dummy_324 f) (nb068_wpp_notmem_0960) (nb068_wpp_notmem_0961 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0234) (nb068_wpp_notmem_0235 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0100) (nb068_wpp_notmem_0101 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0102) (nb068_wpp_notmem_0103 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0104) (nb068_wpp_notmem_0105 x y f) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv)))))))))))))))))))

noncomputable def nb068_wpp_refl_0136 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_445), (nb068_alpha_dummy_446 f)), ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)), ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)), ((nb068_alpha_dummy_443), (nb068_alpha_dummy_444 f)), ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)), ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)), ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)), ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0136 x y f)

noncomputable def nb068_split_alpha_0103 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb068_alpha_dummy_443), (nb068_alpha_dummy_444 f)), ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)), ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)), ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)), ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_443)) (Class.cab (nb068_alpha_dummy_413) (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_408)) (Wff.classEq (Class.cv (nb068_alpha_dummy_413)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_414))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_443)) (Class.cab (nb068_alpha_dummy_413) (syn_wrex (nb068_alpha_dummy_414) (Class.cv (nb068_alpha_dummy_408)) (Wff.classEq (Class.cv (nb068_alpha_dummy_413)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_414))) (syn_csn (syn_c0c))))))))) (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_444 f)) (Class.cab (nb068_alpha_dummy_415 f) (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_410 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_416 f))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_444 f)) (Class.cab (nb068_alpha_dummy_415 f) (syn_wrex (nb068_alpha_dummy_416 f) (Class.cv (nb068_alpha_dummy_410 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_415 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_416 f))) (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0452) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0454 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0452) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0454 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0456) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0457 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0453) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0455 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_407))).fv ∪ ((Class.cv (nb068_alpha_dummy_408))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_409 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_410 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0430) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0431 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0430) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0431 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0460) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0461 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0458) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0459 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_414))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_416 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb068_split_alpha_0102 x y f))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0430) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0431 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0430) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0431 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0460) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0461 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0458) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0459 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_414))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_416 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb068_split_alpha_0102 x y f))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_445), (nb068_alpha_dummy_446 f)), ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)), ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)), ((nb068_alpha_dummy_443), (nb068_alpha_dummy_444 f)), ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)), ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)), ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)), ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_ccompl (syn_csn (syn_c0c))) (nb068_wpp_refl_0136 x y f))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0452) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0454 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0452) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0454 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0456) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0457 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0453) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0455 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_407))).fv ∪ ((Class.cv (nb068_alpha_dummy_408))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_409 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_410 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0430) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0431 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0430) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0431 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0460) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0461 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0458) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0459 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_414))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_416 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb068_split_alpha_0102 x y f))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0430) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0431 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0430) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0431 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0460) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0461 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0458) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0459 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_414))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_416 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb068_split_alpha_0102 x y f))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_445), (nb068_alpha_dummy_446 f)), ((nb068_alpha_dummy_414), (nb068_alpha_dummy_416 f)), ((nb068_alpha_dummy_413), (nb068_alpha_dummy_415 f)), ((nb068_alpha_dummy_443), (nb068_alpha_dummy_444 f)), ((nb068_alpha_dummy_417), (nb068_alpha_dummy_418 f)), ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)), ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)), ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_ccompl (syn_csn (syn_c0c))) (nb068_wpp_refl_0136 x y f)))))))))))))))))))

theorem nb068_compact_fv_empty_0342 : (nb068_alpha_dummy_465) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1158 : (nb068_alpha_dummy_465) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_465, fv_syn_c1c] using (nb068_compact_fv_empty_0342)

theorem nb068_compact_fv_empty_0343 (f : Var) : (nb068_alpha_dummy_468 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1159 (f : Var) : (nb068_alpha_dummy_468 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_468, fv_syn_c1c] using (nb068_compact_fv_empty_0343 f)

theorem nb068_compact_fv_empty_0344 : (nb068_alpha_dummy_464) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1160 : (nb068_alpha_dummy_464) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_464, fv_syn_c1c] using (nb068_compact_fv_empty_0344)

theorem nb068_compact_fv_empty_0345 (f : Var) : (nb068_alpha_dummy_467 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1161 (f : Var) : (nb068_alpha_dummy_467 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_467, fv_syn_c1c] using (nb068_compact_fv_empty_0345 f)

theorem nb068_compact_fv_empty_0346 : (nb068_alpha_dummy_463) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1162 : (nb068_alpha_dummy_463) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_463, fv_syn_c1c] using (nb068_compact_fv_empty_0346)

theorem nb068_compact_fv_empty_0347 (f : Var) : (nb068_alpha_dummy_466 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1163 (f : Var) : (nb068_alpha_dummy_466 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_466, fv_syn_c1c] using (nb068_compact_fv_empty_0347 f)

theorem nb068_compact_fv_empty_0348 : (nb068_alpha_dummy_461) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1164 : (nb068_alpha_dummy_461) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_461, fv_syn_c1c] using (nb068_compact_fv_empty_0348)

theorem nb068_compact_fv_empty_0349 (f : Var) : (nb068_alpha_dummy_462 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1165 (f : Var) : (nb068_alpha_dummy_462 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_462, fv_syn_c1c] using (nb068_compact_fv_empty_0349 f)

theorem nb068_compact_fv_empty_0350 : (nb068_alpha_dummy_457) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1166 : (nb068_alpha_dummy_457) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_457, fv_syn_c1c] using (nb068_compact_fv_empty_0350)

theorem nb068_compact_fv_empty_0351 (f : Var) : (nb068_alpha_dummy_459 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1167 (f : Var) : (nb068_alpha_dummy_459 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_459, fv_syn_c1c] using (nb068_compact_fv_empty_0351 f)

theorem nb068_compact_fv_empty_0352 : (nb068_alpha_dummy_458) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1168 : (nb068_alpha_dummy_458) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_458, fv_syn_c1c] using (nb068_compact_fv_empty_0352)

theorem nb068_compact_fv_empty_0353 (f : Var) : (nb068_alpha_dummy_460 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1169 (f : Var) : (nb068_alpha_dummy_460 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_460, fv_syn_c1c] using (nb068_compact_fv_empty_0353 f)

theorem nb068_compact_fv_empty_0354 : (nb068_alpha_dummy_450) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1170 : (nb068_alpha_dummy_450) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_450, fv_syn_c1c] using (nb068_compact_fv_empty_0354)

theorem nb068_compact_fv_empty_0355 (f : Var) : (nb068_alpha_dummy_452 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1171 (f : Var) : (nb068_alpha_dummy_452 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_452, fv_syn_c1c] using (nb068_compact_fv_empty_0355 f)

theorem nb068_compact_fv_empty_0356 : (nb068_alpha_dummy_449) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1172 : (nb068_alpha_dummy_449) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_449, fv_syn_c1c] using (nb068_compact_fv_empty_0356)

theorem nb068_compact_fv_empty_0357 (f : Var) : (nb068_alpha_dummy_451 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1173 (f : Var) : (nb068_alpha_dummy_451 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_451, fv_syn_c1c] using (nb068_compact_fv_empty_0357 f)

theorem nb068_compact_fv_empty_0358 : (nb068_alpha_dummy_455) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1174 : (nb068_alpha_dummy_455) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_455, fv_syn_c1c] using (nb068_compact_fv_empty_0358)

theorem nb068_compact_fv_empty_0359 (f : Var) : (nb068_alpha_dummy_456 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1175 (f : Var) : (nb068_alpha_dummy_456 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_456, fv_syn_c1c] using (nb068_compact_fv_empty_0359 f)

theorem nb068_compact_fv_empty_0360 : (nb068_alpha_dummy_453) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1176 : (nb068_alpha_dummy_453) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_453, fv_syn_c1c] using (nb068_compact_fv_empty_0360)

theorem nb068_compact_fv_empty_0361 (f : Var) : (nb068_alpha_dummy_454 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_1177 (f : Var) : (nb068_alpha_dummy_454 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_454, fv_syn_c1c] using (nb068_compact_fv_empty_0361 f)

theorem nb068_compact_envfresh_0137 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_465), (nb068_alpha_dummy_468 f)), ((nb068_alpha_dummy_464), (nb068_alpha_dummy_467 f)), ((nb068_alpha_dummy_463), (nb068_alpha_dummy_466 f)), ((nb068_alpha_dummy_461), (nb068_alpha_dummy_462 f)), ((nb068_alpha_dummy_457), (nb068_alpha_dummy_459 f)), ((nb068_alpha_dummy_458), (nb068_alpha_dummy_460 f)), ((nb068_alpha_dummy_450), (nb068_alpha_dummy_452 f)), ((nb068_alpha_dummy_449), (nb068_alpha_dummy_451 f)), ((nb068_alpha_dummy_455), (nb068_alpha_dummy_456 f)), ((nb068_alpha_dummy_453), (nb068_alpha_dummy_454 f)), ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)), ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)), ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_465) (nb068_alpha_dummy_468 f) (nb068_wpp_notmem_1158) (nb068_wpp_notmem_1159 f) (TEnvFresh.consFresh (nb068_alpha_dummy_464) (nb068_alpha_dummy_467 f) (nb068_wpp_notmem_1160) (nb068_wpp_notmem_1161 f) (TEnvFresh.consFresh (nb068_alpha_dummy_463) (nb068_alpha_dummy_466 f) (nb068_wpp_notmem_1162) (nb068_wpp_notmem_1163 f) (TEnvFresh.consFresh (nb068_alpha_dummy_461) (nb068_alpha_dummy_462 f) (nb068_wpp_notmem_1164) (nb068_wpp_notmem_1165 f) (TEnvFresh.consFresh (nb068_alpha_dummy_457) (nb068_alpha_dummy_459 f) (nb068_wpp_notmem_1166) (nb068_wpp_notmem_1167 f) (TEnvFresh.consFresh (nb068_alpha_dummy_458) (nb068_alpha_dummy_460 f) (nb068_wpp_notmem_1168) (nb068_wpp_notmem_1169 f) (TEnvFresh.consFresh (nb068_alpha_dummy_450) (nb068_alpha_dummy_452 f) (nb068_wpp_notmem_1170) (nb068_wpp_notmem_1171 f) (TEnvFresh.consFresh (nb068_alpha_dummy_449) (nb068_alpha_dummy_451 f) (nb068_wpp_notmem_1172) (nb068_wpp_notmem_1173 f) (TEnvFresh.consFresh (nb068_alpha_dummy_455) (nb068_alpha_dummy_456 f) (nb068_wpp_notmem_1174) (nb068_wpp_notmem_1175 f) (TEnvFresh.consFresh (nb068_alpha_dummy_453) (nb068_alpha_dummy_454 f) (nb068_wpp_notmem_1176) (nb068_wpp_notmem_1177 f) (TEnvFresh.consFresh (nb068_alpha_dummy_408) (nb068_alpha_dummy_410 f) (nb068_wpp_notmem_1072) (nb068_wpp_notmem_1073 f) (TEnvFresh.consFresh (nb068_alpha_dummy_407) (nb068_alpha_dummy_409 f) (nb068_wpp_notmem_1074) (nb068_wpp_notmem_1075 f) (TEnvFresh.consFresh (nb068_alpha_dummy_411) (nb068_alpha_dummy_412 f) (nb068_wpp_notmem_1076) (nb068_wpp_notmem_1077 f) (TEnvFresh.consFresh (nb068_alpha_dummy_329) (nb068_alpha_dummy_332 f) (nb068_wpp_notmem_0982) (nb068_wpp_notmem_0983 f) (TEnvFresh.consFresh (nb068_alpha_dummy_328) (nb068_alpha_dummy_331 f) (nb068_wpp_notmem_0860) (nb068_wpp_notmem_0861 f) (TEnvFresh.consFresh (nb068_alpha_dummy_327) (nb068_alpha_dummy_330 f) (nb068_wpp_notmem_0862) (nb068_wpp_notmem_0863 f) (TEnvFresh.consFresh (nb068_alpha_dummy_333) (nb068_alpha_dummy_334 f) (nb068_wpp_notmem_0864) (nb068_wpp_notmem_0865 f) (TEnvFresh.consFresh (nb068_alpha_dummy_325) (nb068_alpha_dummy_326 f) (nb068_wpp_notmem_0866) (nb068_wpp_notmem_0867 f) (TEnvFresh.consFresh (nb068_alpha_dummy_323) (nb068_alpha_dummy_324 f) (nb068_wpp_notmem_0868) (nb068_wpp_notmem_0869 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0136) (nb068_wpp_notmem_0137 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0020) (nb068_wpp_notmem_0021 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0022) (nb068_wpp_notmem_0023 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0024) (nb068_wpp_notmem_0025 x y f) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))))))

noncomputable def nb068_wpp_refl_0137 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_465), (nb068_alpha_dummy_468 f)), ((nb068_alpha_dummy_464), (nb068_alpha_dummy_467 f)), ((nb068_alpha_dummy_463), (nb068_alpha_dummy_466 f)), ((nb068_alpha_dummy_461), (nb068_alpha_dummy_462 f)), ((nb068_alpha_dummy_457), (nb068_alpha_dummy_459 f)), ((nb068_alpha_dummy_458), (nb068_alpha_dummy_460 f)), ((nb068_alpha_dummy_450), (nb068_alpha_dummy_452 f)), ((nb068_alpha_dummy_449), (nb068_alpha_dummy_451 f)), ((nb068_alpha_dummy_455), (nb068_alpha_dummy_456 f)), ((nb068_alpha_dummy_453), (nb068_alpha_dummy_454 f)), ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)), ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)), ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0137 x y f)

theorem nb068_wpp_notmem_1178 : (nb068_alpha_dummy_465) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_465, fv_syn_c0] using (nb068_compact_fv_empty_0342)

theorem nb068_wpp_notmem_1179 (f : Var) : (nb068_alpha_dummy_468 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_468, fv_syn_c0] using (nb068_compact_fv_empty_0343 f)

theorem nb068_wpp_notmem_1180 : (nb068_alpha_dummy_464) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_464, fv_syn_c0] using (nb068_compact_fv_empty_0344)

theorem nb068_wpp_notmem_1181 (f : Var) : (nb068_alpha_dummy_467 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_467, fv_syn_c0] using (nb068_compact_fv_empty_0345 f)

theorem nb068_wpp_notmem_1182 : (nb068_alpha_dummy_463) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_463, fv_syn_c0] using (nb068_compact_fv_empty_0346)

theorem nb068_wpp_notmem_1183 (f : Var) : (nb068_alpha_dummy_466 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_466, fv_syn_c0] using (nb068_compact_fv_empty_0347 f)

theorem nb068_wpp_notmem_1184 : (nb068_alpha_dummy_461) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_461, fv_syn_c0] using (nb068_compact_fv_empty_0348)

theorem nb068_wpp_notmem_1185 (f : Var) : (nb068_alpha_dummy_462 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_462, fv_syn_c0] using (nb068_compact_fv_empty_0349 f)

theorem nb068_wpp_notmem_1186 : (nb068_alpha_dummy_457) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_457, fv_syn_c0] using (nb068_compact_fv_empty_0350)

theorem nb068_wpp_notmem_1187 (f : Var) : (nb068_alpha_dummy_459 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_459, fv_syn_c0] using (nb068_compact_fv_empty_0351 f)

theorem nb068_wpp_notmem_1188 : (nb068_alpha_dummy_458) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_458, fv_syn_c0] using (nb068_compact_fv_empty_0352)

theorem nb068_wpp_notmem_1189 (f : Var) : (nb068_alpha_dummy_460 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_460, fv_syn_c0] using (nb068_compact_fv_empty_0353 f)

theorem nb068_wpp_notmem_1190 : (nb068_alpha_dummy_450) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_450, fv_syn_c0] using (nb068_compact_fv_empty_0354)

theorem nb068_wpp_notmem_1191 (f : Var) : (nb068_alpha_dummy_452 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_452, fv_syn_c0] using (nb068_compact_fv_empty_0355 f)

theorem nb068_wpp_notmem_1192 : (nb068_alpha_dummy_449) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_449, fv_syn_c0] using (nb068_compact_fv_empty_0356)

theorem nb068_wpp_notmem_1193 (f : Var) : (nb068_alpha_dummy_451 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_451, fv_syn_c0] using (nb068_compact_fv_empty_0357 f)

theorem nb068_wpp_notmem_1194 : (nb068_alpha_dummy_455) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_455, fv_syn_c0] using (nb068_compact_fv_empty_0358)

theorem nb068_wpp_notmem_1195 (f : Var) : (nb068_alpha_dummy_456 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_456, fv_syn_c0] using (nb068_compact_fv_empty_0359 f)

theorem nb068_wpp_notmem_1196 : (nb068_alpha_dummy_453) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_453, fv_syn_c0] using (nb068_compact_fv_empty_0360)

theorem nb068_wpp_notmem_1197 (f : Var) : (nb068_alpha_dummy_454 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_454, fv_syn_c0] using (nb068_compact_fv_empty_0361 f)

theorem nb068_compact_envfresh_0138 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_465), (nb068_alpha_dummy_468 f)), ((nb068_alpha_dummy_464), (nb068_alpha_dummy_467 f)), ((nb068_alpha_dummy_463), (nb068_alpha_dummy_466 f)), ((nb068_alpha_dummy_461), (nb068_alpha_dummy_462 f)), ((nb068_alpha_dummy_457), (nb068_alpha_dummy_459 f)), ((nb068_alpha_dummy_458), (nb068_alpha_dummy_460 f)), ((nb068_alpha_dummy_450), (nb068_alpha_dummy_452 f)), ((nb068_alpha_dummy_449), (nb068_alpha_dummy_451 f)), ((nb068_alpha_dummy_455), (nb068_alpha_dummy_456 f)), ((nb068_alpha_dummy_453), (nb068_alpha_dummy_454 f)), ((nb068_alpha_dummy_408), (nb068_alpha_dummy_410 f)), ((nb068_alpha_dummy_407), (nb068_alpha_dummy_409 f)), ((nb068_alpha_dummy_411), (nb068_alpha_dummy_412 f)), ((nb068_alpha_dummy_329), (nb068_alpha_dummy_332 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_465) (nb068_alpha_dummy_468 f) (nb068_wpp_notmem_1178) (nb068_wpp_notmem_1179 f) (TEnvFresh.consFresh (nb068_alpha_dummy_464) (nb068_alpha_dummy_467 f) (nb068_wpp_notmem_1180) (nb068_wpp_notmem_1181 f) (TEnvFresh.consFresh (nb068_alpha_dummy_463) (nb068_alpha_dummy_466 f) (nb068_wpp_notmem_1182) (nb068_wpp_notmem_1183 f) (TEnvFresh.consFresh (nb068_alpha_dummy_461) (nb068_alpha_dummy_462 f) (nb068_wpp_notmem_1184) (nb068_wpp_notmem_1185 f) (TEnvFresh.consFresh (nb068_alpha_dummy_457) (nb068_alpha_dummy_459 f) (nb068_wpp_notmem_1186) (nb068_wpp_notmem_1187 f) (TEnvFresh.consFresh (nb068_alpha_dummy_458) (nb068_alpha_dummy_460 f) (nb068_wpp_notmem_1188) (nb068_wpp_notmem_1189 f) (TEnvFresh.consFresh (nb068_alpha_dummy_450) (nb068_alpha_dummy_452 f) (nb068_wpp_notmem_1190) (nb068_wpp_notmem_1191 f) (TEnvFresh.consFresh (nb068_alpha_dummy_449) (nb068_alpha_dummy_451 f) (nb068_wpp_notmem_1192) (nb068_wpp_notmem_1193 f) (TEnvFresh.consFresh (nb068_alpha_dummy_455) (nb068_alpha_dummy_456 f) (nb068_wpp_notmem_1194) (nb068_wpp_notmem_1195 f) (TEnvFresh.consFresh (nb068_alpha_dummy_453) (nb068_alpha_dummy_454 f) (nb068_wpp_notmem_1196) (nb068_wpp_notmem_1197 f) (TEnvFresh.consFresh (nb068_alpha_dummy_408) (nb068_alpha_dummy_410 f) (nb068_wpp_notmem_1098) (nb068_wpp_notmem_1099 f) (TEnvFresh.consFresh (nb068_alpha_dummy_407) (nb068_alpha_dummy_409 f) (nb068_wpp_notmem_1100) (nb068_wpp_notmem_1101 f) (TEnvFresh.consFresh (nb068_alpha_dummy_411) (nb068_alpha_dummy_412 f) (nb068_wpp_notmem_1102) (nb068_wpp_notmem_1103 f) (TEnvFresh.consFresh (nb068_alpha_dummy_329) (nb068_alpha_dummy_332 f) (nb068_wpp_notmem_1004) (nb068_wpp_notmem_1005 f) (TEnvFresh.consFresh (nb068_alpha_dummy_328) (nb068_alpha_dummy_331 f) (nb068_wpp_notmem_0890) (nb068_wpp_notmem_0891 f) (TEnvFresh.consFresh (nb068_alpha_dummy_327) (nb068_alpha_dummy_330 f) (nb068_wpp_notmem_0892) (nb068_wpp_notmem_0893 f) (TEnvFresh.consFresh (nb068_alpha_dummy_333) (nb068_alpha_dummy_334 f) (nb068_wpp_notmem_0894) (nb068_wpp_notmem_0895 f) (TEnvFresh.consFresh (nb068_alpha_dummy_325) (nb068_alpha_dummy_326 f) (nb068_wpp_notmem_0896) (nb068_wpp_notmem_0897 f) (TEnvFresh.consFresh (nb068_alpha_dummy_323) (nb068_alpha_dummy_324 f) (nb068_wpp_notmem_0898) (nb068_wpp_notmem_0899 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0168) (nb068_wpp_notmem_0169 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0046) (nb068_wpp_notmem_0047 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0048) (nb068_wpp_notmem_0049 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0050) (nb068_wpp_notmem_0051 x y f) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
