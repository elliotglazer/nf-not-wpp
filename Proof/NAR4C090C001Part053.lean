import NAR4C090C001Part052

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

noncomputable def nb090_split_alpha_0030 (v : Var) (u : Var) (A : Class) (h : Var) : TAlphaWff [((nb090_alpha_dummy_323 A), (nb090_alpha_dummy_324 u)), ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)), ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_321 A), (nb090_alpha_dummy_322 u)), ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)), ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_323 A)) (syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_292 A))))) (Wff.neg (Wff.classMem (Class.cv (nb090_alpha_dummy_323 A)) (syn_ccompl (syn_csn (syn_c0c)))))) (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_324 u)) (syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_294 u))))) (Wff.neg (Wff.classMem (Class.cv (nb090_alpha_dummy_324 u)) (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0304 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0305 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0304 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0305 u) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0334 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0335 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0332 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0333 u) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_292 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_294 u))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0308 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0309 u) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0308 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0309 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0306 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0307 u) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_307 A), (nb090_alpha_dummy_310 u)), ((nb090_alpha_dummy_306 A), (nb090_alpha_dummy_309 u)), ((nb090_alpha_dummy_305 A), (nb090_alpha_dummy_308 u)), ((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)), ((nb090_alpha_dummy_299 A), (nb090_alpha_dummy_301 u)), ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)), ((nb090_alpha_dummy_325 A), (nb090_alpha_dummy_326 u)), ((nb090_alpha_dummy_323 A), (nb090_alpha_dummy_324 u)), ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)), ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_321 A), (nb090_alpha_dummy_322 u)), ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)), ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (nb090_wpp_refl_0104 v u A h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0312 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0313 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0310 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0311 u) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0316 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0317 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0314 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0315 u) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0312 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0313 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0310 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0311 u) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0316 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0317 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0314 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0315 u) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_307 A), (nb090_alpha_dummy_310 u)), ((nb090_alpha_dummy_306 A), (nb090_alpha_dummy_309 u)), ((nb090_alpha_dummy_305 A), (nb090_alpha_dummy_308 u)), ((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)), ((nb090_alpha_dummy_299 A), (nb090_alpha_dummy_301 u)), ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)), ((nb090_alpha_dummy_325 A), (nb090_alpha_dummy_326 u)), ((nb090_alpha_dummy_323 A), (nb090_alpha_dummy_324 u)), ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)), ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_321 A), (nb090_alpha_dummy_322 u)), ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)), ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c0) (nb090_wpp_refl_0105 v u A h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0320 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0321 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0318 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0319 u) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0320 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0321 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0318 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0319 u) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0324 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0325 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0322 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0323 u) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0324 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0325 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0322 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0323 u) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0306 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0307 u) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)), ((nb090_alpha_dummy_299 A), (nb090_alpha_dummy_301 u)), ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)), ((nb090_alpha_dummy_325 A), (nb090_alpha_dummy_326 u)), ((nb090_alpha_dummy_323 A), (nb090_alpha_dummy_324 u)), ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)), ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_321 A), (nb090_alpha_dummy_322 u)), ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)), ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0106 v u A h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0306 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0307 u) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0306 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0307 u) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)), ((nb090_alpha_dummy_299 A), (nb090_alpha_dummy_301 u)), ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)), ((nb090_alpha_dummy_325 A), (nb090_alpha_dummy_326 u)), ((nb090_alpha_dummy_323 A), (nb090_alpha_dummy_324 u)), ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)), ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_321 A), (nb090_alpha_dummy_322 u)), ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)), ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0106 v u A h)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0304 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0305 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0304 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0305 u) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0334 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0335 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0332 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0333 u) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_292 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_294 u))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0308 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0309 u) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0308 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0309 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0306 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0307 u) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_307 A), (nb090_alpha_dummy_310 u)), ((nb090_alpha_dummy_306 A), (nb090_alpha_dummy_309 u)), ((nb090_alpha_dummy_305 A), (nb090_alpha_dummy_308 u)), ((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)), ((nb090_alpha_dummy_299 A), (nb090_alpha_dummy_301 u)), ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)), ((nb090_alpha_dummy_325 A), (nb090_alpha_dummy_326 u)), ((nb090_alpha_dummy_323 A), (nb090_alpha_dummy_324 u)), ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)), ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_321 A), (nb090_alpha_dummy_322 u)), ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)), ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (nb090_wpp_refl_0104 v u A h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0312 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0313 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0310 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0311 u) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0316 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0317 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0314 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0315 u) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0312 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0313 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0310 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0311 u) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0316 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0317 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0314 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0315 u) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_307 A), (nb090_alpha_dummy_310 u)), ((nb090_alpha_dummy_306 A), (nb090_alpha_dummy_309 u)), ((nb090_alpha_dummy_305 A), (nb090_alpha_dummy_308 u)), ((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)), ((nb090_alpha_dummy_299 A), (nb090_alpha_dummy_301 u)), ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)), ((nb090_alpha_dummy_325 A), (nb090_alpha_dummy_326 u)), ((nb090_alpha_dummy_323 A), (nb090_alpha_dummy_324 u)), ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)), ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_321 A), (nb090_alpha_dummy_322 u)), ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)), ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c0) (nb090_wpp_refl_0105 v u A h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0320 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0321 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0318 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0319 u) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0320 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0321 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0318 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0319 u) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0324 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0325 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0322 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0323 u) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0324 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0325 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0322 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0323 u) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0306 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0307 u) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)), ((nb090_alpha_dummy_299 A), (nb090_alpha_dummy_301 u)), ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)), ((nb090_alpha_dummy_325 A), (nb090_alpha_dummy_326 u)), ((nb090_alpha_dummy_323 A), (nb090_alpha_dummy_324 u)), ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)), ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_321 A), (nb090_alpha_dummy_322 u)), ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)), ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0106 v u A h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0306 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0307 u) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0306 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0307 u) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)), ((nb090_alpha_dummy_299 A), (nb090_alpha_dummy_301 u)), ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)), ((nb090_alpha_dummy_325 A), (nb090_alpha_dummy_326 u)), ((nb090_alpha_dummy_323 A), (nb090_alpha_dummy_324 u)), ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)), ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_321 A), (nb090_alpha_dummy_322 u)), ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)), ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0106 v u A h)))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_323 A), (nb090_alpha_dummy_324 u)), ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)), ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_321 A), (nb090_alpha_dummy_322 u)), ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)), ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_ccompl (syn_csn (syn_c0c))) (nb090_wpp_refl_0107 v u A h)))))

theorem nb090_wpp_notmem_0838 (A : Class) : (nb090_alpha_dummy_283 A) ∉ ((syn_c2nd)).fv := by
  simpa only [nb090_alpha_dummy_283, fv_syn_c2nd] using (nb090_compact_fv_empty_0232 A)

theorem nb090_wpp_notmem_0839 (u : Var) : (nb090_alpha_dummy_284 u) ∉ ((syn_c2nd)).fv := by
  simpa only [nb090_alpha_dummy_284, fv_syn_c2nd] using (nb090_compact_fv_empty_0233 u)

theorem nb090_wpp_notmem_0840 (A : Class) : (nb090_alpha_dummy_285 A) ∉ ((syn_c2nd)).fv := by
  simpa only [nb090_alpha_dummy_285, fv_syn_c2nd] using (nb090_compact_fv_empty_0234 A)

theorem nb090_wpp_notmem_0841 (u : Var) : (nb090_alpha_dummy_286 u) ∉ ((syn_c2nd)).fv := by
  simpa only [nb090_alpha_dummy_286, fv_syn_c2nd] using (nb090_compact_fv_empty_0235 u)

theorem nb090_wpp_notmem_0842 (A : Class) : (nb090_alpha_dummy_288 A) ∉ ((syn_c2nd)).fv := by
  simpa only [nb090_alpha_dummy_288, fv_syn_c2nd] using (nb090_compact_fv_empty_0236 A)

theorem nb090_wpp_notmem_0843 (u : Var) : (nb090_alpha_dummy_290 u) ∉ ((syn_c2nd)).fv := by
  simpa only [nb090_alpha_dummy_290, fv_syn_c2nd] using (nb090_compact_fv_empty_0237 u)

theorem nb090_wpp_notmem_0844 (A : Class) : (nb090_alpha_dummy_287 A) ∉ ((syn_c2nd)).fv := by
  simpa only [nb090_alpha_dummy_287, fv_syn_c2nd] using (nb090_compact_fv_empty_0238 A)

theorem nb090_wpp_notmem_0845 (u : Var) : (nb090_alpha_dummy_289 u) ∉ ((syn_c2nd)).fv := by
  simpa only [nb090_alpha_dummy_289, fv_syn_c2nd] using (nb090_compact_fv_empty_0239 u)

theorem nb090_wpp_notmem_0846 (A : Class) : (nb090_alpha_dummy_000 A) ∉ ((syn_c2nd)).fv := by
  simpa only [nb090_alpha_dummy_000, fv_syn_c2nd] using (nb090_compact_fv_empty_0062 A)

theorem nb090_wpp_notmem_0847 (h : Var) : h ∉ ((syn_c2nd)).fv := by
  simpa only [fv_syn_c2nd] using (nb090_compact_fv_empty_0063 h)

theorem nb090_wpp_notmem_0848 (A : Class) : (nb090_alpha_dummy_002 A) ∉ ((syn_c2nd)).fv := by
  simpa only [nb090_alpha_dummy_002, fv_syn_c2nd] using (nb090_compact_fv_empty_0020 A)

theorem nb090_wpp_notmem_0849 (v : Var) : v ∉ ((syn_c2nd)).fv := by
  simpa only [fv_syn_c2nd] using (nb090_compact_fv_empty_0021 v)

theorem nb090_wpp_notmem_0850 (A : Class) : (nb090_alpha_dummy_001 A) ∉ ((syn_c2nd)).fv := by
  simpa only [nb090_alpha_dummy_001, fv_syn_c2nd] using (nb090_compact_fv_empty_0022 A)

theorem nb090_wpp_notmem_0851 (u : Var) : u ∉ ((syn_c2nd)).fv := by
  simpa only [fv_syn_c2nd] using (nb090_compact_fv_empty_0023 u)

theorem nb090_wpp_notmem_0852 (A : Class) : (nb090_alpha_dummy_003 A) ∉ ((syn_c2nd)).fv := by
  simpa only [nb090_alpha_dummy_003, fv_syn_c2nd] using (nb090_compact_fv_empty_0024 A)

theorem nb090_wpp_notmem_0853 (v : Var) (u : Var) (A : Class) (h : Var) : (nb090_alpha_dummy_004 v u A h) ∉ ((syn_c2nd)).fv := by
  simpa only [nb090_alpha_dummy_004, fv_syn_c2nd] using (nb090_compact_fv_empty_0025 v u A h)

theorem nb090_compact_envfresh_0108 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c2nd)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_283 A) (nb090_alpha_dummy_284 u) (nb090_wpp_notmem_0838 A) (nb090_wpp_notmem_0839 u) (TEnvFresh.consFresh (nb090_alpha_dummy_285 A) (nb090_alpha_dummy_286 u) (nb090_wpp_notmem_0840 A) (nb090_wpp_notmem_0841 u) (TEnvFresh.consFresh (nb090_alpha_dummy_288 A) (nb090_alpha_dummy_290 u) (nb090_wpp_notmem_0842 A) (nb090_wpp_notmem_0843 u) (TEnvFresh.consFresh (nb090_alpha_dummy_287 A) (nb090_alpha_dummy_289 u) (nb090_wpp_notmem_0844 A) (nb090_wpp_notmem_0845 u) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0846 A) (nb090_wpp_notmem_0847 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0848 A) (nb090_wpp_notmem_0849 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0850 A) (nb090_wpp_notmem_0851 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0852 A) (nb090_wpp_notmem_0853 v u A h) (TEnvFresh.nil ((syn_c2nd)).fv)))))))))

noncomputable def nb090_wpp_refl_0108 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c2nd)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0108 v u A h)

theorem nb090_compact_fv_empty_0246 (A : Class) : (nb090_alpha_dummy_334 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0854 (A : Class) : (nb090_alpha_dummy_334 A) ∉ ((syn_cvv)).fv := by
  simpa only [nb090_alpha_dummy_334, fv_syn_cvv] using (nb090_compact_fv_empty_0246 A)

theorem nb090_compact_fv_empty_0247 (h : Var) : (nb090_alpha_dummy_336 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0855 (h : Var) : (nb090_alpha_dummy_336 h) ∉ ((syn_cvv)).fv := by
  simpa only [nb090_alpha_dummy_336, fv_syn_cvv] using (nb090_compact_fv_empty_0247 h)

theorem nb090_compact_fv_empty_0248 (A : Class) : (nb090_alpha_dummy_333 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0856 (A : Class) : (nb090_alpha_dummy_333 A) ∉ ((syn_cvv)).fv := by
  simpa only [nb090_alpha_dummy_333, fv_syn_cvv] using (nb090_compact_fv_empty_0248 A)

theorem nb090_compact_fv_empty_0249 (h : Var) : (nb090_alpha_dummy_335 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0857 (h : Var) : (nb090_alpha_dummy_335 h) ∉ ((syn_cvv)).fv := by
  simpa only [nb090_alpha_dummy_335, fv_syn_cvv] using (nb090_compact_fv_empty_0249 h)

theorem nb090_compact_fv_empty_0250 (A : Class) : (nb090_alpha_dummy_331 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0858 (A : Class) : (nb090_alpha_dummy_331 A) ∉ ((syn_cvv)).fv := by
  simpa only [nb090_alpha_dummy_331, fv_syn_cvv] using (nb090_compact_fv_empty_0250 A)

theorem nb090_compact_fv_empty_0251 (v : Var) (h : Var) : (nb090_alpha_dummy_332 v h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0859 (v : Var) (h : Var) : (nb090_alpha_dummy_332 v h) ∉ ((syn_cvv)).fv := by
  simpa only [nb090_alpha_dummy_332, fv_syn_cvv] using (nb090_compact_fv_empty_0251 v h)

theorem nb090_compact_fv_empty_0252 (A : Class) : (nb090_alpha_dummy_329 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0860 (A : Class) : (nb090_alpha_dummy_329 A) ∉ ((syn_cvv)).fv := by
  simpa only [nb090_alpha_dummy_329, fv_syn_cvv] using (nb090_compact_fv_empty_0252 A)

theorem nb090_compact_fv_empty_0253 (v : Var) (h : Var) : (nb090_alpha_dummy_330 v h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0861 (v : Var) (h : Var) : (nb090_alpha_dummy_330 v h) ∉ ((syn_cvv)).fv := by
  simpa only [nb090_alpha_dummy_330, fv_syn_cvv] using (nb090_compact_fv_empty_0253 v h)

theorem nb090_compact_envfresh_0109 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)), ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)), ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)), ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_cvv)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_334 A) (nb090_alpha_dummy_336 h) (nb090_wpp_notmem_0854 A) (nb090_wpp_notmem_0855 h) (TEnvFresh.consFresh (nb090_alpha_dummy_333 A) (nb090_alpha_dummy_335 h) (nb090_wpp_notmem_0856 A) (nb090_wpp_notmem_0857 h) (TEnvFresh.consFresh (nb090_alpha_dummy_331 A) (nb090_alpha_dummy_332 v h) (nb090_wpp_notmem_0858 A) (nb090_wpp_notmem_0859 v h) (TEnvFresh.consFresh (nb090_alpha_dummy_329 A) (nb090_alpha_dummy_330 v h) (nb090_wpp_notmem_0860 A) (nb090_wpp_notmem_0861 v h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0618 A) (nb090_wpp_notmem_0619 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0620 A) (nb090_wpp_notmem_0621 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0622 A) (nb090_wpp_notmem_0623 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0624 A) (nb090_wpp_notmem_0625 v u A h) (TEnvFresh.nil ((syn_cvv)).fv)))))))))

noncomputable def nb090_wpp_refl_0109 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)), ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)), ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)), ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_cvv)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0109 v u A h)

theorem nb090_compact_fv_empty_0254 (A : Class) : (nb090_alpha_dummy_353 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0862 (A : Class) : (nb090_alpha_dummy_353 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_353, fv_syn_c1c] using (nb090_compact_fv_empty_0254 A)

theorem nb090_compact_fv_empty_0255 (h : Var) : (nb090_alpha_dummy_356 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0863 (h : Var) : (nb090_alpha_dummy_356 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_356, fv_syn_c1c] using (nb090_compact_fv_empty_0255 h)

theorem nb090_compact_fv_empty_0256 (A : Class) : (nb090_alpha_dummy_352 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0864 (A : Class) : (nb090_alpha_dummy_352 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_352, fv_syn_c1c] using (nb090_compact_fv_empty_0256 A)

theorem nb090_compact_fv_empty_0257 (h : Var) : (nb090_alpha_dummy_355 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0865 (h : Var) : (nb090_alpha_dummy_355 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_355, fv_syn_c1c] using (nb090_compact_fv_empty_0257 h)

theorem nb090_compact_fv_empty_0258 (A : Class) : (nb090_alpha_dummy_351 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0866 (A : Class) : (nb090_alpha_dummy_351 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_351, fv_syn_c1c] using (nb090_compact_fv_empty_0258 A)

theorem nb090_compact_fv_empty_0259 (h : Var) : (nb090_alpha_dummy_354 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0867 (h : Var) : (nb090_alpha_dummy_354 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_354, fv_syn_c1c] using (nb090_compact_fv_empty_0259 h)

theorem nb090_compact_fv_empty_0260 (A : Class) : (nb090_alpha_dummy_349 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0868 (A : Class) : (nb090_alpha_dummy_349 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_349, fv_syn_c1c] using (nb090_compact_fv_empty_0260 A)

theorem nb090_compact_fv_empty_0261 (h : Var) : (nb090_alpha_dummy_350 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0869 (h : Var) : (nb090_alpha_dummy_350 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_350, fv_syn_c1c] using (nb090_compact_fv_empty_0261 h)

theorem nb090_compact_fv_empty_0262 (A : Class) : (nb090_alpha_dummy_345 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0870 (A : Class) : (nb090_alpha_dummy_345 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_345, fv_syn_c1c] using (nb090_compact_fv_empty_0262 A)

theorem nb090_compact_fv_empty_0263 (h : Var) : (nb090_alpha_dummy_347 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0871 (h : Var) : (nb090_alpha_dummy_347 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_347, fv_syn_c1c] using (nb090_compact_fv_empty_0263 h)

theorem nb090_compact_fv_empty_0264 (A : Class) : (nb090_alpha_dummy_346 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0872 (A : Class) : (nb090_alpha_dummy_346 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_346, fv_syn_c1c] using (nb090_compact_fv_empty_0264 A)

theorem nb090_compact_fv_empty_0265 (h : Var) : (nb090_alpha_dummy_348 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0873 (h : Var) : (nb090_alpha_dummy_348 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_348, fv_syn_c1c] using (nb090_compact_fv_empty_0265 h)

theorem nb090_compact_fv_empty_0266 (A : Class) : (nb090_alpha_dummy_338 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0874 (A : Class) : (nb090_alpha_dummy_338 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_338, fv_syn_c1c] using (nb090_compact_fv_empty_0266 A)

theorem nb090_compact_fv_empty_0267 (h : Var) : (nb090_alpha_dummy_340 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0875 (h : Var) : (nb090_alpha_dummy_340 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_340, fv_syn_c1c] using (nb090_compact_fv_empty_0267 h)

theorem nb090_compact_fv_empty_0268 (A : Class) : (nb090_alpha_dummy_337 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0876 (A : Class) : (nb090_alpha_dummy_337 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_337, fv_syn_c1c] using (nb090_compact_fv_empty_0268 A)

theorem nb090_compact_fv_empty_0269 (h : Var) : (nb090_alpha_dummy_339 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0877 (h : Var) : (nb090_alpha_dummy_339 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_339, fv_syn_c1c] using (nb090_compact_fv_empty_0269 h)

theorem nb090_compact_fv_empty_0270 (A : Class) : (nb090_alpha_dummy_343 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0878 (A : Class) : (nb090_alpha_dummy_343 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_343, fv_syn_c1c] using (nb090_compact_fv_empty_0270 A)

theorem nb090_compact_fv_empty_0271 (h : Var) : (nb090_alpha_dummy_344 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0879 (h : Var) : (nb090_alpha_dummy_344 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_344, fv_syn_c1c] using (nb090_compact_fv_empty_0271 h)

theorem nb090_compact_fv_empty_0272 (A : Class) : (nb090_alpha_dummy_341 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0880 (A : Class) : (nb090_alpha_dummy_341 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_341, fv_syn_c1c] using (nb090_compact_fv_empty_0272 A)

theorem nb090_compact_fv_empty_0273 (h : Var) : (nb090_alpha_dummy_342 h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_0881 (h : Var) : (nb090_alpha_dummy_342 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_342, fv_syn_c1c] using (nb090_compact_fv_empty_0273 h)

theorem nb090_wpp_notmem_0882 (A : Class) : (nb090_alpha_dummy_334 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_334, fv_syn_c1c] using (nb090_compact_fv_empty_0246 A)

theorem nb090_wpp_notmem_0883 (h : Var) : (nb090_alpha_dummy_336 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_336, fv_syn_c1c] using (nb090_compact_fv_empty_0247 h)

theorem nb090_wpp_notmem_0884 (A : Class) : (nb090_alpha_dummy_333 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_333, fv_syn_c1c] using (nb090_compact_fv_empty_0248 A)

theorem nb090_wpp_notmem_0885 (h : Var) : (nb090_alpha_dummy_335 h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_335, fv_syn_c1c] using (nb090_compact_fv_empty_0249 h)

theorem nb090_wpp_notmem_0886 (A : Class) : (nb090_alpha_dummy_331 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_331, fv_syn_c1c] using (nb090_compact_fv_empty_0250 A)

theorem nb090_wpp_notmem_0887 (v : Var) (h : Var) : (nb090_alpha_dummy_332 v h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_332, fv_syn_c1c] using (nb090_compact_fv_empty_0251 v h)

theorem nb090_wpp_notmem_0888 (A : Class) : (nb090_alpha_dummy_329 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_329, fv_syn_c1c] using (nb090_compact_fv_empty_0252 A)

theorem nb090_wpp_notmem_0889 (v : Var) (h : Var) : (nb090_alpha_dummy_330 v h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_330, fv_syn_c1c] using (nb090_compact_fv_empty_0253 v h)

theorem nb090_compact_envfresh_0110 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_353 A), (nb090_alpha_dummy_356 h)), ((nb090_alpha_dummy_352 A), (nb090_alpha_dummy_355 h)), ((nb090_alpha_dummy_351 A), (nb090_alpha_dummy_354 h)), ((nb090_alpha_dummy_349 A), (nb090_alpha_dummy_350 h)), ((nb090_alpha_dummy_345 A), (nb090_alpha_dummy_347 h)), ((nb090_alpha_dummy_346 A), (nb090_alpha_dummy_348 h)), ((nb090_alpha_dummy_338 A), (nb090_alpha_dummy_340 h)), ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)), ((nb090_alpha_dummy_343 A), (nb090_alpha_dummy_344 h)), ((nb090_alpha_dummy_341 A), (nb090_alpha_dummy_342 h)), ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)), ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)), ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)), ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_353 A) (nb090_alpha_dummy_356 h) (nb090_wpp_notmem_0862 A) (nb090_wpp_notmem_0863 h) (TEnvFresh.consFresh (nb090_alpha_dummy_352 A) (nb090_alpha_dummy_355 h) (nb090_wpp_notmem_0864 A) (nb090_wpp_notmem_0865 h) (TEnvFresh.consFresh (nb090_alpha_dummy_351 A) (nb090_alpha_dummy_354 h) (nb090_wpp_notmem_0866 A) (nb090_wpp_notmem_0867 h) (TEnvFresh.consFresh (nb090_alpha_dummy_349 A) (nb090_alpha_dummy_350 h) (nb090_wpp_notmem_0868 A) (nb090_wpp_notmem_0869 h) (TEnvFresh.consFresh (nb090_alpha_dummy_345 A) (nb090_alpha_dummy_347 h) (nb090_wpp_notmem_0870 A) (nb090_wpp_notmem_0871 h) (TEnvFresh.consFresh (nb090_alpha_dummy_346 A) (nb090_alpha_dummy_348 h) (nb090_wpp_notmem_0872 A) (nb090_wpp_notmem_0873 h) (TEnvFresh.consFresh (nb090_alpha_dummy_338 A) (nb090_alpha_dummy_340 h) (nb090_wpp_notmem_0874 A) (nb090_wpp_notmem_0875 h) (TEnvFresh.consFresh (nb090_alpha_dummy_337 A) (nb090_alpha_dummy_339 h) (nb090_wpp_notmem_0876 A) (nb090_wpp_notmem_0877 h) (TEnvFresh.consFresh (nb090_alpha_dummy_343 A) (nb090_alpha_dummy_344 h) (nb090_wpp_notmem_0878 A) (nb090_wpp_notmem_0879 h) (TEnvFresh.consFresh (nb090_alpha_dummy_341 A) (nb090_alpha_dummy_342 h) (nb090_wpp_notmem_0880 A) (nb090_wpp_notmem_0881 h) (TEnvFresh.consFresh (nb090_alpha_dummy_334 A) (nb090_alpha_dummy_336 h) (nb090_wpp_notmem_0882 A) (nb090_wpp_notmem_0883 h) (TEnvFresh.consFresh (nb090_alpha_dummy_333 A) (nb090_alpha_dummy_335 h) (nb090_wpp_notmem_0884 A) (nb090_wpp_notmem_0885 h) (TEnvFresh.consFresh (nb090_alpha_dummy_331 A) (nb090_alpha_dummy_332 v h) (nb090_wpp_notmem_0886 A) (nb090_wpp_notmem_0887 v h) (TEnvFresh.consFresh (nb090_alpha_dummy_329 A) (nb090_alpha_dummy_330 v h) (nb090_wpp_notmem_0888 A) (nb090_wpp_notmem_0889 v h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0142 A) (nb090_wpp_notmem_0143 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0020 A) (nb090_wpp_notmem_0021 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0022 A) (nb090_wpp_notmem_0023 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0024 A) (nb090_wpp_notmem_0025 v u A h) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))

noncomputable def nb090_wpp_refl_0110 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_353 A), (nb090_alpha_dummy_356 h)), ((nb090_alpha_dummy_352 A), (nb090_alpha_dummy_355 h)), ((nb090_alpha_dummy_351 A), (nb090_alpha_dummy_354 h)), ((nb090_alpha_dummy_349 A), (nb090_alpha_dummy_350 h)), ((nb090_alpha_dummy_345 A), (nb090_alpha_dummy_347 h)), ((nb090_alpha_dummy_346 A), (nb090_alpha_dummy_348 h)), ((nb090_alpha_dummy_338 A), (nb090_alpha_dummy_340 h)), ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)), ((nb090_alpha_dummy_343 A), (nb090_alpha_dummy_344 h)), ((nb090_alpha_dummy_341 A), (nb090_alpha_dummy_342 h)), ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)), ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)), ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)), ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0110 v u A h)

theorem nb090_wpp_notmem_0890 (A : Class) : (nb090_alpha_dummy_353 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_353, fv_syn_c0] using (nb090_compact_fv_empty_0254 A)

theorem nb090_wpp_notmem_0891 (h : Var) : (nb090_alpha_dummy_356 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_356, fv_syn_c0] using (nb090_compact_fv_empty_0255 h)

theorem nb090_wpp_notmem_0892 (A : Class) : (nb090_alpha_dummy_352 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_352, fv_syn_c0] using (nb090_compact_fv_empty_0256 A)

theorem nb090_wpp_notmem_0893 (h : Var) : (nb090_alpha_dummy_355 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_355, fv_syn_c0] using (nb090_compact_fv_empty_0257 h)

theorem nb090_wpp_notmem_0894 (A : Class) : (nb090_alpha_dummy_351 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_351, fv_syn_c0] using (nb090_compact_fv_empty_0258 A)

theorem nb090_wpp_notmem_0895 (h : Var) : (nb090_alpha_dummy_354 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_354, fv_syn_c0] using (nb090_compact_fv_empty_0259 h)

theorem nb090_wpp_notmem_0896 (A : Class) : (nb090_alpha_dummy_349 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_349, fv_syn_c0] using (nb090_compact_fv_empty_0260 A)

theorem nb090_wpp_notmem_0897 (h : Var) : (nb090_alpha_dummy_350 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_350, fv_syn_c0] using (nb090_compact_fv_empty_0261 h)

theorem nb090_wpp_notmem_0898 (A : Class) : (nb090_alpha_dummy_345 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_345, fv_syn_c0] using (nb090_compact_fv_empty_0262 A)

theorem nb090_wpp_notmem_0899 (h : Var) : (nb090_alpha_dummy_347 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_347, fv_syn_c0] using (nb090_compact_fv_empty_0263 h)

theorem nb090_wpp_notmem_0900 (A : Class) : (nb090_alpha_dummy_346 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_346, fv_syn_c0] using (nb090_compact_fv_empty_0264 A)

theorem nb090_wpp_notmem_0901 (h : Var) : (nb090_alpha_dummy_348 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_348, fv_syn_c0] using (nb090_compact_fv_empty_0265 h)

theorem nb090_wpp_notmem_0902 (A : Class) : (nb090_alpha_dummy_338 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_338, fv_syn_c0] using (nb090_compact_fv_empty_0266 A)

theorem nb090_wpp_notmem_0903 (h : Var) : (nb090_alpha_dummy_340 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_340, fv_syn_c0] using (nb090_compact_fv_empty_0267 h)

theorem nb090_wpp_notmem_0904 (A : Class) : (nb090_alpha_dummy_337 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_337, fv_syn_c0] using (nb090_compact_fv_empty_0268 A)

theorem nb090_wpp_notmem_0905 (h : Var) : (nb090_alpha_dummy_339 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_339, fv_syn_c0] using (nb090_compact_fv_empty_0269 h)

theorem nb090_wpp_notmem_0906 (A : Class) : (nb090_alpha_dummy_343 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_343, fv_syn_c0] using (nb090_compact_fv_empty_0270 A)

theorem nb090_wpp_notmem_0907 (h : Var) : (nb090_alpha_dummy_344 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_344, fv_syn_c0] using (nb090_compact_fv_empty_0271 h)

theorem nb090_wpp_notmem_0908 (A : Class) : (nb090_alpha_dummy_341 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_341, fv_syn_c0] using (nb090_compact_fv_empty_0272 A)

theorem nb090_wpp_notmem_0909 (h : Var) : (nb090_alpha_dummy_342 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_342, fv_syn_c0] using (nb090_compact_fv_empty_0273 h)

theorem nb090_wpp_notmem_0910 (A : Class) : (nb090_alpha_dummy_334 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_334, fv_syn_c0] using (nb090_compact_fv_empty_0246 A)

theorem nb090_wpp_notmem_0911 (h : Var) : (nb090_alpha_dummy_336 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_336, fv_syn_c0] using (nb090_compact_fv_empty_0247 h)

theorem nb090_wpp_notmem_0912 (A : Class) : (nb090_alpha_dummy_333 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_333, fv_syn_c0] using (nb090_compact_fv_empty_0248 A)

theorem nb090_wpp_notmem_0913 (h : Var) : (nb090_alpha_dummy_335 h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_335, fv_syn_c0] using (nb090_compact_fv_empty_0249 h)

theorem nb090_wpp_notmem_0914 (A : Class) : (nb090_alpha_dummy_331 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_331, fv_syn_c0] using (nb090_compact_fv_empty_0250 A)

theorem nb090_wpp_notmem_0915 (v : Var) (h : Var) : (nb090_alpha_dummy_332 v h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_332, fv_syn_c0] using (nb090_compact_fv_empty_0251 v h)

theorem nb090_wpp_notmem_0916 (A : Class) : (nb090_alpha_dummy_329 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_329, fv_syn_c0] using (nb090_compact_fv_empty_0252 A)

theorem nb090_wpp_notmem_0917 (v : Var) (h : Var) : (nb090_alpha_dummy_330 v h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_330, fv_syn_c0] using (nb090_compact_fv_empty_0253 v h)

theorem nb090_compact_envfresh_0111 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_353 A), (nb090_alpha_dummy_356 h)), ((nb090_alpha_dummy_352 A), (nb090_alpha_dummy_355 h)), ((nb090_alpha_dummy_351 A), (nb090_alpha_dummy_354 h)), ((nb090_alpha_dummy_349 A), (nb090_alpha_dummy_350 h)), ((nb090_alpha_dummy_345 A), (nb090_alpha_dummy_347 h)), ((nb090_alpha_dummy_346 A), (nb090_alpha_dummy_348 h)), ((nb090_alpha_dummy_338 A), (nb090_alpha_dummy_340 h)), ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)), ((nb090_alpha_dummy_343 A), (nb090_alpha_dummy_344 h)), ((nb090_alpha_dummy_341 A), (nb090_alpha_dummy_342 h)), ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)), ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)), ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)), ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_353 A) (nb090_alpha_dummy_356 h) (nb090_wpp_notmem_0890 A) (nb090_wpp_notmem_0891 h) (TEnvFresh.consFresh (nb090_alpha_dummy_352 A) (nb090_alpha_dummy_355 h) (nb090_wpp_notmem_0892 A) (nb090_wpp_notmem_0893 h) (TEnvFresh.consFresh (nb090_alpha_dummy_351 A) (nb090_alpha_dummy_354 h) (nb090_wpp_notmem_0894 A) (nb090_wpp_notmem_0895 h) (TEnvFresh.consFresh (nb090_alpha_dummy_349 A) (nb090_alpha_dummy_350 h) (nb090_wpp_notmem_0896 A) (nb090_wpp_notmem_0897 h) (TEnvFresh.consFresh (nb090_alpha_dummy_345 A) (nb090_alpha_dummy_347 h) (nb090_wpp_notmem_0898 A) (nb090_wpp_notmem_0899 h) (TEnvFresh.consFresh (nb090_alpha_dummy_346 A) (nb090_alpha_dummy_348 h) (nb090_wpp_notmem_0900 A) (nb090_wpp_notmem_0901 h) (TEnvFresh.consFresh (nb090_alpha_dummy_338 A) (nb090_alpha_dummy_340 h) (nb090_wpp_notmem_0902 A) (nb090_wpp_notmem_0903 h) (TEnvFresh.consFresh (nb090_alpha_dummy_337 A) (nb090_alpha_dummy_339 h) (nb090_wpp_notmem_0904 A) (nb090_wpp_notmem_0905 h) (TEnvFresh.consFresh (nb090_alpha_dummy_343 A) (nb090_alpha_dummy_344 h) (nb090_wpp_notmem_0906 A) (nb090_wpp_notmem_0907 h) (TEnvFresh.consFresh (nb090_alpha_dummy_341 A) (nb090_alpha_dummy_342 h) (nb090_wpp_notmem_0908 A) (nb090_wpp_notmem_0909 h) (TEnvFresh.consFresh (nb090_alpha_dummy_334 A) (nb090_alpha_dummy_336 h) (nb090_wpp_notmem_0910 A) (nb090_wpp_notmem_0911 h) (TEnvFresh.consFresh (nb090_alpha_dummy_333 A) (nb090_alpha_dummy_335 h) (nb090_wpp_notmem_0912 A) (nb090_wpp_notmem_0913 h) (TEnvFresh.consFresh (nb090_alpha_dummy_331 A) (nb090_alpha_dummy_332 v h) (nb090_wpp_notmem_0914 A) (nb090_wpp_notmem_0915 v h) (TEnvFresh.consFresh (nb090_alpha_dummy_329 A) (nb090_alpha_dummy_330 v h) (nb090_wpp_notmem_0916 A) (nb090_wpp_notmem_0917 v h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0174 A) (nb090_wpp_notmem_0175 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0046 A) (nb090_wpp_notmem_0047 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0048 A) (nb090_wpp_notmem_0049 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0050 A) (nb090_wpp_notmem_0051 v u A h) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))

noncomputable def nb090_wpp_refl_0111 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_353 A), (nb090_alpha_dummy_356 h)), ((nb090_alpha_dummy_352 A), (nb090_alpha_dummy_355 h)), ((nb090_alpha_dummy_351 A), (nb090_alpha_dummy_354 h)), ((nb090_alpha_dummy_349 A), (nb090_alpha_dummy_350 h)), ((nb090_alpha_dummy_345 A), (nb090_alpha_dummy_347 h)), ((nb090_alpha_dummy_346 A), (nb090_alpha_dummy_348 h)), ((nb090_alpha_dummy_338 A), (nb090_alpha_dummy_340 h)), ((nb090_alpha_dummy_337 A), (nb090_alpha_dummy_339 h)), ((nb090_alpha_dummy_343 A), (nb090_alpha_dummy_344 h)), ((nb090_alpha_dummy_341 A), (nb090_alpha_dummy_342 h)), ((nb090_alpha_dummy_334 A), (nb090_alpha_dummy_336 h)), ((nb090_alpha_dummy_333 A), (nb090_alpha_dummy_335 h)), ((nb090_alpha_dummy_331 A), (nb090_alpha_dummy_332 v h)), ((nb090_alpha_dummy_329 A), (nb090_alpha_dummy_330 v h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0111 v u A h)

theorem nb090_wpp_notmem_0918 (A : Class) : (nb090_alpha_dummy_349 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_349, fv_syn_cnnc] using (nb090_compact_fv_empty_0260 A)

theorem nb090_wpp_notmem_0919 (h : Var) : (nb090_alpha_dummy_350 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_350, fv_syn_cnnc] using (nb090_compact_fv_empty_0261 h)

theorem nb090_wpp_notmem_0920 (A : Class) : (nb090_alpha_dummy_345 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_345, fv_syn_cnnc] using (nb090_compact_fv_empty_0262 A)

theorem nb090_wpp_notmem_0921 (h : Var) : (nb090_alpha_dummy_347 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_347, fv_syn_cnnc] using (nb090_compact_fv_empty_0263 h)

theorem nb090_wpp_notmem_0922 (A : Class) : (nb090_alpha_dummy_346 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_346, fv_syn_cnnc] using (nb090_compact_fv_empty_0264 A)

theorem nb090_wpp_notmem_0923 (h : Var) : (nb090_alpha_dummy_348 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_348, fv_syn_cnnc] using (nb090_compact_fv_empty_0265 h)

theorem nb090_wpp_notmem_0924 (A : Class) : (nb090_alpha_dummy_338 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_338, fv_syn_cnnc] using (nb090_compact_fv_empty_0266 A)

theorem nb090_wpp_notmem_0925 (h : Var) : (nb090_alpha_dummy_340 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_340, fv_syn_cnnc] using (nb090_compact_fv_empty_0267 h)

theorem nb090_wpp_notmem_0926 (A : Class) : (nb090_alpha_dummy_337 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_337, fv_syn_cnnc] using (nb090_compact_fv_empty_0268 A)

theorem nb090_wpp_notmem_0927 (h : Var) : (nb090_alpha_dummy_339 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_339, fv_syn_cnnc] using (nb090_compact_fv_empty_0269 h)

theorem nb090_wpp_notmem_0928 (A : Class) : (nb090_alpha_dummy_343 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_343, fv_syn_cnnc] using (nb090_compact_fv_empty_0270 A)

theorem nb090_wpp_notmem_0929 (h : Var) : (nb090_alpha_dummy_344 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_344, fv_syn_cnnc] using (nb090_compact_fv_empty_0271 h)

theorem nb090_wpp_notmem_0930 (A : Class) : (nb090_alpha_dummy_341 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_341, fv_syn_cnnc] using (nb090_compact_fv_empty_0272 A)

theorem nb090_wpp_notmem_0931 (h : Var) : (nb090_alpha_dummy_342 h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_342, fv_syn_cnnc] using (nb090_compact_fv_empty_0273 h)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
