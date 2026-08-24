import NAR4C090C001Part104

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

noncomputable def nb090_split_alpha_0083 (v : Var) (u : Var) (A : Class) (h : Var) : TAlphaWff [((nb090_alpha_dummy_325 A), (nb090_alpha_dummy_326 u)), ((nb090_alpha_dummy_323 A), (nb090_alpha_dummy_324 u)), ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)), ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_321 A), (nb090_alpha_dummy_322 u)), ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)), ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_325 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))) (Wff.neg (Wff.classMem (Class.cv (nb090_alpha_dummy_325 A)) (syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))))) (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_326 u)) (syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))) (Wff.neg (Wff.classMem (Class.cv (nb090_alpha_dummy_326 u)) (syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0304 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0305 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0304 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0305 u) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0334 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0335 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0332 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0333 u) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_292 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_294 u))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0308 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0309 u) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0308 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0309 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0306 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0307 u) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_307 A), (nb090_alpha_dummy_310 u)), ((nb090_alpha_dummy_306 A), (nb090_alpha_dummy_309 u)), ((nb090_alpha_dummy_305 A), (nb090_alpha_dummy_308 u)), ((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)), ((nb090_alpha_dummy_299 A), (nb090_alpha_dummy_301 u)), ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)), ((nb090_alpha_dummy_325 A), (nb090_alpha_dummy_326 u)), ((nb090_alpha_dummy_323 A), (nb090_alpha_dummy_324 u)), ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)), ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_321 A), (nb090_alpha_dummy_322 u)), ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)), ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (nb090_wpp_refl_0279 v u A h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0312 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0313 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0310 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0311 u) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0316 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0317 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0314 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0315 u) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0312 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0313 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0310 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0311 u) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0316 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0317 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0314 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0315 u) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_307 A), (nb090_alpha_dummy_310 u)), ((nb090_alpha_dummy_306 A), (nb090_alpha_dummy_309 u)), ((nb090_alpha_dummy_305 A), (nb090_alpha_dummy_308 u)), ((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)), ((nb090_alpha_dummy_299 A), (nb090_alpha_dummy_301 u)), ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)), ((nb090_alpha_dummy_325 A), (nb090_alpha_dummy_326 u)), ((nb090_alpha_dummy_323 A), (nb090_alpha_dummy_324 u)), ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)), ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_321 A), (nb090_alpha_dummy_322 u)), ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)), ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c0) (nb090_wpp_refl_0280 v u A h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0320 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0321 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0318 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0319 u) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0320 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0321 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0318 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0319 u) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0324 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0325 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0322 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0323 u) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0324 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0325 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0322 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0323 u) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0306 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0307 u) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)), ((nb090_alpha_dummy_299 A), (nb090_alpha_dummy_301 u)), ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)), ((nb090_alpha_dummy_325 A), (nb090_alpha_dummy_326 u)), ((nb090_alpha_dummy_323 A), (nb090_alpha_dummy_324 u)), ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)), ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_321 A), (nb090_alpha_dummy_322 u)), ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)), ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0281 v u A h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0306 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0307 u) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0306 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0307 u) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)), ((nb090_alpha_dummy_299 A), (nb090_alpha_dummy_301 u)), ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)), ((nb090_alpha_dummy_325 A), (nb090_alpha_dummy_326 u)), ((nb090_alpha_dummy_323 A), (nb090_alpha_dummy_324 u)), ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)), ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_321 A), (nb090_alpha_dummy_322 u)), ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)), ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0281 v u A h)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0304 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0305 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0304 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0305 u) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0334 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0335 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0332 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0333 u) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_292 A))).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_294 u))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0308 A) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0309 u) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0308 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0309 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0306 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0307 u) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_307 A), (nb090_alpha_dummy_310 u)), ((nb090_alpha_dummy_306 A), (nb090_alpha_dummy_309 u)), ((nb090_alpha_dummy_305 A), (nb090_alpha_dummy_308 u)), ((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)), ((nb090_alpha_dummy_299 A), (nb090_alpha_dummy_301 u)), ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)), ((nb090_alpha_dummy_325 A), (nb090_alpha_dummy_326 u)), ((nb090_alpha_dummy_323 A), (nb090_alpha_dummy_324 u)), ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)), ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_321 A), (nb090_alpha_dummy_322 u)), ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)), ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (nb090_wpp_refl_0279 v u A h))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0312 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0313 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0310 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0311 u) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0316 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0317 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0314 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0315 u) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0312 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0313 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0310 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0311 u) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0316 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0317 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0314 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0315 u) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_307 A), (nb090_alpha_dummy_310 u)), ((nb090_alpha_dummy_306 A), (nb090_alpha_dummy_309 u)), ((nb090_alpha_dummy_305 A), (nb090_alpha_dummy_308 u)), ((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)), ((nb090_alpha_dummy_299 A), (nb090_alpha_dummy_301 u)), ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)), ((nb090_alpha_dummy_325 A), (nb090_alpha_dummy_326 u)), ((nb090_alpha_dummy_323 A), (nb090_alpha_dummy_324 u)), ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)), ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_321 A), (nb090_alpha_dummy_322 u)), ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)), ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c0) (nb090_wpp_refl_0280 v u A h))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0320 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0321 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0318 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0319 u) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0320 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0321 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0318 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0319 u) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0324 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0325 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0322 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0323 u) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0324 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0325 u) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0322 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0323 u) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0306 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0307 u) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)), ((nb090_alpha_dummy_299 A), (nb090_alpha_dummy_301 u)), ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)), ((nb090_alpha_dummy_325 A), (nb090_alpha_dummy_326 u)), ((nb090_alpha_dummy_323 A), (nb090_alpha_dummy_324 u)), ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)), ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_321 A), (nb090_alpha_dummy_322 u)), ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)), ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0281 v u A h))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0306 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0307 u) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0306 A) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0307 u) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb090_alpha_dummy_303 A), (nb090_alpha_dummy_304 u)), ((nb090_alpha_dummy_299 A), (nb090_alpha_dummy_301 u)), ((nb090_alpha_dummy_300 A), (nb090_alpha_dummy_302 u)), ((nb090_alpha_dummy_325 A), (nb090_alpha_dummy_326 u)), ((nb090_alpha_dummy_323 A), (nb090_alpha_dummy_324 u)), ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)), ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_321 A), (nb090_alpha_dummy_322 u)), ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)), ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc) (nb090_wpp_refl_0281 v u A h))))))))))))))))))))

theorem nb090_wpp_notmem_1604 (A : Class) : (nb090_alpha_dummy_042 A) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_042, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0464 A)

theorem nb090_wpp_notmem_1605 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_044 v u h) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb090_alpha_dummy_044, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb090_compact_fv_empty_0465 v u h)

theorem nb090_compact_envfresh_0282 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_323 A), (nb090_alpha_dummy_324 u)), ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)), ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_321 A), (nb090_alpha_dummy_322 u)), ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)), ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_323 A) (nb090_alpha_dummy_324 u) (nb090_wpp_notmem_0820 A) (nb090_wpp_notmem_0821 u) (TEnvFresh.consFresh (nb090_alpha_dummy_292 A) (nb090_alpha_dummy_294 u) (nb090_wpp_notmem_0822 A) (nb090_wpp_notmem_0823 u) (TEnvFresh.consFresh (nb090_alpha_dummy_291 A) (nb090_alpha_dummy_293 u) (nb090_wpp_notmem_0824 A) (nb090_wpp_notmem_0825 u) (TEnvFresh.consFresh (nb090_alpha_dummy_321 A) (nb090_alpha_dummy_322 u) (nb090_wpp_notmem_0826 A) (nb090_wpp_notmem_0827 u) (TEnvFresh.consFresh (nb090_alpha_dummy_295 A) (nb090_alpha_dummy_296 u) (nb090_wpp_notmem_0828 A) (nb090_wpp_notmem_0829 u) (TEnvFresh.consFresh (nb090_alpha_dummy_283 A) (nb090_alpha_dummy_284 u) (nb090_wpp_notmem_0830 A) (nb090_wpp_notmem_0831 u) (TEnvFresh.consFresh (nb090_alpha_dummy_285 A) (nb090_alpha_dummy_286 u) (nb090_wpp_notmem_0832 A) (nb090_wpp_notmem_0833 u) (TEnvFresh.consFresh (nb090_alpha_dummy_288 A) (nb090_alpha_dummy_290 u) (nb090_wpp_notmem_0834 A) (nb090_wpp_notmem_0835 u) (TEnvFresh.consFresh (nb090_alpha_dummy_287 A) (nb090_alpha_dummy_289 u) (nb090_wpp_notmem_0836 A) (nb090_wpp_notmem_0837 u) (TEnvFresh.consFresh (nb090_alpha_dummy_042 A) (nb090_alpha_dummy_044 v u h) (nb090_wpp_notmem_1604 A) (nb090_wpp_notmem_1605 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_041 A) (nb090_alpha_dummy_043 v u h) (nb090_wpp_notmem_1594 A) (nb090_wpp_notmem_1595 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0240 A) (nb090_wpp_notmem_0241 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0100 A) (nb090_wpp_notmem_0101 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0102 A) (nb090_wpp_notmem_0103 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0104 A) (nb090_wpp_notmem_0105 v u A h) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))))))))))

noncomputable def nb090_wpp_refl_0282 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_323 A), (nb090_alpha_dummy_324 u)), ((nb090_alpha_dummy_292 A), (nb090_alpha_dummy_294 u)), ((nb090_alpha_dummy_291 A), (nb090_alpha_dummy_293 u)), ((nb090_alpha_dummy_321 A), (nb090_alpha_dummy_322 u)), ((nb090_alpha_dummy_295 A), (nb090_alpha_dummy_296 u)), ((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0282 v u A h)

theorem nb090_wpp_notmem_1606 (A : Class) : (nb090_alpha_dummy_042 A) ∉ ((syn_c2nd)).fv := by
  simpa only [nb090_alpha_dummy_042, fv_syn_c2nd] using (nb090_compact_fv_empty_0464 A)

theorem nb090_wpp_notmem_1607 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_044 v u h) ∉ ((syn_c2nd)).fv := by
  simpa only [nb090_alpha_dummy_044, fv_syn_c2nd] using (nb090_compact_fv_empty_0465 v u h)

theorem nb090_compact_envfresh_0283 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c2nd)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_283 A) (nb090_alpha_dummy_284 u) (nb090_wpp_notmem_0838 A) (nb090_wpp_notmem_0839 u) (TEnvFresh.consFresh (nb090_alpha_dummy_285 A) (nb090_alpha_dummy_286 u) (nb090_wpp_notmem_0840 A) (nb090_wpp_notmem_0841 u) (TEnvFresh.consFresh (nb090_alpha_dummy_288 A) (nb090_alpha_dummy_290 u) (nb090_wpp_notmem_0842 A) (nb090_wpp_notmem_0843 u) (TEnvFresh.consFresh (nb090_alpha_dummy_287 A) (nb090_alpha_dummy_289 u) (nb090_wpp_notmem_0844 A) (nb090_wpp_notmem_0845 u) (TEnvFresh.consFresh (nb090_alpha_dummy_042 A) (nb090_alpha_dummy_044 v u h) (nb090_wpp_notmem_1606 A) (nb090_wpp_notmem_1607 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_041 A) (nb090_alpha_dummy_043 v u h) (nb090_wpp_notmem_1596 A) (nb090_wpp_notmem_1597 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0846 A) (nb090_wpp_notmem_0847 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0848 A) (nb090_wpp_notmem_0849 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0850 A) (nb090_wpp_notmem_0851 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0852 A) (nb090_wpp_notmem_0853 v u A h) (TEnvFresh.nil ((syn_c2nd)).fv)))))))))))

noncomputable def nb090_wpp_refl_0283 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_283 A), (nb090_alpha_dummy_284 u)), ((nb090_alpha_dummy_285 A), (nb090_alpha_dummy_286 u)), ((nb090_alpha_dummy_288 A), (nb090_alpha_dummy_290 u)), ((nb090_alpha_dummy_287 A), (nb090_alpha_dummy_289 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c2nd)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0283 v u A h)

theorem nb090_compact_fv_empty_0466 (A : Class) : (nb090_alpha_dummy_633 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1608 (A : Class) : (nb090_alpha_dummy_633 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_633, fv_syn_c1c] using (nb090_compact_fv_empty_0466 A)

theorem nb090_compact_fv_empty_0467 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_636 v u h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1609 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_636 v u h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_636, fv_syn_c1c] using (nb090_compact_fv_empty_0467 v u h)

theorem nb090_compact_fv_empty_0468 (A : Class) : (nb090_alpha_dummy_632 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1610 (A : Class) : (nb090_alpha_dummy_632 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_632, fv_syn_c1c] using (nb090_compact_fv_empty_0468 A)

theorem nb090_compact_fv_empty_0469 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_635 v u h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1611 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_635 v u h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_635, fv_syn_c1c] using (nb090_compact_fv_empty_0469 v u h)

theorem nb090_compact_fv_empty_0470 (A : Class) : (nb090_alpha_dummy_631 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1612 (A : Class) : (nb090_alpha_dummy_631 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_631, fv_syn_c1c] using (nb090_compact_fv_empty_0470 A)

theorem nb090_compact_fv_empty_0471 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_634 v u h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1613 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_634 v u h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_634, fv_syn_c1c] using (nb090_compact_fv_empty_0471 v u h)

theorem nb090_compact_fv_empty_0472 (A : Class) : (nb090_alpha_dummy_629 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1614 (A : Class) : (nb090_alpha_dummy_629 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_629, fv_syn_c1c] using (nb090_compact_fv_empty_0472 A)

theorem nb090_compact_fv_empty_0473 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_630 v u h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1615 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_630 v u h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_630, fv_syn_c1c] using (nb090_compact_fv_empty_0473 v u h)

theorem nb090_compact_fv_empty_0474 (A : Class) : (nb090_alpha_dummy_625 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1616 (A : Class) : (nb090_alpha_dummy_625 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_625, fv_syn_c1c] using (nb090_compact_fv_empty_0474 A)

theorem nb090_compact_fv_empty_0475 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_627 v u h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1617 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_627 v u h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_627, fv_syn_c1c] using (nb090_compact_fv_empty_0475 v u h)

theorem nb090_compact_fv_empty_0476 (A : Class) : (nb090_alpha_dummy_626 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1618 (A : Class) : (nb090_alpha_dummy_626 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_626, fv_syn_c1c] using (nb090_compact_fv_empty_0476 A)

theorem nb090_compact_fv_empty_0477 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_628 v u h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1619 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_628 v u h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_628, fv_syn_c1c] using (nb090_compact_fv_empty_0477 v u h)

theorem nb090_compact_fv_empty_0478 (A : Class) : (nb090_alpha_dummy_618 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1620 (A : Class) : (nb090_alpha_dummy_618 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_618, fv_syn_c1c] using (nb090_compact_fv_empty_0478 A)

theorem nb090_compact_fv_empty_0479 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_620 v u h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1621 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_620 v u h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_620, fv_syn_c1c] using (nb090_compact_fv_empty_0479 v u h)

theorem nb090_compact_fv_empty_0480 (A : Class) : (nb090_alpha_dummy_617 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1622 (A : Class) : (nb090_alpha_dummy_617 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_617, fv_syn_c1c] using (nb090_compact_fv_empty_0480 A)

theorem nb090_compact_fv_empty_0481 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_619 v u h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1623 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_619 v u h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_619, fv_syn_c1c] using (nb090_compact_fv_empty_0481 v u h)

theorem nb090_compact_fv_empty_0482 (A : Class) : (nb090_alpha_dummy_623 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1624 (A : Class) : (nb090_alpha_dummy_623 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_623, fv_syn_c1c] using (nb090_compact_fv_empty_0482 A)

theorem nb090_compact_fv_empty_0483 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_624 v u h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1625 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_624 v u h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_624, fv_syn_c1c] using (nb090_compact_fv_empty_0483 v u h)

theorem nb090_compact_fv_empty_0484 (A : Class) : (nb090_alpha_dummy_621 A) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1626 (A : Class) : (nb090_alpha_dummy_621 A) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_621, fv_syn_c1c] using (nb090_compact_fv_empty_0484 A)

theorem nb090_compact_fv_empty_0485 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_622 v u h) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb090_wpp_notmem_1627 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_622 v u h) ∉ ((syn_c1c)).fv := by
  simpa only [nb090_alpha_dummy_622, fv_syn_c1c] using (nb090_compact_fv_empty_0485 v u h)

theorem nb090_compact_envfresh_0284 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_633 A), (nb090_alpha_dummy_636 v u h)), ((nb090_alpha_dummy_632 A), (nb090_alpha_dummy_635 v u h)), ((nb090_alpha_dummy_631 A), (nb090_alpha_dummy_634 v u h)), ((nb090_alpha_dummy_629 A), (nb090_alpha_dummy_630 v u h)), ((nb090_alpha_dummy_625 A), (nb090_alpha_dummy_627 v u h)), ((nb090_alpha_dummy_626 A), (nb090_alpha_dummy_628 v u h)), ((nb090_alpha_dummy_618 A), (nb090_alpha_dummy_620 v u h)), ((nb090_alpha_dummy_617 A), (nb090_alpha_dummy_619 v u h)), ((nb090_alpha_dummy_623 A), (nb090_alpha_dummy_624 v u h)), ((nb090_alpha_dummy_621 A), (nb090_alpha_dummy_622 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_633 A) (nb090_alpha_dummy_636 v u h) (nb090_wpp_notmem_1608 A) (nb090_wpp_notmem_1609 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_632 A) (nb090_alpha_dummy_635 v u h) (nb090_wpp_notmem_1610 A) (nb090_wpp_notmem_1611 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_631 A) (nb090_alpha_dummy_634 v u h) (nb090_wpp_notmem_1612 A) (nb090_wpp_notmem_1613 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_629 A) (nb090_alpha_dummy_630 v u h) (nb090_wpp_notmem_1614 A) (nb090_wpp_notmem_1615 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_625 A) (nb090_alpha_dummy_627 v u h) (nb090_wpp_notmem_1616 A) (nb090_wpp_notmem_1617 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_626 A) (nb090_alpha_dummy_628 v u h) (nb090_wpp_notmem_1618 A) (nb090_wpp_notmem_1619 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_618 A) (nb090_alpha_dummy_620 v u h) (nb090_wpp_notmem_1620 A) (nb090_wpp_notmem_1621 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_617 A) (nb090_alpha_dummy_619 v u h) (nb090_wpp_notmem_1622 A) (nb090_wpp_notmem_1623 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_623 A) (nb090_alpha_dummy_624 v u h) (nb090_wpp_notmem_1624 A) (nb090_wpp_notmem_1625 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_621 A) (nb090_alpha_dummy_622 v u h) (nb090_wpp_notmem_1626 A) (nb090_wpp_notmem_1627 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_042 A) (nb090_alpha_dummy_044 v u h) (nb090_wpp_notmem_1598 A) (nb090_wpp_notmem_1599 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_041 A) (nb090_alpha_dummy_043 v u h) (nb090_wpp_notmem_1588 A) (nb090_wpp_notmem_1589 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0142 A) (nb090_wpp_notmem_0143 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0020 A) (nb090_wpp_notmem_0021 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0022 A) (nb090_wpp_notmem_0023 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0024 A) (nb090_wpp_notmem_0025 v u A h) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))

noncomputable def nb090_wpp_refl_0284 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_633 A), (nb090_alpha_dummy_636 v u h)), ((nb090_alpha_dummy_632 A), (nb090_alpha_dummy_635 v u h)), ((nb090_alpha_dummy_631 A), (nb090_alpha_dummy_634 v u h)), ((nb090_alpha_dummy_629 A), (nb090_alpha_dummy_630 v u h)), ((nb090_alpha_dummy_625 A), (nb090_alpha_dummy_627 v u h)), ((nb090_alpha_dummy_626 A), (nb090_alpha_dummy_628 v u h)), ((nb090_alpha_dummy_618 A), (nb090_alpha_dummy_620 v u h)), ((nb090_alpha_dummy_617 A), (nb090_alpha_dummy_619 v u h)), ((nb090_alpha_dummy_623 A), (nb090_alpha_dummy_624 v u h)), ((nb090_alpha_dummy_621 A), (nb090_alpha_dummy_622 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0284 v u A h)

theorem nb090_wpp_notmem_1628 (A : Class) : (nb090_alpha_dummy_633 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_633, fv_syn_c0] using (nb090_compact_fv_empty_0466 A)

theorem nb090_wpp_notmem_1629 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_636 v u h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_636, fv_syn_c0] using (nb090_compact_fv_empty_0467 v u h)

theorem nb090_wpp_notmem_1630 (A : Class) : (nb090_alpha_dummy_632 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_632, fv_syn_c0] using (nb090_compact_fv_empty_0468 A)

theorem nb090_wpp_notmem_1631 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_635 v u h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_635, fv_syn_c0] using (nb090_compact_fv_empty_0469 v u h)

theorem nb090_wpp_notmem_1632 (A : Class) : (nb090_alpha_dummy_631 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_631, fv_syn_c0] using (nb090_compact_fv_empty_0470 A)

theorem nb090_wpp_notmem_1633 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_634 v u h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_634, fv_syn_c0] using (nb090_compact_fv_empty_0471 v u h)

theorem nb090_wpp_notmem_1634 (A : Class) : (nb090_alpha_dummy_629 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_629, fv_syn_c0] using (nb090_compact_fv_empty_0472 A)

theorem nb090_wpp_notmem_1635 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_630 v u h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_630, fv_syn_c0] using (nb090_compact_fv_empty_0473 v u h)

theorem nb090_wpp_notmem_1636 (A : Class) : (nb090_alpha_dummy_625 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_625, fv_syn_c0] using (nb090_compact_fv_empty_0474 A)

theorem nb090_wpp_notmem_1637 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_627 v u h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_627, fv_syn_c0] using (nb090_compact_fv_empty_0475 v u h)

theorem nb090_wpp_notmem_1638 (A : Class) : (nb090_alpha_dummy_626 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_626, fv_syn_c0] using (nb090_compact_fv_empty_0476 A)

theorem nb090_wpp_notmem_1639 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_628 v u h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_628, fv_syn_c0] using (nb090_compact_fv_empty_0477 v u h)

theorem nb090_wpp_notmem_1640 (A : Class) : (nb090_alpha_dummy_618 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_618, fv_syn_c0] using (nb090_compact_fv_empty_0478 A)

theorem nb090_wpp_notmem_1641 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_620 v u h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_620, fv_syn_c0] using (nb090_compact_fv_empty_0479 v u h)

theorem nb090_wpp_notmem_1642 (A : Class) : (nb090_alpha_dummy_617 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_617, fv_syn_c0] using (nb090_compact_fv_empty_0480 A)

theorem nb090_wpp_notmem_1643 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_619 v u h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_619, fv_syn_c0] using (nb090_compact_fv_empty_0481 v u h)

theorem nb090_wpp_notmem_1644 (A : Class) : (nb090_alpha_dummy_623 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_623, fv_syn_c0] using (nb090_compact_fv_empty_0482 A)

theorem nb090_wpp_notmem_1645 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_624 v u h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_624, fv_syn_c0] using (nb090_compact_fv_empty_0483 v u h)

theorem nb090_wpp_notmem_1646 (A : Class) : (nb090_alpha_dummy_621 A) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_621, fv_syn_c0] using (nb090_compact_fv_empty_0484 A)

theorem nb090_wpp_notmem_1647 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_622 v u h) ∉ ((syn_c0)).fv := by
  simpa only [nb090_alpha_dummy_622, fv_syn_c0] using (nb090_compact_fv_empty_0485 v u h)

theorem nb090_compact_envfresh_0285 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_633 A), (nb090_alpha_dummy_636 v u h)), ((nb090_alpha_dummy_632 A), (nb090_alpha_dummy_635 v u h)), ((nb090_alpha_dummy_631 A), (nb090_alpha_dummy_634 v u h)), ((nb090_alpha_dummy_629 A), (nb090_alpha_dummy_630 v u h)), ((nb090_alpha_dummy_625 A), (nb090_alpha_dummy_627 v u h)), ((nb090_alpha_dummy_626 A), (nb090_alpha_dummy_628 v u h)), ((nb090_alpha_dummy_618 A), (nb090_alpha_dummy_620 v u h)), ((nb090_alpha_dummy_617 A), (nb090_alpha_dummy_619 v u h)), ((nb090_alpha_dummy_623 A), (nb090_alpha_dummy_624 v u h)), ((nb090_alpha_dummy_621 A), (nb090_alpha_dummy_622 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_633 A) (nb090_alpha_dummy_636 v u h) (nb090_wpp_notmem_1628 A) (nb090_wpp_notmem_1629 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_632 A) (nb090_alpha_dummy_635 v u h) (nb090_wpp_notmem_1630 A) (nb090_wpp_notmem_1631 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_631 A) (nb090_alpha_dummy_634 v u h) (nb090_wpp_notmem_1632 A) (nb090_wpp_notmem_1633 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_629 A) (nb090_alpha_dummy_630 v u h) (nb090_wpp_notmem_1634 A) (nb090_wpp_notmem_1635 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_625 A) (nb090_alpha_dummy_627 v u h) (nb090_wpp_notmem_1636 A) (nb090_wpp_notmem_1637 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_626 A) (nb090_alpha_dummy_628 v u h) (nb090_wpp_notmem_1638 A) (nb090_wpp_notmem_1639 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_618 A) (nb090_alpha_dummy_620 v u h) (nb090_wpp_notmem_1640 A) (nb090_wpp_notmem_1641 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_617 A) (nb090_alpha_dummy_619 v u h) (nb090_wpp_notmem_1642 A) (nb090_wpp_notmem_1643 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_623 A) (nb090_alpha_dummy_624 v u h) (nb090_wpp_notmem_1644 A) (nb090_wpp_notmem_1645 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_621 A) (nb090_alpha_dummy_622 v u h) (nb090_wpp_notmem_1646 A) (nb090_wpp_notmem_1647 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_042 A) (nb090_alpha_dummy_044 v u h) (nb090_wpp_notmem_1600 A) (nb090_wpp_notmem_1601 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_041 A) (nb090_alpha_dummy_043 v u h) (nb090_wpp_notmem_1590 A) (nb090_wpp_notmem_1591 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0174 A) (nb090_wpp_notmem_0175 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0046 A) (nb090_wpp_notmem_0047 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0048 A) (nb090_wpp_notmem_0049 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0050 A) (nb090_wpp_notmem_0051 v u A h) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))

noncomputable def nb090_wpp_refl_0285 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_633 A), (nb090_alpha_dummy_636 v u h)), ((nb090_alpha_dummy_632 A), (nb090_alpha_dummy_635 v u h)), ((nb090_alpha_dummy_631 A), (nb090_alpha_dummy_634 v u h)), ((nb090_alpha_dummy_629 A), (nb090_alpha_dummy_630 v u h)), ((nb090_alpha_dummy_625 A), (nb090_alpha_dummy_627 v u h)), ((nb090_alpha_dummy_626 A), (nb090_alpha_dummy_628 v u h)), ((nb090_alpha_dummy_618 A), (nb090_alpha_dummy_620 v u h)), ((nb090_alpha_dummy_617 A), (nb090_alpha_dummy_619 v u h)), ((nb090_alpha_dummy_623 A), (nb090_alpha_dummy_624 v u h)), ((nb090_alpha_dummy_621 A), (nb090_alpha_dummy_622 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0285 v u A h)

theorem nb090_wpp_notmem_1648 (A : Class) : (nb090_alpha_dummy_629 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_629, fv_syn_cnnc] using (nb090_compact_fv_empty_0472 A)

theorem nb090_wpp_notmem_1649 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_630 v u h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_630, fv_syn_cnnc] using (nb090_compact_fv_empty_0473 v u h)

theorem nb090_wpp_notmem_1650 (A : Class) : (nb090_alpha_dummy_625 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_625, fv_syn_cnnc] using (nb090_compact_fv_empty_0474 A)

theorem nb090_wpp_notmem_1651 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_627 v u h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_627, fv_syn_cnnc] using (nb090_compact_fv_empty_0475 v u h)

theorem nb090_wpp_notmem_1652 (A : Class) : (nb090_alpha_dummy_626 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_626, fv_syn_cnnc] using (nb090_compact_fv_empty_0476 A)

theorem nb090_wpp_notmem_1653 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_628 v u h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_628, fv_syn_cnnc] using (nb090_compact_fv_empty_0477 v u h)

theorem nb090_wpp_notmem_1654 (A : Class) : (nb090_alpha_dummy_618 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_618, fv_syn_cnnc] using (nb090_compact_fv_empty_0478 A)

theorem nb090_wpp_notmem_1655 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_620 v u h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_620, fv_syn_cnnc] using (nb090_compact_fv_empty_0479 v u h)

theorem nb090_wpp_notmem_1656 (A : Class) : (nb090_alpha_dummy_617 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_617, fv_syn_cnnc] using (nb090_compact_fv_empty_0480 A)

theorem nb090_wpp_notmem_1657 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_619 v u h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_619, fv_syn_cnnc] using (nb090_compact_fv_empty_0481 v u h)

theorem nb090_wpp_notmem_1658 (A : Class) : (nb090_alpha_dummy_623 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_623, fv_syn_cnnc] using (nb090_compact_fv_empty_0482 A)

theorem nb090_wpp_notmem_1659 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_624 v u h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_624, fv_syn_cnnc] using (nb090_compact_fv_empty_0483 v u h)

theorem nb090_wpp_notmem_1660 (A : Class) : (nb090_alpha_dummy_621 A) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_621, fv_syn_cnnc] using (nb090_compact_fv_empty_0484 A)

theorem nb090_wpp_notmem_1661 (v : Var) (u : Var) (h : Var) : (nb090_alpha_dummy_622 v u h) ∉ ((syn_cnnc)).fv := by
  simpa only [nb090_alpha_dummy_622, fv_syn_cnnc] using (nb090_compact_fv_empty_0485 v u h)

theorem nb090_compact_envfresh_0286 (v : Var) (u : Var) (A : Class) (h : Var) : TEnvFresh [((nb090_alpha_dummy_629 A), (nb090_alpha_dummy_630 v u h)), ((nb090_alpha_dummy_625 A), (nb090_alpha_dummy_627 v u h)), ((nb090_alpha_dummy_626 A), (nb090_alpha_dummy_628 v u h)), ((nb090_alpha_dummy_618 A), (nb090_alpha_dummy_620 v u h)), ((nb090_alpha_dummy_617 A), (nb090_alpha_dummy_619 v u h)), ((nb090_alpha_dummy_623 A), (nb090_alpha_dummy_624 v u h)), ((nb090_alpha_dummy_621 A), (nb090_alpha_dummy_622 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb090_alpha_dummy_629 A) (nb090_alpha_dummy_630 v u h) (nb090_wpp_notmem_1648 A) (nb090_wpp_notmem_1649 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_625 A) (nb090_alpha_dummy_627 v u h) (nb090_wpp_notmem_1650 A) (nb090_wpp_notmem_1651 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_626 A) (nb090_alpha_dummy_628 v u h) (nb090_wpp_notmem_1652 A) (nb090_wpp_notmem_1653 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_618 A) (nb090_alpha_dummy_620 v u h) (nb090_wpp_notmem_1654 A) (nb090_wpp_notmem_1655 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_617 A) (nb090_alpha_dummy_619 v u h) (nb090_wpp_notmem_1656 A) (nb090_wpp_notmem_1657 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_623 A) (nb090_alpha_dummy_624 v u h) (nb090_wpp_notmem_1658 A) (nb090_wpp_notmem_1659 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_621 A) (nb090_alpha_dummy_622 v u h) (nb090_wpp_notmem_1660 A) (nb090_wpp_notmem_1661 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_042 A) (nb090_alpha_dummy_044 v u h) (nb090_wpp_notmem_1602 A) (nb090_wpp_notmem_1603 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_041 A) (nb090_alpha_dummy_043 v u h) (nb090_wpp_notmem_1592 A) (nb090_wpp_notmem_1593 v u h) (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_0200 A) (nb090_wpp_notmem_0201 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v (nb090_wpp_notmem_0066 A) (nb090_wpp_notmem_0067 v) (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u (nb090_wpp_notmem_0068 A) (nb090_wpp_notmem_0069 u) (TEnvFresh.consFresh (nb090_alpha_dummy_003 A) (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_0070 A) (nb090_wpp_notmem_0071 v u A h) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))

noncomputable def nb090_wpp_refl_0286 (v : Var) (u : Var) (A : Class) (h : Var) : TReflOn [((nb090_alpha_dummy_629 A), (nb090_alpha_dummy_630 v u h)), ((nb090_alpha_dummy_625 A), (nb090_alpha_dummy_627 v u h)), ((nb090_alpha_dummy_626 A), (nb090_alpha_dummy_628 v u h)), ((nb090_alpha_dummy_618 A), (nb090_alpha_dummy_620 v u h)), ((nb090_alpha_dummy_617 A), (nb090_alpha_dummy_619 v u h)), ((nb090_alpha_dummy_623 A), (nb090_alpha_dummy_624 v u h)), ((nb090_alpha_dummy_621 A), (nb090_alpha_dummy_622 v u h)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0286 v u A h)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
