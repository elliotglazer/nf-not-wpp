import NAR4C068C001Part035

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

theorem nb068_compact_envfresh_0111 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_299), (nb068_alpha_dummy_300 f)), ((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)), ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)), ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)), ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)), ((nb068_alpha_dummy_293), (nb068_alpha_dummy_294 f)), ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)), ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)), ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_299) (nb068_alpha_dummy_300 f) (nb068_wpp_notmem_0782) (nb068_wpp_notmem_0783 f) (TEnvFresh.consFresh (nb068_alpha_dummy_295) (nb068_alpha_dummy_297 f) (nb068_wpp_notmem_0784) (nb068_wpp_notmem_0785 f) (TEnvFresh.consFresh (nb068_alpha_dummy_296) (nb068_alpha_dummy_298 f) (nb068_wpp_notmem_0786) (nb068_wpp_notmem_0787 f) (TEnvFresh.consFresh (nb068_alpha_dummy_288) (nb068_alpha_dummy_290 f) (nb068_wpp_notmem_0788) (nb068_wpp_notmem_0789 f) (TEnvFresh.consFresh (nb068_alpha_dummy_287) (nb068_alpha_dummy_289 f) (nb068_wpp_notmem_0790) (nb068_wpp_notmem_0791 f) (TEnvFresh.consFresh (nb068_alpha_dummy_293) (nb068_alpha_dummy_294 f) (nb068_wpp_notmem_0792) (nb068_wpp_notmem_0793 f) (TEnvFresh.consFresh (nb068_alpha_dummy_291) (nb068_alpha_dummy_292 f) (nb068_wpp_notmem_0794) (nb068_wpp_notmem_0795 f) (TEnvFresh.consFresh (nb068_alpha_dummy_284) (nb068_alpha_dummy_286 f) (nb068_wpp_notmem_0796) (nb068_wpp_notmem_0797 f) (TEnvFresh.consFresh (nb068_alpha_dummy_283) (nb068_alpha_dummy_285 f) (nb068_wpp_notmem_0798) (nb068_wpp_notmem_0799 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0194) (nb068_wpp_notmem_0195 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0066) (nb068_wpp_notmem_0067 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0068) (nb068_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0070) (nb068_wpp_notmem_0071 x y f) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))

noncomputable def nb068_wpp_refl_0111 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_299), (nb068_alpha_dummy_300 f)), ((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)), ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)), ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)), ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)), ((nb068_alpha_dummy_293), (nb068_alpha_dummy_294 f)), ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)), ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)), ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0111 x y f)

noncomputable def nb068_split_alpha_0085 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)), ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)), ((nb068_alpha_dummy_293), (nb068_alpha_dummy_294 f)), ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)), ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)), ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (Wff.classEq (Class.cv (nb068_alpha_dummy_287)) (syn_cphi (Class.cv (nb068_alpha_dummy_288)))) (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f)) (syn_cphi (Class.cv (nb068_alpha_dummy_290 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_284))).fv ∪ ((Class.cv (nb068_alpha_dummy_283))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_286 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_285 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0298) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0299 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0298) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0299 f) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_288))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_290 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0302) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0303 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0302) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0303 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0300) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0301 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_303), (nb068_alpha_dummy_306 f)), ((nb068_alpha_dummy_302), (nb068_alpha_dummy_305 f)), ((nb068_alpha_dummy_301), (nb068_alpha_dummy_304 f)), ((nb068_alpha_dummy_299), (nb068_alpha_dummy_300 f)), ((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)), ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)), ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)), ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)), ((nb068_alpha_dummy_293), (nb068_alpha_dummy_294 f)), ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)), ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)), ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_c1c) (nb068_wpp_refl_0109 x y f))) (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0084 x y f)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0300) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0301 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_299), (nb068_alpha_dummy_300 f)), ((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)), ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)), ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)), ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)), ((nb068_alpha_dummy_293), (nb068_alpha_dummy_294 f)), ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)), ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)), ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_cnnc) (nb068_wpp_refl_0111 x y f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0300) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0301 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0300) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0301 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_299), (nb068_alpha_dummy_300 f)), ((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)), ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)), ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)), ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)), ((nb068_alpha_dummy_293), (nb068_alpha_dummy_294 f)), ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)), ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)), ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_cnnc) (nb068_wpp_refl_0111 x y f))))))))))))))))))

theorem nb068_compact_envfresh_0112 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_303), (nb068_alpha_dummy_306 f)), ((nb068_alpha_dummy_302), (nb068_alpha_dummy_305 f)), ((nb068_alpha_dummy_301), (nb068_alpha_dummy_304 f)), ((nb068_alpha_dummy_299), (nb068_alpha_dummy_300 f)), ((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)), ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)), ((nb068_alpha_dummy_321), (nb068_alpha_dummy_322 f)), ((nb068_alpha_dummy_319), (nb068_alpha_dummy_320 f)), ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)), ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)), ((nb068_alpha_dummy_317), (nb068_alpha_dummy_318 f)), ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)), ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)), ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_303) (nb068_alpha_dummy_306 f) (nb068_wpp_notmem_0726) (nb068_wpp_notmem_0727 f) (TEnvFresh.consFresh (nb068_alpha_dummy_302) (nb068_alpha_dummy_305 f) (nb068_wpp_notmem_0728) (nb068_wpp_notmem_0729 f) (TEnvFresh.consFresh (nb068_alpha_dummy_301) (nb068_alpha_dummy_304 f) (nb068_wpp_notmem_0730) (nb068_wpp_notmem_0731 f) (TEnvFresh.consFresh (nb068_alpha_dummy_299) (nb068_alpha_dummy_300 f) (nb068_wpp_notmem_0732) (nb068_wpp_notmem_0733 f) (TEnvFresh.consFresh (nb068_alpha_dummy_295) (nb068_alpha_dummy_297 f) (nb068_wpp_notmem_0734) (nb068_wpp_notmem_0735 f) (TEnvFresh.consFresh (nb068_alpha_dummy_296) (nb068_alpha_dummy_298 f) (nb068_wpp_notmem_0736) (nb068_wpp_notmem_0737 f) (TEnvFresh.consFresh (nb068_alpha_dummy_321) (nb068_alpha_dummy_322 f) (nb068_wpp_notmem_0804) (nb068_wpp_notmem_0805 f) (TEnvFresh.consFresh (nb068_alpha_dummy_319) (nb068_alpha_dummy_320 f) (nb068_wpp_notmem_0806) (nb068_wpp_notmem_0807 f) (TEnvFresh.consFresh (nb068_alpha_dummy_288) (nb068_alpha_dummy_290 f) (nb068_wpp_notmem_0738) (nb068_wpp_notmem_0739 f) (TEnvFresh.consFresh (nb068_alpha_dummy_287) (nb068_alpha_dummy_289 f) (nb068_wpp_notmem_0740) (nb068_wpp_notmem_0741 f) (TEnvFresh.consFresh (nb068_alpha_dummy_317) (nb068_alpha_dummy_318 f) (nb068_wpp_notmem_0808) (nb068_wpp_notmem_0809 f) (TEnvFresh.consFresh (nb068_alpha_dummy_291) (nb068_alpha_dummy_292 f) (nb068_wpp_notmem_0744) (nb068_wpp_notmem_0745 f) (TEnvFresh.consFresh (nb068_alpha_dummy_284) (nb068_alpha_dummy_286 f) (nb068_wpp_notmem_0746) (nb068_wpp_notmem_0747 f) (TEnvFresh.consFresh (nb068_alpha_dummy_283) (nb068_alpha_dummy_285 f) (nb068_wpp_notmem_0748) (nb068_wpp_notmem_0749 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0136) (nb068_wpp_notmem_0137 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0020) (nb068_wpp_notmem_0021 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0022) (nb068_wpp_notmem_0023 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0024) (nb068_wpp_notmem_0025 x y f) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))

noncomputable def nb068_wpp_refl_0112 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_303), (nb068_alpha_dummy_306 f)), ((nb068_alpha_dummy_302), (nb068_alpha_dummy_305 f)), ((nb068_alpha_dummy_301), (nb068_alpha_dummy_304 f)), ((nb068_alpha_dummy_299), (nb068_alpha_dummy_300 f)), ((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)), ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)), ((nb068_alpha_dummy_321), (nb068_alpha_dummy_322 f)), ((nb068_alpha_dummy_319), (nb068_alpha_dummy_320 f)), ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)), ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)), ((nb068_alpha_dummy_317), (nb068_alpha_dummy_318 f)), ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)), ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)), ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0112 x y f)

theorem nb068_compact_envfresh_0113 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_303), (nb068_alpha_dummy_306 f)), ((nb068_alpha_dummy_302), (nb068_alpha_dummy_305 f)), ((nb068_alpha_dummy_301), (nb068_alpha_dummy_304 f)), ((nb068_alpha_dummy_299), (nb068_alpha_dummy_300 f)), ((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)), ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)), ((nb068_alpha_dummy_321), (nb068_alpha_dummy_322 f)), ((nb068_alpha_dummy_319), (nb068_alpha_dummy_320 f)), ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)), ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)), ((nb068_alpha_dummy_317), (nb068_alpha_dummy_318 f)), ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)), ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)), ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_303) (nb068_alpha_dummy_306 f) (nb068_wpp_notmem_0754) (nb068_wpp_notmem_0755 f) (TEnvFresh.consFresh (nb068_alpha_dummy_302) (nb068_alpha_dummy_305 f) (nb068_wpp_notmem_0756) (nb068_wpp_notmem_0757 f) (TEnvFresh.consFresh (nb068_alpha_dummy_301) (nb068_alpha_dummy_304 f) (nb068_wpp_notmem_0758) (nb068_wpp_notmem_0759 f) (TEnvFresh.consFresh (nb068_alpha_dummy_299) (nb068_alpha_dummy_300 f) (nb068_wpp_notmem_0760) (nb068_wpp_notmem_0761 f) (TEnvFresh.consFresh (nb068_alpha_dummy_295) (nb068_alpha_dummy_297 f) (nb068_wpp_notmem_0762) (nb068_wpp_notmem_0763 f) (TEnvFresh.consFresh (nb068_alpha_dummy_296) (nb068_alpha_dummy_298 f) (nb068_wpp_notmem_0764) (nb068_wpp_notmem_0765 f) (TEnvFresh.consFresh (nb068_alpha_dummy_321) (nb068_alpha_dummy_322 f) (nb068_wpp_notmem_0810) (nb068_wpp_notmem_0811 f) (TEnvFresh.consFresh (nb068_alpha_dummy_319) (nb068_alpha_dummy_320 f) (nb068_wpp_notmem_0812) (nb068_wpp_notmem_0813 f) (TEnvFresh.consFresh (nb068_alpha_dummy_288) (nb068_alpha_dummy_290 f) (nb068_wpp_notmem_0766) (nb068_wpp_notmem_0767 f) (TEnvFresh.consFresh (nb068_alpha_dummy_287) (nb068_alpha_dummy_289 f) (nb068_wpp_notmem_0768) (nb068_wpp_notmem_0769 f) (TEnvFresh.consFresh (nb068_alpha_dummy_317) (nb068_alpha_dummy_318 f) (nb068_wpp_notmem_0814) (nb068_wpp_notmem_0815 f) (TEnvFresh.consFresh (nb068_alpha_dummy_291) (nb068_alpha_dummy_292 f) (nb068_wpp_notmem_0772) (nb068_wpp_notmem_0773 f) (TEnvFresh.consFresh (nb068_alpha_dummy_284) (nb068_alpha_dummy_286 f) (nb068_wpp_notmem_0774) (nb068_wpp_notmem_0775 f) (TEnvFresh.consFresh (nb068_alpha_dummy_283) (nb068_alpha_dummy_285 f) (nb068_wpp_notmem_0776) (nb068_wpp_notmem_0777 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0168) (nb068_wpp_notmem_0169 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0046) (nb068_wpp_notmem_0047 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0048) (nb068_wpp_notmem_0049 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0050) (nb068_wpp_notmem_0051 x y f) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))

noncomputable def nb068_wpp_refl_0113 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_303), (nb068_alpha_dummy_306 f)), ((nb068_alpha_dummy_302), (nb068_alpha_dummy_305 f)), ((nb068_alpha_dummy_301), (nb068_alpha_dummy_304 f)), ((nb068_alpha_dummy_299), (nb068_alpha_dummy_300 f)), ((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)), ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)), ((nb068_alpha_dummy_321), (nb068_alpha_dummy_322 f)), ((nb068_alpha_dummy_319), (nb068_alpha_dummy_320 f)), ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)), ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)), ((nb068_alpha_dummy_317), (nb068_alpha_dummy_318 f)), ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)), ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)), ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0113 x y f)

noncomputable def nb068_split_alpha_0086 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb068_alpha_dummy_303), (nb068_alpha_dummy_306 f)), ((nb068_alpha_dummy_302), (nb068_alpha_dummy_305 f)), ((nb068_alpha_dummy_301), (nb068_alpha_dummy_304 f)), ((nb068_alpha_dummy_299), (nb068_alpha_dummy_300 f)), ((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)), ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)), ((nb068_alpha_dummy_321), (nb068_alpha_dummy_322 f)), ((nb068_alpha_dummy_319), (nb068_alpha_dummy_320 f)), ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)), ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)), ((nb068_alpha_dummy_317), (nb068_alpha_dummy_318 f)), ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)), ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)), ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_302)) (Class.cv (nb068_alpha_dummy_303))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_301)) (syn_cun (Class.cv (nb068_alpha_dummy_302)) (Class.cv (nb068_alpha_dummy_303)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb068_alpha_dummy_305 f)) (Class.cv (nb068_alpha_dummy_306 f))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_304 f)) (syn_cun (Class.cv (nb068_alpha_dummy_305 f)) (Class.cv (nb068_alpha_dummy_306 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0306) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0307 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0304) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0305 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0310) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0311 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0308) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0309 f) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0306) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0307 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0304) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0305 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0310) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0311 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0308) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0309 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_303), (nb068_alpha_dummy_306 f)), ((nb068_alpha_dummy_302), (nb068_alpha_dummy_305 f)), ((nb068_alpha_dummy_301), (nb068_alpha_dummy_304 f)), ((nb068_alpha_dummy_299), (nb068_alpha_dummy_300 f)), ((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)), ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)), ((nb068_alpha_dummy_321), (nb068_alpha_dummy_322 f)), ((nb068_alpha_dummy_319), (nb068_alpha_dummy_320 f)), ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)), ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)), ((nb068_alpha_dummy_317), (nb068_alpha_dummy_318 f)), ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)), ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)), ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_c0) (nb068_wpp_refl_0113 x y f))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0314) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0315 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0312) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0313 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0314) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0315 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0312) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0313 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_295))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_297 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0318) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0319 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0316) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0317 f) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0318) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0319 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0316) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0317 f) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb068_compact_envfresh_0114 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_299), (nb068_alpha_dummy_300 f)), ((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)), ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)), ((nb068_alpha_dummy_321), (nb068_alpha_dummy_322 f)), ((nb068_alpha_dummy_319), (nb068_alpha_dummy_320 f)), ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)), ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)), ((nb068_alpha_dummy_317), (nb068_alpha_dummy_318 f)), ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)), ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)), ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_299) (nb068_alpha_dummy_300 f) (nb068_wpp_notmem_0782) (nb068_wpp_notmem_0783 f) (TEnvFresh.consFresh (nb068_alpha_dummy_295) (nb068_alpha_dummy_297 f) (nb068_wpp_notmem_0784) (nb068_wpp_notmem_0785 f) (TEnvFresh.consFresh (nb068_alpha_dummy_296) (nb068_alpha_dummy_298 f) (nb068_wpp_notmem_0786) (nb068_wpp_notmem_0787 f) (TEnvFresh.consFresh (nb068_alpha_dummy_321) (nb068_alpha_dummy_322 f) (nb068_wpp_notmem_0816) (nb068_wpp_notmem_0817 f) (TEnvFresh.consFresh (nb068_alpha_dummy_319) (nb068_alpha_dummy_320 f) (nb068_wpp_notmem_0818) (nb068_wpp_notmem_0819 f) (TEnvFresh.consFresh (nb068_alpha_dummy_288) (nb068_alpha_dummy_290 f) (nb068_wpp_notmem_0788) (nb068_wpp_notmem_0789 f) (TEnvFresh.consFresh (nb068_alpha_dummy_287) (nb068_alpha_dummy_289 f) (nb068_wpp_notmem_0790) (nb068_wpp_notmem_0791 f) (TEnvFresh.consFresh (nb068_alpha_dummy_317) (nb068_alpha_dummy_318 f) (nb068_wpp_notmem_0820) (nb068_wpp_notmem_0821 f) (TEnvFresh.consFresh (nb068_alpha_dummy_291) (nb068_alpha_dummy_292 f) (nb068_wpp_notmem_0794) (nb068_wpp_notmem_0795 f) (TEnvFresh.consFresh (nb068_alpha_dummy_284) (nb068_alpha_dummy_286 f) (nb068_wpp_notmem_0796) (nb068_wpp_notmem_0797 f) (TEnvFresh.consFresh (nb068_alpha_dummy_283) (nb068_alpha_dummy_285 f) (nb068_wpp_notmem_0798) (nb068_wpp_notmem_0799 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0194) (nb068_wpp_notmem_0195 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0066) (nb068_wpp_notmem_0067 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0068) (nb068_wpp_notmem_0069 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0070) (nb068_wpp_notmem_0071 x y f) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))

noncomputable def nb068_wpp_refl_0114 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_299), (nb068_alpha_dummy_300 f)), ((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)), ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)), ((nb068_alpha_dummy_321), (nb068_alpha_dummy_322 f)), ((nb068_alpha_dummy_319), (nb068_alpha_dummy_320 f)), ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)), ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)), ((nb068_alpha_dummy_317), (nb068_alpha_dummy_318 f)), ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)), ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)), ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0114 x y f)

noncomputable def nb068_split_alpha_0087 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)), ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)), ((nb068_alpha_dummy_321), (nb068_alpha_dummy_322 f)), ((nb068_alpha_dummy_319), (nb068_alpha_dummy_320 f)), ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)), ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)), ((nb068_alpha_dummy_317), (nb068_alpha_dummy_318 f)), ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)), ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)), ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_295)) (Class.cv (nb068_alpha_dummy_288))) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_296)) (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_295)) (syn_cnnc)) (syn_cplc (Class.cv (nb068_alpha_dummy_295)) (syn_c1c)) (Class.cv (nb068_alpha_dummy_295)))))) (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_297 f)) (Class.cv (nb068_alpha_dummy_290 f))) (Wff.neg (Wff.classEq (Class.cv (nb068_alpha_dummy_298 f)) (syn_cif (Wff.classMem (Class.cv (nb068_alpha_dummy_297 f)) (syn_cnnc)) (syn_cplc (Class.cv (nb068_alpha_dummy_297 f)) (syn_c1c)) (Class.cv (nb068_alpha_dummy_297 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0298) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0299 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0298) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0299 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0328) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0329 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0326) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0327 f) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_288))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_290 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0302) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0303 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0302) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0303 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0300) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0301 f) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_303), (nb068_alpha_dummy_306 f)), ((nb068_alpha_dummy_302), (nb068_alpha_dummy_305 f)), ((nb068_alpha_dummy_301), (nb068_alpha_dummy_304 f)), ((nb068_alpha_dummy_299), (nb068_alpha_dummy_300 f)), ((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)), ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)), ((nb068_alpha_dummy_321), (nb068_alpha_dummy_322 f)), ((nb068_alpha_dummy_319), (nb068_alpha_dummy_320 f)), ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)), ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)), ((nb068_alpha_dummy_317), (nb068_alpha_dummy_318 f)), ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)), ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)), ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_c1c) (nb068_wpp_refl_0112 x y f))) (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0086 x y f)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0300) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0301 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_299), (nb068_alpha_dummy_300 f)), ((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)), ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)), ((nb068_alpha_dummy_321), (nb068_alpha_dummy_322 f)), ((nb068_alpha_dummy_319), (nb068_alpha_dummy_320 f)), ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)), ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)), ((nb068_alpha_dummy_317), (nb068_alpha_dummy_318 f)), ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)), ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)), ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_cnnc) (nb068_wpp_refl_0114 x y f))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0300) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0301 f) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0300) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0301 f) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_299), (nb068_alpha_dummy_300 f)), ((nb068_alpha_dummy_295), (nb068_alpha_dummy_297 f)), ((nb068_alpha_dummy_296), (nb068_alpha_dummy_298 f)), ((nb068_alpha_dummy_321), (nb068_alpha_dummy_322 f)), ((nb068_alpha_dummy_319), (nb068_alpha_dummy_320 f)), ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)), ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)), ((nb068_alpha_dummy_317), (nb068_alpha_dummy_318 f)), ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)), ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)), ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_cnnc) (nb068_wpp_refl_0114 x y f))))))))))))

theorem nb068_compact_envfresh_0115 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_319), (nb068_alpha_dummy_320 f)), ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)), ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)), ((nb068_alpha_dummy_317), (nb068_alpha_dummy_318 f)), ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)), ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)), ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_319) (nb068_alpha_dummy_320 f) (nb068_wpp_notmem_0822) (nb068_wpp_notmem_0823 f) (TEnvFresh.consFresh (nb068_alpha_dummy_288) (nb068_alpha_dummy_290 f) (nb068_wpp_notmem_0824) (nb068_wpp_notmem_0825 f) (TEnvFresh.consFresh (nb068_alpha_dummy_287) (nb068_alpha_dummy_289 f) (nb068_wpp_notmem_0826) (nb068_wpp_notmem_0827 f) (TEnvFresh.consFresh (nb068_alpha_dummy_317) (nb068_alpha_dummy_318 f) (nb068_wpp_notmem_0828) (nb068_wpp_notmem_0829 f) (TEnvFresh.consFresh (nb068_alpha_dummy_291) (nb068_alpha_dummy_292 f) (nb068_wpp_notmem_0830) (nb068_wpp_notmem_0831 f) (TEnvFresh.consFresh (nb068_alpha_dummy_284) (nb068_alpha_dummy_286 f) (nb068_wpp_notmem_0832) (nb068_wpp_notmem_0833 f) (TEnvFresh.consFresh (nb068_alpha_dummy_283) (nb068_alpha_dummy_285 f) (nb068_wpp_notmem_0834) (nb068_wpp_notmem_0835 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0234) (nb068_wpp_notmem_0235 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0100) (nb068_wpp_notmem_0101 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0102) (nb068_wpp_notmem_0103 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0104) (nb068_wpp_notmem_0105 x y f) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))))))

noncomputable def nb068_wpp_refl_0115 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_319), (nb068_alpha_dummy_320 f)), ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)), ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)), ((nb068_alpha_dummy_317), (nb068_alpha_dummy_318 f)), ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)), ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)), ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0115 x y f)

noncomputable def nb068_split_alpha_0088 (x : Var) (y : Var) (f : Var) : TAlphaWff [((nb068_alpha_dummy_317), (nb068_alpha_dummy_318 f)), ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)), ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)), ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_317)) (Class.cab (nb068_alpha_dummy_287) (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_283)) (Wff.classEq (Class.cv (nb068_alpha_dummy_287)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_288))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_317)) (Class.cab (nb068_alpha_dummy_287) (syn_wrex (nb068_alpha_dummy_288) (Class.cv (nb068_alpha_dummy_283)) (Wff.classEq (Class.cv (nb068_alpha_dummy_287)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_288))) (syn_csn (syn_c0c))))))))) (Wff.imp (Wff.classMem (Class.cv (nb068_alpha_dummy_318 f)) (Class.cab (nb068_alpha_dummy_289 f) (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_285 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_290 f))) (syn_csn (syn_c0c))))))) (Wff.neg (Wff.classMem (Class.cv (nb068_alpha_dummy_318 f)) (Class.cab (nb068_alpha_dummy_289 f) (syn_wrex (nb068_alpha_dummy_290 f) (Class.cv (nb068_alpha_dummy_285 f)) (Wff.classEq (Class.cv (nb068_alpha_dummy_289 f)) (syn_cun (syn_cphi (Class.cv (nb068_alpha_dummy_290 f))) (syn_csn (syn_c0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0320) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0322 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0320) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0322 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0324) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0325 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0321) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0323 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((syn_cvv)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_284))).fv ∪ ((Class.cv (nb068_alpha_dummy_283))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_286 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_285 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0087 x y f))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0087 x y f))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_319), (nb068_alpha_dummy_320 f)), ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)), ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)), ((nb068_alpha_dummy_317), (nb068_alpha_dummy_318 f)), ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)), ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)), ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_ccompl (syn_csn (syn_c0c))) (nb068_wpp_refl_0115 x y f))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0320) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0322 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0320) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0322 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0324) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0325 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0321) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0323 f) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((syn_cvv)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb068_alpha_dummy_284))).fv ∪ ((Class.cv (nb068_alpha_dummy_283))).fv) (by decide)) (freshVar_injective (((Class.cv (nb068_alpha_dummy_286 f))).fv ∪ ((Class.cv (nb068_alpha_dummy_285 f))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0087 x y f))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb068_split_alpha_0087 x y f))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb068_alpha_dummy_319), (nb068_alpha_dummy_320 f)), ((nb068_alpha_dummy_288), (nb068_alpha_dummy_290 f)), ((nb068_alpha_dummy_287), (nb068_alpha_dummy_289 f)), ((nb068_alpha_dummy_317), (nb068_alpha_dummy_318 f)), ((nb068_alpha_dummy_291), (nb068_alpha_dummy_292 f)), ((nb068_alpha_dummy_284), (nb068_alpha_dummy_286 f)), ((nb068_alpha_dummy_283), (nb068_alpha_dummy_285 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] (syn_ccompl (syn_csn (syn_c0c))) (nb068_wpp_refl_0115 x y f)))))))))))))))))))

theorem nb068_compact_fv_empty_0246 : (nb068_alpha_dummy_351) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0840 : (nb068_alpha_dummy_351) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_351, fv_syn_c1c] using (nb068_compact_fv_empty_0246)

theorem nb068_compact_fv_empty_0247 (f : Var) : (nb068_alpha_dummy_354 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0841 (f : Var) : (nb068_alpha_dummy_354 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_354, fv_syn_c1c] using (nb068_compact_fv_empty_0247 f)

theorem nb068_compact_fv_empty_0248 : (nb068_alpha_dummy_350) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0842 : (nb068_alpha_dummy_350) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_350, fv_syn_c1c] using (nb068_compact_fv_empty_0248)

theorem nb068_compact_fv_empty_0249 (f : Var) : (nb068_alpha_dummy_353 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0843 (f : Var) : (nb068_alpha_dummy_353 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_353, fv_syn_c1c] using (nb068_compact_fv_empty_0249 f)

theorem nb068_compact_fv_empty_0250 : (nb068_alpha_dummy_349) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0844 : (nb068_alpha_dummy_349) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_349, fv_syn_c1c] using (nb068_compact_fv_empty_0250)

theorem nb068_compact_fv_empty_0251 (f : Var) : (nb068_alpha_dummy_352 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0845 (f : Var) : (nb068_alpha_dummy_352 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_352, fv_syn_c1c] using (nb068_compact_fv_empty_0251 f)

theorem nb068_compact_fv_empty_0252 : (nb068_alpha_dummy_347) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0846 : (nb068_alpha_dummy_347) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_347, fv_syn_c1c] using (nb068_compact_fv_empty_0252)

theorem nb068_compact_fv_empty_0253 (f : Var) : (nb068_alpha_dummy_348 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0847 (f : Var) : (nb068_alpha_dummy_348 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_348, fv_syn_c1c] using (nb068_compact_fv_empty_0253 f)

theorem nb068_compact_fv_empty_0254 : (nb068_alpha_dummy_343) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0848 : (nb068_alpha_dummy_343) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_343, fv_syn_c1c] using (nb068_compact_fv_empty_0254)

theorem nb068_compact_fv_empty_0255 (f : Var) : (nb068_alpha_dummy_345 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0849 (f : Var) : (nb068_alpha_dummy_345 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_345, fv_syn_c1c] using (nb068_compact_fv_empty_0255 f)

theorem nb068_compact_fv_empty_0256 : (nb068_alpha_dummy_344) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0850 : (nb068_alpha_dummy_344) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_344, fv_syn_c1c] using (nb068_compact_fv_empty_0256)

theorem nb068_compact_fv_empty_0257 (f : Var) : (nb068_alpha_dummy_346 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0851 (f : Var) : (nb068_alpha_dummy_346 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_346, fv_syn_c1c] using (nb068_compact_fv_empty_0257 f)

theorem nb068_compact_fv_empty_0258 : (nb068_alpha_dummy_336) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0852 : (nb068_alpha_dummy_336) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_336, fv_syn_c1c] using (nb068_compact_fv_empty_0258)

theorem nb068_compact_fv_empty_0259 (f : Var) : (nb068_alpha_dummy_338 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0853 (f : Var) : (nb068_alpha_dummy_338 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_338, fv_syn_c1c] using (nb068_compact_fv_empty_0259 f)

theorem nb068_compact_fv_empty_0260 : (nb068_alpha_dummy_335) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0854 : (nb068_alpha_dummy_335) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_335, fv_syn_c1c] using (nb068_compact_fv_empty_0260)

theorem nb068_compact_fv_empty_0261 (f : Var) : (nb068_alpha_dummy_337 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0855 (f : Var) : (nb068_alpha_dummy_337 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_337, fv_syn_c1c] using (nb068_compact_fv_empty_0261 f)

theorem nb068_compact_fv_empty_0262 : (nb068_alpha_dummy_341) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0856 : (nb068_alpha_dummy_341) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_341, fv_syn_c1c] using (nb068_compact_fv_empty_0262)

theorem nb068_compact_fv_empty_0263 (f : Var) : (nb068_alpha_dummy_342 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0857 (f : Var) : (nb068_alpha_dummy_342 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_342, fv_syn_c1c] using (nb068_compact_fv_empty_0263 f)

theorem nb068_compact_fv_empty_0264 : (nb068_alpha_dummy_339) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0858 : (nb068_alpha_dummy_339) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_339, fv_syn_c1c] using (nb068_compact_fv_empty_0264)

theorem nb068_compact_fv_empty_0265 (f : Var) : (nb068_alpha_dummy_340 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0859 (f : Var) : (nb068_alpha_dummy_340 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_340, fv_syn_c1c] using (nb068_compact_fv_empty_0265 f)

theorem nb068_compact_fv_empty_0266 : (nb068_alpha_dummy_328) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0860 : (nb068_alpha_dummy_328) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_328, fv_syn_c1c] using (nb068_compact_fv_empty_0266)

theorem nb068_compact_fv_empty_0267 (f : Var) : (nb068_alpha_dummy_331 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0861 (f : Var) : (nb068_alpha_dummy_331 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_331, fv_syn_c1c] using (nb068_compact_fv_empty_0267 f)

theorem nb068_compact_fv_empty_0268 : (nb068_alpha_dummy_327) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0862 : (nb068_alpha_dummy_327) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_327, fv_syn_c1c] using (nb068_compact_fv_empty_0268)

theorem nb068_compact_fv_empty_0269 (f : Var) : (nb068_alpha_dummy_330 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0863 (f : Var) : (nb068_alpha_dummy_330 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_330, fv_syn_c1c] using (nb068_compact_fv_empty_0269 f)

theorem nb068_compact_fv_empty_0270 : (nb068_alpha_dummy_333) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0864 : (nb068_alpha_dummy_333) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_333, fv_syn_c1c] using (nb068_compact_fv_empty_0270)

theorem nb068_compact_fv_empty_0271 (f : Var) : (nb068_alpha_dummy_334 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0865 (f : Var) : (nb068_alpha_dummy_334 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_334, fv_syn_c1c] using (nb068_compact_fv_empty_0271 f)

theorem nb068_compact_fv_empty_0272 : (nb068_alpha_dummy_325) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0866 : (nb068_alpha_dummy_325) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_325, fv_syn_c1c] using (nb068_compact_fv_empty_0272)

theorem nb068_compact_fv_empty_0273 (f : Var) : (nb068_alpha_dummy_326 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0867 (f : Var) : (nb068_alpha_dummy_326 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_326, fv_syn_c1c] using (nb068_compact_fv_empty_0273 f)

theorem nb068_compact_fv_empty_0274 : (nb068_alpha_dummy_323) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0868 : (nb068_alpha_dummy_323) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_323, fv_syn_c1c] using (nb068_compact_fv_empty_0274)

theorem nb068_compact_fv_empty_0275 (f : Var) : (nb068_alpha_dummy_324 f) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb068_wpp_notmem_0869 (f : Var) : (nb068_alpha_dummy_324 f) ∉ ((syn_c1c)).fv := by
  simpa only [nb068_alpha_dummy_324, fv_syn_c1c] using (nb068_compact_fv_empty_0275 f)

theorem nb068_compact_envfresh_0116 (x : Var) (y : Var) (f : Var) : TEnvFresh [((nb068_alpha_dummy_351), (nb068_alpha_dummy_354 f)), ((nb068_alpha_dummy_350), (nb068_alpha_dummy_353 f)), ((nb068_alpha_dummy_349), (nb068_alpha_dummy_352 f)), ((nb068_alpha_dummy_347), (nb068_alpha_dummy_348 f)), ((nb068_alpha_dummy_343), (nb068_alpha_dummy_345 f)), ((nb068_alpha_dummy_344), (nb068_alpha_dummy_346 f)), ((nb068_alpha_dummy_336), (nb068_alpha_dummy_338 f)), ((nb068_alpha_dummy_335), (nb068_alpha_dummy_337 f)), ((nb068_alpha_dummy_341), (nb068_alpha_dummy_342 f)), ((nb068_alpha_dummy_339), (nb068_alpha_dummy_340 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb068_alpha_dummy_351) (nb068_alpha_dummy_354 f) (nb068_wpp_notmem_0840) (nb068_wpp_notmem_0841 f) (TEnvFresh.consFresh (nb068_alpha_dummy_350) (nb068_alpha_dummy_353 f) (nb068_wpp_notmem_0842) (nb068_wpp_notmem_0843 f) (TEnvFresh.consFresh (nb068_alpha_dummy_349) (nb068_alpha_dummy_352 f) (nb068_wpp_notmem_0844) (nb068_wpp_notmem_0845 f) (TEnvFresh.consFresh (nb068_alpha_dummy_347) (nb068_alpha_dummy_348 f) (nb068_wpp_notmem_0846) (nb068_wpp_notmem_0847 f) (TEnvFresh.consFresh (nb068_alpha_dummy_343) (nb068_alpha_dummy_345 f) (nb068_wpp_notmem_0848) (nb068_wpp_notmem_0849 f) (TEnvFresh.consFresh (nb068_alpha_dummy_344) (nb068_alpha_dummy_346 f) (nb068_wpp_notmem_0850) (nb068_wpp_notmem_0851 f) (TEnvFresh.consFresh (nb068_alpha_dummy_336) (nb068_alpha_dummy_338 f) (nb068_wpp_notmem_0852) (nb068_wpp_notmem_0853 f) (TEnvFresh.consFresh (nb068_alpha_dummy_335) (nb068_alpha_dummy_337 f) (nb068_wpp_notmem_0854) (nb068_wpp_notmem_0855 f) (TEnvFresh.consFresh (nb068_alpha_dummy_341) (nb068_alpha_dummy_342 f) (nb068_wpp_notmem_0856) (nb068_wpp_notmem_0857 f) (TEnvFresh.consFresh (nb068_alpha_dummy_339) (nb068_alpha_dummy_340 f) (nb068_wpp_notmem_0858) (nb068_wpp_notmem_0859 f) (TEnvFresh.consFresh (nb068_alpha_dummy_328) (nb068_alpha_dummy_331 f) (nb068_wpp_notmem_0860) (nb068_wpp_notmem_0861 f) (TEnvFresh.consFresh (nb068_alpha_dummy_327) (nb068_alpha_dummy_330 f) (nb068_wpp_notmem_0862) (nb068_wpp_notmem_0863 f) (TEnvFresh.consFresh (nb068_alpha_dummy_333) (nb068_alpha_dummy_334 f) (nb068_wpp_notmem_0864) (nb068_wpp_notmem_0865 f) (TEnvFresh.consFresh (nb068_alpha_dummy_325) (nb068_alpha_dummy_326 f) (nb068_wpp_notmem_0866) (nb068_wpp_notmem_0867 f) (TEnvFresh.consFresh (nb068_alpha_dummy_323) (nb068_alpha_dummy_324 f) (nb068_wpp_notmem_0868) (nb068_wpp_notmem_0869 f) (TEnvFresh.consFresh (nb068_alpha_dummy_000) f (nb068_wpp_notmem_0136) (nb068_wpp_notmem_0137 f) (TEnvFresh.consFresh (nb068_alpha_dummy_002) y (nb068_wpp_notmem_0020) (nb068_wpp_notmem_0021 y) (TEnvFresh.consFresh (nb068_alpha_dummy_001) x (nb068_wpp_notmem_0022) (nb068_wpp_notmem_0023 x) (TEnvFresh.consFresh (nb068_alpha_dummy_003) (nb068_alpha_dummy_004 x y f) (nb068_wpp_notmem_0024) (nb068_wpp_notmem_0025 x y f) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))

noncomputable def nb068_wpp_refl_0116 (x : Var) (y : Var) (f : Var) : TReflOn [((nb068_alpha_dummy_351), (nb068_alpha_dummy_354 f)), ((nb068_alpha_dummy_350), (nb068_alpha_dummy_353 f)), ((nb068_alpha_dummy_349), (nb068_alpha_dummy_352 f)), ((nb068_alpha_dummy_347), (nb068_alpha_dummy_348 f)), ((nb068_alpha_dummy_343), (nb068_alpha_dummy_345 f)), ((nb068_alpha_dummy_344), (nb068_alpha_dummy_346 f)), ((nb068_alpha_dummy_336), (nb068_alpha_dummy_338 f)), ((nb068_alpha_dummy_335), (nb068_alpha_dummy_337 f)), ((nb068_alpha_dummy_341), (nb068_alpha_dummy_342 f)), ((nb068_alpha_dummy_339), (nb068_alpha_dummy_340 f)), ((nb068_alpha_dummy_328), (nb068_alpha_dummy_331 f)), ((nb068_alpha_dummy_327), (nb068_alpha_dummy_330 f)), ((nb068_alpha_dummy_333), (nb068_alpha_dummy_334 f)), ((nb068_alpha_dummy_325), (nb068_alpha_dummy_326 f)), ((nb068_alpha_dummy_323), (nb068_alpha_dummy_324 f)), ((nb068_alpha_dummy_000), f), ((nb068_alpha_dummy_002), y), ((nb068_alpha_dummy_001), x), ((nb068_alpha_dummy_003), (nb068_alpha_dummy_004 x y f))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb068_compact_envfresh_0116 x y f)

theorem nb068_wpp_notmem_0870 : (nb068_alpha_dummy_351) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_351, fv_syn_c0] using (nb068_compact_fv_empty_0246)

theorem nb068_wpp_notmem_0871 (f : Var) : (nb068_alpha_dummy_354 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_354, fv_syn_c0] using (nb068_compact_fv_empty_0247 f)

theorem nb068_wpp_notmem_0872 : (nb068_alpha_dummy_350) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_350, fv_syn_c0] using (nb068_compact_fv_empty_0248)

theorem nb068_wpp_notmem_0873 (f : Var) : (nb068_alpha_dummy_353 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_353, fv_syn_c0] using (nb068_compact_fv_empty_0249 f)

theorem nb068_wpp_notmem_0874 : (nb068_alpha_dummy_349) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_349, fv_syn_c0] using (nb068_compact_fv_empty_0250)

theorem nb068_wpp_notmem_0875 (f : Var) : (nb068_alpha_dummy_352 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_352, fv_syn_c0] using (nb068_compact_fv_empty_0251 f)

theorem nb068_wpp_notmem_0876 : (nb068_alpha_dummy_347) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_347, fv_syn_c0] using (nb068_compact_fv_empty_0252)

theorem nb068_wpp_notmem_0877 (f : Var) : (nb068_alpha_dummy_348 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_348, fv_syn_c0] using (nb068_compact_fv_empty_0253 f)

theorem nb068_wpp_notmem_0878 : (nb068_alpha_dummy_343) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_343, fv_syn_c0] using (nb068_compact_fv_empty_0254)

theorem nb068_wpp_notmem_0879 (f : Var) : (nb068_alpha_dummy_345 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_345, fv_syn_c0] using (nb068_compact_fv_empty_0255 f)

theorem nb068_wpp_notmem_0880 : (nb068_alpha_dummy_344) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_344, fv_syn_c0] using (nb068_compact_fv_empty_0256)

theorem nb068_wpp_notmem_0881 (f : Var) : (nb068_alpha_dummy_346 f) ∉ ((syn_c0)).fv := by
  simpa only [nb068_alpha_dummy_346, fv_syn_c0] using (nb068_compact_fv_empty_0257 f)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
