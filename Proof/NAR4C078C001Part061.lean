import NAR4C078C001Part060

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

noncomputable def nb078_wpp_refl_0105 (x : Var) (y : Var) (g : Var) : TReflOn [((nb078_alpha_dummy_311), (nb078_alpha_dummy_314 g)), ((nb078_alpha_dummy_310), (nb078_alpha_dummy_313 g)), ((nb078_alpha_dummy_309), (nb078_alpha_dummy_312 g)), ((nb078_alpha_dummy_307), (nb078_alpha_dummy_308 g)), ((nb078_alpha_dummy_303), (nb078_alpha_dummy_305 g)), ((nb078_alpha_dummy_304), (nb078_alpha_dummy_306 g)), ((nb078_alpha_dummy_329), (nb078_alpha_dummy_330 g)), ((nb078_alpha_dummy_327), (nb078_alpha_dummy_328 g)), ((nb078_alpha_dummy_296), (nb078_alpha_dummy_298 g)), ((nb078_alpha_dummy_295), (nb078_alpha_dummy_297 g)), ((nb078_alpha_dummy_325), (nb078_alpha_dummy_326 g)), ((nb078_alpha_dummy_299), (nb078_alpha_dummy_300 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0105 x y g)

theorem nb078_wpp_notmem_0828 : (nb078_alpha_dummy_329) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_329, fv_syn_cnnc] using (nb078_compact_fv_empty_0246)

theorem nb078_wpp_notmem_0829 (g : Var) : (nb078_alpha_dummy_330 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_330, fv_syn_cnnc] using (nb078_compact_fv_empty_0247 g)

theorem nb078_wpp_notmem_0830 : (nb078_alpha_dummy_327) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_327, fv_syn_cnnc] using (nb078_compact_fv_empty_0248)

theorem nb078_wpp_notmem_0831 (g : Var) : (nb078_alpha_dummy_328 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_328, fv_syn_cnnc] using (nb078_compact_fv_empty_0249 g)

theorem nb078_wpp_notmem_0832 : (nb078_alpha_dummy_325) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_325, fv_syn_cnnc] using (nb078_compact_fv_empty_0250)

theorem nb078_wpp_notmem_0833 (g : Var) : (nb078_alpha_dummy_326 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_326, fv_syn_cnnc] using (nb078_compact_fv_empty_0251 g)

theorem nb078_compact_envfresh_0106 (x : Var) (y : Var) (g : Var) : TEnvFresh [((nb078_alpha_dummy_307), (nb078_alpha_dummy_308 g)), ((nb078_alpha_dummy_303), (nb078_alpha_dummy_305 g)), ((nb078_alpha_dummy_304), (nb078_alpha_dummy_306 g)), ((nb078_alpha_dummy_329), (nb078_alpha_dummy_330 g)), ((nb078_alpha_dummy_327), (nb078_alpha_dummy_328 g)), ((nb078_alpha_dummy_296), (nb078_alpha_dummy_298 g)), ((nb078_alpha_dummy_295), (nb078_alpha_dummy_297 g)), ((nb078_alpha_dummy_325), (nb078_alpha_dummy_326 g)), ((nb078_alpha_dummy_299), (nb078_alpha_dummy_300 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_307) (nb078_alpha_dummy_308 g) (nb078_wpp_notmem_0790) (nb078_wpp_notmem_0791 g) (TEnvFresh.consFresh (nb078_alpha_dummy_303) (nb078_alpha_dummy_305 g) (nb078_wpp_notmem_0792) (nb078_wpp_notmem_0793 g) (TEnvFresh.consFresh (nb078_alpha_dummy_304) (nb078_alpha_dummy_306 g) (nb078_wpp_notmem_0794) (nb078_wpp_notmem_0795 g) (TEnvFresh.consFresh (nb078_alpha_dummy_329) (nb078_alpha_dummy_330 g) (nb078_wpp_notmem_0828) (nb078_wpp_notmem_0829 g) (TEnvFresh.consFresh (nb078_alpha_dummy_327) (nb078_alpha_dummy_328 g) (nb078_wpp_notmem_0830) (nb078_wpp_notmem_0831 g) (TEnvFresh.consFresh (nb078_alpha_dummy_296) (nb078_alpha_dummy_298 g) (nb078_wpp_notmem_0796) (nb078_wpp_notmem_0797 g) (TEnvFresh.consFresh (nb078_alpha_dummy_295) (nb078_alpha_dummy_297 g) (nb078_wpp_notmem_0798) (nb078_wpp_notmem_0799 g) (TEnvFresh.consFresh (nb078_alpha_dummy_325) (nb078_alpha_dummy_326 g) (nb078_wpp_notmem_0832) (nb078_wpp_notmem_0833 g) (TEnvFresh.consFresh (nb078_alpha_dummy_299) (nb078_alpha_dummy_300 g) (nb078_wpp_notmem_0802) (nb078_wpp_notmem_0803 g) (TEnvFresh.consFresh (nb078_alpha_dummy_288) (nb078_alpha_dummy_291 g) (nb078_wpp_notmem_0804) (nb078_wpp_notmem_0805 g) (TEnvFresh.consFresh (nb078_alpha_dummy_287) (nb078_alpha_dummy_290 g) (nb078_wpp_notmem_0806) (nb078_wpp_notmem_0807 g) (TEnvFresh.consFresh (nb078_alpha_dummy_293) (nb078_alpha_dummy_294 g) (nb078_wpp_notmem_0808) (nb078_wpp_notmem_0809 g) (TEnvFresh.consFresh (nb078_alpha_dummy_285) (nb078_alpha_dummy_286 g) (nb078_wpp_notmem_0810) (nb078_wpp_notmem_0811 g) (TEnvFresh.consFresh (nb078_alpha_dummy_283) (nb078_alpha_dummy_284 g) (nb078_wpp_notmem_0812) (nb078_wpp_notmem_0813 g) (TEnvFresh.consFresh (nb078_alpha_dummy_001) g (nb078_wpp_notmem_0814) (nb078_wpp_notmem_0815 g) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0098) (nb078_wpp_notmem_0099 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0100) (nb078_wpp_notmem_0101 x) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))))

noncomputable def nb078_wpp_refl_0106 (x : Var) (y : Var) (g : Var) : TReflOn [((nb078_alpha_dummy_307), (nb078_alpha_dummy_308 g)), ((nb078_alpha_dummy_303), (nb078_alpha_dummy_305 g)), ((nb078_alpha_dummy_304), (nb078_alpha_dummy_306 g)), ((nb078_alpha_dummy_329), (nb078_alpha_dummy_330 g)), ((nb078_alpha_dummy_327), (nb078_alpha_dummy_328 g)), ((nb078_alpha_dummy_296), (nb078_alpha_dummy_298 g)), ((nb078_alpha_dummy_295), (nb078_alpha_dummy_297 g)), ((nb078_alpha_dummy_325), (nb078_alpha_dummy_326 g)), ((nb078_alpha_dummy_299), (nb078_alpha_dummy_300 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0106 x y g)

theorem nb078_wpp_notmem_0834 : (nb078_alpha_dummy_327) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_327, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0248)

theorem nb078_wpp_notmem_0835 (g : Var) : (nb078_alpha_dummy_328 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_328, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0249 g)

theorem nb078_wpp_notmem_0836 : (nb078_alpha_dummy_296) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_296, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0226)

theorem nb078_wpp_notmem_0837 (g : Var) : (nb078_alpha_dummy_298 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_298, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0227 g)

theorem nb078_wpp_notmem_0838 : (nb078_alpha_dummy_295) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_295, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0228)

theorem nb078_wpp_notmem_0839 (g : Var) : (nb078_alpha_dummy_297 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_297, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0229 g)

theorem nb078_wpp_notmem_0840 : (nb078_alpha_dummy_325) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_325, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0250)

theorem nb078_wpp_notmem_0841 (g : Var) : (nb078_alpha_dummy_326 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_326, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0251 g)

theorem nb078_wpp_notmem_0842 : (nb078_alpha_dummy_299) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_299, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0232)

theorem nb078_wpp_notmem_0843 (g : Var) : (nb078_alpha_dummy_300 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_300, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0233 g)

theorem nb078_wpp_notmem_0844 : (nb078_alpha_dummy_288) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_288, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0234)

theorem nb078_wpp_notmem_0845 (g : Var) : (nb078_alpha_dummy_291 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_291, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0235 g)

theorem nb078_wpp_notmem_0846 : (nb078_alpha_dummy_287) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_287, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0236)

theorem nb078_wpp_notmem_0847 (g : Var) : (nb078_alpha_dummy_290 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_290, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0237 g)

theorem nb078_wpp_notmem_0848 : (nb078_alpha_dummy_293) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_293, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0238)

theorem nb078_wpp_notmem_0849 (g : Var) : (nb078_alpha_dummy_294 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_294, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0239 g)

theorem nb078_wpp_notmem_0850 : (nb078_alpha_dummy_285) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_285, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0240)

theorem nb078_wpp_notmem_0851 (g : Var) : (nb078_alpha_dummy_286 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_286, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0241 g)

theorem nb078_wpp_notmem_0852 : (nb078_alpha_dummy_283) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_283, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0242)

theorem nb078_wpp_notmem_0853 (g : Var) : (nb078_alpha_dummy_284 g) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_284, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0243 g)

theorem nb078_wpp_notmem_0854 : (nb078_alpha_dummy_001) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb078_alpha_dummy_001, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0244)

theorem nb078_wpp_notmem_0855 (g : Var) : g ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb078_compact_fv_empty_0245 g)

theorem nb078_compact_envfresh_0107 (x : Var) (y : Var) (g : Var) : TEnvFresh [((nb078_alpha_dummy_327), (nb078_alpha_dummy_328 g)), ((nb078_alpha_dummy_296), (nb078_alpha_dummy_298 g)), ((nb078_alpha_dummy_295), (nb078_alpha_dummy_297 g)), ((nb078_alpha_dummy_325), (nb078_alpha_dummy_326 g)), ((nb078_alpha_dummy_299), (nb078_alpha_dummy_300 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_327) (nb078_alpha_dummy_328 g) (nb078_wpp_notmem_0834) (nb078_wpp_notmem_0835 g) (TEnvFresh.consFresh (nb078_alpha_dummy_296) (nb078_alpha_dummy_298 g) (nb078_wpp_notmem_0836) (nb078_wpp_notmem_0837 g) (TEnvFresh.consFresh (nb078_alpha_dummy_295) (nb078_alpha_dummy_297 g) (nb078_wpp_notmem_0838) (nb078_wpp_notmem_0839 g) (TEnvFresh.consFresh (nb078_alpha_dummy_325) (nb078_alpha_dummy_326 g) (nb078_wpp_notmem_0840) (nb078_wpp_notmem_0841 g) (TEnvFresh.consFresh (nb078_alpha_dummy_299) (nb078_alpha_dummy_300 g) (nb078_wpp_notmem_0842) (nb078_wpp_notmem_0843 g) (TEnvFresh.consFresh (nb078_alpha_dummy_288) (nb078_alpha_dummy_291 g) (nb078_wpp_notmem_0844) (nb078_wpp_notmem_0845 g) (TEnvFresh.consFresh (nb078_alpha_dummy_287) (nb078_alpha_dummy_290 g) (nb078_wpp_notmem_0846) (nb078_wpp_notmem_0847 g) (TEnvFresh.consFresh (nb078_alpha_dummy_293) (nb078_alpha_dummy_294 g) (nb078_wpp_notmem_0848) (nb078_wpp_notmem_0849 g) (TEnvFresh.consFresh (nb078_alpha_dummy_285) (nb078_alpha_dummy_286 g) (nb078_wpp_notmem_0850) (nb078_wpp_notmem_0851 g) (TEnvFresh.consFresh (nb078_alpha_dummy_283) (nb078_alpha_dummy_284 g) (nb078_wpp_notmem_0852) (nb078_wpp_notmem_0853 g) (TEnvFresh.consFresh (nb078_alpha_dummy_001) g (nb078_wpp_notmem_0854) (nb078_wpp_notmem_0855 g) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0142) (nb078_wpp_notmem_0143 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0144) (nb078_wpp_notmem_0145 x) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))))))))

noncomputable def nb078_wpp_refl_0107 (x : Var) (y : Var) (g : Var) : TReflOn [((nb078_alpha_dummy_327), (nb078_alpha_dummy_328 g)), ((nb078_alpha_dummy_296), (nb078_alpha_dummy_298 g)), ((nb078_alpha_dummy_295), (nb078_alpha_dummy_297 g)), ((nb078_alpha_dummy_325), (nb078_alpha_dummy_326 g)), ((nb078_alpha_dummy_299), (nb078_alpha_dummy_300 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0107 x y g)

noncomputable def nb078_split_alpha_0031 (x : Var) (y : Var) (g : Var) : TAlphaWff [((nb078_alpha_dummy_327), (nb078_alpha_dummy_328 g)), ((nb078_alpha_dummy_296), (nb078_alpha_dummy_298 g)), ((nb078_alpha_dummy_295), (nb078_alpha_dummy_297 g)), ((nb078_alpha_dummy_325), (nb078_alpha_dummy_326 g)), ((nb078_alpha_dummy_299), (nb078_alpha_dummy_300 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_327)) (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_296))))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_327)) (syn_ccompl (syn_csn (syn_c0c)))))) (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_328 g)) (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_298 g))))) (Wff.neg (Wff.classMem (Class.cv (nb078_alpha_dummy_328 g)) (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0300) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0301 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0300) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0301 g) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0330) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0331 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0328) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0329 g) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_296))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_298 g))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0304) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0305 g) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0304) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0305 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0302) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0303 g) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_311), (nb078_alpha_dummy_314 g)), ((nb078_alpha_dummy_310), (nb078_alpha_dummy_313 g)), ((nb078_alpha_dummy_309), (nb078_alpha_dummy_312 g)), ((nb078_alpha_dummy_307), (nb078_alpha_dummy_308 g)), ((nb078_alpha_dummy_303), (nb078_alpha_dummy_305 g)), ((nb078_alpha_dummy_304), (nb078_alpha_dummy_306 g)), ((nb078_alpha_dummy_329), (nb078_alpha_dummy_330 g)), ((nb078_alpha_dummy_327), (nb078_alpha_dummy_328 g)), ((nb078_alpha_dummy_296), (nb078_alpha_dummy_298 g)), ((nb078_alpha_dummy_295), (nb078_alpha_dummy_297 g)), ((nb078_alpha_dummy_325), (nb078_alpha_dummy_326 g)), ((nb078_alpha_dummy_299), (nb078_alpha_dummy_300 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0104 x y g))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0308) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0309 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0306) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0307 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0312) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0313 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0310) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0311 g) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0308) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0309 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0306) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0307 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0312) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0313 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0310) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0311 g) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_311), (nb078_alpha_dummy_314 g)), ((nb078_alpha_dummy_310), (nb078_alpha_dummy_313 g)), ((nb078_alpha_dummy_309), (nb078_alpha_dummy_312 g)), ((nb078_alpha_dummy_307), (nb078_alpha_dummy_308 g)), ((nb078_alpha_dummy_303), (nb078_alpha_dummy_305 g)), ((nb078_alpha_dummy_304), (nb078_alpha_dummy_306 g)), ((nb078_alpha_dummy_329), (nb078_alpha_dummy_330 g)), ((nb078_alpha_dummy_327), (nb078_alpha_dummy_328 g)), ((nb078_alpha_dummy_296), (nb078_alpha_dummy_298 g)), ((nb078_alpha_dummy_295), (nb078_alpha_dummy_297 g)), ((nb078_alpha_dummy_325), (nb078_alpha_dummy_326 g)), ((nb078_alpha_dummy_299), (nb078_alpha_dummy_300 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0105 x y g))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0316) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0317 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0314) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0315 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0316) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0317 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0314) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0315 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0320) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0321 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0318) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0319 g) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0320) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0321 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0318) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0319 g) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0302) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0303 g) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_307), (nb078_alpha_dummy_308 g)), ((nb078_alpha_dummy_303), (nb078_alpha_dummy_305 g)), ((nb078_alpha_dummy_304), (nb078_alpha_dummy_306 g)), ((nb078_alpha_dummy_329), (nb078_alpha_dummy_330 g)), ((nb078_alpha_dummy_327), (nb078_alpha_dummy_328 g)), ((nb078_alpha_dummy_296), (nb078_alpha_dummy_298 g)), ((nb078_alpha_dummy_295), (nb078_alpha_dummy_297 g)), ((nb078_alpha_dummy_325), (nb078_alpha_dummy_326 g)), ((nb078_alpha_dummy_299), (nb078_alpha_dummy_300 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0106 x y g))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0302) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0303 g) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0302) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0303 g) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_307), (nb078_alpha_dummy_308 g)), ((nb078_alpha_dummy_303), (nb078_alpha_dummy_305 g)), ((nb078_alpha_dummy_304), (nb078_alpha_dummy_306 g)), ((nb078_alpha_dummy_329), (nb078_alpha_dummy_330 g)), ((nb078_alpha_dummy_327), (nb078_alpha_dummy_328 g)), ((nb078_alpha_dummy_296), (nb078_alpha_dummy_298 g)), ((nb078_alpha_dummy_295), (nb078_alpha_dummy_297 g)), ((nb078_alpha_dummy_325), (nb078_alpha_dummy_326 g)), ((nb078_alpha_dummy_299), (nb078_alpha_dummy_300 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0106 x y g)))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0300) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0301 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0300) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0301 g) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0330) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0331 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0328) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0329 g) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_296))).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_298 g))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0304) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0305 g) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0304) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0305 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0302) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0303 g) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_311), (nb078_alpha_dummy_314 g)), ((nb078_alpha_dummy_310), (nb078_alpha_dummy_313 g)), ((nb078_alpha_dummy_309), (nb078_alpha_dummy_312 g)), ((nb078_alpha_dummy_307), (nb078_alpha_dummy_308 g)), ((nb078_alpha_dummy_303), (nb078_alpha_dummy_305 g)), ((nb078_alpha_dummy_304), (nb078_alpha_dummy_306 g)), ((nb078_alpha_dummy_329), (nb078_alpha_dummy_330 g)), ((nb078_alpha_dummy_327), (nb078_alpha_dummy_328 g)), ((nb078_alpha_dummy_296), (nb078_alpha_dummy_298 g)), ((nb078_alpha_dummy_295), (nb078_alpha_dummy_297 g)), ((nb078_alpha_dummy_325), (nb078_alpha_dummy_326 g)), ((nb078_alpha_dummy_299), (nb078_alpha_dummy_300 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c1c) (nb078_wpp_refl_0104 x y g))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0308) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0309 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0306) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0307 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0312) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0313 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0310) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0311 g) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0308) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0309 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0306) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0307 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0312) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0313 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0310) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0311 g) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_311), (nb078_alpha_dummy_314 g)), ((nb078_alpha_dummy_310), (nb078_alpha_dummy_313 g)), ((nb078_alpha_dummy_309), (nb078_alpha_dummy_312 g)), ((nb078_alpha_dummy_307), (nb078_alpha_dummy_308 g)), ((nb078_alpha_dummy_303), (nb078_alpha_dummy_305 g)), ((nb078_alpha_dummy_304), (nb078_alpha_dummy_306 g)), ((nb078_alpha_dummy_329), (nb078_alpha_dummy_330 g)), ((nb078_alpha_dummy_327), (nb078_alpha_dummy_328 g)), ((nb078_alpha_dummy_296), (nb078_alpha_dummy_298 g)), ((nb078_alpha_dummy_295), (nb078_alpha_dummy_297 g)), ((nb078_alpha_dummy_325), (nb078_alpha_dummy_326 g)), ((nb078_alpha_dummy_299), (nb078_alpha_dummy_300 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_c0) (nb078_wpp_refl_0105 x y g))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0316) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0317 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0314) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0315 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0316) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0317 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0314) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0315 g) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0320) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0321 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0318) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0319 g) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0320) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0321 g) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0318) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0319 g) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0302) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0303 g) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_307), (nb078_alpha_dummy_308 g)), ((nb078_alpha_dummy_303), (nb078_alpha_dummy_305 g)), ((nb078_alpha_dummy_304), (nb078_alpha_dummy_306 g)), ((nb078_alpha_dummy_329), (nb078_alpha_dummy_330 g)), ((nb078_alpha_dummy_327), (nb078_alpha_dummy_328 g)), ((nb078_alpha_dummy_296), (nb078_alpha_dummy_298 g)), ((nb078_alpha_dummy_295), (nb078_alpha_dummy_297 g)), ((nb078_alpha_dummy_325), (nb078_alpha_dummy_326 g)), ((nb078_alpha_dummy_299), (nb078_alpha_dummy_300 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0106 x y g))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0302) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0303 g) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0302) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0303 g) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_307), (nb078_alpha_dummy_308 g)), ((nb078_alpha_dummy_303), (nb078_alpha_dummy_305 g)), ((nb078_alpha_dummy_304), (nb078_alpha_dummy_306 g)), ((nb078_alpha_dummy_329), (nb078_alpha_dummy_330 g)), ((nb078_alpha_dummy_327), (nb078_alpha_dummy_328 g)), ((nb078_alpha_dummy_296), (nb078_alpha_dummy_298 g)), ((nb078_alpha_dummy_295), (nb078_alpha_dummy_297 g)), ((nb078_alpha_dummy_325), (nb078_alpha_dummy_326 g)), ((nb078_alpha_dummy_299), (nb078_alpha_dummy_300 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc) (nb078_wpp_refl_0106 x y g)))))))))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb078_alpha_dummy_327), (nb078_alpha_dummy_328 g)), ((nb078_alpha_dummy_296), (nb078_alpha_dummy_298 g)), ((nb078_alpha_dummy_295), (nb078_alpha_dummy_297 g)), ((nb078_alpha_dummy_325), (nb078_alpha_dummy_326 g)), ((nb078_alpha_dummy_299), (nb078_alpha_dummy_300 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (nb078_wpp_refl_0107 x y g)))))

theorem nb078_compact_fv_empty_0252 : (nb078_alpha_dummy_347) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0856 : (nb078_alpha_dummy_347) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_347, fv_syn_c1c] using (nb078_compact_fv_empty_0252)

theorem nb078_compact_fv_empty_0253 (g : Var) : (nb078_alpha_dummy_350 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0857 (g : Var) : (nb078_alpha_dummy_350 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_350, fv_syn_c1c] using (nb078_compact_fv_empty_0253 g)

theorem nb078_compact_fv_empty_0254 : (nb078_alpha_dummy_346) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0858 : (nb078_alpha_dummy_346) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_346, fv_syn_c1c] using (nb078_compact_fv_empty_0254)

theorem nb078_compact_fv_empty_0255 (g : Var) : (nb078_alpha_dummy_349 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0859 (g : Var) : (nb078_alpha_dummy_349 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_349, fv_syn_c1c] using (nb078_compact_fv_empty_0255 g)

theorem nb078_compact_fv_empty_0256 : (nb078_alpha_dummy_345) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0860 : (nb078_alpha_dummy_345) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_345, fv_syn_c1c] using (nb078_compact_fv_empty_0256)

theorem nb078_compact_fv_empty_0257 (g : Var) : (nb078_alpha_dummy_348 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0861 (g : Var) : (nb078_alpha_dummy_348 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_348, fv_syn_c1c] using (nb078_compact_fv_empty_0257 g)

theorem nb078_compact_fv_empty_0258 : (nb078_alpha_dummy_343) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0862 : (nb078_alpha_dummy_343) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_343, fv_syn_c1c] using (nb078_compact_fv_empty_0258)

theorem nb078_compact_fv_empty_0259 (g : Var) : (nb078_alpha_dummy_344 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0863 (g : Var) : (nb078_alpha_dummy_344 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_344, fv_syn_c1c] using (nb078_compact_fv_empty_0259 g)

theorem nb078_compact_fv_empty_0260 : (nb078_alpha_dummy_339) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0864 : (nb078_alpha_dummy_339) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_339, fv_syn_c1c] using (nb078_compact_fv_empty_0260)

theorem nb078_compact_fv_empty_0261 (g : Var) : (nb078_alpha_dummy_341 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0865 (g : Var) : (nb078_alpha_dummy_341 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_341, fv_syn_c1c] using (nb078_compact_fv_empty_0261 g)

theorem nb078_compact_fv_empty_0262 : (nb078_alpha_dummy_340) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0866 : (nb078_alpha_dummy_340) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_340, fv_syn_c1c] using (nb078_compact_fv_empty_0262)

theorem nb078_compact_fv_empty_0263 (g : Var) : (nb078_alpha_dummy_342 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0867 (g : Var) : (nb078_alpha_dummy_342 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_342, fv_syn_c1c] using (nb078_compact_fv_empty_0263 g)

theorem nb078_compact_fv_empty_0264 : (nb078_alpha_dummy_332) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0868 : (nb078_alpha_dummy_332) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_332, fv_syn_c1c] using (nb078_compact_fv_empty_0264)

theorem nb078_compact_fv_empty_0265 (g : Var) : (nb078_alpha_dummy_334 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0869 (g : Var) : (nb078_alpha_dummy_334 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_334, fv_syn_c1c] using (nb078_compact_fv_empty_0265 g)

theorem nb078_compact_fv_empty_0266 : (nb078_alpha_dummy_331) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0870 : (nb078_alpha_dummy_331) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_331, fv_syn_c1c] using (nb078_compact_fv_empty_0266)

theorem nb078_compact_fv_empty_0267 (g : Var) : (nb078_alpha_dummy_333 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0871 (g : Var) : (nb078_alpha_dummy_333 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_333, fv_syn_c1c] using (nb078_compact_fv_empty_0267 g)

theorem nb078_compact_fv_empty_0268 : (nb078_alpha_dummy_337) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0872 : (nb078_alpha_dummy_337) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_337, fv_syn_c1c] using (nb078_compact_fv_empty_0268)

theorem nb078_compact_fv_empty_0269 (g : Var) : (nb078_alpha_dummy_338 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0873 (g : Var) : (nb078_alpha_dummy_338 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_338, fv_syn_c1c] using (nb078_compact_fv_empty_0269 g)

theorem nb078_compact_fv_empty_0270 : (nb078_alpha_dummy_335) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0874 : (nb078_alpha_dummy_335) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_335, fv_syn_c1c] using (nb078_compact_fv_empty_0270)

theorem nb078_compact_fv_empty_0271 (g : Var) : (nb078_alpha_dummy_336 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0875 (g : Var) : (nb078_alpha_dummy_336 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_336, fv_syn_c1c] using (nb078_compact_fv_empty_0271 g)

theorem nb078_compact_fv_empty_0272 : (nb078_alpha_dummy_289) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0876 : (nb078_alpha_dummy_289) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_289, fv_syn_c1c] using (nb078_compact_fv_empty_0272)

theorem nb078_compact_fv_empty_0273 (g : Var) : (nb078_alpha_dummy_292 g) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb078_wpp_notmem_0877 (g : Var) : (nb078_alpha_dummy_292 g) ∉ ((syn_c1c)).fv := by
  simpa only [nb078_alpha_dummy_292, fv_syn_c1c] using (nb078_compact_fv_empty_0273 g)

theorem nb078_compact_envfresh_0108 (x : Var) (y : Var) (g : Var) : TEnvFresh [((nb078_alpha_dummy_347), (nb078_alpha_dummy_350 g)), ((nb078_alpha_dummy_346), (nb078_alpha_dummy_349 g)), ((nb078_alpha_dummy_345), (nb078_alpha_dummy_348 g)), ((nb078_alpha_dummy_343), (nb078_alpha_dummy_344 g)), ((nb078_alpha_dummy_339), (nb078_alpha_dummy_341 g)), ((nb078_alpha_dummy_340), (nb078_alpha_dummy_342 g)), ((nb078_alpha_dummy_332), (nb078_alpha_dummy_334 g)), ((nb078_alpha_dummy_331), (nb078_alpha_dummy_333 g)), ((nb078_alpha_dummy_337), (nb078_alpha_dummy_338 g)), ((nb078_alpha_dummy_335), (nb078_alpha_dummy_336 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_347) (nb078_alpha_dummy_350 g) (nb078_wpp_notmem_0856) (nb078_wpp_notmem_0857 g) (TEnvFresh.consFresh (nb078_alpha_dummy_346) (nb078_alpha_dummy_349 g) (nb078_wpp_notmem_0858) (nb078_wpp_notmem_0859 g) (TEnvFresh.consFresh (nb078_alpha_dummy_345) (nb078_alpha_dummy_348 g) (nb078_wpp_notmem_0860) (nb078_wpp_notmem_0861 g) (TEnvFresh.consFresh (nb078_alpha_dummy_343) (nb078_alpha_dummy_344 g) (nb078_wpp_notmem_0862) (nb078_wpp_notmem_0863 g) (TEnvFresh.consFresh (nb078_alpha_dummy_339) (nb078_alpha_dummy_341 g) (nb078_wpp_notmem_0864) (nb078_wpp_notmem_0865 g) (TEnvFresh.consFresh (nb078_alpha_dummy_340) (nb078_alpha_dummy_342 g) (nb078_wpp_notmem_0866) (nb078_wpp_notmem_0867 g) (TEnvFresh.consFresh (nb078_alpha_dummy_332) (nb078_alpha_dummy_334 g) (nb078_wpp_notmem_0868) (nb078_wpp_notmem_0869 g) (TEnvFresh.consFresh (nb078_alpha_dummy_331) (nb078_alpha_dummy_333 g) (nb078_wpp_notmem_0870) (nb078_wpp_notmem_0871 g) (TEnvFresh.consFresh (nb078_alpha_dummy_337) (nb078_alpha_dummy_338 g) (nb078_wpp_notmem_0872) (nb078_wpp_notmem_0873 g) (TEnvFresh.consFresh (nb078_alpha_dummy_335) (nb078_alpha_dummy_336 g) (nb078_wpp_notmem_0874) (nb078_wpp_notmem_0875 g) (TEnvFresh.consFresh (nb078_alpha_dummy_289) (nb078_alpha_dummy_292 g) (nb078_wpp_notmem_0876) (nb078_wpp_notmem_0877 g) (TEnvFresh.consFresh (nb078_alpha_dummy_288) (nb078_alpha_dummy_291 g) (nb078_wpp_notmem_0746) (nb078_wpp_notmem_0747 g) (TEnvFresh.consFresh (nb078_alpha_dummy_287) (nb078_alpha_dummy_290 g) (nb078_wpp_notmem_0748) (nb078_wpp_notmem_0749 g) (TEnvFresh.consFresh (nb078_alpha_dummy_293) (nb078_alpha_dummy_294 g) (nb078_wpp_notmem_0750) (nb078_wpp_notmem_0751 g) (TEnvFresh.consFresh (nb078_alpha_dummy_285) (nb078_alpha_dummy_286 g) (nb078_wpp_notmem_0752) (nb078_wpp_notmem_0753 g) (TEnvFresh.consFresh (nb078_alpha_dummy_283) (nb078_alpha_dummy_284 g) (nb078_wpp_notmem_0754) (nb078_wpp_notmem_0755 g) (TEnvFresh.consFresh (nb078_alpha_dummy_001) g (nb078_wpp_notmem_0756) (nb078_wpp_notmem_0757 g) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0032) (nb078_wpp_notmem_0033 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0034) (nb078_wpp_notmem_0035 x) (TEnvFresh.nil ((syn_c1c)).fv))))))))))))))))))))

noncomputable def nb078_wpp_refl_0108 (x : Var) (y : Var) (g : Var) : TReflOn [((nb078_alpha_dummy_347), (nb078_alpha_dummy_350 g)), ((nb078_alpha_dummy_346), (nb078_alpha_dummy_349 g)), ((nb078_alpha_dummy_345), (nb078_alpha_dummy_348 g)), ((nb078_alpha_dummy_343), (nb078_alpha_dummy_344 g)), ((nb078_alpha_dummy_339), (nb078_alpha_dummy_341 g)), ((nb078_alpha_dummy_340), (nb078_alpha_dummy_342 g)), ((nb078_alpha_dummy_332), (nb078_alpha_dummy_334 g)), ((nb078_alpha_dummy_331), (nb078_alpha_dummy_333 g)), ((nb078_alpha_dummy_337), (nb078_alpha_dummy_338 g)), ((nb078_alpha_dummy_335), (nb078_alpha_dummy_336 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0108 x y g)

theorem nb078_wpp_notmem_0878 : (nb078_alpha_dummy_347) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_347, fv_syn_c0] using (nb078_compact_fv_empty_0252)

theorem nb078_wpp_notmem_0879 (g : Var) : (nb078_alpha_dummy_350 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_350, fv_syn_c0] using (nb078_compact_fv_empty_0253 g)

theorem nb078_wpp_notmem_0880 : (nb078_alpha_dummy_346) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_346, fv_syn_c0] using (nb078_compact_fv_empty_0254)

theorem nb078_wpp_notmem_0881 (g : Var) : (nb078_alpha_dummy_349 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_349, fv_syn_c0] using (nb078_compact_fv_empty_0255 g)

theorem nb078_wpp_notmem_0882 : (nb078_alpha_dummy_345) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_345, fv_syn_c0] using (nb078_compact_fv_empty_0256)

theorem nb078_wpp_notmem_0883 (g : Var) : (nb078_alpha_dummy_348 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_348, fv_syn_c0] using (nb078_compact_fv_empty_0257 g)

theorem nb078_wpp_notmem_0884 : (nb078_alpha_dummy_343) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_343, fv_syn_c0] using (nb078_compact_fv_empty_0258)

theorem nb078_wpp_notmem_0885 (g : Var) : (nb078_alpha_dummy_344 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_344, fv_syn_c0] using (nb078_compact_fv_empty_0259 g)

theorem nb078_wpp_notmem_0886 : (nb078_alpha_dummy_339) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_339, fv_syn_c0] using (nb078_compact_fv_empty_0260)

theorem nb078_wpp_notmem_0887 (g : Var) : (nb078_alpha_dummy_341 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_341, fv_syn_c0] using (nb078_compact_fv_empty_0261 g)

theorem nb078_wpp_notmem_0888 : (nb078_alpha_dummy_340) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_340, fv_syn_c0] using (nb078_compact_fv_empty_0262)

theorem nb078_wpp_notmem_0889 (g : Var) : (nb078_alpha_dummy_342 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_342, fv_syn_c0] using (nb078_compact_fv_empty_0263 g)

theorem nb078_wpp_notmem_0890 : (nb078_alpha_dummy_332) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_332, fv_syn_c0] using (nb078_compact_fv_empty_0264)

theorem nb078_wpp_notmem_0891 (g : Var) : (nb078_alpha_dummy_334 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_334, fv_syn_c0] using (nb078_compact_fv_empty_0265 g)

theorem nb078_wpp_notmem_0892 : (nb078_alpha_dummy_331) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_331, fv_syn_c0] using (nb078_compact_fv_empty_0266)

theorem nb078_wpp_notmem_0893 (g : Var) : (nb078_alpha_dummy_333 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_333, fv_syn_c0] using (nb078_compact_fv_empty_0267 g)

theorem nb078_wpp_notmem_0894 : (nb078_alpha_dummy_337) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_337, fv_syn_c0] using (nb078_compact_fv_empty_0268)

theorem nb078_wpp_notmem_0895 (g : Var) : (nb078_alpha_dummy_338 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_338, fv_syn_c0] using (nb078_compact_fv_empty_0269 g)

theorem nb078_wpp_notmem_0896 : (nb078_alpha_dummy_335) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_335, fv_syn_c0] using (nb078_compact_fv_empty_0270)

theorem nb078_wpp_notmem_0897 (g : Var) : (nb078_alpha_dummy_336 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_336, fv_syn_c0] using (nb078_compact_fv_empty_0271 g)

theorem nb078_wpp_notmem_0898 : (nb078_alpha_dummy_289) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_289, fv_syn_c0] using (nb078_compact_fv_empty_0272)

theorem nb078_wpp_notmem_0899 (g : Var) : (nb078_alpha_dummy_292 g) ∉ ((syn_c0)).fv := by
  simpa only [nb078_alpha_dummy_292, fv_syn_c0] using (nb078_compact_fv_empty_0273 g)

theorem nb078_compact_envfresh_0109 (x : Var) (y : Var) (g : Var) : TEnvFresh [((nb078_alpha_dummy_347), (nb078_alpha_dummy_350 g)), ((nb078_alpha_dummy_346), (nb078_alpha_dummy_349 g)), ((nb078_alpha_dummy_345), (nb078_alpha_dummy_348 g)), ((nb078_alpha_dummy_343), (nb078_alpha_dummy_344 g)), ((nb078_alpha_dummy_339), (nb078_alpha_dummy_341 g)), ((nb078_alpha_dummy_340), (nb078_alpha_dummy_342 g)), ((nb078_alpha_dummy_332), (nb078_alpha_dummy_334 g)), ((nb078_alpha_dummy_331), (nb078_alpha_dummy_333 g)), ((nb078_alpha_dummy_337), (nb078_alpha_dummy_338 g)), ((nb078_alpha_dummy_335), (nb078_alpha_dummy_336 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb078_alpha_dummy_347) (nb078_alpha_dummy_350 g) (nb078_wpp_notmem_0878) (nb078_wpp_notmem_0879 g) (TEnvFresh.consFresh (nb078_alpha_dummy_346) (nb078_alpha_dummy_349 g) (nb078_wpp_notmem_0880) (nb078_wpp_notmem_0881 g) (TEnvFresh.consFresh (nb078_alpha_dummy_345) (nb078_alpha_dummy_348 g) (nb078_wpp_notmem_0882) (nb078_wpp_notmem_0883 g) (TEnvFresh.consFresh (nb078_alpha_dummy_343) (nb078_alpha_dummy_344 g) (nb078_wpp_notmem_0884) (nb078_wpp_notmem_0885 g) (TEnvFresh.consFresh (nb078_alpha_dummy_339) (nb078_alpha_dummy_341 g) (nb078_wpp_notmem_0886) (nb078_wpp_notmem_0887 g) (TEnvFresh.consFresh (nb078_alpha_dummy_340) (nb078_alpha_dummy_342 g) (nb078_wpp_notmem_0888) (nb078_wpp_notmem_0889 g) (TEnvFresh.consFresh (nb078_alpha_dummy_332) (nb078_alpha_dummy_334 g) (nb078_wpp_notmem_0890) (nb078_wpp_notmem_0891 g) (TEnvFresh.consFresh (nb078_alpha_dummy_331) (nb078_alpha_dummy_333 g) (nb078_wpp_notmem_0892) (nb078_wpp_notmem_0893 g) (TEnvFresh.consFresh (nb078_alpha_dummy_337) (nb078_alpha_dummy_338 g) (nb078_wpp_notmem_0894) (nb078_wpp_notmem_0895 g) (TEnvFresh.consFresh (nb078_alpha_dummy_335) (nb078_alpha_dummy_336 g) (nb078_wpp_notmem_0896) (nb078_wpp_notmem_0897 g) (TEnvFresh.consFresh (nb078_alpha_dummy_289) (nb078_alpha_dummy_292 g) (nb078_wpp_notmem_0898) (nb078_wpp_notmem_0899 g) (TEnvFresh.consFresh (nb078_alpha_dummy_288) (nb078_alpha_dummy_291 g) (nb078_wpp_notmem_0778) (nb078_wpp_notmem_0779 g) (TEnvFresh.consFresh (nb078_alpha_dummy_287) (nb078_alpha_dummy_290 g) (nb078_wpp_notmem_0780) (nb078_wpp_notmem_0781 g) (TEnvFresh.consFresh (nb078_alpha_dummy_293) (nb078_alpha_dummy_294 g) (nb078_wpp_notmem_0782) (nb078_wpp_notmem_0783 g) (TEnvFresh.consFresh (nb078_alpha_dummy_285) (nb078_alpha_dummy_286 g) (nb078_wpp_notmem_0784) (nb078_wpp_notmem_0785 g) (TEnvFresh.consFresh (nb078_alpha_dummy_283) (nb078_alpha_dummy_284 g) (nb078_wpp_notmem_0786) (nb078_wpp_notmem_0787 g) (TEnvFresh.consFresh (nb078_alpha_dummy_001) g (nb078_wpp_notmem_0788) (nb078_wpp_notmem_0789 g) (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0068) (nb078_wpp_notmem_0069 y) (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0070) (nb078_wpp_notmem_0071 x) (TEnvFresh.nil ((syn_c0)).fv))))))))))))))))))))

noncomputable def nb078_wpp_refl_0109 (x : Var) (y : Var) (g : Var) : TReflOn [((nb078_alpha_dummy_347), (nb078_alpha_dummy_350 g)), ((nb078_alpha_dummy_346), (nb078_alpha_dummy_349 g)), ((nb078_alpha_dummy_345), (nb078_alpha_dummy_348 g)), ((nb078_alpha_dummy_343), (nb078_alpha_dummy_344 g)), ((nb078_alpha_dummy_339), (nb078_alpha_dummy_341 g)), ((nb078_alpha_dummy_340), (nb078_alpha_dummy_342 g)), ((nb078_alpha_dummy_332), (nb078_alpha_dummy_334 g)), ((nb078_alpha_dummy_331), (nb078_alpha_dummy_333 g)), ((nb078_alpha_dummy_337), (nb078_alpha_dummy_338 g)), ((nb078_alpha_dummy_335), (nb078_alpha_dummy_336 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0109 x y g)

theorem nb078_wpp_notmem_0900 : (nb078_alpha_dummy_343) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_343, fv_syn_cnnc] using (nb078_compact_fv_empty_0258)

theorem nb078_wpp_notmem_0901 (g : Var) : (nb078_alpha_dummy_344 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_344, fv_syn_cnnc] using (nb078_compact_fv_empty_0259 g)

theorem nb078_wpp_notmem_0902 : (nb078_alpha_dummy_339) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_339, fv_syn_cnnc] using (nb078_compact_fv_empty_0260)

theorem nb078_wpp_notmem_0903 (g : Var) : (nb078_alpha_dummy_341 g) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_341, fv_syn_cnnc] using (nb078_compact_fv_empty_0261 g)

theorem nb078_wpp_notmem_0904 : (nb078_alpha_dummy_340) ∉ ((syn_cnnc)).fv := by
  simpa only [nb078_alpha_dummy_340, fv_syn_cnnc] using (nb078_compact_fv_empty_0262)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
