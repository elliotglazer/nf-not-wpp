import NAR4C060C001Part007

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

theorem nb060_compact_envfresh_0016 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TEnvFresh [((nb060_alpha_dummy_091), (nb060_alpha_dummy_092 y z)), ((nb060_alpha_dummy_087), (nb060_alpha_dummy_089 y z)), ((nb060_alpha_dummy_088), (nb060_alpha_dummy_090 y z)), ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)), ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)), ((nb060_alpha_dummy_085), (nb060_alpha_dummy_086 y z)), ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb060_alpha_dummy_091) (nb060_alpha_dummy_092 y z) (nb060_wpp_notmem_0252) (nb060_wpp_notmem_0253 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_087) (nb060_alpha_dummy_089 y z) (nb060_wpp_notmem_0254) (nb060_wpp_notmem_0255 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_088) (nb060_alpha_dummy_090 y z) (nb060_wpp_notmem_0256) (nb060_wpp_notmem_0257 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_080) (nb060_alpha_dummy_082 y z) (nb060_wpp_notmem_0258) (nb060_wpp_notmem_0259 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_079) (nb060_alpha_dummy_081 y z) (nb060_wpp_notmem_0260) (nb060_wpp_notmem_0261 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_085) (nb060_alpha_dummy_086 y z) (nb060_wpp_notmem_0262) (nb060_wpp_notmem_0263 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_083) (nb060_alpha_dummy_084 y z) (nb060_wpp_notmem_0264) (nb060_wpp_notmem_0265 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_004) z (nb060_wpp_notmem_0172) (nb060_wpp_notmem_0173 z) (TEnvFresh.consFresh (nb060_alpha_dummy_003) y (nb060_wpp_notmem_0174) (nb060_wpp_notmem_0175 y) (TEnvFresh.consFresh (nb060_alpha_dummy_002) x (nb060_wpp_notmem_0176) (nb060_wpp_notmem_0177 x) (TEnvFresh.consFresh (nb060_alpha_dummy_000) a (nb060_wpp_notmem_0066) (nb060_wpp_notmem_0067 a) (TEnvFresh.consFresh (nb060_alpha_dummy_001) r (nb060_wpp_notmem_0068) (nb060_wpp_notmem_0069 r) (TEnvFresh.consFresh (nb060_alpha_dummy_005) (nb060_alpha_dummy_006 x y z r a) (nb060_wpp_notmem_0070) (nb060_wpp_notmem_0071 x y z r a) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))

noncomputable def nb060_wpp_refl_0016 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TReflOn [((nb060_alpha_dummy_091), (nb060_alpha_dummy_092 y z)), ((nb060_alpha_dummy_087), (nb060_alpha_dummy_089 y z)), ((nb060_alpha_dummy_088), (nb060_alpha_dummy_090 y z)), ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)), ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)), ((nb060_alpha_dummy_085), (nb060_alpha_dummy_086 y z)), ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb060_compact_envfresh_0016 x y z r a)

noncomputable def nb060_split_alpha_0011 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) (dv_y_z : y ≠ z) : TAlphaWff [((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)), ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)), ((nb060_alpha_dummy_085), (nb060_alpha_dummy_086 y z)), ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] (Wff.imp (Wff.classMem (Class.cv (nb060_alpha_dummy_080)) (Class.cv (nb060_alpha_dummy_003))) (Wff.neg (Wff.classEq (Class.cv (nb060_alpha_dummy_079)) (syn_cphi (Class.cv (nb060_alpha_dummy_080)))))) (Wff.imp (Wff.classMem (Class.cv (nb060_alpha_dummy_082 y z)) (Class.cv y)) (Wff.neg (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z)) (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0080) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0082 y z) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0080) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0082 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0084) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0085 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0081) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0083 y z) 0)) (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_y_z (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_003))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv) (by decide)) (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv z)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0086) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0087 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0086) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0087 y z) 1)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_080))).fv) (by decide)) (freshVar_injective (((Class.cv (nb060_alpha_dummy_082 y z))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0090) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0091 y z) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0090) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0091 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0088) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0089 y z) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb060_alpha_dummy_095), (nb060_alpha_dummy_098 y z)), ((nb060_alpha_dummy_094), (nb060_alpha_dummy_097 y z)), ((nb060_alpha_dummy_093), (nb060_alpha_dummy_096 y z)), ((nb060_alpha_dummy_091), (nb060_alpha_dummy_092 y z)), ((nb060_alpha_dummy_087), (nb060_alpha_dummy_089 y z)), ((nb060_alpha_dummy_088), (nb060_alpha_dummy_090 y z)), ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)), ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)), ((nb060_alpha_dummy_085), (nb060_alpha_dummy_086 y z)), ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] (syn_c1c) (nb060_wpp_refl_0014 x y z r a))) (TAlphaWff.neg (TAlphaWff.neg (nb060_split_alpha_0010 x y z r a)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0088) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0089 y z) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb060_alpha_dummy_091), (nb060_alpha_dummy_092 y z)), ((nb060_alpha_dummy_087), (nb060_alpha_dummy_089 y z)), ((nb060_alpha_dummy_088), (nb060_alpha_dummy_090 y z)), ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)), ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)), ((nb060_alpha_dummy_085), (nb060_alpha_dummy_086 y z)), ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] (syn_cnnc) (nb060_wpp_refl_0016 x y z r a))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0088) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0089 y z) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0088) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0089 y z) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb060_alpha_dummy_091), (nb060_alpha_dummy_092 y z)), ((nb060_alpha_dummy_087), (nb060_alpha_dummy_089 y z)), ((nb060_alpha_dummy_088), (nb060_alpha_dummy_090 y z)), ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)), ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)), ((nb060_alpha_dummy_085), (nb060_alpha_dummy_086 y z)), ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] (syn_cnnc) (nb060_wpp_refl_0016 x y z r a))))))))))))))))))))

theorem nb060_compact_fv_empty_0084 : (nb060_alpha_dummy_113) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0266 : (nb060_alpha_dummy_113) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_113, fv_syn_c1c] using (nb060_compact_fv_empty_0084)

theorem nb060_compact_fv_empty_0085 (y : Var) (z : Var) : (nb060_alpha_dummy_114 y z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0267 (y : Var) (z : Var) : (nb060_alpha_dummy_114 y z) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_114, fv_syn_c1c] using (nb060_compact_fv_empty_0085 y z)

theorem nb060_compact_fv_empty_0086 : (nb060_alpha_dummy_111) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0268 : (nb060_alpha_dummy_111) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_111, fv_syn_c1c] using (nb060_compact_fv_empty_0086)

theorem nb060_compact_fv_empty_0087 (y : Var) (z : Var) : (nb060_alpha_dummy_112 y z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0269 (y : Var) (z : Var) : (nb060_alpha_dummy_112 y z) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_112, fv_syn_c1c] using (nb060_compact_fv_empty_0087 y z)

theorem nb060_compact_fv_empty_0088 : (nb060_alpha_dummy_109) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0270 : (nb060_alpha_dummy_109) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_109, fv_syn_c1c] using (nb060_compact_fv_empty_0088)

theorem nb060_compact_fv_empty_0089 (y : Var) (z : Var) : (nb060_alpha_dummy_110 y z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0271 (y : Var) (z : Var) : (nb060_alpha_dummy_110 y z) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_110, fv_syn_c1c] using (nb060_compact_fv_empty_0089 y z)

theorem nb060_compact_envfresh_0017 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TEnvFresh [((nb060_alpha_dummy_095), (nb060_alpha_dummy_098 y z)), ((nb060_alpha_dummy_094), (nb060_alpha_dummy_097 y z)), ((nb060_alpha_dummy_093), (nb060_alpha_dummy_096 y z)), ((nb060_alpha_dummy_091), (nb060_alpha_dummy_092 y z)), ((nb060_alpha_dummy_087), (nb060_alpha_dummy_089 y z)), ((nb060_alpha_dummy_088), (nb060_alpha_dummy_090 y z)), ((nb060_alpha_dummy_113), (nb060_alpha_dummy_114 y z)), ((nb060_alpha_dummy_111), (nb060_alpha_dummy_112 y z)), ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)), ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)), ((nb060_alpha_dummy_109), (nb060_alpha_dummy_110 y z)), ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] ((syn_c1c)).fv := by
  exact (TEnvFresh.consFresh (nb060_alpha_dummy_095) (nb060_alpha_dummy_098 y z) (nb060_wpp_notmem_0212) (nb060_wpp_notmem_0213 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_094) (nb060_alpha_dummy_097 y z) (nb060_wpp_notmem_0214) (nb060_wpp_notmem_0215 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_093) (nb060_alpha_dummy_096 y z) (nb060_wpp_notmem_0216) (nb060_wpp_notmem_0217 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_091) (nb060_alpha_dummy_092 y z) (nb060_wpp_notmem_0218) (nb060_wpp_notmem_0219 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_087) (nb060_alpha_dummy_089 y z) (nb060_wpp_notmem_0220) (nb060_wpp_notmem_0221 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_088) (nb060_alpha_dummy_090 y z) (nb060_wpp_notmem_0222) (nb060_wpp_notmem_0223 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_113) (nb060_alpha_dummy_114 y z) (nb060_wpp_notmem_0266) (nb060_wpp_notmem_0267 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_111) (nb060_alpha_dummy_112 y z) (nb060_wpp_notmem_0268) (nb060_wpp_notmem_0269 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_080) (nb060_alpha_dummy_082 y z) (nb060_wpp_notmem_0224) (nb060_wpp_notmem_0225 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_079) (nb060_alpha_dummy_081 y z) (nb060_wpp_notmem_0226) (nb060_wpp_notmem_0227 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_109) (nb060_alpha_dummy_110 y z) (nb060_wpp_notmem_0270) (nb060_wpp_notmem_0271 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_083) (nb060_alpha_dummy_084 y z) (nb060_wpp_notmem_0230) (nb060_wpp_notmem_0231 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_004) z (nb060_wpp_notmem_0126) (nb060_wpp_notmem_0127 z) (TEnvFresh.consFresh (nb060_alpha_dummy_003) y (nb060_wpp_notmem_0128) (nb060_wpp_notmem_0129 y) (TEnvFresh.consFresh (nb060_alpha_dummy_002) x (nb060_wpp_notmem_0130) (nb060_wpp_notmem_0131 x) (TEnvFresh.consFresh (nb060_alpha_dummy_000) a (nb060_wpp_notmem_0020) (nb060_wpp_notmem_0021 a) (TEnvFresh.consFresh (nb060_alpha_dummy_001) r (nb060_wpp_notmem_0022) (nb060_wpp_notmem_0023 r) (TEnvFresh.consFresh (nb060_alpha_dummy_005) (nb060_alpha_dummy_006 x y z r a) (nb060_wpp_notmem_0024) (nb060_wpp_notmem_0025 x y z r a) (TEnvFresh.nil ((syn_c1c)).fv)))))))))))))))))))

noncomputable def nb060_wpp_refl_0017 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TReflOn [((nb060_alpha_dummy_095), (nb060_alpha_dummy_098 y z)), ((nb060_alpha_dummy_094), (nb060_alpha_dummy_097 y z)), ((nb060_alpha_dummy_093), (nb060_alpha_dummy_096 y z)), ((nb060_alpha_dummy_091), (nb060_alpha_dummy_092 y z)), ((nb060_alpha_dummy_087), (nb060_alpha_dummy_089 y z)), ((nb060_alpha_dummy_088), (nb060_alpha_dummy_090 y z)), ((nb060_alpha_dummy_113), (nb060_alpha_dummy_114 y z)), ((nb060_alpha_dummy_111), (nb060_alpha_dummy_112 y z)), ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)), ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)), ((nb060_alpha_dummy_109), (nb060_alpha_dummy_110 y z)), ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] ((syn_c1c)).fv :=
  TEnvFresh.reflOn (nb060_compact_envfresh_0017 x y z r a)

theorem nb060_wpp_notmem_0272 : (nb060_alpha_dummy_113) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_113, fv_syn_c0] using (nb060_compact_fv_empty_0084)

theorem nb060_wpp_notmem_0273 (y : Var) (z : Var) : (nb060_alpha_dummy_114 y z) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_114, fv_syn_c0] using (nb060_compact_fv_empty_0085 y z)

theorem nb060_wpp_notmem_0274 : (nb060_alpha_dummy_111) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_111, fv_syn_c0] using (nb060_compact_fv_empty_0086)

theorem nb060_wpp_notmem_0275 (y : Var) (z : Var) : (nb060_alpha_dummy_112 y z) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_112, fv_syn_c0] using (nb060_compact_fv_empty_0087 y z)

theorem nb060_wpp_notmem_0276 : (nb060_alpha_dummy_109) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_109, fv_syn_c0] using (nb060_compact_fv_empty_0088)

theorem nb060_wpp_notmem_0277 (y : Var) (z : Var) : (nb060_alpha_dummy_110 y z) ∉ ((syn_c0)).fv := by
  simpa only [nb060_alpha_dummy_110, fv_syn_c0] using (nb060_compact_fv_empty_0089 y z)

theorem nb060_compact_envfresh_0018 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TEnvFresh [((nb060_alpha_dummy_095), (nb060_alpha_dummy_098 y z)), ((nb060_alpha_dummy_094), (nb060_alpha_dummy_097 y z)), ((nb060_alpha_dummy_093), (nb060_alpha_dummy_096 y z)), ((nb060_alpha_dummy_091), (nb060_alpha_dummy_092 y z)), ((nb060_alpha_dummy_087), (nb060_alpha_dummy_089 y z)), ((nb060_alpha_dummy_088), (nb060_alpha_dummy_090 y z)), ((nb060_alpha_dummy_113), (nb060_alpha_dummy_114 y z)), ((nb060_alpha_dummy_111), (nb060_alpha_dummy_112 y z)), ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)), ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)), ((nb060_alpha_dummy_109), (nb060_alpha_dummy_110 y z)), ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] ((syn_c0)).fv := by
  exact (TEnvFresh.consFresh (nb060_alpha_dummy_095) (nb060_alpha_dummy_098 y z) (nb060_wpp_notmem_0232) (nb060_wpp_notmem_0233 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_094) (nb060_alpha_dummy_097 y z) (nb060_wpp_notmem_0234) (nb060_wpp_notmem_0235 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_093) (nb060_alpha_dummy_096 y z) (nb060_wpp_notmem_0236) (nb060_wpp_notmem_0237 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_091) (nb060_alpha_dummy_092 y z) (nb060_wpp_notmem_0238) (nb060_wpp_notmem_0239 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_087) (nb060_alpha_dummy_089 y z) (nb060_wpp_notmem_0240) (nb060_wpp_notmem_0241 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_088) (nb060_alpha_dummy_090 y z) (nb060_wpp_notmem_0242) (nb060_wpp_notmem_0243 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_113) (nb060_alpha_dummy_114 y z) (nb060_wpp_notmem_0272) (nb060_wpp_notmem_0273 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_111) (nb060_alpha_dummy_112 y z) (nb060_wpp_notmem_0274) (nb060_wpp_notmem_0275 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_080) (nb060_alpha_dummy_082 y z) (nb060_wpp_notmem_0244) (nb060_wpp_notmem_0245 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_079) (nb060_alpha_dummy_081 y z) (nb060_wpp_notmem_0246) (nb060_wpp_notmem_0247 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_109) (nb060_alpha_dummy_110 y z) (nb060_wpp_notmem_0276) (nb060_wpp_notmem_0277 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_083) (nb060_alpha_dummy_084 y z) (nb060_wpp_notmem_0250) (nb060_wpp_notmem_0251 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_004) z (nb060_wpp_notmem_0152) (nb060_wpp_notmem_0153 z) (TEnvFresh.consFresh (nb060_alpha_dummy_003) y (nb060_wpp_notmem_0154) (nb060_wpp_notmem_0155 y) (TEnvFresh.consFresh (nb060_alpha_dummy_002) x (nb060_wpp_notmem_0156) (nb060_wpp_notmem_0157 x) (TEnvFresh.consFresh (nb060_alpha_dummy_000) a (nb060_wpp_notmem_0046) (nb060_wpp_notmem_0047 a) (TEnvFresh.consFresh (nb060_alpha_dummy_001) r (nb060_wpp_notmem_0048) (nb060_wpp_notmem_0049 r) (TEnvFresh.consFresh (nb060_alpha_dummy_005) (nb060_alpha_dummy_006 x y z r a) (nb060_wpp_notmem_0050) (nb060_wpp_notmem_0051 x y z r a) (TEnvFresh.nil ((syn_c0)).fv)))))))))))))))))))

noncomputable def nb060_wpp_refl_0018 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TReflOn [((nb060_alpha_dummy_095), (nb060_alpha_dummy_098 y z)), ((nb060_alpha_dummy_094), (nb060_alpha_dummy_097 y z)), ((nb060_alpha_dummy_093), (nb060_alpha_dummy_096 y z)), ((nb060_alpha_dummy_091), (nb060_alpha_dummy_092 y z)), ((nb060_alpha_dummy_087), (nb060_alpha_dummy_089 y z)), ((nb060_alpha_dummy_088), (nb060_alpha_dummy_090 y z)), ((nb060_alpha_dummy_113), (nb060_alpha_dummy_114 y z)), ((nb060_alpha_dummy_111), (nb060_alpha_dummy_112 y z)), ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)), ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)), ((nb060_alpha_dummy_109), (nb060_alpha_dummy_110 y z)), ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] ((syn_c0)).fv :=
  TEnvFresh.reflOn (nb060_compact_envfresh_0018 x y z r a)

noncomputable def nb060_split_alpha_0012 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TAlphaWff [((nb060_alpha_dummy_095), (nb060_alpha_dummy_098 y z)), ((nb060_alpha_dummy_094), (nb060_alpha_dummy_097 y z)), ((nb060_alpha_dummy_093), (nb060_alpha_dummy_096 y z)), ((nb060_alpha_dummy_091), (nb060_alpha_dummy_092 y z)), ((nb060_alpha_dummy_087), (nb060_alpha_dummy_089 y z)), ((nb060_alpha_dummy_088), (nb060_alpha_dummy_090 y z)), ((nb060_alpha_dummy_113), (nb060_alpha_dummy_114 y z)), ((nb060_alpha_dummy_111), (nb060_alpha_dummy_112 y z)), ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)), ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)), ((nb060_alpha_dummy_109), (nb060_alpha_dummy_110 y z)), ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb060_alpha_dummy_094)) (Class.cv (nb060_alpha_dummy_095))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb060_alpha_dummy_093)) (syn_cun (Class.cv (nb060_alpha_dummy_094)) (Class.cv (nb060_alpha_dummy_095)))))) (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb060_alpha_dummy_097 y z)) (Class.cv (nb060_alpha_dummy_098 y z))) (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb060_alpha_dummy_096 y z)) (syn_cun (Class.cv (nb060_alpha_dummy_097 y z)) (Class.cv (nb060_alpha_dummy_098 y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0094) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0095 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0092) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0093 y z) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0098) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0099 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0096) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0097 y z) 0)) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0094) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0095 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0092) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0093 y z) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0098) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0099 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0096) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0097 y z) 0)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.refl_of_reflOn [((nb060_alpha_dummy_095), (nb060_alpha_dummy_098 y z)), ((nb060_alpha_dummy_094), (nb060_alpha_dummy_097 y z)), ((nb060_alpha_dummy_093), (nb060_alpha_dummy_096 y z)), ((nb060_alpha_dummy_091), (nb060_alpha_dummy_092 y z)), ((nb060_alpha_dummy_087), (nb060_alpha_dummy_089 y z)), ((nb060_alpha_dummy_088), (nb060_alpha_dummy_090 y z)), ((nb060_alpha_dummy_113), (nb060_alpha_dummy_114 y z)), ((nb060_alpha_dummy_111), (nb060_alpha_dummy_112 y z)), ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)), ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)), ((nb060_alpha_dummy_109), (nb060_alpha_dummy_110 y z)), ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] (syn_c0) (nb060_wpp_refl_0018 x y z r a))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0102) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0103 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0100) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0101 y z) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0102) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0103 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0100) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0101 y z) 0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_087))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb060_alpha_dummy_089 y z))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0106) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0107 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0104) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0105 y z) 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0106) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0107 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0104) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0105 y z) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))

theorem nb060_wpp_notmem_0278 : (nb060_alpha_dummy_113) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_113, fv_syn_cnnc] using (nb060_compact_fv_empty_0084)

theorem nb060_wpp_notmem_0279 (y : Var) (z : Var) : (nb060_alpha_dummy_114 y z) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_114, fv_syn_cnnc] using (nb060_compact_fv_empty_0085 y z)

theorem nb060_wpp_notmem_0280 : (nb060_alpha_dummy_111) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_111, fv_syn_cnnc] using (nb060_compact_fv_empty_0086)

theorem nb060_wpp_notmem_0281 (y : Var) (z : Var) : (nb060_alpha_dummy_112 y z) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_112, fv_syn_cnnc] using (nb060_compact_fv_empty_0087 y z)

theorem nb060_wpp_notmem_0282 : (nb060_alpha_dummy_109) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_109, fv_syn_cnnc] using (nb060_compact_fv_empty_0088)

theorem nb060_wpp_notmem_0283 (y : Var) (z : Var) : (nb060_alpha_dummy_110 y z) ∉ ((syn_cnnc)).fv := by
  simpa only [nb060_alpha_dummy_110, fv_syn_cnnc] using (nb060_compact_fv_empty_0089 y z)

theorem nb060_compact_envfresh_0019 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TEnvFresh [((nb060_alpha_dummy_091), (nb060_alpha_dummy_092 y z)), ((nb060_alpha_dummy_087), (nb060_alpha_dummy_089 y z)), ((nb060_alpha_dummy_088), (nb060_alpha_dummy_090 y z)), ((nb060_alpha_dummy_113), (nb060_alpha_dummy_114 y z)), ((nb060_alpha_dummy_111), (nb060_alpha_dummy_112 y z)), ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)), ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)), ((nb060_alpha_dummy_109), (nb060_alpha_dummy_110 y z)), ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] ((syn_cnnc)).fv := by
  exact (TEnvFresh.consFresh (nb060_alpha_dummy_091) (nb060_alpha_dummy_092 y z) (nb060_wpp_notmem_0252) (nb060_wpp_notmem_0253 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_087) (nb060_alpha_dummy_089 y z) (nb060_wpp_notmem_0254) (nb060_wpp_notmem_0255 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_088) (nb060_alpha_dummy_090 y z) (nb060_wpp_notmem_0256) (nb060_wpp_notmem_0257 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_113) (nb060_alpha_dummy_114 y z) (nb060_wpp_notmem_0278) (nb060_wpp_notmem_0279 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_111) (nb060_alpha_dummy_112 y z) (nb060_wpp_notmem_0280) (nb060_wpp_notmem_0281 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_080) (nb060_alpha_dummy_082 y z) (nb060_wpp_notmem_0258) (nb060_wpp_notmem_0259 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_079) (nb060_alpha_dummy_081 y z) (nb060_wpp_notmem_0260) (nb060_wpp_notmem_0261 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_109) (nb060_alpha_dummy_110 y z) (nb060_wpp_notmem_0282) (nb060_wpp_notmem_0283 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_083) (nb060_alpha_dummy_084 y z) (nb060_wpp_notmem_0264) (nb060_wpp_notmem_0265 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_004) z (nb060_wpp_notmem_0172) (nb060_wpp_notmem_0173 z) (TEnvFresh.consFresh (nb060_alpha_dummy_003) y (nb060_wpp_notmem_0174) (nb060_wpp_notmem_0175 y) (TEnvFresh.consFresh (nb060_alpha_dummy_002) x (nb060_wpp_notmem_0176) (nb060_wpp_notmem_0177 x) (TEnvFresh.consFresh (nb060_alpha_dummy_000) a (nb060_wpp_notmem_0066) (nb060_wpp_notmem_0067 a) (TEnvFresh.consFresh (nb060_alpha_dummy_001) r (nb060_wpp_notmem_0068) (nb060_wpp_notmem_0069 r) (TEnvFresh.consFresh (nb060_alpha_dummy_005) (nb060_alpha_dummy_006 x y z r a) (nb060_wpp_notmem_0070) (nb060_wpp_notmem_0071 x y z r a) (TEnvFresh.nil ((syn_cnnc)).fv))))))))))))))))

noncomputable def nb060_wpp_refl_0019 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TReflOn [((nb060_alpha_dummy_091), (nb060_alpha_dummy_092 y z)), ((nb060_alpha_dummy_087), (nb060_alpha_dummy_089 y z)), ((nb060_alpha_dummy_088), (nb060_alpha_dummy_090 y z)), ((nb060_alpha_dummy_113), (nb060_alpha_dummy_114 y z)), ((nb060_alpha_dummy_111), (nb060_alpha_dummy_112 y z)), ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)), ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)), ((nb060_alpha_dummy_109), (nb060_alpha_dummy_110 y z)), ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] ((syn_cnnc)).fv :=
  TEnvFresh.reflOn (nb060_compact_envfresh_0019 x y z r a)

noncomputable def nb060_split_alpha_0013 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TAlphaWff [((nb060_alpha_dummy_087), (nb060_alpha_dummy_089 y z)), ((nb060_alpha_dummy_088), (nb060_alpha_dummy_090 y z)), ((nb060_alpha_dummy_113), (nb060_alpha_dummy_114 y z)), ((nb060_alpha_dummy_111), (nb060_alpha_dummy_112 y z)), ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)), ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)), ((nb060_alpha_dummy_109), (nb060_alpha_dummy_110 y z)), ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] (Wff.imp (Wff.classMem (Class.cv (nb060_alpha_dummy_087)) (Class.cv (nb060_alpha_dummy_080))) (Wff.neg (Wff.classEq (Class.cv (nb060_alpha_dummy_088)) (syn_cif (Wff.classMem (Class.cv (nb060_alpha_dummy_087)) (syn_cnnc)) (syn_cplc (Class.cv (nb060_alpha_dummy_087)) (syn_c1c)) (Class.cv (nb060_alpha_dummy_087)))))) (Wff.imp (Wff.classMem (Class.cv (nb060_alpha_dummy_089 y z)) (Class.cv (nb060_alpha_dummy_082 y z))) (Wff.neg (Wff.classEq (Class.cv (nb060_alpha_dummy_090 y z)) (syn_cif (Wff.classMem (Class.cv (nb060_alpha_dummy_089 y z)) (syn_cnnc)) (syn_cplc (Class.cv (nb060_alpha_dummy_089 y z)) (syn_c1c)) (Class.cv (nb060_alpha_dummy_089 y z)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0086) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0087 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0086) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0087 y z) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0116) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0117 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0114) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0115 y z) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_080))).fv) (by decide)) (freshVar_injective (((Class.cv (nb060_alpha_dummy_082 y z))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0090) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0091 y z) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0090) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0091 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0088) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0089 y z) 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb060_alpha_dummy_095), (nb060_alpha_dummy_098 y z)), ((nb060_alpha_dummy_094), (nb060_alpha_dummy_097 y z)), ((nb060_alpha_dummy_093), (nb060_alpha_dummy_096 y z)), ((nb060_alpha_dummy_091), (nb060_alpha_dummy_092 y z)), ((nb060_alpha_dummy_087), (nb060_alpha_dummy_089 y z)), ((nb060_alpha_dummy_088), (nb060_alpha_dummy_090 y z)), ((nb060_alpha_dummy_113), (nb060_alpha_dummy_114 y z)), ((nb060_alpha_dummy_111), (nb060_alpha_dummy_112 y z)), ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)), ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)), ((nb060_alpha_dummy_109), (nb060_alpha_dummy_110 y z)), ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] (syn_c1c) (nb060_wpp_refl_0017 x y z r a))) (TAlphaWff.neg (TAlphaWff.neg (nb060_split_alpha_0012 x y z r a)))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0088) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0089 y z) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb060_alpha_dummy_091), (nb060_alpha_dummy_092 y z)), ((nb060_alpha_dummy_087), (nb060_alpha_dummy_089 y z)), ((nb060_alpha_dummy_088), (nb060_alpha_dummy_090 y z)), ((nb060_alpha_dummy_113), (nb060_alpha_dummy_114 y z)), ((nb060_alpha_dummy_111), (nb060_alpha_dummy_112 y z)), ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)), ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)), ((nb060_alpha_dummy_109), (nb060_alpha_dummy_110 y z)), ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] (syn_cnnc) (nb060_wpp_refl_0019 x y z r a))))))) (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0088) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0089 y z) 0)) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0088) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0089 y z) 0)) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_reflOn [((nb060_alpha_dummy_091), (nb060_alpha_dummy_092 y z)), ((nb060_alpha_dummy_087), (nb060_alpha_dummy_089 y z)), ((nb060_alpha_dummy_088), (nb060_alpha_dummy_090 y z)), ((nb060_alpha_dummy_113), (nb060_alpha_dummy_114 y z)), ((nb060_alpha_dummy_111), (nb060_alpha_dummy_112 y z)), ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)), ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)), ((nb060_alpha_dummy_109), (nb060_alpha_dummy_110 y z)), ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] (syn_cnnc) (nb060_wpp_refl_0019 x y z r a))))))))))))

theorem nb060_wpp_notmem_0284 : (nb060_alpha_dummy_111) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb060_alpha_dummy_111, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb060_compact_fv_empty_0086)

theorem nb060_wpp_notmem_0285 (y : Var) (z : Var) : (nb060_alpha_dummy_112 y z) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb060_alpha_dummy_112, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb060_compact_fv_empty_0087 y z)

theorem nb060_wpp_notmem_0286 : (nb060_alpha_dummy_080) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb060_alpha_dummy_080, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb060_compact_fv_empty_0076)

theorem nb060_wpp_notmem_0287 (y : Var) (z : Var) : (nb060_alpha_dummy_082 y z) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb060_alpha_dummy_082, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb060_compact_fv_empty_0077 y z)

theorem nb060_wpp_notmem_0288 : (nb060_alpha_dummy_079) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb060_alpha_dummy_079, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb060_compact_fv_empty_0078)

theorem nb060_wpp_notmem_0289 (y : Var) (z : Var) : (nb060_alpha_dummy_081 y z) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb060_alpha_dummy_081, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb060_compact_fv_empty_0079 y z)

theorem nb060_wpp_notmem_0290 : (nb060_alpha_dummy_109) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb060_alpha_dummy_109, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb060_compact_fv_empty_0088)

theorem nb060_wpp_notmem_0291 (y : Var) (z : Var) : (nb060_alpha_dummy_110 y z) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb060_alpha_dummy_110, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb060_compact_fv_empty_0089 y z)

theorem nb060_wpp_notmem_0292 : (nb060_alpha_dummy_083) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb060_alpha_dummy_083, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb060_compact_fv_empty_0082)

theorem nb060_wpp_notmem_0293 (y : Var) (z : Var) : (nb060_alpha_dummy_084 y z) ∉ ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  simpa only [nb060_alpha_dummy_084, fv_syn_ccompl, fv_syn_csn, fv_syn_c0c] using (nb060_compact_fv_empty_0083 y z)

theorem nb060_compact_envfresh_0020 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TEnvFresh [((nb060_alpha_dummy_111), (nb060_alpha_dummy_112 y z)), ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)), ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)), ((nb060_alpha_dummy_109), (nb060_alpha_dummy_110 y z)), ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] ((syn_ccompl (syn_csn (syn_c0c)))).fv := by
  exact (TEnvFresh.consFresh (nb060_alpha_dummy_111) (nb060_alpha_dummy_112 y z) (nb060_wpp_notmem_0284) (nb060_wpp_notmem_0285 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_080) (nb060_alpha_dummy_082 y z) (nb060_wpp_notmem_0286) (nb060_wpp_notmem_0287 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_079) (nb060_alpha_dummy_081 y z) (nb060_wpp_notmem_0288) (nb060_wpp_notmem_0289 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_109) (nb060_alpha_dummy_110 y z) (nb060_wpp_notmem_0290) (nb060_wpp_notmem_0291 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_083) (nb060_alpha_dummy_084 y z) (nb060_wpp_notmem_0292) (nb060_wpp_notmem_0293 y z) (TEnvFresh.consFresh (nb060_alpha_dummy_004) z (nb060_wpp_notmem_0206) (nb060_wpp_notmem_0207 z) (TEnvFresh.consFresh (nb060_alpha_dummy_003) y (nb060_wpp_notmem_0208) (nb060_wpp_notmem_0209 y) (TEnvFresh.consFresh (nb060_alpha_dummy_002) x (nb060_wpp_notmem_0210) (nb060_wpp_notmem_0211 x) (TEnvFresh.consFresh (nb060_alpha_dummy_000) a (nb060_wpp_notmem_0100) (nb060_wpp_notmem_0101 a) (TEnvFresh.consFresh (nb060_alpha_dummy_001) r (nb060_wpp_notmem_0102) (nb060_wpp_notmem_0103 r) (TEnvFresh.consFresh (nb060_alpha_dummy_005) (nb060_alpha_dummy_006 x y z r a) (nb060_wpp_notmem_0104) (nb060_wpp_notmem_0105 x y z r a) (TEnvFresh.nil ((syn_ccompl (syn_csn (syn_c0c)))).fv))))))))))))

noncomputable def nb060_wpp_refl_0020 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TReflOn [((nb060_alpha_dummy_111), (nb060_alpha_dummy_112 y z)), ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)), ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)), ((nb060_alpha_dummy_109), (nb060_alpha_dummy_110 y z)), ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] ((syn_ccompl (syn_csn (syn_c0c)))).fv :=
  TEnvFresh.reflOn (nb060_compact_envfresh_0020 x y z r a)

noncomputable def nb060_split_alpha_0014 (x : Var) (y : Var) (z : Var) (r : Var) (a : Var) : TAlphaClass [((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] (Class.cab (nb060_alpha_dummy_109) (syn_wnan (Wff.classMem (Class.cv (nb060_alpha_dummy_109)) (Class.cab (nb060_alpha_dummy_079) (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_004)) (Wff.classEq (Class.cv (nb060_alpha_dummy_079)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_080))) (syn_csn (syn_c0c))))))) (Wff.classMem (Class.cv (nb060_alpha_dummy_109)) (Class.cab (nb060_alpha_dummy_079) (syn_wrex (nb060_alpha_dummy_080) (Class.cv (nb060_alpha_dummy_004)) (Wff.classEq (Class.cv (nb060_alpha_dummy_079)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_080))) (syn_csn (syn_c0c))))))))) (Class.cab (nb060_alpha_dummy_110 y z) (syn_wnan (Wff.classMem (Class.cv (nb060_alpha_dummy_110 y z)) (Class.cab (nb060_alpha_dummy_081 y z) (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv z) (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))) (syn_csn (syn_c0c))))))) (Wff.classMem (Class.cv (nb060_alpha_dummy_110 y z)) (Class.cab (nb060_alpha_dummy_081 y z) (syn_wrex (nb060_alpha_dummy_082 y z) (Class.cv z) (Wff.classEq (Class.cv (nb060_alpha_dummy_081 y z)) (syn_cun (syn_cphi (Class.cv (nb060_alpha_dummy_082 y z))) (syn_csn (syn_c0c))))))))) :=
  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0108) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0110 y z) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0108) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0110 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0112) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0113 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0109) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0111 y z) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_003))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv) (by decide)) (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv z)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb060_split_alpha_0013 x y z r a))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb060_split_alpha_0013 x y z r a))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb060_alpha_dummy_111), (nb060_alpha_dummy_112 y z)), ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)), ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)), ((nb060_alpha_dummy_109), (nb060_alpha_dummy_110 y z)), ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] (syn_ccompl (syn_csn (syn_c0c))) (nb060_wpp_refl_0020 x y z r a))))))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0108) 1)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0110 y z) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0108) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0110 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0112) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0113 y z) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0109) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb060_support_mem_0111 y z) 0)) (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb060_alpha_dummy_003))).fv ∪ ((Class.cv (nb060_alpha_dummy_004))).fv) (by decide)) (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv z)).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb060_split_alpha_0013 x y z r a))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.neg (nb060_split_alpha_0013 x y z r a))))))))))))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_reflOn [((nb060_alpha_dummy_111), (nb060_alpha_dummy_112 y z)), ((nb060_alpha_dummy_080), (nb060_alpha_dummy_082 y z)), ((nb060_alpha_dummy_079), (nb060_alpha_dummy_081 y z)), ((nb060_alpha_dummy_109), (nb060_alpha_dummy_110 y z)), ((nb060_alpha_dummy_083), (nb060_alpha_dummy_084 y z)), ((nb060_alpha_dummy_004), z), ((nb060_alpha_dummy_003), y), ((nb060_alpha_dummy_002), x), ((nb060_alpha_dummy_000), a), ((nb060_alpha_dummy_001), r), ((nb060_alpha_dummy_005), (nb060_alpha_dummy_006 x y z r a))] (syn_ccompl (syn_csn (syn_c0c))) (nb060_wpp_refl_0020 x y z r a))))))))))))))))))))))

theorem nb060_compact_fv_empty_0090 : (nb060_alpha_dummy_131) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0294 : (nb060_alpha_dummy_131) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_131, fv_syn_c1c] using (nb060_compact_fv_empty_0090)

theorem nb060_compact_fv_empty_0091 (x : Var) (z : Var) : (nb060_alpha_dummy_134 x z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0295 (x : Var) (z : Var) : (nb060_alpha_dummy_134 x z) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_134, fv_syn_c1c] using (nb060_compact_fv_empty_0091 x z)

theorem nb060_compact_fv_empty_0092 : (nb060_alpha_dummy_130) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0296 : (nb060_alpha_dummy_130) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_130, fv_syn_c1c] using (nb060_compact_fv_empty_0092)

theorem nb060_compact_fv_empty_0093 (x : Var) (z : Var) : (nb060_alpha_dummy_133 x z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0297 (x : Var) (z : Var) : (nb060_alpha_dummy_133 x z) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_133, fv_syn_c1c] using (nb060_compact_fv_empty_0093 x z)

theorem nb060_compact_fv_empty_0094 : (nb060_alpha_dummy_129) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0298 : (nb060_alpha_dummy_129) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_129, fv_syn_c1c] using (nb060_compact_fv_empty_0094)

theorem nb060_compact_fv_empty_0095 (x : Var) (z : Var) : (nb060_alpha_dummy_132 x z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0299 (x : Var) (z : Var) : (nb060_alpha_dummy_132 x z) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_132, fv_syn_c1c] using (nb060_compact_fv_empty_0095 x z)

theorem nb060_compact_fv_empty_0096 : (nb060_alpha_dummy_127) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0300 : (nb060_alpha_dummy_127) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_127, fv_syn_c1c] using (nb060_compact_fv_empty_0096)

theorem nb060_compact_fv_empty_0097 (x : Var) (z : Var) : (nb060_alpha_dummy_128 x z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0301 (x : Var) (z : Var) : (nb060_alpha_dummy_128 x z) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_128, fv_syn_c1c] using (nb060_compact_fv_empty_0097 x z)

theorem nb060_compact_fv_empty_0098 : (nb060_alpha_dummy_123) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0302 : (nb060_alpha_dummy_123) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_123, fv_syn_c1c] using (nb060_compact_fv_empty_0098)

theorem nb060_compact_fv_empty_0099 (x : Var) (z : Var) : (nb060_alpha_dummy_125 x z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0303 (x : Var) (z : Var) : (nb060_alpha_dummy_125 x z) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_125, fv_syn_c1c] using (nb060_compact_fv_empty_0099 x z)

theorem nb060_compact_fv_empty_0100 : (nb060_alpha_dummy_124) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0304 : (nb060_alpha_dummy_124) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_124, fv_syn_c1c] using (nb060_compact_fv_empty_0100)

theorem nb060_compact_fv_empty_0101 (x : Var) (z : Var) : (nb060_alpha_dummy_126 x z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0305 (x : Var) (z : Var) : (nb060_alpha_dummy_126 x z) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_126, fv_syn_c1c] using (nb060_compact_fv_empty_0101 x z)

theorem nb060_compact_fv_empty_0102 : (nb060_alpha_dummy_116) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0306 : (nb060_alpha_dummy_116) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_116, fv_syn_c1c] using (nb060_compact_fv_empty_0102)

theorem nb060_compact_fv_empty_0103 (x : Var) (z : Var) : (nb060_alpha_dummy_118 x z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0307 (x : Var) (z : Var) : (nb060_alpha_dummy_118 x z) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_118, fv_syn_c1c] using (nb060_compact_fv_empty_0103 x z)

theorem nb060_compact_fv_empty_0104 : (nb060_alpha_dummy_115) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0308 : (nb060_alpha_dummy_115) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_115, fv_syn_c1c] using (nb060_compact_fv_empty_0104)

theorem nb060_compact_fv_empty_0105 (x : Var) (z : Var) : (nb060_alpha_dummy_117 x z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0309 (x : Var) (z : Var) : (nb060_alpha_dummy_117 x z) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_117, fv_syn_c1c] using (nb060_compact_fv_empty_0105 x z)

theorem nb060_compact_fv_empty_0106 : (nb060_alpha_dummy_121) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0310 : (nb060_alpha_dummy_121) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_121, fv_syn_c1c] using (nb060_compact_fv_empty_0106)

theorem nb060_compact_fv_empty_0107 (x : Var) (z : Var) : (nb060_alpha_dummy_122 x z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0311 (x : Var) (z : Var) : (nb060_alpha_dummy_122 x z) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_122, fv_syn_c1c] using (nb060_compact_fv_empty_0107 x z)

theorem nb060_compact_fv_empty_0108 : (nb060_alpha_dummy_119) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0312 : (nb060_alpha_dummy_119) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_119, fv_syn_c1c] using (nb060_compact_fv_empty_0108)

theorem nb060_compact_fv_empty_0109 (x : Var) (z : Var) : (nb060_alpha_dummy_120 x z) ∉ (∅ : Finset Var) := by
  intro hmem
  cases hmem

theorem nb060_wpp_notmem_0313 (x : Var) (z : Var) : (nb060_alpha_dummy_120 x z) ∉ ((syn_c1c)).fv := by
  simpa only [nb060_alpha_dummy_120, fv_syn_c1c] using (nb060_compact_fv_empty_0109 x z)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
